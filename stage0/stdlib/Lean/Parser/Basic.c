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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t l_Lean_Syntax_isAntiquots(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
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
lean_object* v_stxStack_639_; lean_object* v_pos_640_; uint8_t v___x_641_; uint8_t v___x_642_; 
v_stxStack_639_ = lean_ctor_get(v_s_637_, 0);
lean_inc_ref(v_stxStack_639_);
v_pos_640_ = lean_ctor_get(v_s_637_, 2);
lean_inc(v_pos_640_);
v___x_641_ = 0;
v___x_642_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_632_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_643_ = l_Lean_Parser_ParserState_stackSize(v_s_637_);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_iniSz_636_, v___x_644_);
v___x_646_ = lean_nat_dec_eq(v___x_643_, v___x_645_);
lean_dec(v___x_643_);
if (v___x_646_ == 0)
{
lean_dec(v___x_645_);
lean_dec(v_pos_640_);
lean_dec_ref(v_stxStack_639_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
else
{
lean_object* v_pBack_647_; uint8_t v___x_648_; 
v_pBack_647_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_639_);
lean_dec_ref(v_stxStack_639_);
lean_inc(v_pBack_647_);
v___x_648_ = l_Lean_Syntax_isAntiquots(v_pBack_647_);
if (v___x_648_ == 0)
{
lean_dec(v_pBack_647_);
lean_dec(v___x_645_);
lean_dec(v_pos_640_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
else
{
lean_object* v_s_649_; lean_object* v_s_650_; lean_object* v_stxStack_654_; lean_object* v_pos_655_; lean_object* v_errorMsg_656_; uint8_t v___x_657_; 
v_s_649_ = l_Lean_Parser_ParserState_restore(v_s_637_, v_iniSz_636_, v_pos_635_);
v_s_650_ = lean_apply_2(v_q_631_, v_c_633_, v_s_649_);
v_stxStack_654_ = lean_ctor_get(v_s_650_, 0);
lean_inc_ref(v_stxStack_654_);
v_pos_655_ = lean_ctor_get(v_s_650_, 2);
lean_inc(v_pos_655_);
v_errorMsg_656_ = lean_ctor_get(v_s_650_, 4);
lean_inc(v_errorMsg_656_);
v___x_657_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_656_, v_errorMsg_638_);
lean_dec(v_errorMsg_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_pos_655_);
lean_dec_ref(v_stxStack_654_);
lean_dec(v___x_645_);
v___x_658_ = l_Lean_Parser_ParserState_restore(v_s_650_, v_iniSz_636_, v_pos_640_);
lean_dec(v_iniSz_636_);
v___x_659_ = l_Lean_Parser_ParserState_pushSyntax(v___x_658_, v_pBack_647_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_nat_add(v_pos_640_, v___x_644_);
v___x_661_ = lean_nat_dec_le(v___x_660_, v_pos_655_);
lean_dec(v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_nat_add(v_pos_655_, v___x_644_);
lean_dec(v_pos_655_);
v___x_663_ = lean_nat_dec_le(v___x_662_, v_pos_640_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; uint8_t v___x_665_; 
v___x_664_ = 2;
v___x_665_ = l_Lean_Parser_instBEqOrElseOnAntiquotBehavior_beq(v_antiquotBehavior_632_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec_ref(v_stxStack_654_);
lean_dec(v___x_645_);
goto v___jp_651_;
}
else
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = l_Lean_Parser_ParserState_stackSize(v_s_650_);
v___x_667_ = lean_nat_dec_eq(v___x_666_, v___x_645_);
lean_dec(v___x_645_);
lean_dec(v___x_666_);
if (v___x_667_ == 0)
{
lean_dec_ref(v_stxStack_654_);
goto v___jp_651_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_654_);
lean_dec_ref(v_stxStack_654_);
lean_inc(v___x_668_);
v___x_669_ = l_Lean_Syntax_isAntiquots(v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v___x_668_);
goto v___jp_651_;
}
else
{
lean_object* v_s_670_; lean_object* v_s_671_; lean_object* v_s_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec(v_pos_640_);
v_s_670_ = l_Lean_Parser_ParserState_popSyntax(v_s_650_);
v_s_671_ = l_Lean_Parser_orelseFnCore___lam__0(v_pBack_647_, v_s_670_);
v_s_672_ = l_Lean_Parser_orelseFnCore___lam__0(v___x_668_, v_s_671_);
v___x_673_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_674_ = l_Lean_Parser_ParserState_mkNode(v_s_672_, v___x_673_, v_iniSz_636_);
lean_dec(v_iniSz_636_);
return v___x_674_;
}
}
}
}
else
{
lean_dec_ref(v_stxStack_654_);
lean_dec(v___x_645_);
goto v___jp_651_;
}
}
else
{
lean_dec(v_pos_655_);
lean_dec_ref(v_stxStack_654_);
lean_dec(v_pBack_647_);
lean_dec(v___x_645_);
lean_dec(v_pos_640_);
lean_dec(v_iniSz_636_);
return v_s_650_;
}
}
v___jp_651_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = l_Lean_Parser_ParserState_restore(v_s_650_, v_iniSz_636_, v_pos_640_);
lean_dec(v_iniSz_636_);
v___x_653_ = l_Lean_Parser_ParserState_pushSyntax(v___x_652_, v_pBack_647_);
return v___x_653_;
}
}
}
}
else
{
lean_dec(v_pos_640_);
lean_dec_ref(v_stxStack_639_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
}
else
{
lean_object* v_pos_675_; lean_object* v_val_676_; uint8_t v_decide_677_; 
v_pos_675_ = lean_ctor_get(v_s_637_, 2);
lean_inc(v_pos_675_);
v_val_676_ = lean_ctor_get(v_errorMsg_638_, 0);
lean_inc(v_val_676_);
lean_dec_ref_known(v_errorMsg_638_, 1);
v_decide_677_ = lean_nat_dec_eq(v_pos_675_, v_pos_635_);
lean_dec(v_pos_675_);
if (v_decide_677_ == 0)
{
lean_dec(v_val_676_);
lean_dec(v_iniSz_636_);
lean_dec(v_pos_635_);
lean_dec_ref(v_c_633_);
lean_dec_ref(v_q_631_);
return v_s_637_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
lean_inc(v_pos_635_);
v___x_678_ = l_Lean_Parser_ParserState_restore(v_s_637_, v_iniSz_636_, v_pos_635_);
lean_dec(v_iniSz_636_);
v___x_679_ = lean_apply_2(v_q_631_, v_c_633_, v___x_678_);
v___x_680_ = l_Lean_Parser_mergeOrElseErrors(v___x_679_, v_val_676_, v_pos_635_, v_decide_677_);
lean_dec(v_pos_635_);
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFnCore___boxed(lean_object* v_p_681_, lean_object* v_q_682_, lean_object* v_antiquotBehavior_683_, lean_object* v_c_684_, lean_object* v_s_685_){
_start:
{
uint8_t v_antiquotBehavior_boxed_686_; lean_object* v_res_687_; 
v_antiquotBehavior_boxed_686_ = lean_unbox(v_antiquotBehavior_683_);
v_res_687_ = l_Lean_Parser_orelseFnCore(v_p_681_, v_q_682_, v_antiquotBehavior_boxed_686_, v_c_684_, v_s_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseFn(lean_object* v_p_688_, lean_object* v_q_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
uint8_t v___x_692_; lean_object* v___x_693_; 
v___x_692_ = 2;
v___x_693_ = l_Lean_Parser_orelseFnCore(v_p_688_, v_q_689_, v___x_692_, v_a_690_, v_a_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelseInfo(lean_object* v_p_694_, lean_object* v_q_695_){
_start:
{
lean_object* v_collectTokens_696_; lean_object* v_collectKinds_697_; lean_object* v_firstTokens_698_; lean_object* v_collectTokens_699_; lean_object* v_collectKinds_700_; lean_object* v_firstTokens_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_711_; 
v_collectTokens_696_ = lean_ctor_get(v_p_694_, 0);
lean_inc_ref(v_collectTokens_696_);
v_collectKinds_697_ = lean_ctor_get(v_p_694_, 1);
lean_inc_ref(v_collectKinds_697_);
v_firstTokens_698_ = lean_ctor_get(v_p_694_, 2);
lean_inc(v_firstTokens_698_);
lean_dec_ref(v_p_694_);
v_collectTokens_699_ = lean_ctor_get(v_q_695_, 0);
v_collectKinds_700_ = lean_ctor_get(v_q_695_, 1);
v_firstTokens_701_ = lean_ctor_get(v_q_695_, 2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_q_695_);
if (v_isSharedCheck_711_ == 0)
{
v___x_703_ = v_q_695_;
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_firstTokens_701_);
lean_inc(v_collectKinds_700_);
lean_inc(v_collectTokens_699_);
lean_dec(v_q_695_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_711_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___f_705_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_705_, 0, v_collectKinds_700_);
lean_closure_set(v___f_705_, 1, v_collectKinds_697_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_706_, 0, v_collectTokens_699_);
lean_closure_set(v___f_706_, 1, v_collectTokens_696_);
v___x_707_ = l_Lean_Parser_FirstTokens_merge(v_firstTokens_698_, v_firstTokens_701_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 2, v___x_707_);
lean_ctor_set(v___x_703_, 1, v___f_705_);
lean_ctor_set(v___x_703_, 0, v___f_706_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___f_706_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___f_705_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParserFn___lam__0(lean_object* v_p1_712_, lean_object* v_p2_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_716_ = lean_box(0);
v___x_717_ = lean_apply_1(v_p2_713_, v___x_716_);
v___x_718_ = l_Lean_Parser_orelseFn(v_p1_712_, v___x_717_, v___y_714_, v___y_715_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_orelse(lean_object* v_p_721_, lean_object* v_q_722_){
_start:
{
lean_object* v_info_723_; lean_object* v_fn_724_; lean_object* v_info_725_; lean_object* v_fn_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_735_; 
v_info_723_ = lean_ctor_get(v_p_721_, 0);
lean_inc_ref(v_info_723_);
v_fn_724_ = lean_ctor_get(v_p_721_, 1);
lean_inc_ref(v_fn_724_);
lean_dec_ref(v_p_721_);
v_info_725_ = lean_ctor_get(v_q_722_, 0);
v_fn_726_ = lean_ctor_get(v_q_722_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v_q_722_);
if (v_isSharedCheck_735_ == 0)
{
v___x_728_ = v_q_722_;
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_fn_726_);
lean_inc(v_info_725_);
lean_dec(v_q_722_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_730_ = l_Lean_Parser_orelseInfo(v_info_723_, v_info_725_);
v___x_731_ = lean_alloc_closure((void*)(l_Lean_Parser_orelseFn), 4, 2);
lean_closure_set(v___x_731_, 0, v_fn_724_);
lean_closure_set(v___x_731_, 1, v_fn_726_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_731_);
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1(){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__1));
v___x_744_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___closed__2));
v___x_745_ = l_Lean_addBuiltinDocString(v___x_743_, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1___boxed(lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Parser_Basic_0__Lean_Parser_orelse___regBuiltin_Lean_Parser_orelse_docString__1();
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instOrElseParser___lam__0(lean_object* v_a_748_, lean_object* v_b_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_box(0);
v___x_751_ = lean_apply_1(v_b_749_, v___x_750_);
v___x_752_ = l_Lean_Parser_orelse(v_a_748_, v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_noFirstTokenInfo(lean_object* v_info_755_){
_start:
{
lean_object* v_collectTokens_756_; lean_object* v_collectKinds_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_collectTokens_756_ = lean_ctor_get(v_info_755_, 0);
v_collectKinds_757_ = lean_ctor_get(v_info_755_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_info_755_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_info_755_, 2);
lean_dec(v_unused_766_);
v___x_759_ = v_info_755_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_collectKinds_757_);
lean_inc(v_collectTokens_756_);
lean_dec(v_info_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_box(1);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 2, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_collectTokens_756_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_collectKinds_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomicFn(lean_object* v_p_767_, lean_object* v_c_768_, lean_object* v_s_769_){
_start:
{
lean_object* v_pos_770_; lean_object* v___x_771_; lean_object* v_errorMsg_772_; 
v_pos_770_ = lean_ctor_get(v_s_769_, 2);
lean_inc(v_pos_770_);
v___x_771_ = lean_apply_2(v_p_767_, v_c_768_, v_s_769_);
v_errorMsg_772_ = lean_ctor_get(v___x_771_, 4);
lean_inc(v_errorMsg_772_);
if (lean_obj_tag(v_errorMsg_772_) == 1)
{
lean_object* v_stxStack_773_; lean_object* v_lhsPrec_774_; lean_object* v_cache_775_; lean_object* v_recoveredErrors_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_stxStack_773_ = lean_ctor_get(v___x_771_, 0);
v_lhsPrec_774_ = lean_ctor_get(v___x_771_, 1);
v_cache_775_ = lean_ctor_get(v___x_771_, 3);
v_recoveredErrors_776_ = lean_ctor_get(v___x_771_, 5);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_784_ = lean_ctor_get(v___x_771_, 4);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v___x_771_, 2);
lean_dec(v_unused_785_);
v___x_778_ = v___x_771_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_recoveredErrors_776_);
lean_inc(v_cache_775_);
lean_inc(v_lhsPrec_774_);
lean_inc(v_stxStack_773_);
lean_dec(v___x_771_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 2, v_pos_770_);
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_stxStack_773_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_lhsPrec_774_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_pos_770_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_cache_775_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_errorMsg_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_recoveredErrors_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
lean_dec(v_errorMsg_772_);
lean_dec(v_pos_770_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_atomic(lean_object* v_p_786_){
_start:
{
lean_object* v_info_787_; lean_object* v_fn_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_796_; 
v_info_787_ = lean_ctor_get(v_p_786_, 0);
v_fn_788_ = lean_ctor_get(v_p_786_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_p_786_);
if (v_isSharedCheck_796_ == 0)
{
v___x_790_ = v_p_786_;
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_fn_788_);
lean_inc(v_info_787_);
lean_dec(v_p_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_796_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_794_; 
v___x_792_ = lean_alloc_closure((void*)(l_Lean_Parser_atomicFn), 3, 1);
lean_closure_set(v___x_792_, 0, v_fn_788_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_792_);
v___x_794_ = v___x_790_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_info_787_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1(){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__1));
v___x_805_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___closed__2));
v___x_806_ = l_Lean_addBuiltinDocString(v___x_804_, v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1___boxed(lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Parser_Basic_0__Lean_Parser_atomic___regBuiltin_Lean_Parser_atomic_docString__1();
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqRecoveryContext_beq(lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v_initialPos_811_; lean_object* v_initialSize_812_; lean_object* v_initialPos_813_; lean_object* v_initialSize_814_; uint8_t v_decide_815_; 
v_initialPos_811_ = lean_ctor_get(v_x_809_, 0);
v_initialSize_812_ = lean_ctor_get(v_x_809_, 1);
v_initialPos_813_ = lean_ctor_get(v_x_810_, 0);
v_initialSize_814_ = lean_ctor_get(v_x_810_, 1);
v_decide_815_ = lean_nat_dec_eq(v_initialPos_811_, v_initialPos_813_);
if (v_decide_815_ == 0)
{
return v_decide_815_;
}
else
{
uint8_t v___x_816_; 
v___x_816_ = lean_nat_dec_eq(v_initialSize_812_, v_initialSize_814_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqRecoveryContext_beq___boxed(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Lean_Parser_instBEqRecoveryContext_beq(v_x_817_, v_x_818_);
lean_dec_ref(v_x_818_);
lean_dec_ref(v_x_817_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext_decEq(lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
lean_object* v_initialPos_825_; lean_object* v_initialSize_826_; lean_object* v_initialPos_827_; lean_object* v_initialSize_828_; uint8_t v_decide_829_; 
v_initialPos_825_ = lean_ctor_get(v_x_823_, 0);
v_initialSize_826_ = lean_ctor_get(v_x_823_, 1);
v_initialPos_827_ = lean_ctor_get(v_x_824_, 0);
v_initialSize_828_ = lean_ctor_get(v_x_824_, 1);
v_decide_829_ = lean_nat_dec_eq(v_initialPos_825_, v_initialPos_827_);
if (v_decide_829_ == 0)
{
return v_decide_829_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = lean_nat_dec_eq(v_initialSize_826_, v_initialSize_828_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext_decEq___boxed(lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_831_, v_x_832_);
lean_dec_ref(v_x_832_);
lean_dec_ref(v_x_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instDecidableEqRecoveryContext(lean_object* v_x_835_, lean_object* v_x_836_){
_start:
{
uint8_t v___x_837_; 
v___x_837_ = l_Lean_Parser_instDecidableEqRecoveryContext_decEq(v_x_835_, v_x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instDecidableEqRecoveryContext___boxed(lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
uint8_t v_res_840_; lean_object* v_r_841_; 
v_res_840_ = l_Lean_Parser_instDecidableEqRecoveryContext(v_x_838_, v_x_839_);
lean_dec_ref(v_x_839_);
lean_dec_ref(v_x_838_);
v_r_841_ = lean_box(v_res_840_);
return v_r_841_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_unsigned_to_nat(14u);
v___x_856_ = lean_nat_to_int(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(15u);
v___x_870_ = lean_nat_to_int(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__0));
v___x_872_ = lean_string_length(v___x_871_);
return v___x_872_;
}
}
static lean_object* _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__17);
v___x_874_ = lean_nat_to_int(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___redArg(lean_object* v_x_877_){
_start:
{
lean_object* v_initialPos_878_; lean_object* v_initialSize_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_917_; 
v_initialPos_878_ = lean_ctor_get(v_x_877_, 0);
v_initialSize_879_ = lean_ctor_get(v_x_877_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_917_ == 0)
{
v___x_881_ = v_x_877_;
v_isShared_882_ = v_isSharedCheck_917_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_initialSize_879_);
lean_inc(v_initialPos_878_);
lean_dec(v_x_877_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_917_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_883_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__5));
v___x_884_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__6));
v___x_885_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__7);
v___x_886_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__9));
v___x_887_ = l_Nat_reprFast(v_initialPos_878_);
v___x_888_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
if (v_isShared_882_ == 0)
{
lean_ctor_set_tag(v___x_881_, 5);
lean_ctor_set(v___x_881_, 1, v___x_888_);
lean_ctor_set(v___x_881_, 0, v___x_886_);
v___x_890_ = v___x_881_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_888_);
v___x_890_ = v_reuseFailAlloc_916_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_891_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__11));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_885_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = 0;
v___x_895_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_894_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_884_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__13));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_box(1);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__15));
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_883_);
v___x_904_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__16);
v___x_905_ = l_Nat_reprFast(v_initialSize_879_);
v___x_906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
v___x_907_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_904_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*1, v___x_894_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_903_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18, &l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18_once, _init_l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__18);
v___x_911_ = ((lean_object*)(l_Lean_Parser_instReprRecoveryContext_repr___redArg___closed__19));
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_909_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_891_);
v___x_914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_910_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_894_);
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr(lean_object* v_x_918_, lean_object* v_prec_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_Parser_instReprRecoveryContext_repr___redArg(v_x_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprRecoveryContext_repr___boxed(lean_object* v_x_921_, lean_object* v_prec_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Parser_instReprRecoveryContext_repr(v_x_921_, v_prec_922_);
lean_dec(v_prec_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recoverFn(lean_object* v_p_926_, lean_object* v_recover_927_, lean_object* v_c_928_, lean_object* v_s_929_){
_start:
{
lean_object* v_stxStack_930_; lean_object* v_pos_931_; lean_object* v_s_932_; lean_object* v_errorMsg_933_; 
v_stxStack_930_ = lean_ctor_get(v_s_929_, 0);
lean_inc_ref(v_stxStack_930_);
v_pos_931_ = lean_ctor_get(v_s_929_, 2);
lean_inc(v_pos_931_);
lean_inc_ref(v_c_928_);
v_s_932_ = lean_apply_2(v_p_926_, v_c_928_, v_s_929_);
v_errorMsg_933_ = lean_ctor_get(v_s_932_, 4);
lean_inc(v_errorMsg_933_);
if (lean_obj_tag(v_errorMsg_933_) == 1)
{
lean_object* v_stxStack_934_; lean_object* v_lhsPrec_935_; lean_object* v_pos_936_; lean_object* v_cache_937_; lean_object* v_recoveredErrors_938_; lean_object* v_val_939_; lean_object* v_iniSz_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_s_x27_944_; lean_object* v_stxStack_945_; lean_object* v_pos_946_; lean_object* v_errorMsg_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_958_; 
v_stxStack_934_ = lean_ctor_get(v_s_932_, 0);
lean_inc_ref(v_stxStack_934_);
v_lhsPrec_935_ = lean_ctor_get(v_s_932_, 1);
lean_inc_n(v_lhsPrec_935_, 2);
v_pos_936_ = lean_ctor_get(v_s_932_, 2);
lean_inc(v_pos_936_);
v_cache_937_ = lean_ctor_get(v_s_932_, 3);
lean_inc_ref_n(v_cache_937_, 2);
v_recoveredErrors_938_ = lean_ctor_get(v_s_932_, 5);
lean_inc_ref_n(v_recoveredErrors_938_, 2);
v_val_939_ = lean_ctor_get(v_errorMsg_933_, 0);
lean_inc(v_val_939_);
lean_dec_ref_known(v_errorMsg_933_, 1);
v_iniSz_940_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_930_);
lean_dec_ref(v_stxStack_930_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_pos_931_);
lean_ctor_set(v___x_941_, 1, v_iniSz_940_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_943_, 0, v_stxStack_934_);
lean_ctor_set(v___x_943_, 1, v_lhsPrec_935_);
lean_ctor_set(v___x_943_, 2, v_pos_936_);
lean_ctor_set(v___x_943_, 3, v_cache_937_);
lean_ctor_set(v___x_943_, 4, v___x_942_);
lean_ctor_set(v___x_943_, 5, v_recoveredErrors_938_);
v_s_x27_944_ = lean_apply_3(v_recover_927_, v___x_941_, v_c_928_, v___x_943_);
v_stxStack_945_ = lean_ctor_get(v_s_x27_944_, 0);
v_pos_946_ = lean_ctor_get(v_s_x27_944_, 2);
v_errorMsg_947_ = lean_ctor_get(v_s_x27_944_, 4);
v_isSharedCheck_958_ = !lean_is_exclusive(v_s_x27_944_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; lean_object* v_unused_960_; lean_object* v_unused_961_; 
v_unused_959_ = lean_ctor_get(v_s_x27_944_, 5);
lean_dec(v_unused_959_);
v_unused_960_ = lean_ctor_get(v_s_x27_944_, 3);
lean_dec(v_unused_960_);
v_unused_961_ = lean_ctor_get(v_s_x27_944_, 1);
lean_dec(v_unused_961_);
v___x_949_ = v_s_x27_944_;
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_errorMsg_947_);
lean_inc(v_pos_946_);
lean_inc(v_stxStack_945_);
lean_dec(v_s_x27_944_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_958_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
uint8_t v___x_951_; 
v___x_951_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_947_, v___x_942_);
lean_dec(v_errorMsg_947_);
if (v___x_951_ == 0)
{
lean_del_object(v___x_949_);
lean_dec(v_pos_946_);
lean_dec_ref(v_stxStack_945_);
lean_dec(v_val_939_);
lean_dec_ref(v_recoveredErrors_938_);
lean_dec_ref(v_cache_937_);
lean_dec(v_lhsPrec_935_);
return v_s_932_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
lean_dec_ref(v_s_932_);
lean_inc_ref(v_stxStack_945_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_stxStack_945_);
lean_ctor_set(v___x_952_, 1, v_val_939_);
lean_inc(v_pos_946_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_pos_946_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_array_push(v_recoveredErrors_938_, v___x_953_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 5, v___x_954_);
lean_ctor_set(v___x_949_, 4, v___x_942_);
lean_ctor_set(v___x_949_, 3, v_cache_937_);
lean_ctor_set(v___x_949_, 1, v_lhsPrec_935_);
v___x_956_ = v___x_949_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_stxStack_945_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_lhsPrec_935_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_pos_946_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_cache_937_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_957_, 5, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_dec(v_errorMsg_933_);
lean_dec(v_pos_931_);
lean_dec_ref(v_stxStack_930_);
lean_dec_ref(v_c_928_);
lean_dec_ref(v_recover_927_);
return v_s_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27___lam__0(lean_object* v_handler_962_, lean_object* v_s_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_966_; lean_object* v_fn_967_; lean_object* v___x_968_; 
v___x_966_ = lean_apply_1(v_handler_962_, v_s_963_);
v_fn_967_ = lean_ctor_get(v___x_966_, 1);
lean_inc_ref(v_fn_967_);
lean_dec_ref(v___x_966_);
v___x_968_ = lean_apply_2(v_fn_967_, v___y_964_, v___y_965_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover_x27(lean_object* v_parser_969_, lean_object* v_handler_970_){
_start:
{
lean_object* v_info_971_; lean_object* v_fn_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_981_; 
v_info_971_ = lean_ctor_get(v_parser_969_, 0);
v_fn_972_ = lean_ctor_get(v_parser_969_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_parser_969_);
if (v_isSharedCheck_981_ == 0)
{
v___x_974_ = v_parser_969_;
v_isShared_975_ = v_isSharedCheck_981_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_fn_972_);
lean_inc(v_info_971_);
lean_dec(v_parser_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_981_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___f_976_; lean_object* v___x_977_; lean_object* v___x_979_; 
v___f_976_ = lean_alloc_closure((void*)(l_Lean_Parser_recover_x27___lam__0), 4, 1);
lean_closure_set(v___f_976_, 0, v_handler_970_);
v___x_977_ = lean_alloc_closure((void*)(l_Lean_Parser_recoverFn), 4, 2);
lean_closure_set(v___x_977_, 0, v_fn_972_);
lean_closure_set(v___x_977_, 1, v___f_976_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v___x_977_);
v___x_979_ = v___x_974_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_info_971_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1(){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__1));
v___x_990_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___closed__2));
v___x_991_ = l_Lean_addBuiltinDocString(v___x_989_, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1___boxed(lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover_x27___regBuiltin_Lean_Parser_recover_x27_docString__1();
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0(lean_object* v_handler_994_, lean_object* v_x_995_){
_start:
{
lean_inc_ref(v_handler_994_);
return v_handler_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover___lam__0___boxed(lean_object* v_handler_996_, lean_object* v_x_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Parser_recover___lam__0(v_handler_996_, v_x_997_);
lean_dec_ref(v_x_997_);
lean_dec_ref(v_handler_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_recover(lean_object* v_parser_999_, lean_object* v_handler_1000_){
_start:
{
lean_object* v___f_1001_; lean_object* v___x_1002_; 
v___f_1001_ = lean_alloc_closure((void*)(l_Lean_Parser_recover___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1001_, 0, v_handler_1000_);
v___x_1002_ = l_Lean_Parser_recover_x27(v_parser_999_, v___f_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1(){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__1));
v___x_1011_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___closed__2));
v___x_1012_ = l_Lean_addBuiltinDocString(v___x_1010_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1___boxed(lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Parser_Basic_0__Lean_Parser_recover___regBuiltin_Lean_Parser_recover_docString__1();
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalFn(lean_object* v_p_1018_, lean_object* v_c_1019_, lean_object* v_s_1020_){
_start:
{
lean_object* v_pos_1021_; lean_object* v_iniSz_1022_; lean_object* v___y_1024_; lean_object* v_s_1027_; lean_object* v_pos_1028_; lean_object* v_errorMsg_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_pos_1021_ = lean_ctor_get(v_s_1020_, 2);
lean_inc(v_pos_1021_);
v_iniSz_1022_ = l_Lean_Parser_ParserState_stackSize(v_s_1020_);
v_s_1027_ = lean_apply_2(v_p_1018_, v_c_1019_, v_s_1020_);
v_pos_1028_ = lean_ctor_get(v_s_1027_, 2);
lean_inc(v_pos_1028_);
v_errorMsg_1029_ = lean_ctor_get(v_s_1027_, 4);
lean_inc(v_errorMsg_1029_);
v___x_1030_ = lean_box(0);
v___x_1031_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1029_, v___x_1030_);
lean_dec(v_errorMsg_1029_);
if (v___x_1031_ == 0)
{
uint8_t v_decide_1032_; 
v_decide_1032_ = lean_nat_dec_eq(v_pos_1028_, v_pos_1021_);
lean_dec(v_pos_1028_);
if (v_decide_1032_ == 0)
{
lean_dec(v_pos_1021_);
v___y_1024_ = v_s_1027_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Parser_ParserState_restore(v_s_1027_, v_iniSz_1022_, v_pos_1021_);
v___y_1024_ = v___x_1033_;
goto v___jp_1023_;
}
}
else
{
lean_dec(v_pos_1028_);
lean_dec(v_pos_1021_);
v___y_1024_ = v_s_1027_;
goto v___jp_1023_;
}
v___jp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1026_ = l_Lean_Parser_ParserState_mkNode(v___y_1024_, v___x_1025_, v_iniSz_1022_);
lean_dec(v_iniSz_1022_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalInfo(lean_object* v_p_1034_){
_start:
{
lean_object* v_collectTokens_1035_; lean_object* v_collectKinds_1036_; lean_object* v_firstTokens_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1045_; 
v_collectTokens_1035_ = lean_ctor_get(v_p_1034_, 0);
v_collectKinds_1036_ = lean_ctor_get(v_p_1034_, 1);
v_firstTokens_1037_ = lean_ctor_get(v_p_1034_, 2);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_p_1034_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1039_ = v_p_1034_;
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_firstTokens_1037_);
lean_inc(v_collectKinds_1036_);
lean_inc(v_collectTokens_1035_);
lean_dec(v_p_1034_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = l_Lean_Parser_FirstTokens_toOptional(v_firstTokens_1037_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 2, v___x_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_collectTokens_1035_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_collectKinds_1036_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_optionalNoAntiquot(lean_object* v_p_1046_){
_start:
{
lean_object* v_info_1047_; lean_object* v_fn_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1057_; 
v_info_1047_ = lean_ctor_get(v_p_1046_, 0);
v_fn_1048_ = lean_ctor_get(v_p_1046_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_p_1046_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1050_ = v_p_1046_;
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_fn_1048_);
lean_inc(v_info_1047_);
lean_dec(v_p_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = l_Lean_Parser_optionalInfo(v_info_1047_);
v___x_1053_ = lean_alloc_closure((void*)(l_Lean_Parser_optionalFn), 3, 1);
lean_closure_set(v___x_1053_, 0, v_fn_1048_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1053_);
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookaheadFn(lean_object* v_p_1058_, lean_object* v_c_1059_, lean_object* v_s_1060_){
_start:
{
lean_object* v_pos_1061_; lean_object* v_iniSz_1062_; lean_object* v_s_1063_; lean_object* v_errorMsg_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_pos_1061_ = lean_ctor_get(v_s_1060_, 2);
lean_inc(v_pos_1061_);
v_iniSz_1062_ = l_Lean_Parser_ParserState_stackSize(v_s_1060_);
v_s_1063_ = lean_apply_2(v_p_1058_, v_c_1059_, v_s_1060_);
v_errorMsg_1064_ = lean_ctor_get(v_s_1063_, 4);
lean_inc(v_errorMsg_1064_);
v___x_1065_ = lean_box(0);
v___x_1066_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1064_, v___x_1065_);
lean_dec(v_errorMsg_1064_);
if (v___x_1066_ == 0)
{
lean_dec(v_iniSz_1062_);
lean_dec(v_pos_1061_);
return v_s_1063_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Parser_ParserState_restore(v_s_1063_, v_iniSz_1062_, v_pos_1061_);
lean_dec(v_iniSz_1062_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_lookahead(lean_object* v_p_1068_){
_start:
{
lean_object* v_info_1069_; lean_object* v_fn_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_info_1069_ = lean_ctor_get(v_p_1068_, 0);
v_fn_1070_ = lean_ctor_get(v_p_1068_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_p_1068_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v_p_1068_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_fn_1070_);
lean_inc(v_info_1069_);
lean_dec(v_p_1068_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_alloc_closure((void*)(l_Lean_Parser_lookaheadFn), 3, 1);
lean_closure_set(v___x_1074_, 0, v_fn_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_info_1069_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1(){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__1));
v___x_1087_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___closed__2));
v___x_1088_ = l_Lean_addBuiltinDocString(v___x_1086_, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1___boxed(lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_Lean_Parser_Basic_0__Lean_Parser_lookahead___regBuiltin_Lean_Parser_lookahead_docString__1();
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn(lean_object* v_p_1092_, lean_object* v_msg_1093_, lean_object* v_c_1094_, lean_object* v_s_1095_){
_start:
{
lean_object* v_pos_1096_; lean_object* v_iniSz_1097_; lean_object* v_s_1098_; lean_object* v_errorMsg_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_pos_1096_ = lean_ctor_get(v_s_1095_, 2);
lean_inc(v_pos_1096_);
v_iniSz_1097_ = l_Lean_Parser_ParserState_stackSize(v_s_1095_);
v_s_1098_ = lean_apply_2(v_p_1092_, v_c_1094_, v_s_1095_);
v_errorMsg_1099_ = lean_ctor_get(v_s_1098_, 4);
lean_inc(v_errorMsg_1099_);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1099_, v___x_1100_);
lean_dec(v_errorMsg_1099_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_Parser_ParserState_restore(v_s_1098_, v_iniSz_1097_, v_pos_1096_);
lean_dec(v_iniSz_1097_);
return v___x_1102_;
}
else
{
lean_object* v_s_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_s_1103_ = l_Lean_Parser_ParserState_restore(v_s_1098_, v_iniSz_1097_, v_pos_1096_);
lean_dec(v_iniSz_1097_);
v___x_1104_ = ((lean_object*)(l_Lean_Parser_notFollowedByFn___closed__0));
v___x_1105_ = lean_string_append(v___x_1104_, v_msg_1093_);
v___x_1106_ = lean_box(0);
v___x_1107_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1103_, v___x_1105_, v___x_1106_, v___x_1101_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedByFn___boxed(lean_object* v_p_1108_, lean_object* v_msg_1109_, lean_object* v_c_1110_, lean_object* v_s_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Parser_notFollowedByFn(v_p_1108_, v_msg_1109_, v_c_1110_, v_s_1111_);
lean_dec_ref(v_msg_1109_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_notFollowedBy(lean_object* v_p_1113_, lean_object* v_msg_1114_){
_start:
{
lean_object* v_fn_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1124_; 
v_fn_1115_ = lean_ctor_get(v_p_1113_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_p_1113_);
if (v_isSharedCheck_1124_ == 0)
{
lean_object* v_unused_1125_; 
v_unused_1125_ = lean_ctor_get(v_p_1113_, 0);
lean_dec(v_unused_1125_);
v___x_1117_ = v_p_1113_;
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_fn_1115_);
lean_dec(v_p_1113_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1124_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1119_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1120_ = lean_alloc_closure((void*)(l_Lean_Parser_notFollowedByFn___boxed), 4, 2);
lean_closure_set(v___x_1120_, 0, v_fn_1115_);
lean_closure_set(v___x_1120_, 1, v_msg_1114_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 1, v___x_1120_);
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1119_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1(){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__1));
v___x_1134_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___closed__2));
v___x_1135_ = l_Lean_addBuiltinDocString(v___x_1133_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1___boxed(lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Lean_Parser_Basic_0__Lean_Parser_notFollowedBy___regBuiltin_Lean_Parser_notFollowedBy_docString__1();
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyAux(lean_object* v_p_1139_, lean_object* v_c_1140_, lean_object* v_s_1141_){
_start:
{
lean_object* v_pos_1142_; lean_object* v_iniSz_1143_; lean_object* v_s_1144_; lean_object* v_pos_1145_; lean_object* v_errorMsg_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_pos_1142_ = lean_ctor_get(v_s_1141_, 2);
lean_inc(v_pos_1142_);
v_iniSz_1143_ = l_Lean_Parser_ParserState_stackSize(v_s_1141_);
lean_inc_ref(v_p_1139_);
lean_inc_ref(v_c_1140_);
v_s_1144_ = lean_apply_2(v_p_1139_, v_c_1140_, v_s_1141_);
v_pos_1145_ = lean_ctor_get(v_s_1144_, 2);
lean_inc(v_pos_1145_);
v_errorMsg_1146_ = lean_ctor_get(v_s_1144_, 4);
lean_inc(v_errorMsg_1146_);
v___x_1147_ = lean_box(0);
v___x_1148_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1146_, v___x_1147_);
lean_dec(v_errorMsg_1146_);
if (v___x_1148_ == 0)
{
uint8_t v_decide_1149_; 
lean_dec_ref(v_c_1140_);
lean_dec_ref(v_p_1139_);
v_decide_1149_ = lean_nat_dec_eq(v_pos_1142_, v_pos_1145_);
lean_dec(v_pos_1145_);
if (v_decide_1149_ == 0)
{
lean_dec(v_iniSz_1143_);
lean_dec(v_pos_1142_);
return v_s_1144_;
}
else
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Parser_ParserState_restore(v_s_1144_, v_iniSz_1143_, v_pos_1142_);
lean_dec(v_iniSz_1143_);
return v___x_1150_;
}
}
else
{
uint8_t v_decide_1151_; 
v_decide_1151_ = lean_nat_dec_eq(v_pos_1142_, v_pos_1145_);
lean_dec(v_pos_1145_);
lean_dec(v_pos_1142_);
if (v_decide_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_add(v_iniSz_1143_, v___x_1152_);
v___x_1154_ = l_Lean_Parser_ParserState_stackSize(v_s_1144_);
v___x_1155_ = lean_nat_dec_lt(v___x_1153_, v___x_1154_);
lean_dec(v___x_1154_);
lean_dec(v___x_1153_);
if (v___x_1155_ == 0)
{
lean_dec(v_iniSz_1143_);
v_s_1141_ = v_s_1144_;
goto _start;
}
else
{
lean_object* v___x_1157_; lean_object* v_s_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1158_ = l_Lean_Parser_ParserState_mkNode(v_s_1144_, v___x_1157_, v_iniSz_1143_);
lean_dec(v_iniSz_1143_);
v_s_1141_ = v_s_1158_;
goto _start;
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_iniSz_1143_);
lean_dec_ref(v_c_1140_);
lean_dec_ref(v_p_1139_);
v___x_1160_ = ((lean_object*)(l_Lean_Parser_manyAux___closed__0));
v___x_1161_ = lean_box(0);
v___x_1162_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1144_, v___x_1160_, v___x_1161_, v___x_1148_);
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyFn(lean_object* v_p_1163_, lean_object* v_c_1164_, lean_object* v_s_1165_){
_start:
{
lean_object* v_iniSz_1166_; lean_object* v_s_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v_iniSz_1166_ = l_Lean_Parser_ParserState_stackSize(v_s_1165_);
v_s_1167_ = l_Lean_Parser_manyAux(v_p_1163_, v_c_1164_, v_s_1165_);
v___x_1168_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1169_ = l_Lean_Parser_ParserState_mkNode(v_s_1167_, v___x_1168_, v_iniSz_1166_);
lean_dec(v_iniSz_1166_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_manyNoAntiquot(lean_object* v_p_1170_){
_start:
{
lean_object* v_info_1171_; lean_object* v_fn_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
v_info_1171_ = lean_ctor_get(v_p_1170_, 0);
v_fn_1172_ = lean_ctor_get(v_p_1170_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_p_1170_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v_p_1170_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_fn_1172_);
lean_inc(v_info_1171_);
lean_dec(v_p_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = l_Lean_Parser_noFirstTokenInfo(v_info_1171_);
v___x_1177_ = lean_alloc_closure((void*)(l_Lean_Parser_manyFn), 3, 1);
lean_closure_set(v___x_1177_, 0, v_fn_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v___x_1177_);
lean_ctor_set(v___x_1174_, 0, v___x_1176_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Fn(lean_object* v_p_1182_, lean_object* v_c_1183_, lean_object* v_s_1184_){
_start:
{
lean_object* v_iniSz_1185_; lean_object* v___x_1186_; lean_object* v_s_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_iniSz_1185_ = l_Lean_Parser_ParserState_stackSize(v_s_1184_);
lean_inc_ref(v_p_1182_);
v___x_1186_ = lean_alloc_closure((void*)(l_Lean_Parser_manyAux), 3, 1);
lean_closure_set(v___x_1186_, 0, v_p_1182_);
v_s_1187_ = l_Lean_Parser_andthenFn(v_p_1182_, v___x_1186_, v_c_1183_, v_s_1184_);
v___x_1188_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1189_ = l_Lean_Parser_ParserState_mkNode(v_s_1187_, v___x_1188_, v_iniSz_1185_);
lean_dec(v_iniSz_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1NoAntiquot(lean_object* v_p_1190_){
_start:
{
lean_object* v_info_1191_; lean_object* v_fn_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_info_1191_ = lean_ctor_get(v_p_1190_, 0);
v_fn_1192_ = lean_ctor_get(v_p_1190_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_p_1190_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v_p_1190_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_fn_1192_);
lean_inc(v_info_1191_);
lean_dec(v_p_1190_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_alloc_closure((void*)(l_Lean_Parser_many1Fn), 3, 1);
lean_closure_set(v___x_1196_, 0, v_fn_1192_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_info_1191_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(lean_object* v_p_1201_, lean_object* v_sep_1202_, uint8_t v_allowTrailingSep_1203_, lean_object* v_iniSz_1204_, uint8_t v_pOpt_1205_, lean_object* v_c_1206_, lean_object* v_s_1207_){
_start:
{
lean_object* v_s_1209_; lean_object* v_pos_1210_; lean_object* v_pos_1227_; lean_object* v_sz_1228_; lean_object* v_s_1229_; lean_object* v_pos_1230_; lean_object* v_errorMsg_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_pos_1227_ = lean_ctor_get(v_s_1207_, 2);
lean_inc(v_pos_1227_);
v_sz_1228_ = l_Lean_Parser_ParserState_stackSize(v_s_1207_);
lean_inc_ref(v_p_1201_);
lean_inc_ref(v_c_1206_);
v_s_1229_ = lean_apply_2(v_p_1201_, v_c_1206_, v_s_1207_);
v_pos_1230_ = lean_ctor_get(v_s_1229_, 2);
lean_inc(v_pos_1230_);
v_errorMsg_1231_ = lean_ctor_get(v_s_1229_, 4);
lean_inc(v_errorMsg_1231_);
v___x_1232_ = lean_box(0);
v___x_1233_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1231_, v___x_1232_);
lean_dec(v_errorMsg_1231_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
lean_dec_ref(v_c_1206_);
lean_dec_ref(v_sep_1202_);
lean_dec_ref(v_p_1201_);
v___x_1234_ = lean_unsigned_to_nat(1u);
v___x_1235_ = lean_nat_add(v_pos_1227_, v___x_1234_);
v___x_1236_ = lean_nat_dec_le(v___x_1235_, v_pos_1230_);
lean_dec(v_pos_1230_);
lean_dec(v___x_1235_);
if (v___x_1236_ == 0)
{
if (v_pOpt_1205_ == 0)
{
lean_object* v___x_1237_; lean_object* v_s_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_sz_1228_);
lean_dec(v_pos_1227_);
v___x_1237_ = lean_box(0);
v_s_1238_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1229_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1240_ = l_Lean_Parser_ParserState_mkNode(v_s_1238_, v___x_1239_, v_iniSz_1204_);
return v___x_1240_;
}
else
{
lean_object* v_s_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_s_1241_ = l_Lean_Parser_ParserState_restore(v_s_1229_, v_sz_1228_, v_pos_1227_);
lean_dec(v_sz_1228_);
v___x_1242_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1243_ = l_Lean_Parser_ParserState_mkNode(v_s_1241_, v___x_1242_, v_iniSz_1204_);
return v___x_1243_;
}
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_dec(v_sz_1228_);
lean_dec(v_pos_1227_);
v___x_1244_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1245_ = l_Lean_Parser_ParserState_mkNode(v_s_1229_, v___x_1244_, v_iniSz_1204_);
return v___x_1245_;
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
lean_dec(v_pos_1227_);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_sz_1228_, v___x_1246_);
v___x_1248_ = l_Lean_Parser_ParserState_stackSize(v_s_1229_);
v___x_1249_ = lean_nat_dec_lt(v___x_1247_, v___x_1248_);
lean_dec(v___x_1248_);
lean_dec(v___x_1247_);
if (v___x_1249_ == 0)
{
lean_dec(v_sz_1228_);
v_s_1209_ = v_s_1229_;
v_pos_1210_ = v_pos_1230_;
goto v___jp_1208_;
}
else
{
lean_object* v___x_1250_; lean_object* v_s_1251_; lean_object* v_pos_1252_; 
lean_dec(v_pos_1230_);
v___x_1250_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1251_ = l_Lean_Parser_ParserState_mkNode(v_s_1229_, v___x_1250_, v_sz_1228_);
lean_dec(v_sz_1228_);
v_pos_1252_ = lean_ctor_get(v_s_1251_, 2);
lean_inc(v_pos_1252_);
v_s_1209_ = v_s_1251_;
v_pos_1210_ = v_pos_1252_;
goto v___jp_1208_;
}
}
v___jp_1208_:
{
lean_object* v_sz_1211_; lean_object* v_s_1212_; lean_object* v_errorMsg_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v_sz_1211_ = l_Lean_Parser_ParserState_stackSize(v_s_1209_);
lean_inc_ref(v_sep_1202_);
lean_inc_ref(v_c_1206_);
v_s_1212_ = lean_apply_2(v_sep_1202_, v_c_1206_, v_s_1209_);
v_errorMsg_1213_ = lean_ctor_get(v_s_1212_, 4);
lean_inc(v_errorMsg_1213_);
v___x_1214_ = lean_box(0);
v___x_1215_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1213_, v___x_1214_);
lean_dec(v_errorMsg_1213_);
if (v___x_1215_ == 0)
{
lean_object* v_s_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v_c_1206_);
lean_dec_ref(v_sep_1202_);
lean_dec_ref(v_p_1201_);
v_s_1216_ = l_Lean_Parser_ParserState_restore(v_s_1212_, v_sz_1211_, v_pos_1210_);
lean_dec(v_sz_1211_);
v___x_1217_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_1218_ = l_Lean_Parser_ParserState_mkNode(v_s_1216_, v___x_1217_, v_iniSz_1204_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
lean_dec(v_pos_1210_);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_add(v_sz_1211_, v___x_1219_);
v___x_1221_ = l_Lean_Parser_ParserState_stackSize(v_s_1212_);
v___x_1222_ = lean_nat_dec_lt(v___x_1220_, v___x_1221_);
lean_dec(v___x_1221_);
lean_dec(v___x_1220_);
if (v___x_1222_ == 0)
{
lean_dec(v_sz_1211_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1203_;
lean_object* _tmp_6 = v_s_1212_;
v_pOpt_1205_ = _tmp_4;
v_s_1207_ = _tmp_6;
}
goto _start;
}
else
{
lean_object* v___x_1224_; lean_object* v_s_1225_; 
v___x_1224_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v_s_1225_ = l_Lean_Parser_ParserState_mkNode(v_s_1212_, v___x_1224_, v_sz_1211_);
lean_dec(v_sz_1211_);
{
uint8_t _tmp_4 = v_allowTrailingSep_1203_;
lean_object* _tmp_6 = v_s_1225_;
v_pOpt_1205_ = _tmp_4;
v_s_1207_ = _tmp_6;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse___boxed(lean_object* v_p_1253_, lean_object* v_sep_1254_, lean_object* v_allowTrailingSep_1255_, lean_object* v_iniSz_1256_, lean_object* v_pOpt_1257_, lean_object* v_c_1258_, lean_object* v_s_1259_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1260_; uint8_t v_pOpt_boxed_1261_; lean_object* v_res_1262_; 
v_allowTrailingSep_boxed_1260_ = lean_unbox(v_allowTrailingSep_1255_);
v_pOpt_boxed_1261_ = lean_unbox(v_pOpt_1257_);
v_res_1262_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1253_, v_sep_1254_, v_allowTrailingSep_boxed_1260_, v_iniSz_1256_, v_pOpt_boxed_1261_, v_c_1258_, v_s_1259_);
lean_dec(v_iniSz_1256_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(lean_object* v_p_1263_, lean_object* v_sep_1264_, uint8_t v_allowTrailingSep_1265_, lean_object* v_iniSz_1266_, uint8_t v_pOpt_1267_, lean_object* v_c_1268_, lean_object* v_s_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1263_, v_sep_1264_, v_allowTrailingSep_1265_, v_iniSz_1266_, v_pOpt_1267_, v_c_1268_, v_s_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux___boxed(lean_object* v_p_1271_, lean_object* v_sep_1272_, lean_object* v_allowTrailingSep_1273_, lean_object* v_iniSz_1274_, lean_object* v_pOpt_1275_, lean_object* v_c_1276_, lean_object* v_s_1277_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1278_; uint8_t v_pOpt_boxed_1279_; lean_object* v_res_1280_; 
v_allowTrailingSep_boxed_1278_ = lean_unbox(v_allowTrailingSep_1273_);
v_pOpt_boxed_1279_ = lean_unbox(v_pOpt_1275_);
v_res_1280_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux(v_p_1271_, v_sep_1272_, v_allowTrailingSep_boxed_1278_, v_iniSz_1274_, v_pOpt_boxed_1279_, v_c_1276_, v_s_1277_);
lean_dec(v_iniSz_1274_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn(uint8_t v_allowTrailingSep_1281_, lean_object* v_p_1282_, lean_object* v_sep_1283_, lean_object* v_c_1284_, lean_object* v_s_1285_){
_start:
{
lean_object* v_iniSz_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; 
v_iniSz_1286_ = l_Lean_Parser_ParserState_stackSize(v_s_1285_);
v___x_1287_ = 1;
v___x_1288_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1282_, v_sep_1283_, v_allowTrailingSep_1281_, v_iniSz_1286_, v___x_1287_, v_c_1284_, v_s_1285_);
lean_dec(v_iniSz_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByFn___boxed(lean_object* v_allowTrailingSep_1289_, lean_object* v_p_1290_, lean_object* v_sep_1291_, lean_object* v_c_1292_, lean_object* v_s_1293_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1294_; lean_object* v_res_1295_; 
v_allowTrailingSep_boxed_1294_ = lean_unbox(v_allowTrailingSep_1289_);
v_res_1295_ = l_Lean_Parser_sepByFn(v_allowTrailingSep_boxed_1294_, v_p_1290_, v_sep_1291_, v_c_1292_, v_s_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn(uint8_t v_allowTrailingSep_1296_, lean_object* v_p_1297_, lean_object* v_sep_1298_, lean_object* v_c_1299_, lean_object* v_s_1300_){
_start:
{
lean_object* v_iniSz_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; 
v_iniSz_1301_ = l_Lean_Parser_ParserState_stackSize(v_s_1300_);
v___x_1302_ = 0;
v___x_1303_ = l___private_Lean_Parser_Basic_0__Lean_Parser_sepByFnAux_parse(v_p_1297_, v_sep_1298_, v_allowTrailingSep_1296_, v_iniSz_1301_, v___x_1302_, v_c_1299_, v_s_1300_);
lean_dec(v_iniSz_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Fn___boxed(lean_object* v_allowTrailingSep_1304_, lean_object* v_p_1305_, lean_object* v_sep_1306_, lean_object* v_c_1307_, lean_object* v_s_1308_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1309_; lean_object* v_res_1310_; 
v_allowTrailingSep_boxed_1309_ = lean_unbox(v_allowTrailingSep_1304_);
v_res_1310_ = l_Lean_Parser_sepBy1Fn(v_allowTrailingSep_boxed_1309_, v_p_1305_, v_sep_1306_, v_c_1307_, v_s_1308_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByInfo(lean_object* v_p_1311_, lean_object* v_sep_1312_){
_start:
{
lean_object* v_collectTokens_1313_; lean_object* v_collectKinds_1314_; lean_object* v_collectTokens_1315_; lean_object* v_collectKinds_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1326_; 
v_collectTokens_1313_ = lean_ctor_get(v_p_1311_, 0);
lean_inc_ref(v_collectTokens_1313_);
v_collectKinds_1314_ = lean_ctor_get(v_p_1311_, 1);
lean_inc_ref(v_collectKinds_1314_);
lean_dec_ref(v_p_1311_);
v_collectTokens_1315_ = lean_ctor_get(v_sep_1312_, 0);
v_collectKinds_1316_ = lean_ctor_get(v_sep_1312_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_sep_1312_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v_sep_1312_, 2);
lean_dec(v_unused_1327_);
v___x_1318_ = v_sep_1312_;
v_isShared_1319_ = v_isSharedCheck_1326_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_collectKinds_1316_);
lean_inc(v_collectTokens_1315_);
lean_dec(v_sep_1312_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1326_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___f_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1320_, 0, v_collectKinds_1316_);
lean_closure_set(v___f_1320_, 1, v_collectKinds_1314_);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1321_, 0, v_collectTokens_1315_);
lean_closure_set(v___f_1321_, 1, v_collectTokens_1313_);
v___x_1322_ = lean_box(1);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 2, v___x_1322_);
lean_ctor_set(v___x_1318_, 1, v___f_1320_);
lean_ctor_set(v___x_1318_, 0, v___f_1321_);
v___x_1324_ = v___x_1318_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___f_1321_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___f_1320_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1Info(lean_object* v_p_1328_, lean_object* v_sep_1329_){
_start:
{
lean_object* v_collectTokens_1330_; lean_object* v_collectKinds_1331_; lean_object* v_firstTokens_1332_; lean_object* v_collectTokens_1333_; lean_object* v_collectKinds_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1343_; 
v_collectTokens_1330_ = lean_ctor_get(v_p_1328_, 0);
lean_inc_ref(v_collectTokens_1330_);
v_collectKinds_1331_ = lean_ctor_get(v_p_1328_, 1);
lean_inc_ref(v_collectKinds_1331_);
v_firstTokens_1332_ = lean_ctor_get(v_p_1328_, 2);
lean_inc(v_firstTokens_1332_);
lean_dec_ref(v_p_1328_);
v_collectTokens_1333_ = lean_ctor_get(v_sep_1329_, 0);
v_collectKinds_1334_ = lean_ctor_get(v_sep_1329_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_sep_1329_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v_sep_1329_, 2);
lean_dec(v_unused_1344_);
v___x_1336_ = v_sep_1329_;
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_collectKinds_1334_);
lean_inc(v_collectTokens_1333_);
lean_dec(v_sep_1329_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1343_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___f_1338_; lean_object* v___f_1339_; lean_object* v___x_1341_; 
v___f_1338_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__0), 3, 2);
lean_closure_set(v___f_1338_, 0, v_collectKinds_1334_);
lean_closure_set(v___f_1338_, 1, v_collectKinds_1331_);
v___f_1339_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenInfo___lam__1), 3, 2);
lean_closure_set(v___f_1339_, 0, v_collectTokens_1333_);
lean_closure_set(v___f_1339_, 1, v_collectTokens_1330_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 2, v_firstTokens_1332_);
lean_ctor_set(v___x_1336_, 1, v___f_1338_);
lean_ctor_set(v___x_1336_, 0, v___f_1339_);
v___x_1341_ = v___x_1336_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___f_1339_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___f_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_firstTokens_1332_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object* v_p_1345_, lean_object* v_sep_1346_, uint8_t v_allowTrailingSep_1347_){
_start:
{
lean_object* v_info_1348_; lean_object* v_fn_1349_; lean_object* v_info_1350_; lean_object* v_fn_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1361_; 
v_info_1348_ = lean_ctor_get(v_p_1345_, 0);
lean_inc_ref(v_info_1348_);
v_fn_1349_ = lean_ctor_get(v_p_1345_, 1);
lean_inc_ref(v_fn_1349_);
lean_dec_ref(v_p_1345_);
v_info_1350_ = lean_ctor_get(v_sep_1346_, 0);
v_fn_1351_ = lean_ctor_get(v_sep_1346_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_sep_1346_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1353_ = v_sep_1346_;
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_fn_1351_);
lean_inc(v_info_1350_);
lean_dec(v_sep_1346_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1361_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1355_ = l_Lean_Parser_sepByInfo(v_info_1348_, v_info_1350_);
v___x_1356_ = lean_box(v_allowTrailingSep_1347_);
v___x_1357_ = lean_alloc_closure((void*)(l_Lean_Parser_sepByFn___boxed), 5, 3);
lean_closure_set(v___x_1357_, 0, v___x_1356_);
lean_closure_set(v___x_1357_, 1, v_fn_1349_);
lean_closure_set(v___x_1357_, 2, v_fn_1351_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 1, v___x_1357_);
lean_ctor_set(v___x_1353_, 0, v___x_1355_);
v___x_1359_ = v___x_1353_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByNoAntiquot___boxed(lean_object* v_p_1362_, lean_object* v_sep_1363_, lean_object* v_allowTrailingSep_1364_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1365_; lean_object* v_res_1366_; 
v_allowTrailingSep_boxed_1365_ = lean_unbox(v_allowTrailingSep_1364_);
v_res_1366_ = l_Lean_Parser_sepByNoAntiquot(v_p_1362_, v_sep_1363_, v_allowTrailingSep_boxed_1365_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot(lean_object* v_p_1367_, lean_object* v_sep_1368_, uint8_t v_allowTrailingSep_1369_){
_start:
{
lean_object* v_info_1370_; lean_object* v_fn_1371_; lean_object* v_info_1372_; lean_object* v_fn_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1383_; 
v_info_1370_ = lean_ctor_get(v_p_1367_, 0);
lean_inc_ref(v_info_1370_);
v_fn_1371_ = lean_ctor_get(v_p_1367_, 1);
lean_inc_ref(v_fn_1371_);
lean_dec_ref(v_p_1367_);
v_info_1372_ = lean_ctor_get(v_sep_1368_, 0);
v_fn_1373_ = lean_ctor_get(v_sep_1368_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v_sep_1368_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1375_ = v_sep_1368_;
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_fn_1373_);
lean_inc(v_info_1372_);
lean_dec(v_sep_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1383_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1377_ = l_Lean_Parser_sepBy1Info(v_info_1370_, v_info_1372_);
v___x_1378_ = lean_box(v_allowTrailingSep_1369_);
v___x_1379_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1Fn___boxed), 5, 3);
lean_closure_set(v___x_1379_, 0, v___x_1378_);
lean_closure_set(v___x_1379_, 1, v_fn_1371_);
lean_closure_set(v___x_1379_, 2, v_fn_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1379_);
lean_ctor_set(v___x_1375_, 0, v___x_1377_);
v___x_1381_ = v___x_1375_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1NoAntiquot___boxed(lean_object* v_p_1384_, lean_object* v_sep_1385_, lean_object* v_allowTrailingSep_1386_){
_start:
{
uint8_t v_allowTrailingSep_boxed_1387_; lean_object* v_res_1388_; 
v_allowTrailingSep_boxed_1387_ = lean_unbox(v_allowTrailingSep_1386_);
v_res_1388_ = l_Lean_Parser_sepBy1NoAntiquot(v_p_1384_, v_sep_1385_, v_allowTrailingSep_boxed_1387_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfFn(lean_object* v_p_1389_, lean_object* v_f_1390_, lean_object* v_c_1391_, lean_object* v_s_1392_){
_start:
{
lean_object* v_s_1393_; lean_object* v_stxStack_1394_; lean_object* v_errorMsg_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v_s_1393_ = lean_apply_2(v_p_1389_, v_c_1391_, v_s_1392_);
v_stxStack_1394_ = lean_ctor_get(v_s_1393_, 0);
lean_inc_ref(v_stxStack_1394_);
v_errorMsg_1395_ = lean_ctor_get(v_s_1393_, 4);
lean_inc(v_errorMsg_1395_);
v___x_1396_ = lean_box(0);
v___x_1397_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1395_, v___x_1396_);
lean_dec(v_errorMsg_1395_);
if (v___x_1397_ == 0)
{
lean_dec_ref(v_stxStack_1394_);
lean_dec_ref(v_f_1390_);
return v_s_1393_;
}
else
{
lean_object* v_stx_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_stx_1398_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1394_);
lean_dec_ref(v_stxStack_1394_);
v___x_1399_ = l_Lean_Parser_ParserState_popSyntax(v_s_1393_);
v___x_1400_ = lean_apply_1(v_f_1390_, v_stx_1398_);
v___x_1401_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1399_, v___x_1400_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOfInfo(lean_object* v_p_1402_){
_start:
{
lean_object* v_collectTokens_1403_; lean_object* v_collectKinds_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1412_; 
v_collectTokens_1403_ = lean_ctor_get(v_p_1402_, 0);
v_collectKinds_1404_ = lean_ctor_get(v_p_1402_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_p_1402_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_p_1402_, 2);
lean_dec(v_unused_1413_);
v___x_1406_ = v_p_1402_;
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_collectKinds_1404_);
lean_inc(v_collectTokens_1403_);
lean_dec(v_p_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_box(1);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 2, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_collectTokens_1403_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_collectKinds_1404_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResultOf(lean_object* v_p_1414_, lean_object* v_f_1415_){
_start:
{
lean_object* v_info_1416_; lean_object* v_fn_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1426_; 
v_info_1416_ = lean_ctor_get(v_p_1414_, 0);
v_fn_1417_ = lean_ctor_get(v_p_1414_, 1);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_p_1414_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1419_ = v_p_1414_;
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_fn_1417_);
lean_inc(v_info_1416_);
lean_dec(v_p_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1421_ = l_Lean_Parser_withResultOfInfo(v_info_1416_);
v___x_1422_ = lean_alloc_closure((void*)(l_Lean_Parser_withResultOfFn), 4, 2);
lean_closure_set(v___x_1422_, 0, v_fn_1417_);
lean_closure_set(v___x_1422_, 1, v_f_1415_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 1, v___x_1422_);
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1424_ = v___x_1419_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1421_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0(lean_object* v_stx_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = l_Lean_Syntax_getNumArgs(v_stx_1427_);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_nat_dec_eq(v___x_1428_, v___x_1429_);
lean_dec(v___x_1428_);
if (v___x_1430_ == 0)
{
lean_inc(v_stx_1427_);
return v_stx_1427_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = l_Lean_Syntax_getArg(v_stx_1427_, v___x_1431_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox___lam__0___boxed(lean_object* v_stx_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Parser_many1Unbox___lam__0(v_stx_1433_);
lean_dec(v_stx_1433_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_many1Unbox(lean_object* v_p_1436_){
_start:
{
lean_object* v___f_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___f_1437_ = ((lean_object*)(l_Lean_Parser_many1Unbox___closed__0));
v___x_1438_ = l_Lean_Parser_many1NoAntiquot(v_p_1436_);
v___x_1439_ = l_Lean_Parser_withResultOf(v___x_1438_, v___f_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn(lean_object* v_p_1440_, lean_object* v_errorMsg_1441_, lean_object* v_c_1442_, lean_object* v_s_1443_){
_start:
{
lean_object* v_pos_1444_; lean_object* v_toInputContext_1445_; uint8_t v___x_1446_; 
v_pos_1444_ = lean_ctor_get(v_s_1443_, 2);
v_toInputContext_1445_ = lean_ctor_get(v_c_1442_, 0);
v___x_1446_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1445_, v_pos_1444_);
if (v___x_1446_ == 0)
{
lean_object* v_inputString_1447_; uint32_t v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_inputString_1447_ = lean_ctor_get(v_toInputContext_1445_, 0);
v___x_1448_ = lean_string_utf8_get_fast(v_inputString_1447_, v_pos_1444_);
v___x_1449_ = lean_box_uint32(v___x_1448_);
v___x_1450_ = lean_apply_1(v_p_1440_, v___x_1449_);
v___x_1451_ = lean_unbox(v___x_1450_);
if (v___x_1451_ == 0)
{
uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = 1;
v___x_1453_ = lean_box(0);
v___x_1454_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1443_, v_errorMsg_1441_, v___x_1453_, v___x_1452_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
lean_inc(v_pos_1444_);
lean_dec_ref(v_errorMsg_1441_);
v___x_1455_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1443_, v_c_1442_, v_pos_1444_);
lean_dec(v_pos_1444_);
return v___x_1455_;
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v_errorMsg_1441_);
lean_dec_ref(v_p_1440_);
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1443_, v___x_1456_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object* v_p_1458_, lean_object* v_errorMsg_1459_, lean_object* v_c_1460_, lean_object* v_s_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_Parser_satisfyFn(v_p_1458_, v_errorMsg_1459_, v_c_1460_, v_s_1461_);
lean_dec_ref(v_c_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn(lean_object* v_p_1463_, lean_object* v_c_1464_, lean_object* v_s_1465_){
_start:
{
lean_object* v_pos_1466_; lean_object* v_toInputContext_1467_; uint8_t v___x_1468_; 
v_pos_1466_ = lean_ctor_get(v_s_1465_, 2);
v_toInputContext_1467_ = lean_ctor_get(v_c_1464_, 0);
v___x_1468_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1467_, v_pos_1466_);
if (v___x_1468_ == 0)
{
lean_object* v_inputString_1469_; uint32_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_inputString_1469_ = lean_ctor_get(v_toInputContext_1467_, 0);
v___x_1470_ = lean_string_utf8_get_fast(v_inputString_1469_, v_pos_1466_);
v___x_1471_ = lean_box_uint32(v___x_1470_);
lean_inc_ref(v_p_1463_);
v___x_1472_ = lean_apply_1(v_p_1463_, v___x_1471_);
v___x_1473_ = lean_unbox(v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_inc(v_pos_1466_);
v___x_1474_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1465_, v_c_1464_, v_pos_1466_);
lean_dec(v_pos_1466_);
v_s_1465_ = v___x_1474_;
goto _start;
}
else
{
lean_dec_ref(v_p_1463_);
return v_s_1465_;
}
}
else
{
lean_dec_ref(v_p_1463_);
return v_s_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeUntilFn___boxed(lean_object* v_p_1476_, lean_object* v_c_1477_, lean_object* v_s_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Parser_takeUntilFn(v_p_1476_, v_c_1477_, v_s_1478_);
lean_dec_ref(v_c_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_takeWhileFn___lam__0(lean_object* v_p_1480_, uint32_t v_c_1481_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_box_uint32(v_c_1481_);
v___x_1483_ = lean_apply_1(v_p_1480_, v___x_1482_);
v___x_1484_ = lean_unbox(v___x_1483_);
if (v___x_1484_ == 0)
{
uint8_t v___x_1485_; 
v___x_1485_ = 1;
return v___x_1485_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = 0;
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___lam__0___boxed(lean_object* v_p_1487_, lean_object* v_c_1488_){
_start:
{
uint32_t v_c_boxed_1489_; uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_c_boxed_1489_ = lean_unbox_uint32(v_c_1488_);
lean_dec(v_c_1488_);
v_res_1490_ = l_Lean_Parser_takeWhileFn___lam__0(v_p_1487_, v_c_boxed_1489_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn(lean_object* v_p_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___f_1495_; lean_object* v___x_1496_; 
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1495_, 0, v_p_1492_);
v___x_1496_ = l_Lean_Parser_takeUntilFn(v___f_1495_, v_a_1493_, v_a_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhileFn___boxed(lean_object* v_p_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Parser_takeWhileFn(v_p_1497_, v_a_1498_, v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeWhile1Fn(lean_object* v_p_1501_, lean_object* v_errorMsg_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_inc_ref(v_p_1501_);
v___x_1505_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1505_, 0, v_p_1501_);
lean_closure_set(v___x_1505_, 1, v_errorMsg_1502_);
v___x_1506_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhileFn___boxed), 3, 1);
lean_closure_set(v___x_1506_, 0, v_p_1501_);
v___x_1507_ = l_Lean_Parser_andthenFn(v___x_1505_, v___x_1506_, v_a_1503_, v_a_1504_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(uint8_t v_pushMissingOnError_1509_, lean_object* v_s_1510_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___closed__0));
v___x_1512_ = lean_box(0);
v___x_1513_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1510_, v___x_1511_, v___x_1512_, v_pushMissingOnError_1509_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi___boxed(lean_object* v_pushMissingOnError_1514_, lean_object* v_s_1515_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1516_; lean_object* v_res_1517_; 
v_pushMissingOnError_boxed_1516_ = lean_unbox(v_pushMissingOnError_1514_);
v_res_1517_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_boxed_1516_, v_s_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock(uint8_t v_pushMissingOnError_1518_, lean_object* v_nesting_1519_, lean_object* v_c_1520_, lean_object* v_s_1521_){
_start:
{
lean_object* v_pos_1522_; lean_object* v_toInputContext_1523_; uint8_t v___x_1524_; 
v_pos_1522_ = lean_ctor_get(v_s_1521_, 2);
v_toInputContext_1523_ = lean_ctor_get(v_c_1520_, 0);
v___x_1524_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1523_, v_pos_1522_);
if (v___x_1524_ == 0)
{
lean_object* v_inputString_1525_; uint32_t v_curr_1526_; lean_object* v_i_1527_; uint32_t v___x_1528_; uint8_t v___x_1529_; 
v_inputString_1525_ = lean_ctor_get(v_toInputContext_1523_, 0);
v_curr_1526_ = lean_string_utf8_get_fast(v_inputString_1525_, v_pos_1522_);
v_i_1527_ = lean_string_utf8_next_fast(v_inputString_1525_, v_pos_1522_);
v___x_1528_ = 45;
v___x_1529_ = lean_uint32_dec_eq(v_curr_1526_, v___x_1528_);
if (v___x_1529_ == 0)
{
uint32_t v___x_1530_; uint8_t v___x_1531_; 
v___x_1530_ = 47;
v___x_1531_ = lean_uint32_dec_eq(v_curr_1526_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Parser_ParserState_setPos(v_s_1521_, v_i_1527_);
v_s_1521_ = v___x_1532_;
goto _start;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1523_, v_i_1527_);
if (v___x_1534_ == 0)
{
uint32_t v_curr_1535_; uint8_t v___x_1536_; 
v_curr_1535_ = lean_string_utf8_get_fast(v_inputString_1525_, v_i_1527_);
v___x_1536_ = lean_uint32_dec_eq(v_curr_1535_, v___x_1528_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Parser_ParserState_setPos(v_s_1521_, v_i_1527_);
v_s_1521_ = v___x_1537_;
goto _start;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_add(v_nesting_1519_, v___x_1539_);
lean_dec(v_nesting_1519_);
v___x_1541_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1521_, v_c_1520_, v_i_1527_);
v_nesting_1519_ = v___x_1540_;
v_s_1521_ = v___x_1541_;
goto _start;
}
}
else
{
lean_object* v___x_1543_; 
lean_dec(v_nesting_1519_);
v___x_1543_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1518_, v_s_1521_);
return v___x_1543_;
}
}
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1523_, v_i_1527_);
if (v___x_1544_ == 0)
{
uint32_t v_curr_1545_; uint32_t v___x_1546_; uint8_t v___x_1547_; 
v_curr_1545_ = lean_string_utf8_get_fast(v_inputString_1525_, v_i_1527_);
v___x_1546_ = 47;
v___x_1547_ = lean_uint32_dec_eq(v_curr_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Parser_ParserState_setPos(v_s_1521_, v_i_1527_);
v_s_1521_ = v___x_1548_;
goto _start;
}
else
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_nat_dec_eq(v_nesting_1519_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_nat_sub(v_nesting_1519_, v___x_1550_);
lean_dec(v_nesting_1519_);
v___x_1553_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1521_, v_c_1520_, v_i_1527_);
v_nesting_1519_ = v___x_1552_;
v_s_1521_ = v___x_1553_;
goto _start;
}
else
{
lean_object* v___x_1555_; 
lean_dec(v_nesting_1519_);
v___x_1555_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1521_, v_c_1520_, v_i_1527_);
return v___x_1555_;
}
}
}
else
{
lean_object* v___x_1556_; 
lean_dec(v_nesting_1519_);
v___x_1556_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1518_, v_s_1521_);
return v___x_1556_;
}
}
}
else
{
lean_object* v___x_1557_; 
lean_dec(v_nesting_1519_);
v___x_1557_ = l___private_Lean_Parser_Basic_0__Lean_Parser_finishCommentBlock_eoi(v_pushMissingOnError_1518_, v_s_1521_);
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_finishCommentBlock___boxed(lean_object* v_pushMissingOnError_1558_, lean_object* v_nesting_1559_, lean_object* v_c_1560_, lean_object* v_s_1561_){
_start:
{
uint8_t v_pushMissingOnError_boxed_1562_; lean_object* v_res_1563_; 
v_pushMissingOnError_boxed_1562_ = lean_unbox(v_pushMissingOnError_1558_);
v_res_1563_ = l_Lean_Parser_finishCommentBlock(v_pushMissingOnError_boxed_1562_, v_nesting_1559_, v_c_1560_, v_s_1561_);
lean_dec_ref(v_c_1560_);
return v_res_1563_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_whitespace___lam__0(uint32_t v_c_1564_){
_start:
{
uint32_t v___x_1565_; uint8_t v___x_1566_; 
v___x_1565_ = 10;
v___x_1566_ = lean_uint32_dec_eq(v_c_1564_, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace___lam__0___boxed(lean_object* v_c_1567_){
_start:
{
uint32_t v_c_boxed_1568_; uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_c_boxed_1568_ = lean_unbox_uint32(v_c_1567_);
lean_dec(v_c_1567_);
v_res_1569_ = l_Lean_Parser_whitespace___lam__0(v_c_boxed_1568_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_whitespace(lean_object* v_c_1576_, lean_object* v_s_1577_){
_start:
{
lean_object* v_pos_1578_; lean_object* v_toInputContext_1582_; uint8_t v___x_1583_; 
v_pos_1578_ = lean_ctor_get(v_s_1577_, 2);
v_toInputContext_1582_ = lean_ctor_get(v_c_1576_, 0);
v___x_1583_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1582_, v_pos_1578_);
if (v___x_1583_ == 0)
{
lean_object* v_inputString_1584_; uint32_t v_curr_1585_; uint32_t v___x_1586_; uint8_t v___x_1587_; 
v_inputString_1584_ = lean_ctor_get(v_toInputContext_1582_, 0);
v_curr_1585_ = lean_string_utf8_get_fast(v_inputString_1584_, v_pos_1578_);
v___x_1586_ = 9;
v___x_1587_ = lean_uint32_dec_eq(v_curr_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
uint32_t v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = 13;
v___x_1589_ = lean_uint32_dec_eq(v_curr_1585_, v___x_1588_);
if (v___x_1589_ == 0)
{
uint32_t v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = 32;
v___x_1591_ = lean_uint32_dec_eq(v_curr_1585_, v___x_1590_);
if (v___x_1591_ == 0)
{
uint32_t v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = 10;
v___x_1593_ = lean_uint32_dec_eq(v_curr_1585_, v___x_1592_);
if (v___x_1593_ == 0)
{
uint32_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = 45;
v___x_1595_ = lean_uint32_dec_eq(v_curr_1585_, v___x_1594_);
if (v___x_1595_ == 0)
{
uint32_t v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = 47;
v___x_1597_ = lean_uint32_dec_eq(v_curr_1585_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v_c_1576_);
return v_s_1577_;
}
else
{
lean_object* v_i_1598_; uint32_t v_curr_1599_; uint8_t v___x_1600_; 
v_i_1598_ = lean_string_utf8_next_fast(v_inputString_1584_, v_pos_1578_);
v_curr_1599_ = lean_string_utf8_get(v_inputString_1584_, v_i_1598_);
v___x_1600_ = lean_uint32_dec_eq(v_curr_1599_, v___x_1594_);
if (v___x_1600_ == 0)
{
lean_dec_ref(v_c_1576_);
return v_s_1577_;
}
else
{
lean_object* v_i_1601_; uint32_t v_curr_1602_; uint8_t v___x_1603_; 
v_i_1601_ = lean_string_utf8_next(v_inputString_1584_, v_i_1598_);
v_curr_1602_ = lean_string_utf8_get(v_inputString_1584_, v_i_1601_);
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
v___x_1610_ = l_Lean_Parser_ParserState_next(v_s_1577_, v_c_1576_, v_i_1601_);
lean_dec(v_i_1601_);
v___x_1611_ = l_Lean_Parser_andthenFn(v___x_1608_, v___x_1609_, v_c_1576_, v___x_1610_);
return v___x_1611_;
}
else
{
lean_dec(v_i_1601_);
lean_dec_ref(v_c_1576_);
return v_s_1577_;
}
}
else
{
lean_dec(v_i_1601_);
lean_dec_ref(v_c_1576_);
return v_s_1577_;
}
}
}
}
else
{
lean_object* v_i_1612_; uint32_t v_curr_1613_; uint8_t v___x_1614_; 
v_i_1612_ = lean_string_utf8_next_fast(v_inputString_1584_, v_pos_1578_);
v_curr_1613_ = lean_string_utf8_get(v_inputString_1584_, v_i_1612_);
v___x_1614_ = lean_uint32_dec_eq(v_curr_1613_, v___x_1594_);
if (v___x_1614_ == 0)
{
lean_dec_ref(v_c_1576_);
return v_s_1577_;
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1615_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__1));
v___x_1616_ = lean_alloc_closure((void*)(l_Lean_Parser_whitespace), 2, 0);
v___x_1617_ = l_Lean_Parser_ParserState_next(v_s_1577_, v_c_1576_, v_i_1612_);
v___x_1618_ = l_Lean_Parser_andthenFn(v___x_1615_, v___x_1616_, v_c_1576_, v___x_1617_);
return v___x_1618_;
}
}
}
else
{
lean_inc(v_pos_1578_);
goto v___jp_1579_;
}
}
else
{
lean_inc(v_pos_1578_);
goto v___jp_1579_;
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
lean_dec_ref(v_c_1576_);
v___x_1619_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__2));
v___x_1620_ = lean_box(0);
v___x_1621_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1577_, v___x_1619_, v___x_1620_, v___x_1587_);
return v___x_1621_;
}
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v_c_1576_);
v___x_1622_ = ((lean_object*)(l_Lean_Parser_whitespace___closed__3));
v___x_1623_ = lean_box(0);
v___x_1624_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1577_, v___x_1622_, v___x_1623_, v___x_1583_);
return v___x_1624_;
}
}
else
{
lean_dec_ref(v_c_1576_);
return v_s_1577_;
}
v___jp_1579_:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1577_, v_c_1576_, v_pos_1578_);
lean_dec(v_pos_1578_);
v_s_1577_ = v___x_1580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt(lean_object* v_c_1625_, lean_object* v_p_1626_){
_start:
{
lean_object* v_toInputContext_1627_; lean_object* v_inputString_1628_; lean_object* v_endPos_1629_; uint8_t v___x_1630_; 
v_toInputContext_1627_ = lean_ctor_get(v_c_1625_, 0);
v_inputString_1628_ = lean_ctor_get(v_toInputContext_1627_, 0);
v_endPos_1629_ = lean_ctor_get(v_toInputContext_1627_, 3);
v___x_1630_ = lean_nat_dec_le(v_p_1626_, v_endPos_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_inc(v_endPos_1629_);
lean_inc_ref(v_inputString_1628_);
v___x_1631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1631_, 0, v_inputString_1628_);
lean_ctor_set(v___x_1631_, 1, v_p_1626_);
lean_ctor_set(v___x_1631_, 2, v_endPos_1629_);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; 
lean_inc(v_p_1626_);
lean_inc_ref(v_inputString_1628_);
v___x_1632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1632_, 0, v_inputString_1628_);
lean_ctor_set(v___x_1632_, 1, v_p_1626_);
lean_ctor_set(v___x_1632_, 2, v_p_1626_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_mkEmptySubstringAt___boxed(lean_object* v_c_1633_, lean_object* v_p_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1633_, v_p_1634_);
lean_dec_ref(v_c_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(lean_object* v_startPos_1636_, uint8_t v_trailingWs_1637_, lean_object* v_c_1638_, lean_object* v_s_1639_){
_start:
{
lean_object* v_toInputContext_1640_; lean_object* v_pos_1641_; lean_object* v_inputString_1642_; lean_object* v_endPos_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1671_; 
v_toInputContext_1640_ = lean_ctor_get(v_c_1638_, 0);
lean_inc_ref(v_toInputContext_1640_);
v_pos_1641_ = lean_ctor_get(v_s_1639_, 2);
v_inputString_1642_ = lean_ctor_get(v_toInputContext_1640_, 0);
v_endPos_1643_ = lean_ctor_get(v_toInputContext_1640_, 3);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_toInputContext_1640_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; lean_object* v_unused_1673_; 
v_unused_1672_ = lean_ctor_get(v_toInputContext_1640_, 2);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_toInputContext_1640_, 1);
lean_dec(v_unused_1673_);
v___x_1645_ = v_toInputContext_1640_;
v_isShared_1646_ = v_isSharedCheck_1671_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_endPos_1643_);
lean_inc(v_inputString_1642_);
lean_dec(v_toInputContext_1640_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1671_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_leading_1647_; lean_object* v_val_1648_; 
lean_inc(v_startPos_1636_);
v_leading_1647_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1638_, v_startPos_1636_);
v_val_1648_ = lean_string_utf8_extract(v_inputString_1642_, v_startPos_1636_, v_pos_1641_);
if (v_trailingWs_1637_ == 0)
{
lean_object* v_trailing_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_dec(v_endPos_1643_);
lean_dec_ref(v_inputString_1642_);
lean_inc(v_pos_1641_);
v_trailing_1649_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1638_, v_pos_1641_);
lean_dec_ref(v_c_1638_);
v___x_1650_ = lean_string_utf8_byte_size(v_val_1648_);
v___x_1651_ = lean_nat_add(v_startPos_1636_, v___x_1650_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 3, v___x_1651_);
lean_ctor_set(v___x_1645_, 2, v_trailing_1649_);
lean_ctor_set(v___x_1645_, 1, v_startPos_1636_);
lean_ctor_set(v___x_1645_, 0, v_leading_1647_);
v___x_1653_ = v___x_1645_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_leading_1647_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_startPos_1636_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_trailing_1649_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v_atom_1654_; lean_object* v___x_1655_; 
v_atom_1654_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1654_, 0, v___x_1653_);
lean_ctor_set(v_atom_1654_, 1, v_val_1648_);
v___x_1655_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1639_, v_atom_1654_);
return v___x_1655_;
}
}
else
{
lean_object* v_s_1657_; lean_object* v___y_1659_; lean_object* v_pos_1667_; uint8_t v___x_1668_; 
lean_inc(v_pos_1641_);
v_s_1657_ = l_Lean_Parser_whitespace(v_c_1638_, v_s_1639_);
v_pos_1667_ = lean_ctor_get(v_s_1657_, 2);
v___x_1668_ = lean_nat_dec_le(v_pos_1667_, v_endPos_1643_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1669_, 0, v_inputString_1642_);
lean_ctor_set(v___x_1669_, 1, v_pos_1641_);
lean_ctor_set(v___x_1669_, 2, v_endPos_1643_);
v___y_1659_ = v___x_1669_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1670_; 
lean_dec(v_endPos_1643_);
lean_inc(v_pos_1667_);
v___x_1670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1670_, 0, v_inputString_1642_);
lean_ctor_set(v___x_1670_, 1, v_pos_1641_);
lean_ctor_set(v___x_1670_, 2, v_pos_1667_);
v___y_1659_ = v___x_1670_;
goto v___jp_1658_;
}
v___jp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1660_ = lean_string_utf8_byte_size(v_val_1648_);
v___x_1661_ = lean_nat_add(v_startPos_1636_, v___x_1660_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 3, v___x_1661_);
lean_ctor_set(v___x_1645_, 2, v___y_1659_);
lean_ctor_set(v___x_1645_, 1, v_startPos_1636_);
lean_ctor_set(v___x_1645_, 0, v_leading_1647_);
v___x_1663_ = v___x_1645_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_leading_1647_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_startPos_1636_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v___y_1659_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v_atom_1664_; lean_object* v___x_1665_; 
v_atom_1664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_1664_, 0, v___x_1663_);
lean_ctor_set(v_atom_1664_, 1, v_val_1648_);
v___x_1665_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1657_, v_atom_1664_);
return v___x_1665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux___boxed(lean_object* v_startPos_1674_, lean_object* v_trailingWs_1675_, lean_object* v_c_1676_, lean_object* v_s_1677_){
_start:
{
uint8_t v_trailingWs_boxed_1678_; lean_object* v_res_1679_; 
v_trailingWs_boxed_1678_ = lean_unbox(v_trailingWs_1675_);
v_res_1679_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_startPos_1674_, v_trailingWs_boxed_1678_, v_c_1676_, v_s_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn(lean_object* v_p_1680_, uint8_t v_trailingWs_1681_, lean_object* v_c_1682_, lean_object* v_s_1683_){
_start:
{
lean_object* v_pos_1684_; lean_object* v_s_1685_; lean_object* v_errorMsg_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_pos_1684_ = lean_ctor_get(v_s_1683_, 2);
lean_inc(v_pos_1684_);
lean_inc_ref(v_c_1682_);
v_s_1685_ = lean_apply_2(v_p_1680_, v_c_1682_, v_s_1683_);
v_errorMsg_1686_ = lean_ctor_get(v_s_1685_, 4);
lean_inc(v_errorMsg_1686_);
v___x_1687_ = lean_box(0);
v___x_1688_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1686_, v___x_1687_);
lean_dec(v_errorMsg_1686_);
if (v___x_1688_ == 0)
{
lean_dec(v_pos_1684_);
lean_dec_ref(v_c_1682_);
return v_s_1685_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawAux(v_pos_1684_, v_trailingWs_1681_, v_c_1682_, v_s_1685_);
return v___x_1689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawFn___boxed(lean_object* v_p_1690_, lean_object* v_trailingWs_1691_, lean_object* v_c_1692_, lean_object* v_s_1693_){
_start:
{
uint8_t v_trailingWs_boxed_1694_; lean_object* v_res_1695_; 
v_trailingWs_boxed_1694_ = lean_unbox(v_trailingWs_1691_);
v_res_1695_ = l_Lean_Parser_rawFn(v_p_1690_, v_trailingWs_boxed_1694_, v_c_1692_, v_s_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_chFn___lam__0(uint32_t v_c_1696_, uint32_t v_d_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_uint32_dec_eq(v_c_1696_, v_d_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___lam__0___boxed(lean_object* v_c_1699_, lean_object* v_d_1700_){
_start:
{
uint32_t v_c_boxed_1701_; uint32_t v_d_boxed_1702_; uint8_t v_res_1703_; lean_object* v_r_1704_; 
v_c_boxed_1701_ = lean_unbox_uint32(v_c_1699_);
lean_dec(v_c_1699_);
v_d_boxed_1702_ = lean_unbox_uint32(v_d_1700_);
lean_dec(v_d_1700_);
v_res_1703_ = l_Lean_Parser_chFn___lam__0(v_c_boxed_1701_, v_d_boxed_1702_);
v_r_1704_ = lean_box(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn(uint32_t v_c_1707_, uint8_t v_trailingWs_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_){
_start:
{
lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1711_ = lean_box_uint32(v_c_1707_);
v___f_1712_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1712_, 0, v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_1714_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_1715_ = lean_string_push(v___x_1714_, v_c_1707_);
v___x_1716_ = lean_string_append(v___x_1713_, v___x_1715_);
lean_dec_ref(v___x_1715_);
v___x_1717_ = lean_string_append(v___x_1716_, v___x_1713_);
v___x_1718_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1718_, 0, v___f_1712_);
lean_closure_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = l_Lean_Parser_rawFn(v___x_1718_, v_trailingWs_1708_, v_a_1709_, v_a_1710_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_chFn___boxed(lean_object* v_c_1720_, lean_object* v_trailingWs_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
uint32_t v_c_boxed_1724_; uint8_t v_trailingWs_boxed_1725_; lean_object* v_res_1726_; 
v_c_boxed_1724_ = lean_unbox_uint32(v_c_1720_);
lean_dec(v_c_1720_);
v_trailingWs_boxed_1725_ = lean_unbox(v_trailingWs_1721_);
v_res_1726_ = l_Lean_Parser_chFn(v_c_boxed_1724_, v_trailingWs_boxed_1725_, v_a_1722_, v_a_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh(uint32_t v_c_1727_, uint8_t v_trailingWs_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1729_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_1730_ = lean_box_uint32(v_c_1727_);
v___x_1731_ = lean_box(v_trailingWs_1728_);
v___x_1732_ = lean_alloc_closure((void*)(l_Lean_Parser_chFn___boxed), 4, 2);
lean_closure_set(v___x_1732_, 0, v___x_1730_);
lean_closure_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1729_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawCh___boxed(lean_object* v_c_1734_, lean_object* v_trailingWs_1735_){
_start:
{
uint32_t v_c_boxed_1736_; uint8_t v_trailingWs_boxed_1737_; lean_object* v_res_1738_; 
v_c_boxed_1736_ = lean_unbox_uint32(v_c_1734_);
lean_dec(v_c_1734_);
v_trailingWs_boxed_1737_ = lean_unbox(v_trailingWs_1735_);
v_res_1738_ = l_Lean_Parser_rawCh(v_c_boxed_1736_, v_trailingWs_boxed_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn(lean_object* v_c_1740_, lean_object* v_s_1741_){
_start:
{
lean_object* v_pos_1742_; lean_object* v_toInputContext_1743_; uint8_t v___x_1744_; 
v_pos_1742_ = lean_ctor_get(v_s_1741_, 2);
v_toInputContext_1743_ = lean_ctor_get(v_c_1740_, 0);
v___x_1744_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1743_, v_pos_1742_);
if (v___x_1744_ == 0)
{
lean_object* v_inputString_1745_; uint8_t v___x_1746_; uint32_t v_curr_1751_; lean_object* v_i_1752_; uint32_t v___x_1765_; uint8_t v___x_1766_; 
v_inputString_1745_ = lean_ctor_get(v_toInputContext_1743_, 0);
v___x_1746_ = 1;
v_curr_1751_ = lean_string_utf8_get_fast(v_inputString_1745_, v_pos_1742_);
v_i_1752_ = lean_string_utf8_next_fast(v_inputString_1745_, v_pos_1742_);
v___x_1765_ = 48;
v___x_1766_ = lean_uint32_dec_le(v___x_1765_, v_curr_1751_);
if (v___x_1766_ == 0)
{
goto v___jp_1759_;
}
else
{
uint32_t v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = 57;
v___x_1768_ = lean_uint32_dec_le(v_curr_1751_, v___x_1767_);
if (v___x_1768_ == 0)
{
goto v___jp_1759_;
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Parser_ParserState_setPos(v_s_1741_, v_i_1752_);
return v___x_1769_;
}
}
v___jp_1747_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = ((lean_object*)(l_Lean_Parser_hexDigitFn___closed__0));
v___x_1749_ = lean_box(0);
v___x_1750_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1741_, v___x_1748_, v___x_1749_, v___x_1746_);
return v___x_1750_;
}
v___jp_1753_:
{
uint32_t v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = 65;
v___x_1755_ = lean_uint32_dec_le(v___x_1754_, v_curr_1751_);
if (v___x_1755_ == 0)
{
goto v___jp_1747_;
}
else
{
uint32_t v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = 70;
v___x_1757_ = lean_uint32_dec_le(v_curr_1751_, v___x_1756_);
if (v___x_1757_ == 0)
{
goto v___jp_1747_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Parser_ParserState_setPos(v_s_1741_, v_i_1752_);
return v___x_1758_;
}
}
}
v___jp_1759_:
{
uint32_t v___x_1760_; uint8_t v___x_1761_; 
v___x_1760_ = 97;
v___x_1761_ = lean_uint32_dec_le(v___x_1760_, v_curr_1751_);
if (v___x_1761_ == 0)
{
goto v___jp_1753_;
}
else
{
uint32_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = 102;
v___x_1763_ = lean_uint32_dec_le(v_curr_1751_, v___x_1762_);
if (v___x_1763_ == 0)
{
goto v___jp_1753_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Parser_ParserState_setPos(v_s_1741_, v_i_1752_);
return v___x_1764_;
}
}
}
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1741_, v___x_1770_);
return v___x_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexDigitFn___boxed(lean_object* v_c_1772_, lean_object* v_s_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Parser_hexDigitFn(v_c_1772_, v_s_1773_);
lean_dec_ref(v_c_1772_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn(uint8_t v_seenNewline_1777_, lean_object* v_c_1778_, lean_object* v_s_1779_){
_start:
{
lean_object* v_pos_1780_; lean_object* v_toInputContext_1784_; uint8_t v___x_1785_; 
v_pos_1780_ = lean_ctor_get(v_s_1779_, 2);
v_toInputContext_1784_ = lean_ctor_get(v_c_1778_, 0);
v___x_1785_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1784_, v_pos_1780_);
if (v___x_1785_ == 0)
{
lean_object* v_inputString_1786_; uint8_t v___x_1787_; uint32_t v_curr_1788_; uint32_t v___x_1789_; uint8_t v___x_1790_; 
v_inputString_1786_ = lean_ctor_get(v_toInputContext_1784_, 0);
v___x_1787_ = 1;
v_curr_1788_ = lean_string_utf8_get_fast(v_inputString_1786_, v_pos_1780_);
v___x_1789_ = 10;
v___x_1790_ = lean_uint32_dec_eq(v_curr_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
uint32_t v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = 32;
v___x_1792_ = lean_uint32_dec_eq(v_curr_1788_, v___x_1791_);
if (v___x_1792_ == 0)
{
uint32_t v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = 9;
v___x_1794_ = lean_uint32_dec_eq(v_curr_1788_, v___x_1793_);
if (v___x_1794_ == 0)
{
uint32_t v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = 13;
v___x_1796_ = lean_uint32_dec_eq(v_curr_1788_, v___x_1795_);
if (v___x_1796_ == 0)
{
if (v_seenNewline_1777_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__0));
v___x_1798_ = lean_box(0);
v___x_1799_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1779_, v___x_1797_, v___x_1798_, v___x_1787_);
return v___x_1799_;
}
else
{
return v_s_1779_;
}
}
else
{
lean_inc(v_pos_1780_);
goto v___jp_1781_;
}
}
else
{
lean_inc(v_pos_1780_);
goto v___jp_1781_;
}
}
else
{
lean_inc(v_pos_1780_);
goto v___jp_1781_;
}
}
else
{
if (v_seenNewline_1777_ == 0)
{
lean_object* v___x_1800_; 
lean_inc(v_pos_1780_);
v___x_1800_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1779_, v_c_1778_, v_pos_1780_);
lean_dec(v_pos_1780_);
v_seenNewline_1777_ = v___x_1787_;
v_s_1779_ = v___x_1800_;
goto _start;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = ((lean_object*)(l_Lean_Parser_stringGapFn___closed__1));
v___x_1803_ = lean_box(0);
v___x_1804_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1779_, v___x_1802_, v___x_1803_, v___x_1787_);
return v___x_1804_;
}
}
}
else
{
return v_s_1779_;
}
v___jp_1781_:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1779_, v_c_1778_, v_pos_1780_);
lean_dec(v_pos_1780_);
v_s_1779_ = v___x_1782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_stringGapFn___boxed(lean_object* v_seenNewline_1805_, lean_object* v_c_1806_, lean_object* v_s_1807_){
_start:
{
uint8_t v_seenNewline_boxed_1808_; lean_object* v_res_1809_; 
v_seenNewline_boxed_1808_ = lean_unbox(v_seenNewline_1805_);
v_res_1809_ = l_Lean_Parser_stringGapFn(v_seenNewline_boxed_1808_, v_c_1806_, v_s_1807_);
lean_dec_ref(v_c_1806_);
return v_res_1809_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__1(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
lean_inc_ref(v___x_1811_);
v___x_1812_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1812_, 0, v___x_1811_);
lean_closure_set(v___x_1812_, 1, v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_Parser_quotedCharCoreFn___closed__2(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__1, &l_Lean_Parser_quotedCharCoreFn___closed__1_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__1);
v___x_1814_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1815_ = lean_alloc_closure((void*)(l_Lean_Parser_andthenFn), 4, 2);
lean_closure_set(v___x_1815_, 0, v___x_1814_);
lean_closure_set(v___x_1815_, 1, v___x_1813_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn(lean_object* v_isQuotable_1816_, uint8_t v_inString_1817_, lean_object* v_c_1818_, lean_object* v_s_1819_){
_start:
{
lean_object* v_pos_1820_; lean_object* v_toInputContext_1821_; uint8_t v___x_1822_; 
v_pos_1820_ = lean_ctor_get(v_s_1819_, 2);
v_toInputContext_1821_ = lean_ctor_get(v_c_1818_, 0);
v___x_1822_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1821_, v_pos_1820_);
if (v___x_1822_ == 0)
{
lean_object* v_inputString_1823_; uint32_t v_curr_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_inputString_1823_ = lean_ctor_get(v_toInputContext_1821_, 0);
v_curr_1824_ = lean_string_utf8_get_fast(v_inputString_1823_, v_pos_1820_);
v___x_1825_ = lean_box_uint32(v_curr_1824_);
v___x_1826_ = lean_apply_1(v_isQuotable_1816_, v___x_1825_);
v___x_1827_ = lean_unbox(v___x_1826_);
if (v___x_1827_ == 0)
{
uint32_t v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = 120;
v___x_1829_ = lean_uint32_dec_eq(v_curr_1824_, v___x_1828_);
if (v___x_1829_ == 0)
{
uint32_t v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = 117;
v___x_1831_ = lean_uint32_dec_eq(v_curr_1824_, v___x_1830_);
if (v___x_1831_ == 0)
{
uint8_t v___x_1832_; 
v___x_1832_ = 1;
if (v_inString_1817_ == 0)
{
lean_dec_ref(v_c_1818_);
goto v___jp_1833_;
}
else
{
uint32_t v___x_1837_; uint8_t v___x_1838_; 
v___x_1837_ = 10;
v___x_1838_ = lean_uint32_dec_eq(v_curr_1824_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_dec_ref(v_c_1818_);
goto v___jp_1833_;
}
else
{
lean_object* v___x_1839_; 
v___x_1839_ = l_Lean_Parser_stringGapFn(v___x_1831_, v_c_1818_, v_s_1819_);
lean_dec_ref(v_c_1818_);
return v___x_1839_;
}
}
v___jp_1833_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((lean_object*)(l_Lean_Parser_quotedCharCoreFn___closed__0));
v___x_1835_ = lean_box(0);
v___x_1836_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1819_, v___x_1834_, v___x_1835_, v___x_1832_);
return v___x_1836_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_inc(v_pos_1820_);
v___x_1840_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1841_ = lean_obj_once(&l_Lean_Parser_quotedCharCoreFn___closed__2, &l_Lean_Parser_quotedCharCoreFn___closed__2_once, _init_l_Lean_Parser_quotedCharCoreFn___closed__2);
v___x_1842_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1819_, v_c_1818_, v_pos_1820_);
lean_dec(v_pos_1820_);
v___x_1843_ = l_Lean_Parser_andthenFn(v___x_1840_, v___x_1841_, v_c_1818_, v___x_1842_);
return v___x_1843_;
}
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_inc(v_pos_1820_);
v___x_1844_ = lean_alloc_closure((void*)(l_Lean_Parser_hexDigitFn___boxed), 2, 0);
v___x_1845_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1819_, v_c_1818_, v_pos_1820_);
lean_dec(v_pos_1820_);
lean_inc_ref(v___x_1844_);
v___x_1846_ = l_Lean_Parser_andthenFn(v___x_1844_, v___x_1844_, v_c_1818_, v___x_1845_);
return v___x_1846_;
}
}
else
{
lean_object* v___x_1847_; 
lean_inc(v_pos_1820_);
v___x_1847_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1819_, v_c_1818_, v_pos_1820_);
lean_dec(v_pos_1820_);
lean_dec_ref(v_c_1818_);
return v___x_1847_;
}
}
else
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
lean_dec_ref(v_c_1818_);
lean_dec_ref(v_isQuotable_1816_);
v___x_1848_ = lean_box(0);
v___x_1849_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1819_, v___x_1848_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharCoreFn___boxed(lean_object* v_isQuotable_1850_, lean_object* v_inString_1851_, lean_object* v_c_1852_, lean_object* v_s_1853_){
_start:
{
uint8_t v_inString_boxed_1854_; lean_object* v_res_1855_; 
v_inString_boxed_1854_ = lean_unbox(v_inString_1851_);
v_res_1855_ = l_Lean_Parser_quotedCharCoreFn(v_isQuotable_1850_, v_inString_boxed_1854_, v_c_1852_, v_s_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isQuotableCharDefault(uint32_t v_c_1856_){
_start:
{
uint32_t v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = 92;
v___x_1858_ = lean_uint32_dec_eq(v_c_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
uint32_t v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = 34;
v___x_1860_ = lean_uint32_dec_eq(v_c_1856_, v___x_1859_);
if (v___x_1860_ == 0)
{
uint32_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = 39;
v___x_1862_ = lean_uint32_dec_eq(v_c_1856_, v___x_1861_);
if (v___x_1862_ == 0)
{
uint32_t v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = 114;
v___x_1864_ = lean_uint32_dec_eq(v_c_1856_, v___x_1863_);
if (v___x_1864_ == 0)
{
uint32_t v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = 110;
v___x_1866_ = lean_uint32_dec_eq(v_c_1856_, v___x_1865_);
if (v___x_1866_ == 0)
{
uint32_t v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = 116;
v___x_1868_ = lean_uint32_dec_eq(v_c_1856_, v___x_1867_);
return v___x_1868_;
}
else
{
return v___x_1866_;
}
}
else
{
return v___x_1864_;
}
}
else
{
return v___x_1862_;
}
}
else
{
return v___x_1860_;
}
}
else
{
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isQuotableCharDefault___boxed(lean_object* v_c_1869_){
_start:
{
uint32_t v_c_boxed_1870_; uint8_t v_res_1871_; lean_object* v_r_1872_; 
v_c_boxed_1870_ = lean_unbox_uint32(v_c_1869_);
lean_dec(v_c_1869_);
v_res_1871_ = l_Lean_Parser_isQuotableCharDefault(v_c_boxed_1870_);
v_r_1872_ = lean_box(v_res_1871_);
return v_r_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedCharFn(lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1877_ = 0;
v___x_1878_ = l_Lean_Parser_quotedCharCoreFn(v___x_1876_, v___x_1877_, v_a_1874_, v_a_1875_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_quotedStringFn(lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1881_ = ((lean_object*)(l_Lean_Parser_quotedCharFn___closed__0));
v___x_1882_ = 1;
v___x_1883_ = l_Lean_Parser_quotedCharCoreFn(v___x_1881_, v___x_1882_, v_a_1879_, v_a_1880_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken(lean_object* v_n_1884_, lean_object* v_startPos_1885_, uint8_t v_includeWhitespace_1886_, lean_object* v_c_1887_, lean_object* v_s_1888_){
_start:
{
lean_object* v_pos_1889_; lean_object* v_errorMsg_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_pos_1889_ = lean_ctor_get(v_s_1888_, 2);
v_errorMsg_1890_ = lean_ctor_get(v_s_1888_, 4);
v___x_1891_ = lean_box(0);
v___x_1892_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec_ref(v_c_1887_);
lean_dec(v_startPos_1885_);
lean_dec(v_n_1884_);
return v_s_1888_;
}
else
{
lean_object* v_toInputContext_1893_; lean_object* v_inputString_1894_; lean_object* v_endPos_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1917_; 
lean_inc(v_pos_1889_);
v_toInputContext_1893_ = lean_ctor_get(v_c_1887_, 0);
lean_inc_ref(v_toInputContext_1893_);
v_inputString_1894_ = lean_ctor_get(v_toInputContext_1893_, 0);
v_endPos_1895_ = lean_ctor_get(v_toInputContext_1893_, 3);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_toInputContext_1893_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; lean_object* v_unused_1919_; 
v_unused_1918_ = lean_ctor_get(v_toInputContext_1893_, 2);
lean_dec(v_unused_1918_);
v_unused_1919_ = lean_ctor_get(v_toInputContext_1893_, 1);
lean_dec(v_unused_1919_);
v___x_1897_ = v_toInputContext_1893_;
v_isShared_1898_ = v_isSharedCheck_1917_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_endPos_1895_);
lean_inc(v_inputString_1894_);
lean_dec(v_toInputContext_1893_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1917_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_leading_1899_; lean_object* v_val_1900_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1910_; lean_object* v_pos_1911_; 
lean_inc(v_startPos_1885_);
v_leading_1899_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_1887_, v_startPos_1885_);
v_val_1900_ = lean_string_utf8_extract(v_inputString_1894_, v_startPos_1885_, v_pos_1889_);
if (v_includeWhitespace_1886_ == 0)
{
lean_dec_ref(v_c_1887_);
lean_inc(v_pos_1889_);
v___y_1910_ = v_s_1888_;
v_pos_1911_ = v_pos_1889_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1915_; lean_object* v_pos_1916_; 
v___x_1915_ = l_Lean_Parser_whitespace(v_c_1887_, v_s_1888_);
v_pos_1916_ = lean_ctor_get(v___x_1915_, 2);
lean_inc(v_pos_1916_);
v___y_1910_ = v___x_1915_;
v_pos_1911_ = v_pos_1916_;
goto v___jp_1909_;
}
v___jp_1901_:
{
lean_object* v_info_1905_; 
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 3, v_pos_1889_);
lean_ctor_set(v___x_1897_, 2, v___y_1903_);
lean_ctor_set(v___x_1897_, 1, v_startPos_1885_);
lean_ctor_set(v___x_1897_, 0, v_leading_1899_);
v_info_1905_ = v___x_1897_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_leading_1899_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_startPos_1885_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v___y_1903_);
lean_ctor_set(v_reuseFailAlloc_1908_, 3, v_pos_1889_);
v_info_1905_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = l_Lean_Syntax_mkLit(v_n_1884_, v_val_1900_, v_info_1905_);
v___x_1907_ = l_Lean_Parser_ParserState_pushSyntax(v___y_1902_, v___x_1906_);
return v___x_1907_;
}
}
v___jp_1909_:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_le(v_pos_1911_, v_endPos_1895_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec(v_pos_1911_);
lean_inc(v_pos_1889_);
v___x_1913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1913_, 0, v_inputString_1894_);
lean_ctor_set(v___x_1913_, 1, v_pos_1889_);
lean_ctor_set(v___x_1913_, 2, v_endPos_1895_);
v___y_1902_ = v___y_1910_;
v___y_1903_ = v___x_1913_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1914_; 
lean_dec(v_endPos_1895_);
lean_inc(v_pos_1889_);
v___x_1914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1914_, 0, v_inputString_1894_);
lean_ctor_set(v___x_1914_, 1, v_pos_1889_);
lean_ctor_set(v___x_1914_, 2, v_pos_1911_);
v___y_1902_ = v___y_1910_;
v___y_1903_ = v___x_1914_;
goto v___jp_1901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkNodeToken___boxed(lean_object* v_n_1920_, lean_object* v_startPos_1921_, lean_object* v_includeWhitespace_1922_, lean_object* v_c_1923_, lean_object* v_s_1924_){
_start:
{
uint8_t v_includeWhitespace_boxed_1925_; lean_object* v_res_1926_; 
v_includeWhitespace_boxed_1925_ = lean_unbox(v_includeWhitespace_1922_);
v_res_1926_ = l_Lean_Parser_mkNodeToken(v_n_1920_, v_startPos_1921_, v_includeWhitespace_boxed_1925_, v_c_1923_, v_s_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFnAux(lean_object* v_startPos_1931_, lean_object* v_c_1932_, lean_object* v_s_1933_){
_start:
{
lean_object* v_pos_1934_; lean_object* v_toInputContext_1935_; uint8_t v___x_1936_; 
v_pos_1934_ = lean_ctor_get(v_s_1933_, 2);
v_toInputContext_1935_ = lean_ctor_get(v_c_1932_, 0);
v___x_1936_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1935_, v_pos_1934_);
if (v___x_1936_ == 0)
{
lean_object* v_inputString_1937_; uint8_t v___x_1938_; lean_object* v___y_1940_; uint32_t v_curr_1955_; lean_object* v___x_1956_; lean_object* v_s_1957_; uint32_t v___x_1958_; uint8_t v___x_1959_; 
v_inputString_1937_ = lean_ctor_get(v_toInputContext_1935_, 0);
v___x_1938_ = 1;
v_curr_1955_ = lean_string_utf8_get_fast(v_inputString_1937_, v_pos_1934_);
v___x_1956_ = lean_string_utf8_next_fast(v_inputString_1937_, v_pos_1934_);
v_s_1957_ = l_Lean_Parser_ParserState_setPos(v_s_1933_, v___x_1956_);
v___x_1958_ = 92;
v___x_1959_ = lean_uint32_dec_eq(v_curr_1955_, v___x_1958_);
if (v___x_1959_ == 0)
{
v___y_1940_ = v_s_1957_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1960_; 
lean_inc_ref(v_c_1932_);
v___x_1960_ = l_Lean_Parser_quotedCharFn(v_c_1932_, v_s_1957_);
v___y_1940_ = v___x_1960_;
goto v___jp_1939_;
}
v___jp_1939_:
{
lean_object* v_pos_1941_; lean_object* v_errorMsg_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v_pos_1941_ = lean_ctor_get(v___y_1940_, 2);
v_errorMsg_1942_ = lean_ctor_get(v___y_1940_, 4);
v___x_1943_ = lean_box(0);
v___x_1944_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_dec_ref(v_c_1932_);
lean_dec(v_startPos_1931_);
return v___y_1940_;
}
else
{
uint32_t v_curr_1945_; lean_object* v___x_1946_; lean_object* v_s_1947_; uint32_t v___x_1948_; uint8_t v___x_1949_; 
v_curr_1945_ = lean_string_utf8_get(v_inputString_1937_, v_pos_1941_);
v___x_1946_ = lean_string_utf8_next(v_inputString_1937_, v_pos_1941_);
v_s_1947_ = l_Lean_Parser_ParserState_setPos(v___y_1940_, v___x_1946_);
v___x_1948_ = 39;
v___x_1949_ = lean_uint32_dec_eq(v_curr_1945_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec_ref(v_c_1932_);
lean_dec(v_startPos_1931_);
v___x_1950_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__0));
v___x_1951_ = lean_box(0);
v___x_1952_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1947_, v___x_1950_, v___x_1951_, v___x_1938_);
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_1954_ = l_Lean_Parser_mkNodeToken(v___x_1953_, v_startPos_1931_, v___x_1938_, v_c_1932_, v_s_1947_);
return v___x_1954_;
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec_ref(v_c_1932_);
lean_dec(v_startPos_1931_);
v___x_1961_ = lean_box(0);
v___x_1962_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1933_, v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux___boxed(lean_object* v_startPos_1967_, lean_object* v_includeWhitespace_1968_, lean_object* v_c_1969_, lean_object* v_s_1970_){
_start:
{
uint8_t v_includeWhitespace_boxed_1971_; lean_object* v_res_1972_; 
v_includeWhitespace_boxed_1971_ = lean_unbox(v_includeWhitespace_1968_);
v_res_1972_ = l_Lean_Parser_strLitFnAux(v_startPos_1967_, v_includeWhitespace_boxed_1971_, v_c_1969_, v_s_1970_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFnAux(lean_object* v_startPos_1973_, uint8_t v_includeWhitespace_1974_, lean_object* v_c_1975_, lean_object* v_s_1976_){
_start:
{
lean_object* v_pos_1977_; lean_object* v_toInputContext_1978_; uint8_t v___x_1979_; 
v_pos_1977_ = lean_ctor_get(v_s_1976_, 2);
v_toInputContext_1978_ = lean_ctor_get(v_c_1975_, 0);
v___x_1979_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1978_, v_pos_1977_);
if (v___x_1979_ == 0)
{
lean_object* v_inputString_1980_; uint32_t v_curr_1981_; lean_object* v___x_1982_; lean_object* v_s_1983_; uint32_t v___x_1984_; uint8_t v___x_1985_; 
v_inputString_1980_ = lean_ctor_get(v_toInputContext_1978_, 0);
v_curr_1981_ = lean_string_utf8_get_fast(v_inputString_1980_, v_pos_1977_);
v___x_1982_ = lean_string_utf8_next_fast(v_inputString_1980_, v_pos_1977_);
v_s_1983_ = l_Lean_Parser_ParserState_setPos(v_s_1976_, v___x_1982_);
v___x_1984_ = 34;
v___x_1985_ = lean_uint32_dec_eq(v_curr_1981_, v___x_1984_);
if (v___x_1985_ == 0)
{
uint32_t v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = 92;
v___x_1987_ = lean_uint32_dec_eq(v_curr_1981_, v___x_1986_);
if (v___x_1987_ == 0)
{
v_s_1976_ = v_s_1983_;
goto _start;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1989_ = lean_alloc_closure((void*)(l_Lean_Parser_quotedStringFn), 2, 0);
v___x_1990_ = lean_box(v_includeWhitespace_1974_);
v___x_1991_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFnAux___boxed), 4, 2);
lean_closure_set(v___x_1991_, 0, v_startPos_1973_);
lean_closure_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_Lean_Parser_andthenFn(v___x_1989_, v___x_1991_, v_c_1975_, v_s_1983_);
return v___x_1992_;
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_1994_ = l_Lean_Parser_mkNodeToken(v___x_1993_, v_startPos_1973_, v_includeWhitespace_1974_, v_c_1975_, v_s_1983_);
return v___x_1994_;
}
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_dec_ref(v_c_1975_);
v___x_1995_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__2));
v___x_1996_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_1976_, v___x_1995_, v_startPos_1973_);
return v___x_1996_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isRawStrLitStart(lean_object* v_c_1997_, lean_object* v_i_1998_){
_start:
{
lean_object* v_toInputContext_1999_; uint8_t v___x_2000_; 
v_toInputContext_1999_ = lean_ctor_get(v_c_1997_, 0);
v___x_2000_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1999_, v_i_1998_);
if (v___x_2000_ == 0)
{
lean_object* v_inputString_2001_; uint32_t v_curr_2002_; uint32_t v___x_2003_; uint8_t v___x_2004_; 
v_inputString_2001_ = lean_ctor_get(v_toInputContext_1999_, 0);
v_curr_2002_ = lean_string_utf8_get_fast(v_inputString_2001_, v_i_1998_);
v___x_2003_ = 35;
v___x_2004_ = lean_uint32_dec_eq(v_curr_2002_, v___x_2003_);
if (v___x_2004_ == 0)
{
uint32_t v___x_2005_; uint8_t v___x_2006_; 
lean_dec(v_i_1998_);
v___x_2005_ = 34;
v___x_2006_ = lean_uint32_dec_eq(v_curr_2002_, v___x_2005_);
return v___x_2006_;
}
else
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_string_utf8_next_fast(v_inputString_2001_, v_i_1998_);
lean_dec(v_i_1998_);
v_i_1998_ = v___x_2007_;
goto _start;
}
}
else
{
uint8_t v___x_2009_; 
lean_dec(v_i_1998_);
v___x_2009_ = 0;
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isRawStrLitStart___boxed(lean_object* v_c_2010_, lean_object* v_i_2011_){
_start:
{
uint8_t v_res_2012_; lean_object* v_r_2013_; 
v_res_2012_ = l_Lean_Parser_isRawStrLitStart(v_c_2010_, v_i_2011_);
lean_dec_ref(v_c_2010_);
v_r_2013_ = lean_box(v_res_2012_);
return v_r_2013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(lean_object* v_startPos_2015_, lean_object* v_s_2016_){
_start:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated___closed__0));
v___x_2018_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2016_, v___x_2017_, v_startPos_2015_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(lean_object* v_startPos_2019_, lean_object* v_num_2020_, lean_object* v_closingNum_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_pos_2024_; lean_object* v_toInputContext_2025_; uint8_t v___x_2026_; 
v_pos_2024_ = lean_ctor_get(v_a_2023_, 2);
v_toInputContext_2025_ = lean_ctor_get(v_a_2022_, 0);
v___x_2026_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2025_, v_pos_2024_);
if (v___x_2026_ == 0)
{
lean_object* v_inputString_2027_; uint32_t v_curr_2028_; lean_object* v___x_2029_; lean_object* v_s_2030_; uint32_t v___x_2031_; uint8_t v___x_2032_; 
v_inputString_2027_ = lean_ctor_get(v_toInputContext_2025_, 0);
v_curr_2028_ = lean_string_utf8_get_fast(v_inputString_2027_, v_pos_2024_);
v___x_2029_ = lean_string_utf8_next_fast(v_inputString_2027_, v_pos_2024_);
v_s_2030_ = l_Lean_Parser_ParserState_setPos(v_a_2023_, v___x_2029_);
v___x_2031_ = 35;
v___x_2032_ = lean_uint32_dec_eq(v_curr_2028_, v___x_2031_);
if (v___x_2032_ == 0)
{
uint32_t v___x_2033_; uint8_t v___x_2034_; 
lean_dec(v_closingNum_2021_);
v___x_2033_ = 34;
v___x_2034_ = lean_uint32_dec_eq(v_curr_2028_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
v___x_2035_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2019_, v_num_2020_, v_a_2022_, v_s_2030_);
return v___x_2035_;
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v_closingNum_2021_ = v___x_2036_;
v_a_2023_ = v_s_2030_;
goto _start;
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_add(v_closingNum_2021_, v___x_2038_);
lean_dec(v_closingNum_2021_);
v___x_2040_ = lean_nat_dec_eq(v___x_2039_, v_num_2020_);
if (v___x_2040_ == 0)
{
v_closingNum_2021_ = v___x_2039_;
v_a_2023_ = v_s_2030_;
goto _start;
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec(v___x_2039_);
v___x_2042_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2043_ = l_Lean_Parser_mkNodeToken(v___x_2042_, v_startPos_2019_, v___x_2040_, v_a_2022_, v_s_2030_);
return v___x_2043_;
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec_ref(v_a_2022_);
lean_dec(v_closingNum_2021_);
v___x_2044_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2019_, v_a_2023_);
return v___x_2044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(lean_object* v_startPos_2045_, lean_object* v_num_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_pos_2049_; lean_object* v_toInputContext_2050_; uint8_t v___x_2051_; 
v_pos_2049_ = lean_ctor_get(v_a_2048_, 2);
v_toInputContext_2050_ = lean_ctor_get(v_a_2047_, 0);
v___x_2051_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2050_, v_pos_2049_);
if (v___x_2051_ == 0)
{
lean_object* v_inputString_2052_; uint32_t v_curr_2053_; lean_object* v___x_2054_; lean_object* v_s_2055_; uint32_t v___x_2056_; uint8_t v___x_2057_; 
v_inputString_2052_ = lean_ctor_get(v_toInputContext_2050_, 0);
v_curr_2053_ = lean_string_utf8_get_fast(v_inputString_2052_, v_pos_2049_);
v___x_2054_ = lean_string_utf8_next_fast(v_inputString_2052_, v_pos_2049_);
v_s_2055_ = l_Lean_Parser_ParserState_setPos(v_a_2048_, v___x_2054_);
v___x_2056_ = 34;
v___x_2057_ = lean_uint32_dec_eq(v_curr_2053_, v___x_2056_);
if (v___x_2057_ == 0)
{
v_a_2048_ = v_s_2055_;
goto _start;
}
else
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = lean_nat_dec_eq(v_num_2046_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
v___x_2061_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2045_, v_num_2046_, v___x_2059_, v_a_2047_, v_s_2055_);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_2063_ = l_Lean_Parser_mkNodeToken(v___x_2062_, v_startPos_2045_, v___x_2060_, v_a_2047_, v_s_2055_);
return v___x_2063_;
}
}
}
else
{
lean_object* v___x_2064_; 
lean_dec_ref(v_a_2047_);
v___x_2064_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2045_, v_a_2048_);
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState___boxed(lean_object* v_startPos_2065_, lean_object* v_num_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2065_, v_num_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_num_2066_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState___boxed(lean_object* v_startPos_2070_, lean_object* v_num_2071_, lean_object* v_closingNum_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_closingState(v_startPos_2070_, v_num_2071_, v_closingNum_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_num_2071_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(lean_object* v_startPos_2076_, lean_object* v_num_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_pos_2080_; lean_object* v_toInputContext_2081_; uint8_t v___x_2082_; 
v_pos_2080_ = lean_ctor_get(v_a_2079_, 2);
v_toInputContext_2081_ = lean_ctor_get(v_a_2078_, 0);
v___x_2082_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2081_, v_pos_2080_);
if (v___x_2082_ == 0)
{
lean_object* v_inputString_2083_; uint32_t v_curr_2084_; lean_object* v___x_2085_; lean_object* v_s_2086_; uint32_t v___x_2087_; uint8_t v___x_2088_; 
v_inputString_2083_ = lean_ctor_get(v_toInputContext_2081_, 0);
v_curr_2084_ = lean_string_utf8_get_fast(v_inputString_2083_, v_pos_2080_);
v___x_2085_ = lean_string_utf8_next_fast(v_inputString_2083_, v_pos_2080_);
v_s_2086_ = l_Lean_Parser_ParserState_setPos(v_a_2079_, v___x_2085_);
v___x_2087_ = 35;
v___x_2088_ = lean_uint32_dec_eq(v_curr_2084_, v___x_2087_);
if (v___x_2088_ == 0)
{
uint32_t v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = 34;
v___x_2090_ = lean_uint32_dec_eq(v_curr_2084_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref(v_a_2078_);
lean_dec(v_num_2077_);
v___x_2091_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2076_, v_s_2086_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; 
v___x_2092_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_normalState(v_startPos_2076_, v_num_2077_, v_a_2078_, v_s_2086_);
lean_dec(v_num_2077_);
return v___x_2092_;
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_add(v_num_2077_, v___x_2093_);
lean_dec(v_num_2077_);
v_num_2077_ = v___x_2094_;
v_a_2079_ = v_s_2086_;
goto _start;
}
}
else
{
lean_object* v___x_2096_; 
lean_dec_ref(v_a_2078_);
lean_dec(v_num_2077_);
v___x_2096_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_errorUnterminated(v_startPos_2076_, v_a_2079_);
return v___x_2096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawStrLitFnAux(lean_object* v_startPos_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = l___private_Lean_Parser_Basic_0__Lean_Parser_rawStrLitFnAux_initState(v_startPos_2097_, v___x_2100_, v_a_2098_, v_a_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn(lean_object* v_isDigit_2103_, lean_object* v_expecting_2104_, uint8_t v_needDigit_2105_, lean_object* v_c_2106_, lean_object* v_s_2107_){
_start:
{
lean_object* v_pos_2108_; lean_object* v_toInputContext_2109_; uint8_t v___x_2110_; 
v_pos_2108_ = lean_ctor_get(v_s_2107_, 2);
v_toInputContext_2109_ = lean_ctor_get(v_c_2106_, 0);
v___x_2110_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2109_, v_pos_2108_);
if (v___x_2110_ == 0)
{
lean_object* v_inputString_2111_; uint8_t v___x_2112_; uint32_t v_curr_2113_; uint32_t v___x_2114_; uint8_t v___x_2115_; 
v_inputString_2111_ = lean_ctor_get(v_toInputContext_2109_, 0);
v___x_2112_ = 1;
v_curr_2113_ = lean_string_utf8_get_fast(v_inputString_2111_, v_pos_2108_);
v___x_2114_ = 95;
v___x_2115_ = lean_uint32_dec_eq(v_curr_2113_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = lean_box_uint32(v_curr_2113_);
lean_inc_ref(v_isDigit_2103_);
v___x_2117_ = lean_apply_1(v_isDigit_2103_, v___x_2116_);
v___x_2118_ = lean_unbox(v___x_2117_);
if (v___x_2118_ == 0)
{
lean_dec_ref(v_isDigit_2103_);
if (v_needDigit_2105_ == 0)
{
lean_dec_ref(v_expecting_2104_);
return v_s_2107_;
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = ((lean_object*)(l_Lean_Parser_takeDigitsFn___closed__0));
v___x_2120_ = lean_box(0);
v___x_2121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_expecting_2104_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2107_, v___x_2119_, v___x_2121_, v___x_2112_);
return v___x_2122_;
}
}
else
{
lean_object* v___x_2123_; 
lean_inc(v_pos_2108_);
v___x_2123_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2107_, v_c_2106_, v_pos_2108_);
lean_dec(v_pos_2108_);
v_needDigit_2105_ = v___x_2115_;
v_s_2107_ = v___x_2123_;
goto _start;
}
}
else
{
lean_object* v___x_2125_; 
lean_inc(v_pos_2108_);
v___x_2125_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2107_, v_c_2106_, v_pos_2108_);
lean_dec(v_pos_2108_);
v_needDigit_2105_ = v___x_2112_;
v_s_2107_ = v___x_2125_;
goto _start;
}
}
else
{
lean_dec_ref(v_isDigit_2103_);
if (v_needDigit_2105_ == 0)
{
lean_dec_ref(v_expecting_2104_);
return v_s_2107_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2128_, 0, v_expecting_2104_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2107_, v___x_2128_);
return v___x_2129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_takeDigitsFn___boxed(lean_object* v_isDigit_2130_, lean_object* v_expecting_2131_, lean_object* v_needDigit_2132_, lean_object* v_c_2133_, lean_object* v_s_2134_){
_start:
{
uint8_t v_needDigit_boxed_2135_; lean_object* v_res_2136_; 
v_needDigit_boxed_2135_ = lean_unbox(v_needDigit_2132_);
v_res_2136_ = l_Lean_Parser_takeDigitsFn(v_isDigit_2130_, v_expecting_2131_, v_needDigit_boxed_2135_, v_c_2133_, v_s_2134_);
lean_dec_ref(v_c_2133_);
return v_res_2136_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(uint32_t v_c_2137_){
_start:
{
uint32_t v___x_2138_; uint8_t v___x_2139_; 
v___x_2138_ = 48;
v___x_2139_ = lean_uint32_dec_le(v___x_2138_, v_c_2137_);
if (v___x_2139_ == 0)
{
return v___x_2139_;
}
else
{
uint32_t v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = 57;
v___x_2141_ = lean_uint32_dec_le(v_c_2137_, v___x_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0___boxed(lean_object* v_c_2142_){
_start:
{
uint32_t v_c_boxed_2143_; uint8_t v_res_2144_; lean_object* v_r_2145_; 
v_c_boxed_2143_ = lean_unbox_uint32(v_c_2142_);
lean_dec(v_c_2142_);
v_res_2144_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___lam__0(v_c_boxed_2143_);
v_r_2145_ = lean_box(v_res_2144_);
return v_r_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(lean_object* v_startPos_2150_, lean_object* v_c_2151_, lean_object* v_s_2152_, uint8_t v_hasBareDot_2153_){
_start:
{
lean_object* v_toInputContext_2154_; lean_object* v_pos_2155_; uint8_t v___x_2156_; 
v_toInputContext_2154_ = lean_ctor_get(v_c_2151_, 0);
v_pos_2155_ = lean_ctor_get(v_s_2152_, 2);
v___x_2156_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2154_, v_pos_2155_);
if (v___x_2156_ == 0)
{
lean_object* v_inputString_2157_; lean_object* v___f_2158_; uint8_t v___x_2159_; lean_object* v___y_2165_; lean_object* v___y_2175_; lean_object* v___y_2176_; uint32_t v_curr_2190_; uint32_t v___x_2202_; uint8_t v___x_2203_; 
v_inputString_2157_ = lean_ctor_get(v_toInputContext_2154_, 0);
v___f_2158_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2159_ = 1;
v_curr_2190_ = lean_string_utf8_get_fast(v_inputString_2157_, v_pos_2155_);
v___x_2202_ = 101;
v___x_2203_ = lean_uint32_dec_eq(v_curr_2190_, v___x_2202_);
if (v___x_2203_ == 0)
{
uint32_t v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = 69;
v___x_2205_ = lean_uint32_dec_eq(v_curr_2190_, v___x_2204_);
if (v___x_2205_ == 0)
{
if (v_hasBareDot_2153_ == 0)
{
lean_dec(v_startPos_2150_);
return v_s_2152_;
}
else
{
uint32_t v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = 65;
v___x_2207_ = lean_uint32_dec_le(v___x_2206_, v_curr_2190_);
if (v___x_2207_ == 0)
{
goto v___jp_2197_;
}
else
{
uint32_t v___x_2208_; uint8_t v___x_2209_; 
v___x_2208_ = 90;
v___x_2209_ = lean_uint32_dec_le(v_curr_2190_, v___x_2208_);
if (v___x_2209_ == 0)
{
goto v___jp_2197_;
}
else
{
goto v___jp_2185_;
}
}
}
}
else
{
lean_dec(v_startPos_2150_);
goto v___jp_2178_;
}
}
else
{
lean_dec(v_startPos_2150_);
goto v___jp_2178_;
}
v___jp_2160_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__1));
v___x_2162_ = lean_box(0);
v___x_2163_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_2152_, v___x_2161_, v___x_2162_, v___x_2159_);
return v___x_2163_;
}
v___jp_2164_:
{
uint32_t v_curr_2166_; uint32_t v___x_2167_; uint8_t v___x_2168_; 
v_curr_2166_ = lean_string_utf8_get(v_inputString_2157_, v___y_2165_);
v___x_2167_ = 48;
v___x_2168_ = lean_uint32_dec_le(v___x_2167_, v_curr_2166_);
if (v___x_2168_ == 0)
{
lean_dec(v___y_2165_);
goto v___jp_2160_;
}
else
{
uint32_t v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = 57;
v___x_2170_ = lean_uint32_dec_le(v_curr_2166_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_dec(v___y_2165_);
goto v___jp_2160_;
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2172_ = l_Lean_Parser_ParserState_setPos(v_s_2152_, v___y_2165_);
v___x_2173_ = l_Lean_Parser_takeDigitsFn(v___f_2158_, v___x_2171_, v___x_2156_, v_c_2151_, v___x_2172_);
return v___x_2173_;
}
}
}
v___jp_2174_:
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_string_utf8_next(v___y_2176_, v___y_2175_);
lean_dec(v___y_2175_);
v___y_2165_ = v___x_2177_;
goto v___jp_2164_;
}
v___jp_2178_:
{
lean_object* v_i_2179_; uint32_t v___x_2180_; uint32_t v___x_2181_; uint8_t v___x_2182_; 
v_i_2179_ = lean_string_utf8_next(v_inputString_2157_, v_pos_2155_);
v___x_2180_ = lean_string_utf8_get(v_inputString_2157_, v_i_2179_);
v___x_2181_ = 45;
v___x_2182_ = lean_uint32_dec_eq(v___x_2180_, v___x_2181_);
if (v___x_2182_ == 0)
{
uint32_t v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = 43;
v___x_2184_ = lean_uint32_dec_eq(v___x_2180_, v___x_2183_);
if (v___x_2184_ == 0)
{
v___y_2165_ = v_i_2179_;
goto v___jp_2164_;
}
else
{
v___y_2175_ = v_i_2179_;
v___y_2176_ = v_inputString_2157_;
goto v___jp_2174_;
}
}
else
{
v___y_2175_ = v_i_2179_;
v___y_2176_ = v_inputString_2157_;
goto v___jp_2174_;
}
}
v___jp_2185_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2186_ = l_Lean_Parser_ParserState_setPos(v_s_2152_, v_startPos_2150_);
v___x_2187_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__3));
v___x_2188_ = lean_box(0);
v___x_2189_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_2186_, v___x_2187_, v___x_2188_, v___x_2159_);
return v___x_2189_;
}
v___jp_2191_:
{
uint32_t v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = 95;
v___x_2193_ = lean_uint32_dec_eq(v_curr_2190_, v___x_2192_);
if (v___x_2193_ == 0)
{
uint8_t v___x_2194_; 
v___x_2194_ = l_Lean_isLetterLike(v_curr_2190_);
if (v___x_2194_ == 0)
{
uint32_t v___x_2195_; uint8_t v___x_2196_; 
v___x_2195_ = l_Lean_idBeginEscape;
v___x_2196_ = lean_uint32_dec_eq(v_curr_2190_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_dec(v_startPos_2150_);
return v_s_2152_;
}
else
{
goto v___jp_2185_;
}
}
else
{
goto v___jp_2185_;
}
}
else
{
goto v___jp_2185_;
}
}
v___jp_2197_:
{
uint32_t v___x_2198_; uint8_t v___x_2199_; 
v___x_2198_ = 97;
v___x_2199_ = lean_uint32_dec_le(v___x_2198_, v_curr_2190_);
if (v___x_2199_ == 0)
{
goto v___jp_2191_;
}
else
{
uint32_t v___x_2200_; uint8_t v___x_2201_; 
v___x_2200_ = 122;
v___x_2201_ = lean_uint32_dec_le(v_curr_2190_, v___x_2200_);
if (v___x_2201_ == 0)
{
goto v___jp_2191_;
}
else
{
goto v___jp_2185_;
}
}
}
}
else
{
lean_dec(v_startPos_2150_);
return v_s_2152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___boxed(lean_object* v_startPos_2210_, lean_object* v_c_2211_, lean_object* v_s_2212_, lean_object* v_hasBareDot_2213_){
_start:
{
uint8_t v_hasBareDot_boxed_2214_; lean_object* v_res_2215_; 
v_hasBareDot_boxed_2214_ = lean_unbox(v_hasBareDot_2213_);
v_res_2215_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2210_, v_c_2211_, v_s_2212_, v_hasBareDot_boxed_2214_);
lean_dec_ref(v_c_2211_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(lean_object* v_c_2216_, lean_object* v_s_2217_){
_start:
{
lean_object* v_toInputContext_2218_; lean_object* v_pos_2219_; lean_object* v_inputString_2220_; uint32_t v_curr_2221_; uint32_t v___x_2222_; uint8_t v___x_2223_; 
v_toInputContext_2218_ = lean_ctor_get(v_c_2216_, 0);
v_pos_2219_ = lean_ctor_get(v_s_2217_, 2);
v_inputString_2220_ = lean_ctor_get(v_toInputContext_2218_, 0);
v_curr_2221_ = lean_string_utf8_get(v_inputString_2220_, v_pos_2219_);
v___x_2222_ = 46;
v___x_2223_ = lean_uint32_dec_eq(v_curr_2221_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_box(v___x_2223_);
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v_s_2217_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
return v___x_2225_;
}
else
{
lean_object* v_i_2226_; uint32_t v_curr_2231_; uint32_t v___x_2232_; uint8_t v___x_2233_; 
v_i_2226_ = lean_string_utf8_next(v_inputString_2220_, v_pos_2219_);
v_curr_2231_ = lean_string_utf8_get(v_inputString_2220_, v_i_2226_);
v___x_2232_ = 48;
v___x_2233_ = lean_uint32_dec_le(v___x_2232_, v_curr_2231_);
if (v___x_2233_ == 0)
{
goto v___jp_2227_;
}
else
{
uint32_t v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = 57;
v___x_2235_ = lean_uint32_dec_le(v_curr_2231_, v___x_2234_);
if (v___x_2235_ == 0)
{
goto v___jp_2227_;
}
else
{
lean_object* v___f_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___f_2236_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2237_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2238_ = 0;
v___x_2239_ = l_Lean_Parser_ParserState_setPos(v_s_2217_, v_i_2226_);
v___x_2240_ = l_Lean_Parser_takeDigitsFn(v___f_2236_, v___x_2237_, v___x_2238_, v_c_2216_, v___x_2239_);
v___x_2241_ = lean_box(v___x_2238_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
return v___x_2242_;
}
}
v___jp_2227_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = l_Lean_Parser_ParserState_setPos(v_s_2217_, v_i_2226_);
v___x_2229_ = lean_box(v___x_2223_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
return v___x_2230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot___boxed(lean_object* v_c_2243_, lean_object* v_s_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2243_, v_s_2244_);
lean_dec_ref(v_c_2243_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(lean_object* v_startPos_2249_, uint8_t v_includeWhitespace_2250_, lean_object* v_c_2251_, lean_object* v_s_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v_fst_2254_; lean_object* v_snd_2255_; uint8_t v___x_2256_; lean_object* v_s_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2253_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptDot(v_c_2251_, v_s_2252_);
v_fst_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_fst_2254_);
v_snd_2255_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2253_);
v___x_2256_ = lean_unbox(v_snd_2255_);
lean_dec(v_snd_2255_);
lean_inc(v_startPos_2249_);
v_s_2257_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp(v_startPos_2249_, v_c_2251_, v_fst_2254_, v___x_2256_);
v___x_2258_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_2259_ = l_Lean_Parser_mkNodeToken(v___x_2258_, v_startPos_2249_, v_includeWhitespace_2250_, v_c_2251_, v_s_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___boxed(lean_object* v_startPos_2260_, lean_object* v_includeWhitespace_2261_, lean_object* v_c_2262_, lean_object* v_s_2263_){
_start:
{
uint8_t v_includeWhitespace_boxed_2264_; lean_object* v_res_2265_; 
v_includeWhitespace_boxed_2264_ = lean_unbox(v_includeWhitespace_2261_);
v_res_2265_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2260_, v_includeWhitespace_boxed_2264_, v_c_2262_, v_s_2263_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn(lean_object* v_startPos_2269_, uint8_t v_includeWhitespace_2270_, lean_object* v_c_2271_, lean_object* v_s_2272_){
_start:
{
lean_object* v___f_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; lean_object* v_s_2276_; lean_object* v_pos_2277_; lean_object* v_toInputContext_2278_; uint8_t v___x_2279_; 
v___f_2273_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v___x_2274_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__2));
v___x_2275_ = 0;
v_s_2276_ = l_Lean_Parser_takeDigitsFn(v___f_2273_, v___x_2274_, v___x_2275_, v_c_2271_, v_s_2272_);
v_pos_2277_ = lean_ctor_get(v_s_2276_, 2);
v_toInputContext_2278_ = lean_ctor_get(v_c_2271_, 0);
v___x_2279_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2278_, v_pos_2277_);
if (v___x_2279_ == 0)
{
lean_object* v_inputString_2280_; uint32_t v_curr_2281_; lean_object* v_j_2294_; uint8_t v___x_2295_; 
v_inputString_2280_ = lean_ctor_get(v_toInputContext_2278_, 0);
v_curr_2281_ = lean_string_utf8_get_fast(v_inputString_2280_, v_pos_2277_);
v_j_2294_ = lean_string_utf8_next(v_inputString_2280_, v_pos_2277_);
v___x_2295_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2278_, v_j_2294_);
if (v___x_2295_ == 0)
{
uint32_t v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = 46;
v___x_2297_ = lean_uint32_dec_eq(v_curr_2281_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_dec(v_j_2294_);
goto v___jp_2282_;
}
else
{
uint32_t v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = lean_string_utf8_get_fast(v_inputString_2280_, v_j_2294_);
lean_dec(v_j_2294_);
v___x_2299_ = lean_uint32_dec_eq(v___x_2298_, v___x_2296_);
if (v___x_2299_ == 0)
{
goto v___jp_2282_;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2301_ = l_Lean_Parser_mkNodeToken(v___x_2300_, v_startPos_2269_, v_includeWhitespace_2270_, v_c_2271_, v_s_2276_);
return v___x_2301_;
}
}
}
else
{
lean_dec(v_j_2294_);
goto v___jp_2282_;
}
v___jp_2282_:
{
uint32_t v___x_2283_; uint8_t v___x_2284_; 
v___x_2283_ = 46;
v___x_2284_ = lean_uint32_dec_eq(v_curr_2281_, v___x_2283_);
if (v___x_2284_ == 0)
{
uint32_t v___x_2285_; uint8_t v___x_2286_; 
v___x_2285_ = 101;
v___x_2286_ = lean_uint32_dec_eq(v_curr_2281_, v___x_2285_);
if (v___x_2286_ == 0)
{
uint32_t v___x_2287_; uint8_t v___x_2288_; 
v___x_2287_ = 69;
v___x_2288_ = lean_uint32_dec_eq(v_curr_2281_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2290_ = l_Lean_Parser_mkNodeToken(v___x_2289_, v_startPos_2269_, v_includeWhitespace_2270_, v_c_2271_, v_s_2276_);
return v___x_2290_;
}
else
{
lean_object* v___x_2291_; 
v___x_2291_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2269_, v_includeWhitespace_2270_, v_c_2271_, v_s_2276_);
return v___x_2291_;
}
}
else
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2269_, v_includeWhitespace_2270_, v_c_2271_, v_s_2276_);
return v___x_2292_;
}
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific(v_startPos_2269_, v_includeWhitespace_2270_, v_c_2271_, v_s_2276_);
return v___x_2293_;
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2303_ = l_Lean_Parser_mkNodeToken(v___x_2302_, v_startPos_2269_, v___x_2279_, v_c_2271_, v_s_2276_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_decimalNumberFn___boxed(lean_object* v_startPos_2304_, lean_object* v_includeWhitespace_2305_, lean_object* v_c_2306_, lean_object* v_s_2307_){
_start:
{
uint8_t v_includeWhitespace_boxed_2308_; lean_object* v_res_2309_; 
v_includeWhitespace_boxed_2308_ = lean_unbox(v_includeWhitespace_2305_);
v_res_2309_ = l_Lean_Parser_decimalNumberFn(v_startPos_2304_, v_includeWhitespace_boxed_2308_, v_c_2306_, v_s_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_binNumberFn___lam__0(uint32_t v_c_2310_){
_start:
{
uint32_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = 48;
v___x_2312_ = lean_uint32_dec_eq(v_c_2310_, v___x_2311_);
if (v___x_2312_ == 0)
{
uint32_t v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = 49;
v___x_2314_ = lean_uint32_dec_eq(v_c_2310_, v___x_2313_);
return v___x_2314_;
}
else
{
return v___x_2312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___lam__0___boxed(lean_object* v_c_2315_){
_start:
{
uint32_t v_c_boxed_2316_; uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_c_boxed_2316_ = lean_unbox_uint32(v_c_2315_);
lean_dec(v_c_2315_);
v_res_2317_ = l_Lean_Parser_binNumberFn___lam__0(v_c_boxed_2316_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn(lean_object* v_startPos_2321_, uint8_t v_includeWhitespace_2322_, lean_object* v_c_2323_, lean_object* v_s_2324_){
_start:
{
lean_object* v___f_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; lean_object* v_s_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___f_2325_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__0));
v___x_2326_ = ((lean_object*)(l_Lean_Parser_binNumberFn___closed__1));
v___x_2327_ = 1;
v_s_2328_ = l_Lean_Parser_takeDigitsFn(v___f_2325_, v___x_2326_, v___x_2327_, v_c_2323_, v_s_2324_);
v___x_2329_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2330_ = l_Lean_Parser_mkNodeToken(v___x_2329_, v_startPos_2321_, v_includeWhitespace_2322_, v_c_2323_, v_s_2328_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_binNumberFn___boxed(lean_object* v_startPos_2331_, lean_object* v_includeWhitespace_2332_, lean_object* v_c_2333_, lean_object* v_s_2334_){
_start:
{
uint8_t v_includeWhitespace_boxed_2335_; lean_object* v_res_2336_; 
v_includeWhitespace_boxed_2335_ = lean_unbox(v_includeWhitespace_2332_);
v_res_2336_ = l_Lean_Parser_binNumberFn(v_startPos_2331_, v_includeWhitespace_boxed_2335_, v_c_2333_, v_s_2334_);
return v_res_2336_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_octalNumberFn___lam__0(uint32_t v_c_2337_){
_start:
{
uint32_t v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = 48;
v___x_2339_ = lean_uint32_dec_le(v___x_2338_, v_c_2337_);
if (v___x_2339_ == 0)
{
return v___x_2339_;
}
else
{
uint32_t v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = 55;
v___x_2341_ = lean_uint32_dec_le(v_c_2337_, v___x_2340_);
return v___x_2341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___lam__0___boxed(lean_object* v_c_2342_){
_start:
{
uint32_t v_c_boxed_2343_; uint8_t v_res_2344_; lean_object* v_r_2345_; 
v_c_boxed_2343_ = lean_unbox_uint32(v_c_2342_);
lean_dec(v_c_2342_);
v_res_2344_ = l_Lean_Parser_octalNumberFn___lam__0(v_c_boxed_2343_);
v_r_2345_ = lean_box(v_res_2344_);
return v_r_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn(lean_object* v_startPos_2348_, uint8_t v_includeWhitespace_2349_, lean_object* v_c_2350_, lean_object* v_s_2351_){
_start:
{
lean_object* v___f_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; lean_object* v_s_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___f_2352_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__0));
v___x_2353_ = ((lean_object*)(l_Lean_Parser_octalNumberFn___closed__1));
v___x_2354_ = 1;
v_s_2355_ = l_Lean_Parser_takeDigitsFn(v___f_2352_, v___x_2353_, v___x_2354_, v_c_2350_, v_s_2351_);
v___x_2356_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2357_ = l_Lean_Parser_mkNodeToken(v___x_2356_, v_startPos_2348_, v_includeWhitespace_2349_, v_c_2350_, v_s_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_octalNumberFn___boxed(lean_object* v_startPos_2358_, lean_object* v_includeWhitespace_2359_, lean_object* v_c_2360_, lean_object* v_s_2361_){
_start:
{
uint8_t v_includeWhitespace_boxed_2362_; lean_object* v_res_2363_; 
v_includeWhitespace_boxed_2362_ = lean_unbox(v_includeWhitespace_2359_);
v_res_2363_ = l_Lean_Parser_octalNumberFn(v_startPos_2358_, v_includeWhitespace_boxed_2362_, v_c_2360_, v_s_2361_);
return v_res_2363_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(uint32_t v_c_2364_){
_start:
{
uint32_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2375_ = 48;
v___x_2376_ = lean_uint32_dec_le(v___x_2375_, v_c_2364_);
if (v___x_2376_ == 0)
{
goto v___jp_2370_;
}
else
{
uint32_t v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = 57;
v___x_2378_ = lean_uint32_dec_le(v_c_2364_, v___x_2377_);
if (v___x_2378_ == 0)
{
goto v___jp_2370_;
}
else
{
return v___x_2378_;
}
}
v___jp_2365_:
{
uint32_t v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = 65;
v___x_2367_ = lean_uint32_dec_le(v___x_2366_, v_c_2364_);
if (v___x_2367_ == 0)
{
return v___x_2367_;
}
else
{
uint32_t v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = 70;
v___x_2369_ = lean_uint32_dec_le(v_c_2364_, v___x_2368_);
return v___x_2369_;
}
}
v___jp_2370_:
{
uint32_t v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = 97;
v___x_2372_ = lean_uint32_dec_le(v___x_2371_, v_c_2364_);
if (v___x_2372_ == 0)
{
goto v___jp_2365_;
}
else
{
uint32_t v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = 102;
v___x_2374_ = lean_uint32_dec_le(v_c_2364_, v___x_2373_);
if (v___x_2374_ == 0)
{
goto v___jp_2365_;
}
else
{
return v___x_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit___boxed(lean_object* v_c_2379_){
_start:
{
uint32_t v_c_boxed_2380_; uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_c_boxed_2380_ = lean_unbox_uint32(v_c_2379_);
lean_dec(v_c_2379_);
v_res_2381_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isHexDigit(v_c_boxed_2380_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_hexNumberFn___lam__0(uint32_t v___y_2383_){
_start:
{
uint32_t v___x_2394_; uint8_t v___x_2395_; 
v___x_2394_ = 48;
v___x_2395_ = lean_uint32_dec_le(v___x_2394_, v___y_2383_);
if (v___x_2395_ == 0)
{
goto v___jp_2389_;
}
else
{
uint32_t v___x_2396_; uint8_t v___x_2397_; 
v___x_2396_ = 57;
v___x_2397_ = lean_uint32_dec_le(v___y_2383_, v___x_2396_);
if (v___x_2397_ == 0)
{
goto v___jp_2389_;
}
else
{
return v___x_2397_;
}
}
v___jp_2384_:
{
uint32_t v___x_2385_; uint8_t v___x_2386_; 
v___x_2385_ = 65;
v___x_2386_ = lean_uint32_dec_le(v___x_2385_, v___y_2383_);
if (v___x_2386_ == 0)
{
return v___x_2386_;
}
else
{
uint32_t v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = 70;
v___x_2388_ = lean_uint32_dec_le(v___y_2383_, v___x_2387_);
return v___x_2388_;
}
}
v___jp_2389_:
{
uint32_t v___x_2390_; uint8_t v___x_2391_; 
v___x_2390_ = 97;
v___x_2391_ = lean_uint32_dec_le(v___x_2390_, v___y_2383_);
if (v___x_2391_ == 0)
{
goto v___jp_2384_;
}
else
{
uint32_t v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = 102;
v___x_2393_ = lean_uint32_dec_le(v___y_2383_, v___x_2392_);
if (v___x_2393_ == 0)
{
goto v___jp_2384_;
}
else
{
return v___x_2393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___lam__0___boxed(lean_object* v___y_2398_){
_start:
{
uint32_t v___y_110__boxed_2399_; uint8_t v_res_2400_; lean_object* v_r_2401_; 
v___y_110__boxed_2399_ = lean_unbox_uint32(v___y_2398_);
lean_dec(v___y_2398_);
v_res_2400_ = l_Lean_Parser_hexNumberFn___lam__0(v___y_110__boxed_2399_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn(lean_object* v_startPos_2404_, uint8_t v_includeWhitespace_2405_, lean_object* v_kind_2406_, lean_object* v_c_2407_, lean_object* v_s_2408_){
_start:
{
lean_object* v___f_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v_s_2412_; lean_object* v___x_2413_; 
v___f_2409_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__0));
v___x_2410_ = ((lean_object*)(l_Lean_Parser_hexNumberFn___closed__1));
v___x_2411_ = 1;
v_s_2412_ = l_Lean_Parser_takeDigitsFn(v___f_2409_, v___x_2410_, v___x_2411_, v_c_2407_, v_s_2408_);
v___x_2413_ = l_Lean_Parser_mkNodeToken(v_kind_2406_, v_startPos_2404_, v_includeWhitespace_2405_, v_c_2407_, v_s_2412_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexNumberFn___boxed(lean_object* v_startPos_2414_, lean_object* v_includeWhitespace_2415_, lean_object* v_kind_2416_, lean_object* v_c_2417_, lean_object* v_s_2418_){
_start:
{
uint8_t v_includeWhitespace_boxed_2419_; lean_object* v_res_2420_; 
v_includeWhitespace_boxed_2419_ = lean_unbox(v_includeWhitespace_2415_);
v_res_2420_ = l_Lean_Parser_hexNumberFn(v_startPos_2414_, v_includeWhitespace_boxed_2419_, v_kind_2416_, v_c_2417_, v_s_2418_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux(uint8_t v_includeWhitespace_2422_, lean_object* v_c_2423_, lean_object* v_s_2424_){
_start:
{
lean_object* v_pos_2428_; lean_object* v_toInputContext_2429_; uint8_t v___x_2430_; 
v_pos_2428_ = lean_ctor_get(v_s_2424_, 2);
v_toInputContext_2429_ = lean_ctor_get(v_c_2423_, 0);
v___x_2430_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2429_, v_pos_2428_);
if (v___x_2430_ == 0)
{
lean_object* v_inputString_2431_; uint32_t v_curr_2432_; uint32_t v___x_2433_; uint8_t v___x_2434_; 
v_inputString_2431_ = lean_ctor_get(v_toInputContext_2429_, 0);
v_curr_2432_ = lean_string_utf8_get_fast(v_inputString_2431_, v_pos_2428_);
v___x_2433_ = 48;
v___x_2434_ = lean_uint32_dec_eq(v_curr_2432_, v___x_2433_);
if (v___x_2434_ == 0)
{
uint8_t v___x_2435_; 
v___x_2435_ = lean_uint32_dec_le(v___x_2433_, v_curr_2432_);
if (v___x_2435_ == 0)
{
lean_dec_ref(v_c_2423_);
goto v___jp_2425_;
}
else
{
uint32_t v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = 57;
v___x_2437_ = lean_uint32_dec_le(v_curr_2432_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_dec_ref(v_c_2423_);
goto v___jp_2425_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
lean_inc(v_pos_2428_);
v___x_2438_ = l_Lean_Parser_ParserState_next(v_s_2424_, v_c_2423_, v_pos_2428_);
v___x_2439_ = l_Lean_Parser_decimalNumberFn(v_pos_2428_, v_includeWhitespace_2422_, v_c_2423_, v___x_2438_);
return v___x_2439_;
}
}
}
else
{
lean_object* v_i_2440_; uint32_t v_curr_2451_; uint32_t v___x_2452_; uint8_t v___x_2453_; 
lean_inc(v_pos_2428_);
v_i_2440_ = lean_string_utf8_next_fast(v_inputString_2431_, v_pos_2428_);
v_curr_2451_ = lean_string_utf8_get(v_inputString_2431_, v_i_2440_);
v___x_2452_ = 98;
v___x_2453_ = lean_uint32_dec_eq(v_curr_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
uint32_t v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = 66;
v___x_2455_ = lean_uint32_dec_eq(v_curr_2451_, v___x_2454_);
if (v___x_2455_ == 0)
{
uint32_t v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = 111;
v___x_2457_ = lean_uint32_dec_eq(v_curr_2451_, v___x_2456_);
if (v___x_2457_ == 0)
{
uint32_t v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = 79;
v___x_2459_ = lean_uint32_dec_eq(v_curr_2451_, v___x_2458_);
if (v___x_2459_ == 0)
{
uint32_t v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = 120;
v___x_2461_ = lean_uint32_dec_eq(v_curr_2451_, v___x_2460_);
if (v___x_2461_ == 0)
{
uint32_t v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = 88;
v___x_2463_ = lean_uint32_dec_eq(v_curr_2451_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = l_Lean_Parser_ParserState_setPos(v_s_2424_, v_i_2440_);
v___x_2465_ = l_Lean_Parser_decimalNumberFn(v_pos_2428_, v_includeWhitespace_2422_, v_c_2423_, v___x_2464_);
return v___x_2465_;
}
else
{
goto v___jp_2441_;
}
}
else
{
goto v___jp_2441_;
}
}
else
{
goto v___jp_2445_;
}
}
else
{
goto v___jp_2445_;
}
}
else
{
goto v___jp_2448_;
}
}
else
{
goto v___jp_2448_;
}
v___jp_2441_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_2443_ = l_Lean_Parser_ParserState_next(v_s_2424_, v_c_2423_, v_i_2440_);
v___x_2444_ = l_Lean_Parser_hexNumberFn(v_pos_2428_, v_includeWhitespace_2422_, v___x_2442_, v_c_2423_, v___x_2443_);
return v___x_2444_;
}
v___jp_2445_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = l_Lean_Parser_ParserState_next(v_s_2424_, v_c_2423_, v_i_2440_);
v___x_2447_ = l_Lean_Parser_octalNumberFn(v_pos_2428_, v_includeWhitespace_2422_, v_c_2423_, v___x_2446_);
return v___x_2447_;
}
v___jp_2448_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = l_Lean_Parser_ParserState_next(v_s_2424_, v_c_2423_, v_i_2440_);
v___x_2450_ = l_Lean_Parser_binNumberFn(v_pos_2428_, v_includeWhitespace_2422_, v_c_2423_, v___x_2449_);
return v___x_2450_;
}
}
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec_ref(v_c_2423_);
v___x_2466_ = lean_box(0);
v___x_2467_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2424_, v___x_2466_);
return v___x_2467_;
}
v___jp_2425_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_2427_ = l_Lean_Parser_ParserState_mkError(v_s_2424_, v___x_2426_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numberFnAux___boxed(lean_object* v_includeWhitespace_2468_, lean_object* v_c_2469_, lean_object* v_s_2470_){
_start:
{
uint8_t v_includeWhitespace_boxed_2471_; lean_object* v_res_2472_; 
v_includeWhitespace_boxed_2471_ = lean_unbox(v_includeWhitespace_2468_);
v_res_2472_ = l_Lean_Parser_numberFnAux(v_includeWhitespace_boxed_2471_, v_c_2469_, v_s_2470_);
return v_res_2472_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_isIdCont(lean_object* v_c_2473_, lean_object* v_s_2474_){
_start:
{
lean_object* v_toInputContext_2475_; lean_object* v_pos_2476_; lean_object* v_inputString_2477_; uint32_t v_curr_2478_; uint32_t v___x_2479_; uint8_t v___x_2480_; 
v_toInputContext_2475_ = lean_ctor_get(v_c_2473_, 0);
v_pos_2476_ = lean_ctor_get(v_s_2474_, 2);
v_inputString_2477_ = lean_ctor_get(v_toInputContext_2475_, 0);
v_curr_2478_ = lean_string_utf8_get(v_inputString_2477_, v_pos_2476_);
v___x_2479_ = 46;
v___x_2480_ = lean_uint32_dec_eq(v_curr_2478_, v___x_2479_);
if (v___x_2480_ == 0)
{
return v___x_2480_;
}
else
{
lean_object* v_i_2481_; uint8_t v___x_2482_; 
v_i_2481_ = lean_string_utf8_next(v_inputString_2477_, v_pos_2476_);
v___x_2482_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2475_, v_i_2481_);
if (v___x_2482_ == 0)
{
uint32_t v_curr_2483_; uint32_t v___x_2495_; uint8_t v___x_2496_; 
v_curr_2483_ = lean_string_utf8_get(v_inputString_2477_, v_i_2481_);
lean_dec(v_i_2481_);
v___x_2495_ = 65;
v___x_2496_ = lean_uint32_dec_le(v___x_2495_, v_curr_2483_);
if (v___x_2496_ == 0)
{
goto v___jp_2490_;
}
else
{
uint32_t v___x_2497_; uint8_t v___x_2498_; 
v___x_2497_ = 90;
v___x_2498_ = lean_uint32_dec_le(v_curr_2483_, v___x_2497_);
if (v___x_2498_ == 0)
{
goto v___jp_2490_;
}
else
{
return v___x_2480_;
}
}
v___jp_2484_:
{
uint32_t v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = 95;
v___x_2486_ = lean_uint32_dec_eq(v_curr_2483_, v___x_2485_);
if (v___x_2486_ == 0)
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Lean_isLetterLike(v_curr_2483_);
if (v___x_2487_ == 0)
{
uint32_t v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = l_Lean_idBeginEscape;
v___x_2489_ = lean_uint32_dec_eq(v_curr_2483_, v___x_2488_);
return v___x_2489_;
}
else
{
return v___x_2480_;
}
}
else
{
return v___x_2480_;
}
}
v___jp_2490_:
{
uint32_t v___x_2491_; uint8_t v___x_2492_; 
v___x_2491_ = 97;
v___x_2492_ = lean_uint32_dec_le(v___x_2491_, v_curr_2483_);
if (v___x_2492_ == 0)
{
goto v___jp_2484_;
}
else
{
uint32_t v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = 122;
v___x_2494_ = lean_uint32_dec_le(v_curr_2483_, v___x_2493_);
if (v___x_2494_ == 0)
{
goto v___jp_2484_;
}
else
{
return v___x_2480_;
}
}
}
}
else
{
uint8_t v___x_2499_; 
lean_dec(v_i_2481_);
v___x_2499_ = 0;
return v___x_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_isIdCont___boxed(lean_object* v_c_2500_, lean_object* v_s_2501_){
_start:
{
uint8_t v_res_2502_; lean_object* v_r_2503_; 
v_res_2502_ = l_Lean_Parser_isIdCont(v_c_2500_, v_s_2501_);
lean_dec_ref(v_s_2501_);
lean_dec_ref(v_c_2500_);
v_r_2503_ = lean_box(v_res_2502_);
return v_r_2503_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(lean_object* v_idStartPos_2504_, lean_object* v_idStopPos_2505_, lean_object* v_tk_2506_){
_start:
{
if (lean_obj_tag(v_tk_2506_) == 0)
{
uint8_t v___x_2507_; 
v___x_2507_ = 0;
return v___x_2507_;
}
else
{
lean_object* v_val_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v_val_2508_ = lean_ctor_get(v_tk_2506_, 0);
v___x_2509_ = lean_nat_sub(v_idStopPos_2505_, v_idStartPos_2504_);
v___x_2510_ = lean_string_utf8_byte_size(v_val_2508_);
v___x_2511_ = lean_nat_dec_le(v___x_2509_, v___x_2510_);
lean_dec(v___x_2509_);
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isToken___boxed(lean_object* v_idStartPos_2512_, lean_object* v_idStopPos_2513_, lean_object* v_tk_2514_){
_start:
{
uint8_t v_res_2515_; lean_object* v_r_2516_; 
v_res_2515_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_idStartPos_2512_, v_idStopPos_2513_, v_tk_2514_);
lean_dec(v_tk_2514_);
lean_dec(v_idStopPos_2513_);
lean_dec(v_idStartPos_2512_);
v_r_2516_ = lean_box(v_res_2515_);
return v_r_2516_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(lean_object* v_a_2517_, lean_object* v_as_2518_, size_t v_i_2519_, size_t v_stop_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_eq(v_i_2519_, v_stop_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = lean_array_uget_borrowed(v_as_2518_, v_i_2519_);
v___x_2523_ = lean_string_dec_eq(v_a_2517_, v___x_2522_);
if (v___x_2523_ == 0)
{
size_t v___x_2524_; size_t v___x_2525_; 
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2519_, v___x_2524_);
v_i_2519_ = v___x_2525_;
goto _start;
}
else
{
return v___x_2523_;
}
}
else
{
uint8_t v___x_2527_; 
v___x_2527_ = 0;
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0___boxed(lean_object* v_a_2528_, lean_object* v_as_2529_, lean_object* v_i_2530_, lean_object* v_stop_2531_){
_start:
{
size_t v_i_boxed_2532_; size_t v_stop_boxed_2533_; uint8_t v_res_2534_; lean_object* v_r_2535_; 
v_i_boxed_2532_ = lean_unbox_usize(v_i_2530_);
lean_dec(v_i_2530_);
v_stop_boxed_2533_ = lean_unbox_usize(v_stop_2531_);
lean_dec(v_stop_2531_);
v_res_2534_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2528_, v_as_2529_, v_i_boxed_2532_, v_stop_boxed_2533_);
lean_dec_ref(v_as_2529_);
lean_dec_ref(v_a_2528_);
v_r_2535_ = lean_box(v_res_2534_);
return v_r_2535_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(lean_object* v_as_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = lean_unsigned_to_nat(0u);
v___x_2539_ = lean_array_get_size(v_as_2536_);
v___x_2540_ = lean_nat_dec_lt(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
return v___x_2540_;
}
else
{
size_t v___x_2541_; size_t v___x_2542_; uint8_t v___x_2543_; 
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = lean_usize_of_nat(v___x_2539_);
v___x_2543_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0_spec__0(v_a_2537_, v_as_2536_, v___x_2541_, v___x_2542_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0___boxed(lean_object* v_as_2544_, lean_object* v_a_2545_){
_start:
{
uint8_t v_res_2546_; lean_object* v_r_2547_; 
v_res_2546_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_as_2544_, v_a_2545_);
lean_dec_ref(v_a_2545_);
lean_dec_ref(v_as_2544_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos(lean_object* v_startPos_2550_, lean_object* v_tk_2551_, lean_object* v_c_2552_, lean_object* v_s_2553_){
_start:
{
if (lean_obj_tag(v_tk_2551_) == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
lean_dec_ref(v_c_2552_);
v___x_2554_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__0));
v___x_2555_ = lean_box(0);
v___x_2556_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2553_, v___x_2554_, v_startPos_2550_, v___x_2555_);
return v___x_2556_;
}
else
{
lean_object* v_toCacheableParserContext_2557_; lean_object* v_val_2558_; lean_object* v_toInputContext_2559_; lean_object* v_forbiddenTks_2560_; uint8_t v___x_2561_; 
v_toCacheableParserContext_2557_ = lean_ctor_get(v_c_2552_, 2);
v_val_2558_ = lean_ctor_get(v_tk_2551_, 0);
v_toInputContext_2559_ = lean_ctor_get(v_c_2552_, 0);
lean_inc_ref(v_toInputContext_2559_);
v_forbiddenTks_2560_ = lean_ctor_get(v_toCacheableParserContext_2557_, 3);
v___x_2561_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_2560_, v_val_2558_);
if (v___x_2561_ == 0)
{
lean_object* v_leading_2562_; lean_object* v___x_2563_; lean_object* v_stopPos_2564_; lean_object* v_s_2565_; lean_object* v_s_2566_; lean_object* v___y_2568_; lean_object* v_pos_2572_; lean_object* v_inputString_2573_; lean_object* v_endPos_2574_; uint8_t v___x_2575_; 
lean_inc(v_startPos_2550_);
v_leading_2562_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2552_, v_startPos_2550_);
v___x_2563_ = lean_string_utf8_byte_size(v_val_2558_);
v_stopPos_2564_ = lean_nat_add(v_startPos_2550_, v___x_2563_);
lean_inc(v_stopPos_2564_);
v_s_2565_ = l_Lean_Parser_ParserState_setPos(v_s_2553_, v_stopPos_2564_);
v_s_2566_ = l_Lean_Parser_whitespace(v_c_2552_, v_s_2565_);
v_pos_2572_ = lean_ctor_get(v_s_2566_, 2);
v_inputString_2573_ = lean_ctor_get(v_toInputContext_2559_, 0);
lean_inc_ref(v_inputString_2573_);
v_endPos_2574_ = lean_ctor_get(v_toInputContext_2559_, 3);
lean_inc(v_endPos_2574_);
lean_dec_ref(v_toInputContext_2559_);
v___x_2575_ = lean_nat_dec_le(v_pos_2572_, v_endPos_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
lean_inc(v_stopPos_2564_);
v___x_2576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2576_, 0, v_inputString_2573_);
lean_ctor_set(v___x_2576_, 1, v_stopPos_2564_);
lean_ctor_set(v___x_2576_, 2, v_endPos_2574_);
v___y_2568_ = v___x_2576_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2577_; 
lean_dec(v_endPos_2574_);
lean_inc(v_pos_2572_);
lean_inc(v_stopPos_2564_);
v___x_2577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2577_, 0, v_inputString_2573_);
lean_ctor_set(v___x_2577_, 1, v_stopPos_2564_);
lean_ctor_set(v___x_2577_, 2, v_pos_2572_);
v___y_2568_ = v___x_2577_;
goto v___jp_2567_;
}
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v_atom_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2569_, 0, v_leading_2562_);
lean_ctor_set(v___x_2569_, 1, v_startPos_2550_);
lean_ctor_set(v___x_2569_, 2, v___y_2568_);
lean_ctor_set(v___x_2569_, 3, v_stopPos_2564_);
lean_inc(v_val_2558_);
v_atom_2570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_atom_2570_, 0, v___x_2569_);
lean_ctor_set(v_atom_2570_, 1, v_val_2558_);
v___x_2571_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2566_, v_atom_2570_);
return v___x_2571_;
}
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec_ref(v_toInputContext_2559_);
lean_dec_ref(v_c_2552_);
v___x_2578_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_2579_ = lean_box(0);
v___x_2580_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2553_, v___x_2578_, v_startPos_2550_, v___x_2579_);
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkTokenAndFixPos___boxed(lean_object* v_startPos_2581_, lean_object* v_tk_2582_, lean_object* v_c_2583_, lean_object* v_s_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2581_, v_tk_2582_, v_c_2583_, v_s_2584_);
lean_dec(v_tk_2582_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult(lean_object* v_startPos_2586_, lean_object* v_tk_2587_, lean_object* v_val_2588_, uint8_t v_includeWhitespace_2589_, lean_object* v_c_2590_, lean_object* v_s_2591_){
_start:
{
lean_object* v_pos_2592_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; uint8_t v___x_2602_; 
v_pos_2592_ = lean_ctor_get(v_s_2591_, 2);
v___x_2602_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isToken(v_startPos_2586_, v_pos_2592_, v_tk_2587_);
if (v___x_2602_ == 0)
{
lean_object* v_toInputContext_2603_; lean_object* v_inputString_2604_; lean_object* v_endPos_2605_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v_pos_2609_; lean_object* v___y_2615_; uint8_t v___x_2618_; 
lean_inc(v_pos_2592_);
v_toInputContext_2603_ = lean_ctor_get(v_c_2590_, 0);
v_inputString_2604_ = lean_ctor_get(v_toInputContext_2603_, 0);
lean_inc_ref(v_inputString_2604_);
v_endPos_2605_ = lean_ctor_get(v_toInputContext_2603_, 3);
lean_inc(v_endPos_2605_);
v___x_2618_ = lean_nat_dec_le(v_pos_2592_, v_endPos_2605_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_inc(v_endPos_2605_);
lean_inc(v_startPos_2586_);
lean_inc_ref(v_inputString_2604_);
v___x_2619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2619_, 0, v_inputString_2604_);
lean_ctor_set(v___x_2619_, 1, v_startPos_2586_);
lean_ctor_set(v___x_2619_, 2, v_endPos_2605_);
v___y_2615_ = v___x_2619_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2620_; 
lean_inc(v_pos_2592_);
lean_inc(v_startPos_2586_);
lean_inc_ref(v_inputString_2604_);
v___x_2620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2620_, 0, v_inputString_2604_);
lean_ctor_set(v___x_2620_, 1, v_startPos_2586_);
lean_ctor_set(v___x_2620_, 2, v_pos_2592_);
v___y_2615_ = v___x_2620_;
goto v___jp_2614_;
}
v___jp_2606_:
{
lean_object* v_leading_2610_; uint8_t v___x_2611_; 
lean_inc(v_startPos_2586_);
v_leading_2610_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2590_, v_startPos_2586_);
lean_dec_ref(v_c_2590_);
v___x_2611_ = lean_nat_dec_le(v_pos_2609_, v_endPos_2605_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; 
lean_dec(v_pos_2609_);
lean_inc(v_pos_2592_);
v___x_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2612_, 0, v_inputString_2604_);
lean_ctor_set(v___x_2612_, 1, v_pos_2592_);
lean_ctor_set(v___x_2612_, 2, v_endPos_2605_);
v___y_2594_ = v_leading_2610_;
v___y_2595_ = v___y_2607_;
v___y_2596_ = v___y_2608_;
v___y_2597_ = v___x_2612_;
goto v___jp_2593_;
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_endPos_2605_);
lean_inc(v_pos_2592_);
v___x_2613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2613_, 0, v_inputString_2604_);
lean_ctor_set(v___x_2613_, 1, v_pos_2592_);
lean_ctor_set(v___x_2613_, 2, v_pos_2609_);
v___y_2594_ = v_leading_2610_;
v___y_2595_ = v___y_2607_;
v___y_2596_ = v___y_2608_;
v___y_2597_ = v___x_2613_;
goto v___jp_2593_;
}
}
v___jp_2614_:
{
if (v_includeWhitespace_2589_ == 0)
{
lean_inc(v_pos_2592_);
v___y_2607_ = v___y_2615_;
v___y_2608_ = v_s_2591_;
v_pos_2609_ = v_pos_2592_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2616_; lean_object* v_pos_2617_; 
lean_inc_ref(v_c_2590_);
v___x_2616_ = l_Lean_Parser_whitespace(v_c_2590_, v_s_2591_);
v_pos_2617_ = lean_ctor_get(v___x_2616_, 2);
lean_inc(v_pos_2617_);
v___y_2607_ = v___y_2615_;
v___y_2608_ = v___x_2616_;
v_pos_2609_ = v_pos_2617_;
goto v___jp_2606_;
}
}
}
else
{
lean_object* v___x_2621_; 
lean_dec(v_val_2588_);
v___x_2621_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2586_, v_tk_2587_, v_c_2590_, v_s_2591_);
return v___x_2621_;
}
v___jp_2593_:
{
lean_object* v_info_2598_; lean_object* v___x_2599_; lean_object* v_atom_2600_; lean_object* v___x_2601_; 
v_info_2598_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_2598_, 0, v___y_2594_);
lean_ctor_set(v_info_2598_, 1, v_startPos_2586_);
lean_ctor_set(v_info_2598_, 2, v___y_2597_);
lean_ctor_set(v_info_2598_, 3, v_pos_2592_);
v___x_2599_ = lean_box(0);
v_atom_2600_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_atom_2600_, 0, v_info_2598_);
lean_ctor_set(v_atom_2600_, 1, v___y_2595_);
lean_ctor_set(v_atom_2600_, 2, v_val_2588_);
lean_ctor_set(v_atom_2600_, 3, v___x_2599_);
v___x_2601_ = l_Lean_Parser_ParserState_pushSyntax(v___y_2596_, v_atom_2600_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdResult___boxed(lean_object* v_startPos_2622_, lean_object* v_tk_2623_, lean_object* v_val_2624_, lean_object* v_includeWhitespace_2625_, lean_object* v_c_2626_, lean_object* v_s_2627_){
_start:
{
uint8_t v_includeWhitespace_boxed_2628_; lean_object* v_res_2629_; 
v_includeWhitespace_boxed_2628_ = lean_unbox(v_includeWhitespace_2625_);
v_res_2629_ = l_Lean_Parser_mkIdResult(v_startPos_2622_, v_tk_2623_, v_val_2624_, v_includeWhitespace_boxed_2628_, v_c_2626_, v_s_2627_);
lean_dec(v_tk_2623_);
return v_res_2629_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(uint32_t v___y_2630_){
_start:
{
uint32_t v___x_2652_; uint8_t v___x_2653_; 
v___x_2652_ = 65;
v___x_2653_ = lean_uint32_dec_le(v___x_2652_, v___y_2630_);
if (v___x_2653_ == 0)
{
goto v___jp_2647_;
}
else
{
uint32_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = 90;
v___x_2655_ = lean_uint32_dec_le(v___y_2630_, v___x_2654_);
if (v___x_2655_ == 0)
{
goto v___jp_2647_;
}
else
{
return v___x_2655_;
}
}
v___jp_2631_:
{
uint32_t v___x_2632_; uint8_t v___x_2633_; 
v___x_2632_ = 95;
v___x_2633_ = lean_uint32_dec_eq(v___y_2630_, v___x_2632_);
if (v___x_2633_ == 0)
{
uint32_t v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = 39;
v___x_2635_ = lean_uint32_dec_eq(v___y_2630_, v___x_2634_);
if (v___x_2635_ == 0)
{
uint32_t v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = 33;
v___x_2637_ = lean_uint32_dec_eq(v___y_2630_, v___x_2636_);
if (v___x_2637_ == 0)
{
uint32_t v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = 63;
v___x_2639_ = lean_uint32_dec_eq(v___y_2630_, v___x_2638_);
if (v___x_2639_ == 0)
{
uint8_t v___x_2640_; 
v___x_2640_ = l_Lean_isLetterLike(v___y_2630_);
if (v___x_2640_ == 0)
{
uint8_t v___x_2641_; 
v___x_2641_ = l_Lean_isSubScriptAlnum(v___y_2630_);
return v___x_2641_;
}
else
{
return v___x_2640_;
}
}
else
{
return v___x_2639_;
}
}
else
{
return v___x_2637_;
}
}
else
{
return v___x_2635_;
}
}
else
{
return v___x_2633_;
}
}
v___jp_2642_:
{
uint32_t v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = 48;
v___x_2644_ = lean_uint32_dec_le(v___x_2643_, v___y_2630_);
if (v___x_2644_ == 0)
{
goto v___jp_2631_;
}
else
{
uint32_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2645_ = 57;
v___x_2646_ = lean_uint32_dec_le(v___y_2630_, v___x_2645_);
if (v___x_2646_ == 0)
{
goto v___jp_2631_;
}
else
{
return v___x_2646_;
}
}
}
v___jp_2647_:
{
uint32_t v___x_2648_; uint8_t v___x_2649_; 
v___x_2648_ = 97;
v___x_2649_ = lean_uint32_dec_le(v___x_2648_, v___y_2630_);
if (v___x_2649_ == 0)
{
goto v___jp_2642_;
}
else
{
uint32_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2650_ = 122;
v___x_2651_ = lean_uint32_dec_le(v___y_2630_, v___x_2650_);
if (v___x_2651_ == 0)
{
goto v___jp_2642_;
}
else
{
return v___x_2651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0___boxed(lean_object* v___y_2656_){
_start:
{
uint32_t v___y_274__boxed_2657_; uint8_t v_res_2658_; lean_object* v_r_2659_; 
v___y_274__boxed_2657_ = lean_unbox_uint32(v___y_2656_);
lean_dec(v___y_2656_);
v_res_2658_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__0(v___y_274__boxed_2657_);
v_r_2659_ = lean_box(v_res_2658_);
return v_r_2659_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(uint32_t v___y_2660_){
_start:
{
uint32_t v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = l_Lean_idEndEscape;
v___x_2662_ = lean_uint32_dec_eq(v___y_2660_, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1___boxed(lean_object* v___y_2663_){
_start:
{
uint32_t v___y_327__boxed_2664_; uint8_t v_res_2665_; lean_object* v_r_2666_; 
v___y_327__boxed_2664_ = lean_unbox_uint32(v___y_2663_);
lean_dec(v___y_2663_);
v_res_2665_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___lam__1(v___y_327__boxed_2664_);
v_r_2666_ = lean_box(v_res_2665_);
return v_r_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(lean_object* v_startPos_2670_, lean_object* v_tk_2671_, uint8_t v_includeWhitespace_2672_, lean_object* v_r_2673_, lean_object* v_c_2674_, lean_object* v_s_2675_){
_start:
{
lean_object* v_pos_2676_; lean_object* v_toInputContext_2677_; uint8_t v___x_2678_; 
v_pos_2676_ = lean_ctor_get(v_s_2675_, 2);
v_toInputContext_2677_ = lean_ctor_get(v_c_2674_, 0);
v___x_2678_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2677_, v_pos_2676_);
if (v___x_2678_ == 0)
{
lean_object* v_inputString_2679_; uint32_t v_curr_2680_; uint32_t v___x_2681_; uint8_t v___x_2682_; 
v_inputString_2679_ = lean_ctor_get(v_toInputContext_2677_, 0);
v_curr_2680_ = lean_string_utf8_get_fast(v_inputString_2679_, v_pos_2676_);
v___x_2681_ = l_Lean_idBeginEscape;
v___x_2682_ = lean_uint32_dec_eq(v_curr_2680_, v___x_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___f_2683_; uint32_t v___x_2704_; uint8_t v___x_2705_; 
v___f_2683_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__0));
v___x_2704_ = 65;
v___x_2705_ = lean_uint32_dec_le(v___x_2704_, v_curr_2680_);
if (v___x_2705_ == 0)
{
goto v___jp_2699_;
}
else
{
uint32_t v___x_2706_; uint8_t v___x_2707_; 
v___x_2706_ = 90;
v___x_2707_ = lean_uint32_dec_le(v_curr_2680_, v___x_2706_);
if (v___x_2707_ == 0)
{
goto v___jp_2699_;
}
else
{
lean_inc(v_pos_2676_);
goto v___jp_2684_;
}
}
v___jp_2684_:
{
lean_object* v___x_2685_; lean_object* v_s_2686_; lean_object* v_pos_2687_; lean_object* v___x_2688_; lean_object* v_r_2689_; uint8_t v___x_2690_; 
v___x_2685_ = l_Lean_Parser_ParserState_next(v_s_2675_, v_c_2674_, v_pos_2676_);
v_s_2686_ = l_Lean_Parser_takeWhileFn(v___f_2683_, v_c_2674_, v___x_2685_);
v_pos_2687_ = lean_ctor_get(v_s_2686_, 2);
v___x_2688_ = lean_string_utf8_extract(v_inputString_2679_, v_pos_2676_, v_pos_2687_);
lean_dec(v_pos_2676_);
v_r_2689_ = l_Lean_Name_str___override(v_r_2673_, v___x_2688_);
v___x_2690_ = l_Lean_Parser_isIdCont(v_c_2674_, v_s_2686_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_Parser_mkIdResult(v_startPos_2670_, v_tk_2671_, v_r_2689_, v_includeWhitespace_2672_, v_c_2674_, v_s_2686_);
return v___x_2691_;
}
else
{
lean_object* v_s_2692_; 
lean_inc(v_pos_2687_);
v_s_2692_ = l_Lean_Parser_ParserState_next(v_s_2686_, v_c_2674_, v_pos_2687_);
lean_dec(v_pos_2687_);
v_r_2673_ = v_r_2689_;
v_s_2675_ = v_s_2692_;
goto _start;
}
}
v___jp_2694_:
{
uint32_t v___x_2695_; uint8_t v___x_2696_; 
v___x_2695_ = 95;
v___x_2696_ = lean_uint32_dec_eq(v_curr_2680_, v___x_2695_);
if (v___x_2696_ == 0)
{
uint8_t v___x_2697_; 
v___x_2697_ = l_Lean_isLetterLike(v_curr_2680_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_dec(v_r_2673_);
v___x_2698_ = l_Lean_Parser_mkTokenAndFixPos(v_startPos_2670_, v_tk_2671_, v_c_2674_, v_s_2675_);
return v___x_2698_;
}
else
{
lean_inc(v_pos_2676_);
goto v___jp_2684_;
}
}
else
{
lean_inc(v_pos_2676_);
goto v___jp_2684_;
}
}
v___jp_2699_:
{
uint32_t v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = 97;
v___x_2701_ = lean_uint32_dec_le(v___x_2700_, v_curr_2680_);
if (v___x_2701_ == 0)
{
goto v___jp_2694_;
}
else
{
uint32_t v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = 122;
v___x_2703_ = lean_uint32_dec_le(v_curr_2680_, v___x_2702_);
if (v___x_2703_ == 0)
{
goto v___jp_2694_;
}
else
{
lean_inc(v_pos_2676_);
goto v___jp_2684_;
}
}
}
}
else
{
lean_object* v___f_2708_; lean_object* v_startPart_2709_; lean_object* v___x_2710_; lean_object* v_s_2711_; lean_object* v_pos_2712_; uint8_t v___x_2713_; 
v___f_2708_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__1));
v_startPart_2709_ = lean_string_utf8_next_fast(v_inputString_2679_, v_pos_2676_);
v___x_2710_ = l_Lean_Parser_ParserState_setPos(v_s_2675_, v_startPart_2709_);
v_s_2711_ = l_Lean_Parser_takeUntilFn(v___f_2708_, v_c_2674_, v___x_2710_);
v_pos_2712_ = lean_ctor_get(v_s_2711_, 2);
v___x_2713_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2677_, v_pos_2712_);
if (v___x_2713_ == 0)
{
lean_object* v_s_2714_; lean_object* v___x_2715_; lean_object* v_r_2716_; uint8_t v___x_2717_; 
lean_inc(v_pos_2712_);
v_s_2714_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2711_, v_c_2674_, v_pos_2712_);
v___x_2715_ = lean_string_utf8_extract(v_inputString_2679_, v_startPart_2709_, v_pos_2712_);
lean_dec(v_pos_2712_);
v_r_2716_ = l_Lean_Name_str___override(v_r_2673_, v___x_2715_);
v___x_2717_ = l_Lean_Parser_isIdCont(v_c_2674_, v_s_2714_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Parser_mkIdResult(v_startPos_2670_, v_tk_2671_, v_r_2716_, v_includeWhitespace_2672_, v_c_2674_, v_s_2714_);
return v___x_2718_;
}
else
{
lean_object* v_pos_2719_; lean_object* v_s_2720_; 
v_pos_2719_ = lean_ctor_get(v_s_2714_, 2);
lean_inc(v_pos_2719_);
v_s_2720_ = l_Lean_Parser_ParserState_next(v_s_2714_, v_c_2674_, v_pos_2719_);
lean_dec(v_pos_2719_);
v_r_2673_ = v_r_2716_;
v_s_2675_ = v_s_2720_;
goto _start;
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec_ref(v_c_2674_);
lean_dec(v_r_2673_);
lean_dec(v_startPos_2670_);
v___x_2722_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___closed__2));
v___x_2723_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_2711_, v___x_2722_, v_startPart_2709_);
return v___x_2723_;
}
}
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref(v_c_2674_);
lean_dec(v_r_2673_);
lean_dec(v_startPos_2670_);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2675_, v___x_2724_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse___boxed(lean_object* v_startPos_2726_, lean_object* v_tk_2727_, lean_object* v_includeWhitespace_2728_, lean_object* v_r_2729_, lean_object* v_c_2730_, lean_object* v_s_2731_){
_start:
{
uint8_t v_includeWhitespace_boxed_2732_; lean_object* v_res_2733_; 
v_includeWhitespace_boxed_2732_ = lean_unbox(v_includeWhitespace_2728_);
v_res_2733_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2726_, v_tk_2727_, v_includeWhitespace_boxed_2732_, v_r_2729_, v_c_2730_, v_s_2731_);
lean_dec(v_tk_2727_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux(lean_object* v_startPos_2734_, lean_object* v_tk_2735_, lean_object* v_r_2736_, uint8_t v_includeWhitespace_2737_, lean_object* v_c_2738_, lean_object* v_s_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2734_, v_tk_2735_, v_includeWhitespace_2737_, v_r_2736_, v_c_2738_, v_s_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFnAux___boxed(lean_object* v_startPos_2741_, lean_object* v_tk_2742_, lean_object* v_r_2743_, lean_object* v_includeWhitespace_2744_, lean_object* v_c_2745_, lean_object* v_s_2746_){
_start:
{
uint8_t v_includeWhitespace_boxed_2747_; lean_object* v_res_2748_; 
v_includeWhitespace_boxed_2747_ = lean_unbox(v_includeWhitespace_2744_);
v_res_2748_ = l_Lean_Parser_identFnAux(v_startPos_2741_, v_tk_2742_, v_r_2743_, v_includeWhitespace_boxed_2747_, v_c_2745_, v_s_2746_);
lean_dec(v_tk_2742_);
return v_res_2748_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(uint32_t v_c_2749_){
_start:
{
uint32_t v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = 65;
v___x_2762_ = lean_uint32_dec_le(v___x_2761_, v_c_2749_);
if (v___x_2762_ == 0)
{
goto v___jp_2756_;
}
else
{
uint32_t v___x_2763_; uint8_t v___x_2764_; 
v___x_2763_ = 90;
v___x_2764_ = lean_uint32_dec_le(v_c_2749_, v___x_2763_);
if (v___x_2764_ == 0)
{
goto v___jp_2756_;
}
else
{
return v___x_2764_;
}
}
v___jp_2750_:
{
uint32_t v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = 95;
v___x_2752_ = lean_uint32_dec_eq(v_c_2749_, v___x_2751_);
if (v___x_2752_ == 0)
{
uint8_t v___x_2753_; 
v___x_2753_ = l_Lean_isLetterLike(v_c_2749_);
if (v___x_2753_ == 0)
{
uint32_t v___x_2754_; uint8_t v___x_2755_; 
v___x_2754_ = l_Lean_idBeginEscape;
v___x_2755_ = lean_uint32_dec_eq(v_c_2749_, v___x_2754_);
return v___x_2755_;
}
else
{
return v___x_2753_;
}
}
else
{
return v___x_2752_;
}
}
v___jp_2756_:
{
uint32_t v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = 97;
v___x_2758_ = lean_uint32_dec_le(v___x_2757_, v_c_2749_);
if (v___x_2758_ == 0)
{
goto v___jp_2750_;
}
else
{
uint32_t v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = 122;
v___x_2760_ = lean_uint32_dec_le(v_c_2749_, v___x_2759_);
if (v___x_2760_ == 0)
{
goto v___jp_2750_;
}
else
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape___boxed(lean_object* v_c_2765_){
_start:
{
uint32_t v_c_boxed_2766_; uint8_t v_res_2767_; lean_object* v_r_2768_; 
v_c_boxed_2766_ = lean_unbox_uint32(v_c_2765_);
lean_dec(v_c_2765_);
v_res_2767_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v_c_boxed_2766_);
v_r_2768_ = lean_box(v_res_2767_);
return v_r_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(lean_object* v_startPos_2770_, lean_object* v_c_2771_, lean_object* v_s_2772_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v_s_2777_; lean_object* v_stxStack_2778_; lean_object* v_errorMsg_2779_; uint8_t v___x_2780_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_box(0);
v___x_2775_ = 1;
v___x_2776_ = l_Lean_Parser_ParserState_next(v_s_2772_, v_c_2771_, v_startPos_2770_);
v_s_2777_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_startPos_2770_, v___x_2773_, v___x_2775_, v___x_2774_, v_c_2771_, v___x_2776_);
v_stxStack_2778_ = lean_ctor_get(v_s_2777_, 0);
v_errorMsg_2779_ = lean_ctor_get(v_s_2777_, 4);
v___x_2780_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2779_, v___x_2773_);
if (v___x_2780_ == 0)
{
return v_s_2777_;
}
else
{
lean_object* v_stx_2781_; 
v_stx_2781_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2778_);
if (lean_obj_tag(v_stx_2781_) == 3)
{
lean_object* v_rawVal_2782_; lean_object* v_info_2783_; lean_object* v_str_2784_; lean_object* v_startPos_2785_; lean_object* v_stopPos_2786_; lean_object* v_s_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_rawVal_2782_ = lean_ctor_get(v_stx_2781_, 1);
lean_inc_ref(v_rawVal_2782_);
v_info_2783_ = lean_ctor_get(v_stx_2781_, 0);
lean_inc(v_info_2783_);
lean_dec_ref_known(v_stx_2781_, 4);
v_str_2784_ = lean_ctor_get(v_rawVal_2782_, 0);
lean_inc_ref(v_str_2784_);
v_startPos_2785_ = lean_ctor_get(v_rawVal_2782_, 1);
lean_inc(v_startPos_2785_);
v_stopPos_2786_ = lean_ctor_get(v_rawVal_2782_, 2);
lean_inc(v_stopPos_2786_);
lean_dec_ref(v_rawVal_2782_);
v_s_2787_ = l_Lean_Parser_ParserState_popSyntax(v_s_2777_);
v___x_2788_ = lean_string_utf8_extract(v_str_2784_, v_startPos_2785_, v_stopPos_2786_);
lean_dec(v_stopPos_2786_);
lean_dec(v_startPos_2785_);
lean_dec_ref(v_str_2784_);
v___x_2789_ = l_Lean_Syntax_mkNameLit(v___x_2788_, v_info_2783_);
v___x_2790_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2787_, v___x_2789_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_dec(v_stx_2781_);
v___x_2791_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux___closed__0));
v___x_2792_ = l_Lean_Parser_ParserState_mkError(v_s_2777_, v___x_2791_);
return v___x_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(lean_object* v_c_2793_, lean_object* v_s_2794_){
_start:
{
lean_object* v_toInputContext_2795_; lean_object* v_pos_2796_; lean_object* v_tokens_2797_; lean_object* v_inputString_2798_; lean_object* v_endPos_2799_; uint32_t v_curr_2800_; uint32_t v___x_2801_; uint8_t v___x_2802_; uint8_t v___x_2803_; 
v_toInputContext_2795_ = lean_ctor_get(v_c_2793_, 0);
v_pos_2796_ = lean_ctor_get(v_s_2794_, 2);
v_tokens_2797_ = lean_ctor_get(v_c_2793_, 3);
v_inputString_2798_ = lean_ctor_get(v_toInputContext_2795_, 0);
v_endPos_2799_ = lean_ctor_get(v_toInputContext_2795_, 3);
v_curr_2800_ = lean_string_utf8_get(v_inputString_2798_, v_pos_2796_);
v___x_2801_ = 34;
v___x_2802_ = lean_uint32_dec_eq(v_curr_2800_, v___x_2801_);
v___x_2803_ = 1;
if (v___x_2802_ == 0)
{
uint32_t v___x_2828_; uint8_t v___x_2829_; 
v___x_2828_ = 39;
v___x_2829_ = lean_uint32_dec_eq(v_curr_2800_, v___x_2828_);
if (v___x_2829_ == 0)
{
goto v___jp_2822_;
}
else
{
lean_object* v___x_2830_; uint32_t v___x_2831_; uint8_t v___x_2832_; 
v___x_2830_ = lean_string_utf8_next(v_inputString_2798_, v_pos_2796_);
v___x_2831_ = lean_string_utf8_get(v_inputString_2798_, v___x_2830_);
lean_dec(v___x_2830_);
v___x_2832_ = lean_uint32_dec_eq(v___x_2831_, v___x_2828_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_inc(v_pos_2796_);
v___x_2833_ = l_Lean_Parser_ParserState_next(v_s_2794_, v_c_2793_, v_pos_2796_);
v___x_2834_ = l_Lean_Parser_charLitFnAux(v_pos_2796_, v_c_2793_, v___x_2833_);
return v___x_2834_;
}
else
{
goto v___jp_2822_;
}
}
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_inc(v_pos_2796_);
v___x_2835_ = l_Lean_Parser_ParserState_next(v_s_2794_, v_c_2793_, v_pos_2796_);
v___x_2836_ = l_Lean_Parser_strLitFnAux(v_pos_2796_, v___x_2803_, v_c_2793_, v___x_2835_);
return v___x_2836_;
}
v___jp_2804_:
{
lean_object* v_tk_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_inc(v_pos_2796_);
v_tk_2805_ = l_Lean_Data_Trie_matchPrefix___redArg(v_inputString_2798_, v_tokens_2797_, v_pos_2796_, v_endPos_2799_);
v___x_2806_ = lean_box(0);
v___x_2807_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2796_, v_tk_2805_, v___x_2803_, v___x_2806_, v_c_2793_, v_s_2794_);
lean_dec(v_tk_2805_);
return v___x_2807_;
}
v___jp_2808_:
{
uint32_t v___x_2809_; uint8_t v___x_2810_; 
v___x_2809_ = 114;
v___x_2810_ = lean_uint32_dec_eq(v_curr_2800_, v___x_2809_);
if (v___x_2810_ == 0)
{
goto v___jp_2804_;
}
else
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = lean_string_utf8_next(v_inputString_2798_, v_pos_2796_);
v___x_2812_ = l_Lean_Parser_isRawStrLitStart(v_c_2793_, v___x_2811_);
if (v___x_2812_ == 0)
{
goto v___jp_2804_;
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = l_Lean_Parser_ParserState_next(v_s_2794_, v_c_2793_, v_pos_2796_);
v___x_2814_ = l_Lean_Parser_rawStrLitFnAux(v_pos_2796_, v_c_2793_, v___x_2813_);
return v___x_2814_;
}
}
}
v___jp_2815_:
{
uint32_t v___x_2816_; uint8_t v___x_2817_; 
v___x_2816_ = 96;
v___x_2817_ = lean_uint32_dec_eq(v_curr_2800_, v___x_2816_);
if (v___x_2817_ == 0)
{
goto v___jp_2808_;
}
else
{
lean_object* v___x_2818_; uint32_t v___x_2819_; uint8_t v___x_2820_; 
v___x_2818_ = lean_string_utf8_next(v_inputString_2798_, v_pos_2796_);
v___x_2819_ = lean_string_utf8_get(v_inputString_2798_, v___x_2818_);
lean_dec(v___x_2818_);
v___x_2820_ = l___private_Lean_Parser_Basic_0__Lean_Parser_isIdFirstOrBeginEscape(v___x_2819_);
if (v___x_2820_ == 0)
{
goto v___jp_2808_;
}
else
{
lean_object* v___x_2821_; 
v___x_2821_ = l___private_Lean_Parser_Basic_0__Lean_Parser_nameLitAux(v_pos_2796_, v_c_2793_, v_s_2794_);
return v___x_2821_;
}
}
}
v___jp_2822_:
{
uint32_t v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = 48;
v___x_2824_ = lean_uint32_dec_le(v___x_2823_, v_curr_2800_);
if (v___x_2824_ == 0)
{
lean_inc(v_pos_2796_);
goto v___jp_2815_;
}
else
{
uint32_t v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = 57;
v___x_2826_ = lean_uint32_dec_le(v_curr_2800_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_inc(v_pos_2796_);
goto v___jp_2815_;
}
else
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Parser_numberFnAux(v___x_2803_, v_c_2793_, v_s_2794_);
return v___x_2827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(lean_object* v_startPos_2837_, lean_object* v_s_2838_){
_start:
{
lean_object* v_cache_2839_; lean_object* v_errorMsg_2840_; 
v_cache_2839_ = lean_ctor_get(v_s_2838_, 3);
lean_inc_ref(v_cache_2839_);
v_errorMsg_2840_ = lean_ctor_get(v_s_2838_, 4);
if (lean_obj_tag(v_errorMsg_2840_) == 0)
{
lean_object* v_stxStack_2841_; lean_object* v_lhsPrec_2842_; lean_object* v_pos_2843_; lean_object* v_recoveredErrors_2844_; lean_object* v_parserCache_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2870_; 
v_stxStack_2841_ = lean_ctor_get(v_s_2838_, 0);
v_lhsPrec_2842_ = lean_ctor_get(v_s_2838_, 1);
v_pos_2843_ = lean_ctor_get(v_s_2838_, 2);
v_recoveredErrors_2844_ = lean_ctor_get(v_s_2838_, 5);
v_parserCache_2845_ = lean_ctor_get(v_cache_2839_, 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_cache_2839_);
if (v_isSharedCheck_2870_ == 0)
{
lean_object* v_unused_2871_; 
v_unused_2871_ = lean_ctor_get(v_cache_2839_, 0);
lean_dec(v_unused_2871_);
v___x_2847_ = v_cache_2839_;
v_isShared_2848_ = v_isSharedCheck_2870_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_parserCache_2845_);
lean_dec(v_cache_2839_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2870_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2849_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_2841_);
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_nat_dec_eq(v___x_2849_, v___x_2850_);
lean_dec(v___x_2849_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2863_; 
lean_inc_ref(v_recoveredErrors_2844_);
lean_inc(v_pos_2843_);
lean_inc(v_lhsPrec_2842_);
lean_inc(v_errorMsg_2840_);
lean_inc_ref(v_stxStack_2841_);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_s_2838_);
if (v_isSharedCheck_2863_ == 0)
{
lean_object* v_unused_2864_; lean_object* v_unused_2865_; lean_object* v_unused_2866_; lean_object* v_unused_2867_; lean_object* v_unused_2868_; lean_object* v_unused_2869_; 
v_unused_2864_ = lean_ctor_get(v_s_2838_, 5);
lean_dec(v_unused_2864_);
v_unused_2865_ = lean_ctor_get(v_s_2838_, 4);
lean_dec(v_unused_2865_);
v_unused_2866_ = lean_ctor_get(v_s_2838_, 3);
lean_dec(v_unused_2866_);
v_unused_2867_ = lean_ctor_get(v_s_2838_, 2);
lean_dec(v_unused_2867_);
v_unused_2868_ = lean_ctor_get(v_s_2838_, 1);
lean_dec(v_unused_2868_);
v_unused_2869_ = lean_ctor_get(v_s_2838_, 0);
lean_dec(v_unused_2869_);
v___x_2853_ = v_s_2838_;
v_isShared_2854_ = v_isSharedCheck_2863_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v_s_2838_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2863_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_tk_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
v_tk_2855_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2841_);
lean_inc(v_pos_2843_);
v___x_2856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2856_, 0, v_startPos_2837_);
lean_ctor_set(v___x_2856_, 1, v_pos_2843_);
lean_ctor_set(v___x_2856_, 2, v_tk_2855_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2856_);
v___x_2858_ = v___x_2847_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_parserCache_2845_);
v___x_2858_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2860_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 3, v___x_2858_);
v___x_2860_ = v___x_2853_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_stxStack_2841_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_lhsPrec_2842_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_pos_2843_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v_errorMsg_2840_);
lean_ctor_set(v_reuseFailAlloc_2861_, 5, v_recoveredErrors_2844_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_del_object(v___x_2847_);
lean_dec_ref(v_parserCache_2845_);
lean_dec(v_startPos_2837_);
return v_s_2838_;
}
}
}
else
{
lean_dec_ref(v_cache_2839_);
lean_dec(v_startPos_2837_);
return v_s_2838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenFn(lean_object* v_expected_2872_, lean_object* v_c_2873_, lean_object* v_s_2874_){
_start:
{
lean_object* v_pos_2875_; lean_object* v_cache_2876_; lean_object* v_toInputContext_2877_; uint8_t v___x_2878_; 
v_pos_2875_ = lean_ctor_get(v_s_2874_, 2);
v_cache_2876_ = lean_ctor_get(v_s_2874_, 3);
v_toInputContext_2877_ = lean_ctor_get(v_c_2873_, 0);
v___x_2878_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2877_, v_pos_2875_);
if (v___x_2878_ == 0)
{
lean_object* v_tokenCache_2879_; lean_object* v_startPos_2880_; lean_object* v_stopPos_2881_; lean_object* v_token_2882_; uint8_t v_decide_2883_; 
lean_dec(v_expected_2872_);
v_tokenCache_2879_ = lean_ctor_get(v_cache_2876_, 0);
v_startPos_2880_ = lean_ctor_get(v_tokenCache_2879_, 0);
v_stopPos_2881_ = lean_ctor_get(v_tokenCache_2879_, 1);
v_token_2882_ = lean_ctor_get(v_tokenCache_2879_, 2);
v_decide_2883_ = lean_nat_dec_eq(v_startPos_2880_, v_pos_2875_);
if (v_decide_2883_ == 0)
{
lean_object* v_s_2884_; lean_object* v___x_2885_; 
lean_inc(v_pos_2875_);
v_s_2884_ = l___private_Lean_Parser_Basic_0__Lean_Parser_tokenFnAux(v_c_2873_, v_s_2874_);
v___x_2885_ = l___private_Lean_Parser_Basic_0__Lean_Parser_updateTokenCache(v_pos_2875_, v_s_2884_);
return v___x_2885_;
}
else
{
lean_object* v_s_2886_; lean_object* v___x_2887_; 
lean_inc(v_token_2882_);
lean_inc(v_stopPos_2881_);
lean_dec_ref(v_c_2873_);
v_s_2886_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2874_, v_token_2882_);
v___x_2887_ = l_Lean_Parser_ParserState_setPos(v_s_2886_, v_stopPos_2881_);
return v___x_2887_;
}
}
else
{
lean_object* v___x_2888_; 
lean_dec_ref(v_c_2873_);
v___x_2888_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2874_, v_expected_2872_);
return v___x_2888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekTokenAux(lean_object* v_c_2889_, lean_object* v_s_2890_){
_start:
{
lean_object* v_pos_2891_; lean_object* v_iniSz_2892_; lean_object* v___x_2893_; lean_object* v_s_2894_; lean_object* v_errorMsg_2895_; 
v_pos_2891_ = lean_ctor_get(v_s_2890_, 2);
lean_inc(v_pos_2891_);
v_iniSz_2892_ = l_Lean_Parser_ParserState_stackSize(v_s_2890_);
v___x_2893_ = lean_box(0);
v_s_2894_ = l_Lean_Parser_tokenFn(v___x_2893_, v_c_2889_, v_s_2890_);
v_errorMsg_2895_ = lean_ctor_get(v_s_2894_, 4);
lean_inc(v_errorMsg_2895_);
if (lean_obj_tag(v_errorMsg_2895_) == 1)
{
lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2904_; 
v_isSharedCheck_2904_ = !lean_is_exclusive(v_errorMsg_2895_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v_errorMsg_2895_, 0);
lean_dec(v_unused_2905_);
v___x_2897_ = v_errorMsg_2895_;
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
else
{
lean_dec(v_errorMsg_2895_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
lean_inc_ref(v_s_2894_);
v___x_2899_ = l_Lean_Parser_ParserState_restore(v_s_2894_, v_iniSz_2892_, v_pos_2891_);
lean_dec(v_iniSz_2892_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set_tag(v___x_2897_, 0);
lean_ctor_set(v___x_2897_, 0, v_s_2894_);
v___x_2901_ = v___x_2897_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_s_2894_);
v___x_2901_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2899_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
return v___x_2902_;
}
}
}
else
{
lean_object* v_stxStack_2906_; lean_object* v_stx_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
lean_dec(v_errorMsg_2895_);
v_stxStack_2906_ = lean_ctor_get(v_s_2894_, 0);
v_stx_2907_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2906_);
v___x_2908_ = l_Lean_Parser_ParserState_restore(v_s_2894_, v_iniSz_2892_, v_pos_2891_);
lean_dec(v_iniSz_2892_);
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_stx_2907_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
return v___x_2910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_peekToken(lean_object* v_c_2911_, lean_object* v_s_2912_){
_start:
{
lean_object* v_cache_2913_; lean_object* v_tokenCache_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2927_; 
v_cache_2913_ = lean_ctor_get(v_s_2912_, 3);
lean_inc_ref(v_cache_2913_);
v_tokenCache_2914_ = lean_ctor_get(v_cache_2913_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_cache_2913_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; 
v_unused_2928_ = lean_ctor_get(v_cache_2913_, 1);
lean_dec(v_unused_2928_);
v___x_2916_ = v_cache_2913_;
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_tokenCache_2914_);
lean_dec(v_cache_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_pos_2918_; lean_object* v_startPos_2919_; lean_object* v_token_2920_; uint8_t v_decide_2921_; 
v_pos_2918_ = lean_ctor_get(v_s_2912_, 2);
v_startPos_2919_ = lean_ctor_get(v_tokenCache_2914_, 0);
lean_inc(v_startPos_2919_);
v_token_2920_ = lean_ctor_get(v_tokenCache_2914_, 2);
lean_inc(v_token_2920_);
lean_dec_ref(v_tokenCache_2914_);
v_decide_2921_ = lean_nat_dec_eq(v_startPos_2919_, v_pos_2918_);
lean_dec(v_startPos_2919_);
if (v_decide_2921_ == 0)
{
lean_object* v___x_2922_; 
lean_dec(v_token_2920_);
lean_del_object(v___x_2916_);
v___x_2922_ = l_Lean_Parser_peekTokenAux(v_c_2911_, v_s_2912_);
return v___x_2922_;
}
else
{
lean_object* v___x_2923_; lean_object* v___x_2925_; 
lean_dec_ref(v_c_2911_);
v___x_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_token_2920_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v___x_2923_);
lean_ctor_set(v___x_2916_, 0, v_s_2912_);
v___x_2925_ = v___x_2916_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_s_2912_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v___x_2923_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn(uint8_t v_includeWhitespace_2929_, lean_object* v_c_2930_, lean_object* v_s_2931_){
_start:
{
lean_object* v_pos_2932_; lean_object* v_toInputContext_2933_; uint8_t v___x_2934_; 
v_pos_2932_ = lean_ctor_get(v_s_2931_, 2);
v_toInputContext_2933_ = lean_ctor_get(v_c_2930_, 0);
v___x_2934_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2933_, v_pos_2932_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_inc(v_pos_2932_);
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_box(0);
v___x_2937_ = l___private_Lean_Parser_Basic_0__Lean_Parser_identFnAux_parse(v_pos_2932_, v___x_2935_, v_includeWhitespace_2929_, v___x_2936_, v_c_2930_, v_s_2931_);
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec_ref(v_c_2930_);
v___x_2938_ = lean_box(0);
v___x_2939_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2931_, v___x_2938_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_rawIdentFn___boxed(lean_object* v_includeWhitespace_2940_, lean_object* v_c_2941_, lean_object* v_s_2942_){
_start:
{
uint8_t v_includeWhitespace_boxed_2943_; lean_object* v_res_2944_; 
v_includeWhitespace_boxed_2943_ = lean_unbox(v_includeWhitespace_2940_);
v_res_2944_ = l_Lean_Parser_rawIdentFn(v_includeWhitespace_boxed_2943_, v_c_2941_, v_s_2942_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_satisfySymbolFn(lean_object* v_p_2945_, lean_object* v_expected_2946_, lean_object* v_c_2947_, lean_object* v_s_2948_){
_start:
{
lean_object* v_pos_2949_; lean_object* v_s_2950_; lean_object* v_stxStack_2951_; lean_object* v_errorMsg_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; 
v_pos_2949_ = lean_ctor_get(v_s_2948_, 2);
lean_inc(v_pos_2949_);
lean_inc(v_expected_2946_);
v_s_2950_ = l_Lean_Parser_tokenFn(v_expected_2946_, v_c_2947_, v_s_2948_);
v_stxStack_2951_ = lean_ctor_get(v_s_2950_, 0);
v_errorMsg_2952_ = lean_ctor_get(v_s_2950_, 4);
v___x_2953_ = lean_box(0);
v___x_2954_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_2952_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec(v_pos_2949_);
lean_dec(v_expected_2946_);
lean_dec_ref(v_p_2945_);
return v_s_2950_;
}
else
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2951_);
if (lean_obj_tag(v___x_2955_) == 2)
{
lean_object* v_val_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v_val_2956_ = lean_ctor_get(v___x_2955_, 1);
lean_inc_ref(v_val_2956_);
lean_dec_ref_known(v___x_2955_, 2);
v___x_2957_ = lean_apply_1(v_p_2945_, v_val_2956_);
v___x_2958_ = lean_unbox(v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2950_, v_expected_2946_, v_pos_2949_);
return v___x_2959_;
}
else
{
lean_dec(v_pos_2949_);
lean_dec(v_expected_2946_);
return v_s_2950_;
}
}
else
{
lean_object* v___x_2960_; 
lean_dec(v___x_2955_);
lean_dec_ref(v_p_2945_);
v___x_2960_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_2950_, v_expected_2946_, v_pos_2949_);
return v___x_2960_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_symbolFnAux___lam__0(lean_object* v_sym_2961_, lean_object* v_s_2962_){
_start:
{
uint8_t v___x_2963_; 
v___x_2963_ = lean_string_dec_eq(v_s_2962_, v_sym_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux___lam__0___boxed(lean_object* v_sym_2964_, lean_object* v_s_2965_){
_start:
{
uint8_t v_res_2966_; lean_object* v_r_2967_; 
v_res_2966_ = l_Lean_Parser_symbolFnAux___lam__0(v_sym_2964_, v_s_2965_);
lean_dec_ref(v_s_2965_);
lean_dec_ref(v_sym_2964_);
v_r_2967_ = lean_box(v_res_2966_);
return v_r_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFnAux(lean_object* v_sym_2968_, lean_object* v_errorMsg_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFnAux___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2972_, 0, v_sym_2968_);
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2974_, 0, v_errorMsg_2969_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = l_Lean_Parser_satisfySymbolFn(v___f_2972_, v___x_2974_, v_a_2970_, v_a_2971_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo___lam__0(lean_object* v_sym_2976_, lean_object* v_tks_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2978_, 0, v_sym_2976_);
lean_ctor_set(v___x_2978_, 1, v_tks_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolInfo(lean_object* v_sym_2979_){
_start:
{
lean_object* v___f_2980_; lean_object* v___f_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_inc_ref(v_sym_2979_);
v___f_2980_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolInfo___lam__0), 2, 1);
lean_closure_set(v___f_2980_, 0, v_sym_2979_);
v___f_2981_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_2982_ = lean_box(0);
v___x_2983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2983_, 0, v_sym_2979_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2985_, 0, v___f_2980_);
lean_ctor_set(v___x_2985_, 1, v___f_2981_);
lean_ctor_set(v___x_2985_, 2, v___x_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolFn(lean_object* v_sym_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2989_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_2990_ = lean_string_append(v___x_2989_, v_sym_2986_);
v___x_2991_ = lean_string_append(v___x_2990_, v___x_2989_);
v___x_2992_ = l_Lean_Parser_symbolFnAux(v_sym_2986_, v___x_2991_, v_a_2987_, v_a_2988_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbolNoAntiquot(lean_object* v_sym_2993_){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_str_2998_; lean_object* v_startInclusive_2999_; lean_object* v_endExclusive_3000_; lean_object* v_sym_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_string_utf8_byte_size(v_sym_2993_);
v___x_2996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2996_, 0, v_sym_2993_);
lean_ctor_set(v___x_2996_, 1, v___x_2994_);
lean_ctor_set(v___x_2996_, 2, v___x_2995_);
v___x_2997_ = l_String_Slice_trimAscii(v___x_2996_);
v_str_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc_ref(v_str_2998_);
v_startInclusive_2999_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_startInclusive_2999_);
v_endExclusive_3000_ = lean_ctor_get(v___x_2997_, 2);
lean_inc(v_endExclusive_3000_);
lean_dec_ref(v___x_2997_);
v_sym_3001_ = lean_string_utf8_extract_fast(v_str_2998_, v_startInclusive_2999_, v_endExclusive_3000_);
lean_dec(v_endExclusive_3000_);
lean_dec(v_startInclusive_2999_);
lean_dec_ref(v_str_2998_);
lean_inc_ref(v_sym_3001_);
v___x_3002_ = l_Lean_Parser_symbolInfo(v_sym_3001_);
v___x_3003_ = lean_alloc_closure((void*)(l_Lean_Parser_symbolFn), 3, 1);
lean_closure_set(v___x_3003_, 0, v_sym_3001_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFnAux(lean_object* v_sym_3005_, lean_object* v_errorMsg_3006_, lean_object* v_c_3007_, lean_object* v_s_3008_){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v_s_3011_; lean_object* v_stxStack_3015_; lean_object* v_errorMsg_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3009_ = lean_box(0);
lean_inc_ref(v_errorMsg_3006_);
v___x_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3010_, 0, v_errorMsg_3006_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v_s_3011_ = l_Lean_Parser_tokenFn(v___x_3010_, v_c_3007_, v_s_3008_);
v_stxStack_3015_ = lean_ctor_get(v_s_3011_, 0);
v_errorMsg_3016_ = lean_ctor_get(v_s_3011_, 4);
v___x_3017_ = lean_box(0);
v___x_3018_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_dec_ref(v_errorMsg_3006_);
lean_dec_ref(v_sym_3005_);
return v_s_3011_;
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3015_);
switch(lean_obj_tag(v___x_3019_))
{
case 2:
{
lean_object* v_val_3020_; uint8_t v___x_3021_; 
v_val_3020_ = lean_ctor_get(v___x_3019_, 1);
lean_inc_ref(v_val_3020_);
lean_dec_ref_known(v___x_3019_, 2);
v___x_3021_ = lean_string_dec_eq(v_sym_3005_, v_val_3020_);
lean_dec_ref(v_val_3020_);
lean_dec_ref(v_sym_3005_);
if (v___x_3021_ == 0)
{
goto v___jp_3012_;
}
else
{
lean_dec_ref(v_errorMsg_3006_);
return v_s_3011_;
}
}
case 3:
{
lean_object* v_rawVal_3022_; lean_object* v_info_3023_; lean_object* v_str_3024_; lean_object* v_startPos_3025_; lean_object* v_stopPos_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_rawVal_3022_ = lean_ctor_get(v___x_3019_, 1);
lean_inc_ref(v_rawVal_3022_);
v_info_3023_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_info_3023_);
lean_dec_ref_known(v___x_3019_, 4);
v_str_3024_ = lean_ctor_get(v_rawVal_3022_, 0);
lean_inc_ref(v_str_3024_);
v_startPos_3025_ = lean_ctor_get(v_rawVal_3022_, 1);
lean_inc(v_startPos_3025_);
v_stopPos_3026_ = lean_ctor_get(v_rawVal_3022_, 2);
lean_inc(v_stopPos_3026_);
lean_dec_ref(v_rawVal_3022_);
v___x_3027_ = lean_string_utf8_extract(v_str_3024_, v_startPos_3025_, v_stopPos_3026_);
lean_dec(v_stopPos_3026_);
lean_dec(v_startPos_3025_);
lean_dec_ref(v_str_3024_);
v___x_3028_ = lean_string_dec_eq(v_sym_3005_, v___x_3027_);
lean_dec_ref(v___x_3027_);
if (v___x_3028_ == 0)
{
lean_dec(v_info_3023_);
lean_dec_ref(v_sym_3005_);
goto v___jp_3012_;
}
else
{
lean_object* v_s_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec_ref(v_errorMsg_3006_);
v_s_3029_ = l_Lean_Parser_ParserState_popSyntax(v_s_3011_);
v___x_3030_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_info_3023_);
lean_ctor_set(v___x_3030_, 1, v_sym_3005_);
v___x_3031_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3029_, v___x_3030_);
return v___x_3031_;
}
}
default: 
{
lean_dec(v___x_3019_);
lean_dec_ref(v_sym_3005_);
goto v___jp_3012_;
}
}
}
v___jp_3012_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3011_, v_errorMsg_3006_, v___x_3013_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolFn(lean_object* v_sym_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3035_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3036_ = lean_string_append(v___x_3035_, v_sym_3032_);
v___x_3037_ = lean_string_append(v___x_3036_, v___x_3035_);
v___x_3038_ = l_Lean_Parser_nonReservedSymbolFnAux(v_sym_3032_, v___x_3037_, v_a_3033_, v_a_3034_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo(lean_object* v_sym_3043_, uint8_t v_includeIdent_3044_){
_start:
{
lean_object* v___f_3045_; lean_object* v___f_3046_; 
v___f_3045_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3046_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
if (v_includeIdent_3044_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3047_ = lean_box(0);
v___x_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3048_, 0, v_sym_3043_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
v___x_3049_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3050_, 0, v___f_3045_);
lean_ctor_set(v___x_3050_, 1, v___f_3046_);
lean_ctor_set(v___x_3050_, 2, v___x_3049_);
return v___x_3050_;
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3051_ = ((lean_object*)(l_Lean_Parser_nonReservedSymbolInfo___closed__1));
v___x_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_sym_3043_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
v___x_3054_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3054_, 0, v___f_3045_);
lean_ctor_set(v___x_3054_, 1, v___f_3046_);
lean_ctor_set(v___x_3054_, 2, v___x_3053_);
return v___x_3054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolInfo___boxed(lean_object* v_sym_3055_, lean_object* v_includeIdent_3056_){
_start:
{
uint8_t v_includeIdent_boxed_3057_; lean_object* v_res_3058_; 
v_includeIdent_boxed_3057_ = lean_unbox(v_includeIdent_3056_);
v_res_3058_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3055_, v_includeIdent_boxed_3057_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot(lean_object* v_sym_3059_, uint8_t v_includeIdent_3060_){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v_str_3065_; lean_object* v_startInclusive_3066_; lean_object* v_endExclusive_3067_; lean_object* v_sym_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = lean_string_utf8_byte_size(v_sym_3059_);
v___x_3063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3063_, 0, v_sym_3059_);
lean_ctor_set(v___x_3063_, 1, v___x_3061_);
lean_ctor_set(v___x_3063_, 2, v___x_3062_);
v___x_3064_ = l_String_Slice_trimAscii(v___x_3063_);
v_str_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc_ref(v_str_3065_);
v_startInclusive_3066_ = lean_ctor_get(v___x_3064_, 1);
lean_inc(v_startInclusive_3066_);
v_endExclusive_3067_ = lean_ctor_get(v___x_3064_, 2);
lean_inc(v_endExclusive_3067_);
lean_dec_ref(v___x_3064_);
v_sym_3068_ = lean_string_utf8_extract_fast(v_str_3065_, v_startInclusive_3066_, v_endExclusive_3067_);
lean_dec(v_endExclusive_3067_);
lean_dec(v_startInclusive_3066_);
lean_dec_ref(v_str_3065_);
lean_inc_ref(v_sym_3068_);
v___x_3069_ = l_Lean_Parser_nonReservedSymbolInfo(v_sym_3068_, v_includeIdent_3060_);
v___x_3070_ = lean_alloc_closure((void*)(l_Lean_Parser_nonReservedSymbolFn), 3, 1);
lean_closure_set(v___x_3070_, 0, v_sym_3068_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbolNoAntiquot___boxed(lean_object* v_sym_3072_, lean_object* v_includeIdent_3073_){
_start:
{
uint8_t v_includeIdent_boxed_3074_; lean_object* v_res_3075_; 
v_includeIdent_boxed_3074_ = lean_unbox(v_includeIdent_3073_);
v_res_3075_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_3072_, v_includeIdent_boxed_3074_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(lean_object* v_sym_3076_, lean_object* v_errorMsg_3077_, lean_object* v_j_3078_, lean_object* v_c_3079_, lean_object* v_s_3080_){
_start:
{
uint8_t v___x_3081_; 
v___x_3081_ = lean_string_utf8_at_end(v_sym_3076_, v_j_3078_);
if (v___x_3081_ == 0)
{
lean_object* v_pos_3082_; lean_object* v_toInputContext_3083_; uint8_t v___x_3084_; 
v_pos_3082_ = lean_ctor_get(v_s_3080_, 2);
v_toInputContext_3083_ = lean_ctor_get(v_c_3079_, 0);
v___x_3084_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_3083_, v_pos_3082_);
if (v___x_3084_ == 0)
{
lean_object* v_inputString_3085_; uint32_t v___x_3086_; uint32_t v___x_3087_; uint8_t v___x_3088_; 
v_inputString_3085_ = lean_ctor_get(v_toInputContext_3083_, 0);
v___x_3086_ = lean_string_utf8_get_fast(v_sym_3076_, v_j_3078_);
v___x_3087_ = lean_string_utf8_get_fast(v_inputString_3085_, v_pos_3082_);
v___x_3088_ = lean_uint32_dec_eq(v___x_3086_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
lean_dec(v_j_3078_);
v___x_3089_ = l_Lean_Parser_ParserState_mkError(v_s_3080_, v_errorMsg_3077_);
return v___x_3089_;
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_inc(v_pos_3082_);
v___x_3090_ = lean_string_utf8_next_fast(v_sym_3076_, v_j_3078_);
lean_dec(v_j_3078_);
v___x_3091_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_3080_, v_c_3079_, v_pos_3082_);
lean_dec(v_pos_3082_);
v_j_3078_ = v___x_3090_;
v_s_3080_ = v___x_3091_;
goto _start;
}
}
else
{
lean_object* v___x_3093_; 
lean_dec(v_j_3078_);
v___x_3093_ = l_Lean_Parser_ParserState_mkError(v_s_3080_, v_errorMsg_3077_);
return v___x_3093_;
}
}
else
{
lean_dec(v_j_3078_);
lean_dec_ref(v_errorMsg_3077_);
return v_s_3080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse___boxed(lean_object* v_sym_3094_, lean_object* v_errorMsg_3095_, lean_object* v_j_3096_, lean_object* v_c_3097_, lean_object* v_s_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3094_, v_errorMsg_3095_, v_j_3096_, v_c_3097_, v_s_3098_);
lean_dec_ref(v_c_3097_);
lean_dec_ref(v_sym_3094_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux(lean_object* v_sym_3100_, lean_object* v_errorMsg_3101_, lean_object* v_j_3102_, lean_object* v_c_3103_, lean_object* v_s_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Parser_Basic_0__Lean_Parser_strAux_parse(v_sym_3100_, v_errorMsg_3101_, v_j_3102_, v_c_3103_, v_s_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strAux___boxed(lean_object* v_sym_3106_, lean_object* v_errorMsg_3107_, lean_object* v_j_3108_, lean_object* v_c_3109_, lean_object* v_s_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Lean_Parser_strAux(v_sym_3106_, v_errorMsg_3107_, v_j_3108_, v_c_3109_, v_s_3110_);
lean_dec_ref(v_c_3109_);
lean_dec_ref(v_sym_3106_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(lean_object* v_as_3112_, lean_object* v_i_3113_){
_start:
{
lean_object* v_zero_3114_; uint8_t v_isZero_3115_; 
v_zero_3114_ = lean_unsigned_to_nat(0u);
v_isZero_3115_ = lean_nat_dec_eq(v_i_3113_, v_zero_3114_);
if (v_isZero_3115_ == 1)
{
lean_object* v___x_3116_; 
lean_dec(v_i_3113_);
v___x_3116_ = lean_box(0);
return v___x_3116_;
}
else
{
lean_object* v_one_3117_; lean_object* v_n_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v_one_3117_ = lean_unsigned_to_nat(1u);
v_n_3118_ = lean_nat_sub(v_i_3113_, v_one_3117_);
lean_dec(v_i_3113_);
v___x_3119_ = l_Subarray_get___redArg(v_as_3112_, v_n_3118_);
v___x_3120_ = l_Lean_Syntax_isNone(v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_dec(v_n_3118_);
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
return v___x_3121_;
}
else
{
lean_dec(v___x_3119_);
v_i_3113_ = v_n_3118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg___boxed(lean_object* v_as_3123_, lean_object* v_i_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3123_, v_i_3124_);
lean_dec_ref(v_as_3123_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(lean_object* v_stack_3126_){
_start:
{
lean_object* v___x_3127_; lean_object* v_start_3128_; lean_object* v_stop_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3127_ = l_Lean_Parser_SyntaxStack_toSubarray(v_stack_3126_);
v_start_3128_ = lean_ctor_get(v___x_3127_, 1);
v_stop_3129_ = lean_ctor_get(v___x_3127_, 2);
v___x_3130_ = lean_nat_sub(v_stop_3129_, v_start_3128_);
v___x_3131_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v___x_3127_, v___x_3130_);
lean_dec_ref(v___x_3127_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_box(0);
return v___x_3132_;
}
else
{
lean_object* v_val_3133_; 
v_val_3133_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_val_3133_);
lean_dec_ref_known(v___x_3131_, 1);
return v_val_3133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(lean_object* v_as_3134_, lean_object* v_i_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___redArg(v_as_3134_, v_i_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0___boxed(lean_object* v_as_3138_, lean_object* v_i_3139_, lean_object* v_a_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l___private_Init_Data_Array_Subarray_0__Subarray_findSomeRevM_x3f_find___at___00__private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone_spec__0(v_as_3138_, v_i_3139_, v_a_3140_);
lean_dec_ref(v_as_3138_);
return v_res_3141_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailWs(lean_object* v_prev_3142_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_Lean_Syntax_getTailInfo(v_prev_3142_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_trailing_3144_; lean_object* v_startPos_3145_; lean_object* v_stopPos_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_trailing_3144_ = lean_ctor_get(v___x_3143_, 2);
lean_inc_ref(v_trailing_3144_);
lean_dec_ref_known(v___x_3143_, 4);
v_startPos_3145_ = lean_ctor_get(v_trailing_3144_, 1);
lean_inc(v_startPos_3145_);
v_stopPos_3146_ = lean_ctor_get(v_trailing_3144_, 2);
lean_inc(v_stopPos_3146_);
lean_dec_ref(v_trailing_3144_);
v___x_3147_ = lean_unsigned_to_nat(1u);
v___x_3148_ = lean_nat_add(v_startPos_3145_, v___x_3147_);
lean_dec(v_startPos_3145_);
v___x_3149_ = lean_nat_dec_le(v___x_3148_, v_stopPos_3146_);
lean_dec(v_stopPos_3146_);
lean_dec(v___x_3148_);
return v___x_3149_;
}
else
{
uint8_t v___x_3150_; 
lean_dec(v___x_3143_);
v___x_3150_ = 0;
return v___x_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailWs___boxed(lean_object* v_prev_3151_){
_start:
{
uint8_t v_res_3152_; lean_object* v_r_3153_; 
v_res_3152_ = l_Lean_Parser_checkTailWs(v_prev_3151_);
lean_dec(v_prev_3151_);
v_r_3153_ = lean_box(v_res_3152_);
return v_r_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___redArg(lean_object* v_errorMsg_3154_, lean_object* v_s_3155_){
_start:
{
lean_object* v_stxStack_3156_; lean_object* v_prev_3157_; uint8_t v___x_3158_; 
v_stxStack_3156_ = lean_ctor_get(v_s_3155_, 0);
lean_inc_ref(v_stxStack_3156_);
v_prev_3157_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3156_);
v___x_3158_ = l_Lean_Parser_checkTailWs(v_prev_3157_);
lean_dec(v_prev_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_Parser_ParserState_mkError(v_s_3155_, v_errorMsg_3154_);
return v___x_3159_;
}
else
{
lean_dec_ref(v_errorMsg_3154_);
return v_s_3155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn(lean_object* v_errorMsg_3160_, lean_object* v_x_3161_, lean_object* v_s_3162_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_Parser_checkWsBeforeFn___redArg(v_errorMsg_3160_, v_s_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBeforeFn___boxed(lean_object* v_errorMsg_3164_, lean_object* v_x_3165_, lean_object* v_s_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Lean_Parser_checkWsBeforeFn(v_errorMsg_3164_, v_x_3165_, v_s_3166_);
lean_dec_ref(v_x_3165_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkWsBefore(lean_object* v_errorMsg_3168_){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3170_ = lean_alloc_closure((void*)(l_Lean_Parser_checkWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3170_, 0, v_errorMsg_3168_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1(){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__1));
v___x_3180_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___closed__2));
v___x_3181_ = l_Lean_addBuiltinDocString(v___x_3179_, v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1___boxed(lean_object* v_a_3182_){
_start:
{
lean_object* v_res_3183_; 
v_res_3183_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkWsBefore___regBuiltin_Lean_Parser_checkWsBefore_docString__1();
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(lean_object* v_msg_3184_){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = l_String_instInhabitedSlice;
v___x_3186_ = lean_panic_fn_borrowed(v___x_3185_, v_msg_3184_);
return v___x_3186_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(lean_object* v_s_3187_, lean_object* v_a_3188_, uint8_t v_b_3189_){
_start:
{
lean_object* v_str_3190_; lean_object* v_startInclusive_3191_; lean_object* v_endExclusive_3192_; lean_object* v___x_3193_; uint8_t v_decide_3194_; 
v_str_3190_ = lean_ctor_get(v_s_3187_, 0);
v_startInclusive_3191_ = lean_ctor_get(v_s_3187_, 1);
v_endExclusive_3192_ = lean_ctor_get(v_s_3187_, 2);
v___x_3193_ = lean_nat_sub(v_endExclusive_3192_, v_startInclusive_3191_);
v_decide_3194_ = lean_nat_dec_eq(v_a_3188_, v___x_3193_);
lean_dec(v___x_3193_);
if (v_decide_3194_ == 0)
{
uint32_t v___x_3195_; lean_object* v___x_3196_; uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3195_ = 10;
v___x_3196_ = lean_nat_add(v_startInclusive_3191_, v_a_3188_);
lean_dec(v_a_3188_);
v___x_3197_ = lean_string_utf8_get_fast(v_str_3190_, v___x_3196_);
v___x_3198_ = lean_uint32_dec_eq(v___x_3197_, v___x_3195_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = lean_string_utf8_next_fast(v_str_3190_, v___x_3196_);
lean_dec(v___x_3196_);
v___x_3200_ = lean_nat_sub(v___x_3199_, v_startInclusive_3191_);
v_a_3188_ = v___x_3200_;
v_b_3189_ = v___x_3198_;
goto _start;
}
else
{
lean_dec(v___x_3196_);
return v___x_3198_;
}
}
else
{
lean_dec(v_a_3188_);
return v_b_3189_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg___boxed(lean_object* v_s_3202_, lean_object* v_a_3203_, lean_object* v_b_3204_){
_start:
{
uint8_t v_b_boxed_3205_; uint8_t v_res_3206_; lean_object* v_r_3207_; 
v_b_boxed_3205_ = lean_unbox(v_b_3204_);
v_res_3206_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3202_, v_a_3203_, v_b_boxed_3205_);
lean_dec_ref(v_s_3202_);
v_r_3207_ = lean_box(v_res_3206_);
return v_r_3207_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(lean_object* v_s_3208_){
_start:
{
lean_object* v_searcher_3209_; uint8_t v___x_3210_; uint8_t v___x_3211_; 
v_searcher_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = 0;
v___x_3211_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3208_, v_searcher_3209_, v___x_3210_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1___boxed(lean_object* v_s_3212_){
_start:
{
uint8_t v_res_3213_; lean_object* v_r_3214_; 
v_res_3213_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v_s_3212_);
lean_dec_ref(v_s_3212_);
v_r_3214_ = lean_box(v_res_3213_);
return v_r_3214_;
}
}
static lean_object* _init_l_Lean_Parser_checkTailLinebreak___closed__3(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3218_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__2));
v___x_3219_ = lean_unsigned_to_nat(14u);
v___x_3220_ = lean_unsigned_to_nat(22u);
v___x_3221_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__1));
v___x_3222_ = ((lean_object*)(l_Lean_Parser_checkTailLinebreak___closed__0));
v___x_3223_ = l_mkPanicMessageWithDecl(v___x_3222_, v___x_3221_, v___x_3220_, v___x_3219_, v___x_3218_);
return v___x_3223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailLinebreak(lean_object* v_prev_3224_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Syntax_getTailInfo(v_prev_3224_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_trailing_3230_; lean_object* v_str_3231_; lean_object* v_startPos_3232_; lean_object* v_stopPos_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3244_; 
v_trailing_3230_ = lean_ctor_get(v___x_3229_, 2);
lean_inc_ref(v_trailing_3230_);
lean_dec_ref_known(v___x_3229_, 4);
v_str_3231_ = lean_ctor_get(v_trailing_3230_, 0);
v_startPos_3232_ = lean_ctor_get(v_trailing_3230_, 1);
v_stopPos_3233_ = lean_ctor_get(v_trailing_3230_, 2);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_trailing_3230_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3235_ = v_trailing_3230_;
v_isShared_3236_ = v_isSharedCheck_3244_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_stopPos_3233_);
lean_inc(v_startPos_3232_);
lean_inc(v_str_3231_);
lean_dec(v_trailing_3230_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3244_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
uint8_t v___x_3237_; 
v___x_3237_ = lean_string_is_valid_pos(v_str_3231_, v_startPos_3232_);
if (v___x_3237_ == 0)
{
lean_del_object(v___x_3235_);
lean_dec(v_stopPos_3233_);
lean_dec(v_startPos_3232_);
lean_dec_ref(v_str_3231_);
goto v___jp_3225_;
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_string_is_valid_pos(v_str_3231_, v_stopPos_3233_);
if (v___x_3238_ == 0)
{
lean_del_object(v___x_3235_);
lean_dec(v_stopPos_3233_);
lean_dec(v_startPos_3232_);
lean_dec_ref(v_str_3231_);
goto v___jp_3225_;
}
else
{
uint8_t v___x_3239_; 
v___x_3239_ = lean_nat_dec_le(v_startPos_3232_, v_stopPos_3233_);
if (v___x_3239_ == 0)
{
lean_del_object(v___x_3235_);
lean_dec(v_stopPos_3233_);
lean_dec(v_startPos_3232_);
lean_dec_ref(v_str_3231_);
goto v___jp_3225_;
}
else
{
lean_object* v___x_3241_; 
if (v_isShared_3236_ == 0)
{
v___x_3241_ = v___x_3235_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_str_3231_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_startPos_3232_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_stopPos_3233_);
v___x_3241_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
uint8_t v___x_3242_; 
v___x_3242_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3241_);
lean_dec_ref(v___x_3241_);
return v___x_3242_;
}
}
}
}
}
}
else
{
uint8_t v___x_3245_; 
lean_dec(v___x_3229_);
v___x_3245_ = 0;
return v___x_3245_;
}
v___jp_3225_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; 
v___x_3226_ = lean_obj_once(&l_Lean_Parser_checkTailLinebreak___closed__3, &l_Lean_Parser_checkTailLinebreak___closed__3_once, _init_l_Lean_Parser_checkTailLinebreak___closed__3);
v___x_3227_ = l_panic___at___00Lean_Parser_checkTailLinebreak_spec__0(v___x_3226_);
v___x_3228_ = l_String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1(v___x_3227_);
lean_dec_ref(v___x_3227_);
return v___x_3228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailLinebreak___boxed(lean_object* v_prev_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Lean_Parser_checkTailLinebreak(v_prev_3246_);
lean_dec(v_prev_3246_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(lean_object* v_s_3249_, lean_object* v_inst_3250_, lean_object* v_R_3251_, lean_object* v_a_3252_, uint8_t v_b_3253_, lean_object* v_c_3254_){
_start:
{
uint8_t v___x_3255_; 
v___x_3255_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___redArg(v_s_3249_, v_a_3252_, v_b_3253_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1___boxed(lean_object* v_s_3256_, lean_object* v_inst_3257_, lean_object* v_R_3258_, lean_object* v_a_3259_, lean_object* v_b_3260_, lean_object* v_c_3261_){
_start:
{
uint8_t v_b_boxed_3262_; uint8_t v_res_3263_; lean_object* v_r_3264_; 
v_b_boxed_3262_ = lean_unbox(v_b_3260_);
v_res_3263_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Parser_checkTailLinebreak_spec__1_spec__1(v_s_3256_, v_inst_3257_, v_R_3258_, v_a_3259_, v_b_boxed_3262_, v_c_3261_);
lean_dec_ref(v_s_3256_);
v_r_3264_ = lean_box(v_res_3263_);
return v_r_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___redArg(lean_object* v_errorMsg_3265_, lean_object* v_s_3266_){
_start:
{
lean_object* v_stxStack_3267_; lean_object* v_prev_3268_; uint8_t v___x_3269_; 
v_stxStack_3267_ = lean_ctor_get(v_s_3266_, 0);
v_prev_3268_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3267_);
v___x_3269_ = l_Lean_Parser_checkTailLinebreak(v_prev_3268_);
lean_dec(v_prev_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_Parser_ParserState_mkError(v_s_3266_, v_errorMsg_3265_);
return v___x_3270_;
}
else
{
lean_dec_ref(v_errorMsg_3265_);
return v_s_3266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn(lean_object* v_errorMsg_3271_, lean_object* v_x_3272_, lean_object* v_s_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_Parser_checkLinebreakBeforeFn___redArg(v_errorMsg_3271_, v_s_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBeforeFn___boxed(lean_object* v_errorMsg_3275_, lean_object* v_x_3276_, lean_object* v_s_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_Parser_checkLinebreakBeforeFn(v_errorMsg_3275_, v_x_3276_, v_s_3277_);
lean_dec_ref(v_x_3276_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object* v_errorMsg_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3281_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLinebreakBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3281_, 0, v_errorMsg_3279_);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1(){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__1));
v___x_3291_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___closed__2));
v___x_3292_ = l_Lean_addBuiltinDocString(v___x_3290_, v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1___boxed(lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLinebreakBefore___regBuiltin_Lean_Parser_checkLinebreakBefore_docString__1();
return v_res_3294_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_checkTailNoWs(lean_object* v_prev_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Syntax_getTailInfo(v_prev_3295_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_trailing_3297_; lean_object* v_startPos_3298_; lean_object* v_stopPos_3299_; uint8_t v_decide_3300_; 
v_trailing_3297_ = lean_ctor_get(v___x_3296_, 2);
lean_inc_ref(v_trailing_3297_);
lean_dec_ref_known(v___x_3296_, 4);
v_startPos_3298_ = lean_ctor_get(v_trailing_3297_, 1);
lean_inc(v_startPos_3298_);
v_stopPos_3299_ = lean_ctor_get(v_trailing_3297_, 2);
lean_inc(v_stopPos_3299_);
lean_dec_ref(v_trailing_3297_);
v_decide_3300_ = lean_nat_dec_eq(v_stopPos_3299_, v_startPos_3298_);
lean_dec(v_startPos_3298_);
lean_dec(v_stopPos_3299_);
return v_decide_3300_;
}
else
{
uint8_t v___x_3301_; 
lean_dec(v___x_3296_);
v___x_3301_ = 0;
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkTailNoWs___boxed(lean_object* v_prev_3302_){
_start:
{
uint8_t v_res_3303_; lean_object* v_r_3304_; 
v_res_3303_ = l_Lean_Parser_checkTailNoWs(v_prev_3302_);
lean_dec(v_prev_3302_);
v_r_3304_ = lean_box(v_res_3303_);
return v_r_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___redArg(lean_object* v_errorMsg_3305_, lean_object* v_s_3306_){
_start:
{
lean_object* v_stxStack_3307_; lean_object* v_prev_3308_; uint8_t v___x_3309_; 
v_stxStack_3307_ = lean_ctor_get(v_s_3306_, 0);
lean_inc_ref(v_stxStack_3307_);
v_prev_3308_ = l___private_Lean_Parser_Basic_0__Lean_Parser_pickNonNone(v_stxStack_3307_);
v___x_3309_ = l_Lean_Parser_checkTailNoWs(v_prev_3308_);
lean_dec(v_prev_3308_);
if (v___x_3309_ == 0)
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Parser_ParserState_mkError(v_s_3306_, v_errorMsg_3305_);
return v___x_3310_;
}
else
{
lean_dec_ref(v_errorMsg_3305_);
return v_s_3306_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn(lean_object* v_errorMsg_3311_, lean_object* v_x_3312_, lean_object* v_s_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_Parser_checkNoWsBeforeFn___redArg(v_errorMsg_3311_, v_s_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBeforeFn___boxed(lean_object* v_errorMsg_3315_, lean_object* v_x_3316_, lean_object* v_s_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l_Lean_Parser_checkNoWsBeforeFn(v_errorMsg_3315_, v_x_3316_, v_s_3317_);
lean_dec_ref(v_x_3316_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoWsBefore(lean_object* v_errorMsg_3319_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_3321_ = lean_alloc_closure((void*)(l_Lean_Parser_checkNoWsBeforeFn___boxed), 3, 1);
lean_closure_set(v___x_3321_, 0, v_errorMsg_3319_);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1(){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__1));
v___x_3331_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___closed__2));
v___x_3332_ = l_Lean_addBuiltinDocString(v___x_3330_, v___x_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1___boxed(lean_object* v_a_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoWsBefore___regBuiltin_Lean_Parser_checkNoWsBefore_docString__1();
return v_res_3334_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_unicodeSymbolFnAux___lam__0(lean_object* v_sym_3335_, lean_object* v_asciiSym_3336_, lean_object* v_s_3337_){
_start:
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_string_dec_eq(v_s_3337_, v_sym_3335_);
if (v___x_3338_ == 0)
{
uint8_t v___x_3339_; 
v___x_3339_ = lean_string_dec_eq(v_s_3337_, v_asciiSym_3336_);
return v___x_3339_;
}
else
{
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed(lean_object* v_sym_3340_, lean_object* v_asciiSym_3341_, lean_object* v_s_3342_){
_start:
{
uint8_t v_res_3343_; lean_object* v_r_3344_; 
v_res_3343_ = l_Lean_Parser_unicodeSymbolFnAux___lam__0(v_sym_3340_, v_asciiSym_3341_, v_s_3342_);
lean_dec_ref(v_s_3342_);
lean_dec_ref(v_asciiSym_3341_);
lean_dec_ref(v_sym_3340_);
v_r_3344_ = lean_box(v_res_3343_);
return v_r_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFnAux(lean_object* v_sym_3345_, lean_object* v_asciiSym_3346_, lean_object* v_expected_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v___f_3350_; lean_object* v___x_3351_; 
v___f_3350_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFnAux___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3350_, 0, v_sym_3345_);
lean_closure_set(v___f_3350_, 1, v_asciiSym_3346_);
v___x_3351_ = l_Lean_Parser_satisfySymbolFn(v___f_3350_, v_expected_3347_, v_a_3348_, v_a_3349_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo___lam__0(lean_object* v_asciiSym_3352_, lean_object* v_sym_3353_, lean_object* v_tks_3354_){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_asciiSym_3352_);
lean_ctor_set(v___x_3355_, 1, v_tks_3354_);
v___x_3356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_sym_3353_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolInfo(lean_object* v_sym_3357_, lean_object* v_asciiSym_3358_){
_start:
{
lean_object* v___f_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
lean_inc_ref(v_sym_3357_);
lean_inc_ref(v_asciiSym_3358_);
v___f_3359_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolInfo___lam__0), 3, 2);
lean_closure_set(v___f_3359_, 0, v_asciiSym_3358_);
lean_closure_set(v___f_3359_, 1, v_sym_3357_);
v___f_3360_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3361_ = lean_box(0);
v___x_3362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3362_, 0, v_asciiSym_3358_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_sym_3357_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3365_, 0, v___f_3359_);
lean_ctor_set(v___x_3365_, 1, v___f_3360_);
lean_ctor_set(v___x_3365_, 2, v___x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolFn(lean_object* v_sym_3367_, lean_object* v_asciiSym_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3371_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_3372_ = lean_string_append(v___x_3371_, v_sym_3367_);
v___x_3373_ = ((lean_object*)(l_Lean_Parser_unicodeSymbolFn___closed__0));
v___x_3374_ = lean_string_append(v___x_3372_, v___x_3373_);
v___x_3375_ = lean_string_append(v___x_3374_, v_asciiSym_3368_);
v___x_3376_ = lean_string_append(v___x_3375_, v___x_3371_);
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = l_Lean_Parser_unicodeSymbolFnAux(v_sym_3367_, v_asciiSym_3368_, v___x_3378_, v_a_3369_, v_a_3370_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(lean_object* v_sym_3380_, lean_object* v_asciiSym_3381_){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v_str_3386_; lean_object* v_startInclusive_3387_; lean_object* v_endExclusive_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3405_; 
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_string_utf8_byte_size(v_sym_3380_);
v___x_3384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3384_, 0, v_sym_3380_);
lean_ctor_set(v___x_3384_, 1, v___x_3382_);
lean_ctor_set(v___x_3384_, 2, v___x_3383_);
v___x_3385_ = l_String_Slice_trimAscii(v___x_3384_);
v_str_3386_ = lean_ctor_get(v___x_3385_, 0);
v_startInclusive_3387_ = lean_ctor_get(v___x_3385_, 1);
v_endExclusive_3388_ = lean_ctor_get(v___x_3385_, 2);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3390_ = v___x_3385_;
v_isShared_3391_ = v_isSharedCheck_3405_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_endExclusive_3388_);
lean_inc(v_startInclusive_3387_);
lean_inc(v_str_3386_);
lean_dec(v___x_3385_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3405_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_string_utf8_byte_size(v_asciiSym_3381_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 2, v___x_3392_);
lean_ctor_set(v___x_3390_, 1, v___x_3382_);
lean_ctor_set(v___x_3390_, 0, v_asciiSym_3381_);
v___x_3394_ = v___x_3390_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_asciiSym_3381_);
lean_ctor_set(v_reuseFailAlloc_3404_, 1, v___x_3382_);
lean_ctor_set(v_reuseFailAlloc_3404_, 2, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; lean_object* v_str_3396_; lean_object* v_startInclusive_3397_; lean_object* v_endExclusive_3398_; lean_object* v_sym_3399_; lean_object* v_asciiSym_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3395_ = l_String_Slice_trimAscii(v___x_3394_);
v_str_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc_ref(v_str_3396_);
v_startInclusive_3397_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_startInclusive_3397_);
v_endExclusive_3398_ = lean_ctor_get(v___x_3395_, 2);
lean_inc(v_endExclusive_3398_);
lean_dec_ref(v___x_3395_);
v_sym_3399_ = lean_string_utf8_extract_fast(v_str_3386_, v_startInclusive_3387_, v_endExclusive_3388_);
lean_dec(v_endExclusive_3388_);
lean_dec(v_startInclusive_3387_);
lean_dec_ref(v_str_3386_);
v_asciiSym_3400_ = lean_string_utf8_extract_fast(v_str_3396_, v_startInclusive_3397_, v_endExclusive_3398_);
lean_dec(v_endExclusive_3398_);
lean_dec(v_startInclusive_3397_);
lean_dec_ref(v_str_3396_);
lean_inc_ref(v_asciiSym_3400_);
lean_inc_ref(v_sym_3399_);
v___x_3401_ = l_Lean_Parser_unicodeSymbolInfo(v_sym_3399_, v_asciiSym_3400_);
v___x_3402_ = lean_alloc_closure((void*)(l_Lean_Parser_unicodeSymbolFn), 4, 2);
lean_closure_set(v___x_3402_, 0, v_sym_3399_);
lean_closure_set(v___x_3402_, 1, v_asciiSym_3400_);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
return v___x_3403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot(lean_object* v_sym_3406_, lean_object* v_asciiSym_3407_, uint8_t v_preserveForPP_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_3406_, v_asciiSym_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbolNoAntiquot___boxed(lean_object* v_sym_3410_, lean_object* v_asciiSym_3411_, lean_object* v_preserveForPP_3412_){
_start:
{
uint8_t v_preserveForPP_boxed_3413_; lean_object* v_res_3414_; 
v_preserveForPP_boxed_3413_ = lean_unbox(v_preserveForPP_3412_);
v_res_3414_ = l_Lean_Parser_unicodeSymbolNoAntiquot(v_sym_3410_, v_asciiSym_3411_, v_preserveForPP_boxed_3413_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtomicInfo(lean_object* v_k_3415_){
_start:
{
lean_object* v___f_3416_; lean_object* v___f_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___f_3416_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__0));
v___f_3417_ = ((lean_object*)(l_Lean_Parser_epsilonInfo___closed__1));
v___x_3418_ = lean_box(0);
v___x_3419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3419_, 0, v_k_3415_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
v___x_3421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3421_, 0, v___f_3416_);
lean_ctor_set(v___x_3421_, 1, v___f_3417_);
lean_ctor_set(v___x_3421_, 2, v___x_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn(lean_object* v_k_3422_, lean_object* v_desc_3423_, lean_object* v_c_3424_, lean_object* v_s_3425_){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v_s_3428_; lean_object* v_stxStack_3429_; lean_object* v_errorMsg_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3426_ = lean_box(0);
lean_inc_ref(v_desc_3423_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v_desc_3423_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v_s_3428_ = l_Lean_Parser_tokenFn(v___x_3427_, v_c_3424_, v_s_3425_);
v_stxStack_3429_ = lean_ctor_get(v_s_3428_, 0);
v_errorMsg_3430_ = lean_ctor_get(v_s_3428_, 4);
v___x_3431_ = lean_box(0);
v___x_3432_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3430_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_dec_ref(v_desc_3423_);
return v_s_3428_;
}
else
{
lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3429_);
v___x_3434_ = l_Lean_Syntax_isOfKind(v___x_3433_, v_k_3422_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_unsigned_to_nat(0u);
v___x_3436_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_3428_, v_desc_3423_, v___x_3435_);
return v___x_3436_;
}
else
{
lean_dec_ref(v_desc_3423_);
return v_s_3428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_expectTokenFn___boxed(lean_object* v_k_3437_, lean_object* v_desc_3438_, lean_object* v_c_3439_, lean_object* v_s_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Parser_expectTokenFn(v_k_3437_, v_desc_3438_, v_c_3439_, v_s_3440_);
lean_dec(v_k_3437_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_numLitFn(lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__1));
v___x_3445_ = ((lean_object*)(l_Lean_Parser_numberFnAux___closed__0));
v___x_3446_ = l_Lean_Parser_expectTokenFn(v___x_3444_, v___x_3445_, v_a_3442_, v_a_3443_);
return v___x_3446_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = ((lean_object*)(l_Lean_Parser_decimalNumberFn___closed__0));
v___x_3448_ = l_Lean_Parser_mkAtomicInfo(v___x_3447_);
return v___x_3448_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = lean_alloc_closure((void*)(l_Lean_Parser_numLitFn), 2, 0);
v___x_3450_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__0, &l_Lean_Parser_numLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__0);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v___x_3449_);
return v___x_3451_;
}
}
static lean_object* _init_l_Lean_Parser_numLitNoAntiquot(void){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = lean_obj_once(&l_Lean_Parser_numLitNoAntiquot___closed__1, &l_Lean_Parser_numLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_numLitNoAntiquot___closed__1);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_hexnumFn(lean_object* v_ctx_3456_, lean_object* v_s_3457_){
_start:
{
lean_object* v_pos_3458_; uint8_t v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v_pos_3458_ = lean_ctor_get(v_s_3457_, 2);
lean_inc(v_pos_3458_);
v___x_3459_ = 1;
v___x_3460_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__1));
v___x_3461_ = l_Lean_Parser_hexNumberFn(v_pos_3458_, v___x_3459_, v___x_3460_, v_ctx_3456_, v_s_3457_);
return v___x_3461_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = ((lean_object*)(l_Lean_Parser_hexnumFn___closed__0));
v___x_3463_ = l_Lean_Parser_mkAtomicInfo(v___x_3462_);
return v___x_3463_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_alloc_closure((void*)(l_Lean_Parser_hexnumFn), 2, 0);
v___x_3465_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__0, &l_Lean_Parser_hexnumNoAntiquot___closed__0_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__0);
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_3464_);
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_Parser_hexnumNoAntiquot(void){
_start:
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_obj_once(&l_Lean_Parser_hexnumNoAntiquot___closed__1, &l_Lean_Parser_hexnumNoAntiquot___closed__1_once, _init_l_Lean_Parser_hexnumNoAntiquot___closed__1);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_scientificLitFn(lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3471_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__1));
v___x_3472_ = ((lean_object*)(l_Lean_Parser_scientificLitFn___closed__0));
v___x_3473_ = l_Lean_Parser_expectTokenFn(v___x_3471_, v___x_3472_, v_a_3469_, v_a_3470_);
return v___x_3473_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseScientific___closed__0));
v___x_3475_ = l_Lean_Parser_mkAtomicInfo(v___x_3474_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3476_ = lean_alloc_closure((void*)(l_Lean_Parser_scientificLitFn), 2, 0);
v___x_3477_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__0, &l_Lean_Parser_scientificLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__0);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v___x_3476_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_Parser_scientificLitNoAntiquot(void){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_obj_once(&l_Lean_Parser_scientificLitNoAntiquot___closed__1, &l_Lean_Parser_scientificLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_scientificLitNoAntiquot___closed__1);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_strLitFn(lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3483_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__1));
v___x_3484_ = ((lean_object*)(l_Lean_Parser_strLitFn___closed__0));
v___x_3485_ = l_Lean_Parser_expectTokenFn(v___x_3483_, v___x_3484_, v_a_3481_, v_a_3482_);
return v___x_3485_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_Parser_strLitFnAux___closed__0));
v___x_3487_ = l_Lean_Parser_mkAtomicInfo(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3488_ = lean_alloc_closure((void*)(l_Lean_Parser_strLitFn), 2, 0);
v___x_3489_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__0, &l_Lean_Parser_strLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__0);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___x_3488_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_Parser_strLitNoAntiquot(void){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_obj_once(&l_Lean_Parser_strLitNoAntiquot___closed__1, &l_Lean_Parser_strLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_strLitNoAntiquot___closed__1);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_charLitFn(lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__2));
v___x_3496_ = ((lean_object*)(l_Lean_Parser_charLitFn___closed__0));
v___x_3497_ = l_Lean_Parser_expectTokenFn(v___x_3495_, v___x_3496_, v_a_3493_, v_a_3494_);
return v___x_3497_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = ((lean_object*)(l_Lean_Parser_charLitFnAux___closed__1));
v___x_3499_ = l_Lean_Parser_mkAtomicInfo(v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3500_ = lean_alloc_closure((void*)(l_Lean_Parser_charLitFn), 2, 0);
v___x_3501_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__0, &l_Lean_Parser_charLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__0);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___x_3500_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lean_Parser_charLitNoAntiquot(void){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = lean_obj_once(&l_Lean_Parser_charLitNoAntiquot___closed__1, &l_Lean_Parser_charLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_charLitNoAntiquot___closed__1);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nameLitFn(lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__1));
v___x_3511_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__2));
v___x_3512_ = l_Lean_Parser_expectTokenFn(v___x_3510_, v___x_3511_, v_a_3508_, v_a_3509_);
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__0(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = ((lean_object*)(l_Lean_Parser_nameLitFn___closed__0));
v___x_3514_ = l_Lean_Parser_mkAtomicInfo(v___x_3513_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot___closed__1(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_alloc_closure((void*)(l_Lean_Parser_nameLitFn), 2, 0);
v___x_3516_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__0, &l_Lean_Parser_nameLitNoAntiquot___closed__0_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__0);
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_Parser_nameLitNoAntiquot(void){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = lean_obj_once(&l_Lean_Parser_nameLitNoAntiquot___closed__1, &l_Lean_Parser_nameLitNoAntiquot___closed__1_once, _init_l_Lean_Parser_nameLitNoAntiquot___closed__1);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_identFn(lean_object* v_c_3522_, lean_object* v_s_3523_){
_start:
{
lean_object* v_toCacheableParserContext_3524_; lean_object* v_forbiddenTks_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v_toCacheableParserContext_3524_ = lean_ctor_get(v_c_3522_, 2);
v_forbiddenTks_3525_ = lean_ctor_get(v_toCacheableParserContext_3524_, 3);
v___x_3526_ = lean_array_get_size(v_forbiddenTks_3525_);
v___x_3527_ = lean_unsigned_to_nat(0u);
v___x_3528_ = lean_nat_dec_eq(v___x_3526_, v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v_pos_3529_; lean_object* v_iniSz_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v_s_3533_; lean_object* v_stxStack_3534_; lean_object* v_errorMsg_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
lean_inc_ref(v_forbiddenTks_3525_);
v_pos_3529_ = lean_ctor_get(v_s_3523_, 2);
lean_inc(v_pos_3529_);
v_iniSz_3530_ = l_Lean_Parser_ParserState_stackSize(v_s_3523_);
v___x_3531_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3532_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v_s_3533_ = l_Lean_Parser_expectTokenFn(v___x_3531_, v___x_3532_, v_c_3522_, v_s_3523_);
v_stxStack_3534_ = lean_ctor_get(v_s_3533_, 0);
v_errorMsg_3535_ = lean_ctor_get(v_s_3533_, 4);
v___x_3536_ = lean_box(0);
v___x_3537_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_dec(v_iniSz_3530_);
lean_dec(v_pos_3529_);
lean_dec_ref(v_forbiddenTks_3525_);
return v_s_3533_;
}
else
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3534_);
if (lean_obj_tag(v___x_3538_) == 3)
{
lean_object* v_rawVal_3539_; lean_object* v_str_3540_; lean_object* v_startPos_3541_; lean_object* v_stopPos_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v_rawVal_3539_ = lean_ctor_get(v___x_3538_, 1);
lean_inc_ref(v_rawVal_3539_);
lean_dec_ref_known(v___x_3538_, 4);
v_str_3540_ = lean_ctor_get(v_rawVal_3539_, 0);
lean_inc_ref(v_str_3540_);
v_startPos_3541_ = lean_ctor_get(v_rawVal_3539_, 1);
lean_inc(v_startPos_3541_);
v_stopPos_3542_ = lean_ctor_get(v_rawVal_3539_, 2);
lean_inc(v_stopPos_3542_);
lean_dec_ref(v_rawVal_3539_);
v___x_3543_ = lean_string_utf8_extract(v_str_3540_, v_startPos_3541_, v_stopPos_3542_);
lean_dec(v_stopPos_3542_);
lean_dec(v_startPos_3541_);
lean_dec_ref(v_str_3540_);
v___x_3544_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_3525_, v___x_3543_);
lean_dec_ref(v___x_3543_);
lean_dec_ref(v_forbiddenTks_3525_);
if (v___x_3544_ == 0)
{
lean_dec(v_iniSz_3530_);
lean_dec(v_pos_3529_);
return v_s_3533_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = ((lean_object*)(l_Lean_Parser_mkTokenAndFixPos___closed__1));
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_iniSz_3530_);
v___x_3547_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_3533_, v___x_3545_, v_pos_3529_, v___x_3546_);
lean_dec_ref_known(v___x_3546_, 1);
return v___x_3547_;
}
}
else
{
lean_dec(v___x_3538_);
lean_dec(v_iniSz_3530_);
lean_dec(v_pos_3529_);
lean_dec_ref(v_forbiddenTks_3525_);
return v_s_3533_;
}
}
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_3549_ = ((lean_object*)(l_Lean_Parser_identFn___closed__1));
v___x_3550_ = l_Lean_Parser_expectTokenFn(v___x_3548_, v___x_3549_, v_c_3522_, v_s_3523_);
return v___x_3550_;
}
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
v_errorMsg_3575_ = lean_ctor_get(v_s_3573_, 4);
v___x_3576_ = lean_box(0);
v___x_3577_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3575_, v___x_3576_);
if (v___x_3577_ == 0)
{
lean_dec(v_id_3568_);
return v_s_3573_;
}
else
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_3574_);
if (lean_obj_tag(v___x_3578_) == 3)
{
lean_object* v_val_3579_; uint8_t v___x_3580_; 
v_val_3579_ = lean_ctor_get(v___x_3578_, 2);
lean_inc(v_val_3579_);
lean_dec_ref_known(v___x_3578_, 4);
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
lean_inc_n(v_endPos_3625_, 2);
v_str_3629_ = l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_3597_, v_endPos_3625_);
v___x_3630_ = l_Lean_Parser_ParserState_popSyntax(v_s_3598_);
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
lean_dec_ref_known(v_errorMsg_3706_, 1);
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
lean_object* v___y_3756_; lean_object* v_s_3757_; lean_object* v_stxStack_3770_; lean_object* v_pos_3771_; lean_object* v_cache_3772_; lean_object* v_errorMsg_3773_; lean_object* v_recoveredErrors_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3787_; 
v_stxStack_3770_ = lean_ctor_get(v_s_3754_, 0);
v_pos_3771_ = lean_ctor_get(v_s_3754_, 2);
v_cache_3772_ = lean_ctor_get(v_s_3754_, 3);
v_errorMsg_3773_ = lean_ctor_get(v_s_3754_, 4);
v_recoveredErrors_3774_ = lean_ctor_get(v_s_3754_, 5);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_s_3754_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; 
v_unused_3788_ = lean_ctor_get(v_s_3754_, 1);
lean_dec(v_unused_3788_);
v___x_3776_ = v_s_3754_;
v_isShared_3777_ = v_isSharedCheck_3787_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_recoveredErrors_3774_);
lean_inc(v_errorMsg_3773_);
lean_inc(v_cache_3772_);
lean_inc(v_pos_3771_);
lean_inc(v_stxStack_3770_);
lean_dec(v_s_3754_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3787_;
goto v_resetjp_3775_;
}
v___jp_3755_:
{
lean_object* v_s_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_s_3758_ = lean_apply_2(v_p_3752_, v_c_3753_, v_s_3757_);
v___x_3759_ = l_Lean_Parser_ParserState_stackSize(v_s_3758_);
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = lean_nat_add(v___y_3756_, v___x_3760_);
v___x_3762_ = lean_nat_dec_eq(v___x_3759_, v___x_3761_);
lean_dec(v___x_3761_);
lean_dec(v___x_3759_);
if (v___x_3762_ == 0)
{
lean_object* v_errorMsg_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v_errorMsg_3763_ = lean_ctor_get(v_s_3758_, 4);
lean_inc(v_errorMsg_3763_);
v___x_3764_ = lean_box(0);
v___x_3765_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_3763_, v___x_3764_);
lean_dec(v_errorMsg_3763_);
if (v___x_3765_ == 0)
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3766_ = l_Lean_Parser_ParserState_shrinkStack(v_s_3758_, v___y_3756_);
lean_dec(v___y_3756_);
v___x_3767_ = lean_box(0);
v___x_3768_ = l_Lean_Parser_ParserState_pushSyntax(v___x_3766_, v___x_3767_);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; 
lean_dec(v___y_3756_);
v___x_3769_ = l_Lean_Parser_invalidLongestMatchParser(v_s_3758_);
return v___x_3769_;
}
}
else
{
lean_dec(v___y_3756_);
return v_s_3758_;
}
}
v_resetjp_3775_:
{
lean_object* v___y_3779_; 
if (lean_obj_tag(v_left_x3f_3750_) == 0)
{
lean_object* v___x_3786_; 
lean_dec(v_startLhsPrec_3751_);
v___x_3786_ = l_Lean_Parser_maxPrec;
v___y_3779_ = v___x_3786_;
goto v___jp_3778_;
}
else
{
v___y_3779_ = v_startLhsPrec_3751_;
goto v___jp_3778_;
}
v___jp_3778_:
{
lean_object* v_s_3781_; 
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 1, v___y_3779_);
v_s_3781_ = v___x_3776_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_stxStack_3770_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v___y_3779_);
lean_ctor_set(v_reuseFailAlloc_3785_, 2, v_pos_3771_);
lean_ctor_set(v_reuseFailAlloc_3785_, 3, v_cache_3772_);
lean_ctor_set(v_reuseFailAlloc_3785_, 4, v_errorMsg_3773_);
lean_ctor_set(v_reuseFailAlloc_3785_, 5, v_recoveredErrors_3774_);
v_s_3781_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v_startSize_3782_; 
v_startSize_3782_ = l_Lean_Parser_ParserState_stackSize(v_s_3781_);
if (lean_obj_tag(v_left_x3f_3750_) == 1)
{
lean_object* v_val_3783_; lean_object* v_s_3784_; 
v_val_3783_ = lean_ctor_get(v_left_x3f_3750_, 0);
lean_inc(v_val_3783_);
lean_dec_ref_known(v_left_x3f_3750_, 1);
v_s_3784_ = l_Lean_Parser_ParserState_pushSyntax(v_s_3781_, v_val_3783_);
v___y_3756_ = v_startSize_3782_;
v_s_3757_ = v_s_3784_;
goto v___jp_3755_;
}
else
{
lean_dec(v_left_x3f_3750_);
v___y_3756_ = v_startSize_3782_;
v_s_3757_ = v_s_3781_;
goto v___jp_3755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0(lean_object* v_s_3789_, lean_object* v_prio_3790_){
_start:
{
lean_object* v_pos_3791_; lean_object* v_errorMsg_3792_; lean_object* v___y_3794_; 
v_pos_3791_ = lean_ctor_get(v_s_3789_, 2);
v_errorMsg_3792_ = lean_ctor_get(v_s_3789_, 4);
if (lean_obj_tag(v_errorMsg_3792_) == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_unsigned_to_nat(1u);
v___y_3794_ = v___x_3797_;
goto v___jp_3793_;
}
else
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_unsigned_to_nat(0u);
v___y_3794_ = v___x_3798_;
goto v___jp_3793_;
}
v___jp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___y_3794_);
lean_ctor_set(v___x_3795_, 1, v_prio_3790_);
lean_inc(v_pos_3791_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v_pos_3791_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___lam__0___boxed(lean_object* v_s_3799_, lean_object* v_prio_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3799_, v_prio_3800_);
lean_dec_ref(v_s_3799_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep(lean_object* v_left_x3f_3802_, lean_object* v_startSize_3803_, lean_object* v_startLhsPrec_3804_, lean_object* v_startPos_3805_, lean_object* v_prevPrio_3806_, lean_object* v_prio_3807_, lean_object* v_p_3808_, lean_object* v_c_3809_, lean_object* v_s_3810_){
_start:
{
lean_object* v_lhsPrec_3811_; lean_object* v_pos_3812_; lean_object* v_errorMsg_3813_; lean_object* v_previousScore_3814_; lean_object* v_fst_3815_; lean_object* v_snd_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3872_; 
v_lhsPrec_3811_ = lean_ctor_get(v_s_3810_, 1);
lean_inc(v_lhsPrec_3811_);
v_pos_3812_ = lean_ctor_get(v_s_3810_, 2);
lean_inc(v_pos_3812_);
v_errorMsg_3813_ = lean_ctor_get(v_s_3810_, 4);
lean_inc(v_errorMsg_3813_);
lean_inc(v_prevPrio_3806_);
v_previousScore_3814_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3810_, v_prevPrio_3806_);
v_fst_3815_ = lean_ctor_get(v_previousScore_3814_, 0);
v_snd_3816_ = lean_ctor_get(v_previousScore_3814_, 1);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_previousScore_3814_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3818_ = v_previousScore_3814_;
v_isShared_3819_ = v_isSharedCheck_3872_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_snd_3816_);
lean_inc(v_fst_3815_);
lean_dec(v_previousScore_3814_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3872_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_prevSize_3820_; lean_object* v_s_3821_; lean_object* v_s_3822_; lean_object* v___x_3831_; lean_object* v_fst_3832_; lean_object* v_snd_3833_; uint8_t v___x_3834_; 
v_prevSize_3820_ = l_Lean_Parser_ParserState_stackSize(v_s_3810_);
v_s_3821_ = l_Lean_Parser_ParserState_restore(v_s_3810_, v_prevSize_3820_, v_startPos_3805_);
v_s_3822_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3802_, v_startLhsPrec_3804_, v_p_3808_, v_c_3809_, v_s_3821_);
lean_inc(v_prio_3807_);
v___x_3831_ = l_Lean_Parser_longestMatchStep___lam__0(v_s_3822_, v_prio_3807_);
v_fst_3832_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_fst_3832_);
v_snd_3833_ = lean_ctor_get(v___x_3831_, 1);
lean_inc(v_snd_3833_);
lean_dec_ref(v___x_3831_);
v___x_3834_ = lean_nat_dec_lt(v_fst_3815_, v_fst_3832_);
if (v___x_3834_ == 0)
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_nat_dec_eq(v_fst_3815_, v_fst_3832_);
lean_dec(v_fst_3832_);
lean_dec(v_fst_3815_);
if (v___x_3835_ == 0)
{
lean_dec(v_snd_3833_);
lean_del_object(v___x_3818_);
lean_dec(v_snd_3816_);
lean_dec(v_prio_3807_);
goto v___jp_3828_;
}
else
{
lean_object* v_fst_3836_; lean_object* v_snd_3837_; lean_object* v_fst_3838_; lean_object* v_snd_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3871_; 
v_fst_3836_ = lean_ctor_get(v_snd_3816_, 0);
lean_inc(v_fst_3836_);
v_snd_3837_ = lean_ctor_get(v_snd_3816_, 1);
lean_inc(v_snd_3837_);
lean_dec(v_snd_3816_);
v_fst_3838_ = lean_ctor_get(v_snd_3833_, 0);
v_snd_3839_ = lean_ctor_get(v_snd_3833_, 1);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_snd_3833_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3841_ = v_snd_3833_;
v_isShared_3842_ = v_isSharedCheck_3871_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_snd_3839_);
lean_inc(v_fst_3838_);
lean_dec(v_snd_3833_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3871_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
uint8_t v___x_3843_; 
v___x_3843_ = lean_nat_dec_lt(v_fst_3836_, v_fst_3838_);
if (v___x_3843_ == 0)
{
uint8_t v___x_3844_; 
v___x_3844_ = lean_nat_dec_eq(v_fst_3836_, v_fst_3838_);
lean_dec(v_fst_3838_);
lean_dec(v_fst_3836_);
if (v___x_3844_ == 0)
{
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_snd_3837_);
lean_del_object(v___x_3818_);
lean_dec(v_prio_3807_);
goto v___jp_3828_;
}
else
{
uint8_t v___x_3845_; 
v___x_3845_ = lean_nat_dec_lt(v_snd_3837_, v_snd_3839_);
if (v___x_3845_ == 0)
{
uint8_t v___x_3846_; 
lean_del_object(v___x_3818_);
v___x_3846_ = lean_nat_dec_eq(v_snd_3837_, v_snd_3839_);
lean_dec(v_snd_3839_);
lean_dec(v_snd_3837_);
if (v___x_3846_ == 0)
{
lean_del_object(v___x_3841_);
lean_dec(v_prio_3807_);
goto v___jp_3828_;
}
else
{
lean_dec(v_pos_3812_);
lean_dec(v_prevPrio_3806_);
if (lean_obj_tag(v_errorMsg_3813_) == 0)
{
lean_object* v_stxStack_3847_; lean_object* v_lhsPrec_3848_; lean_object* v_pos_3849_; lean_object* v_cache_3850_; lean_object* v_errorMsg_3851_; lean_object* v_recoveredErrors_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v_prevSize_3820_);
v_stxStack_3847_ = lean_ctor_get(v_s_3822_, 0);
v_lhsPrec_3848_ = lean_ctor_get(v_s_3822_, 1);
v_pos_3849_ = lean_ctor_get(v_s_3822_, 2);
v_cache_3850_ = lean_ctor_get(v_s_3822_, 3);
v_errorMsg_3851_ = lean_ctor_get(v_s_3822_, 4);
v_recoveredErrors_3852_ = lean_ctor_get(v_s_3822_, 5);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_s_3822_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3854_ = v_s_3822_;
v_isShared_3855_ = v_isSharedCheck_3865_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_recoveredErrors_3852_);
lean_inc(v_errorMsg_3851_);
lean_inc(v_cache_3850_);
lean_inc(v_pos_3849_);
lean_inc(v_lhsPrec_3848_);
lean_inc(v_stxStack_3847_);
lean_dec(v_s_3822_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3865_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___y_3857_; uint8_t v___x_3864_; 
v___x_3864_ = lean_nat_dec_le(v_lhsPrec_3848_, v_lhsPrec_3811_);
if (v___x_3864_ == 0)
{
lean_dec(v_lhsPrec_3848_);
v___y_3857_ = v_lhsPrec_3811_;
goto v___jp_3856_;
}
else
{
lean_dec(v_lhsPrec_3811_);
v___y_3857_ = v_lhsPrec_3848_;
goto v___jp_3856_;
}
v___jp_3856_:
{
lean_object* v___x_3859_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 1, v___y_3857_);
v___x_3859_ = v___x_3854_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_stxStack_3847_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v___y_3857_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_pos_3849_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v_cache_3850_);
lean_ctor_set(v_reuseFailAlloc_3863_, 4, v_errorMsg_3851_);
lean_ctor_set(v_reuseFailAlloc_3863_, 5, v_recoveredErrors_3852_);
v___x_3859_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; 
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v_prio_3807_);
lean_ctor_set(v___x_3841_, 0, v___x_3859_);
v___x_3861_ = v___x_3841_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_prio_3807_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
else
{
lean_object* v_val_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
lean_dec(v_lhsPrec_3811_);
v_val_3866_ = lean_ctor_get(v_errorMsg_3813_, 0);
lean_inc(v_val_3866_);
lean_dec_ref_known(v_errorMsg_3813_, 1);
v___x_3867_ = l_Lean_Parser_ParserState_mergeErrors(v_s_3822_, v_prevSize_3820_, v_val_3866_);
lean_dec(v_prevSize_3820_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v_prio_3807_);
lean_ctor_set(v___x_3841_, 0, v___x_3867_);
v___x_3869_ = v___x_3841_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_prio_3807_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
else
{
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_prevSize_3820_);
lean_dec(v_errorMsg_3813_);
lean_dec(v_pos_3812_);
lean_dec(v_lhsPrec_3811_);
lean_dec(v_prevPrio_3806_);
goto v___jp_3823_;
}
}
}
else
{
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_fst_3838_);
lean_dec(v_snd_3837_);
lean_dec(v_fst_3836_);
lean_dec(v_prevSize_3820_);
lean_dec(v_errorMsg_3813_);
lean_dec(v_pos_3812_);
lean_dec(v_lhsPrec_3811_);
lean_dec(v_prevPrio_3806_);
goto v___jp_3823_;
}
}
}
}
else
{
lean_dec(v_snd_3833_);
lean_dec(v_fst_3832_);
lean_dec(v_prevSize_3820_);
lean_dec(v_snd_3816_);
lean_dec(v_fst_3815_);
lean_dec(v_errorMsg_3813_);
lean_dec(v_pos_3812_);
lean_dec(v_lhsPrec_3811_);
lean_dec(v_prevPrio_3806_);
goto v___jp_3823_;
}
v___jp_3823_:
{
lean_object* v___x_3824_; lean_object* v___x_3826_; 
v___x_3824_ = l_Lean_Parser_ParserState_keepNewError(v_s_3822_, v_startSize_3803_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 1, v_prio_3807_);
lean_ctor_set(v___x_3818_, 0, v___x_3824_);
v___x_3826_ = v___x_3818_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v_prio_3807_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
v___jp_3828_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = l_Lean_Parser_ParserState_keepPrevError(v_s_3822_, v_prevSize_3820_, v_pos_3812_, v_errorMsg_3813_, v_lhsPrec_3811_);
lean_dec(v_prevSize_3820_);
v___x_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
lean_ctor_set(v___x_3830_, 1, v_prevPrio_3806_);
return v___x_3830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchStep___boxed(lean_object* v_left_x3f_3873_, lean_object* v_startSize_3874_, lean_object* v_startLhsPrec_3875_, lean_object* v_startPos_3876_, lean_object* v_prevPrio_3877_, lean_object* v_prio_3878_, lean_object* v_p_3879_, lean_object* v_c_3880_, lean_object* v_s_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3873_, v_startSize_3874_, v_startLhsPrec_3875_, v_startPos_3876_, v_prevPrio_3877_, v_prio_3878_, v_p_3879_, v_c_3880_, v_s_3881_);
lean_dec(v_startSize_3874_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult(lean_object* v_startSize_3883_, lean_object* v_s_3884_){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3885_ = lean_unsigned_to_nat(1u);
v___x_3886_ = lean_nat_add(v_startSize_3883_, v___x_3885_);
v___x_3887_ = l_Lean_Parser_ParserState_stackSize(v_s_3884_);
v___x_3888_ = lean_nat_dec_lt(v___x_3886_, v___x_3887_);
lean_dec(v___x_3887_);
lean_dec(v___x_3886_);
if (v___x_3888_ == 0)
{
return v_s_3884_;
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = ((lean_object*)(l_Lean_Parser_orelseFnCore___lam__0___closed__1));
v___x_3890_ = l_Lean_Parser_ParserState_mkNode(v_s_3884_, v___x_3889_, v_startSize_3883_);
return v___x_3890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchMkResult___boxed(lean_object* v_startSize_3891_, lean_object* v_s_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3891_, v_s_3892_);
lean_dec(v_startSize_3891_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(lean_object* v_left_x3f_3894_, lean_object* v_startSize_3895_, lean_object* v_startLhsPrec_3896_, lean_object* v_startPos_3897_, lean_object* v_prevPrio_3898_, lean_object* v_ps_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_){
_start:
{
if (lean_obj_tag(v_ps_3899_) == 0)
{
lean_object* v___x_3902_; 
lean_dec_ref(v_a_3900_);
lean_dec(v_prevPrio_3898_);
lean_dec(v_startPos_3897_);
lean_dec(v_startLhsPrec_3896_);
lean_dec(v_left_x3f_3894_);
v___x_3902_ = l_Lean_Parser_longestMatchMkResult(v_startSize_3895_, v_a_3901_);
return v___x_3902_;
}
else
{
lean_object* v_head_3903_; lean_object* v_fst_3904_; lean_object* v_tail_3905_; lean_object* v_snd_3906_; lean_object* v_fn_3907_; lean_object* v___x_3908_; lean_object* v_fst_3909_; lean_object* v_snd_3910_; 
v_head_3903_ = lean_ctor_get(v_ps_3899_, 0);
lean_inc(v_head_3903_);
v_fst_3904_ = lean_ctor_get(v_head_3903_, 0);
lean_inc(v_fst_3904_);
v_tail_3905_ = lean_ctor_get(v_ps_3899_, 1);
lean_inc(v_tail_3905_);
lean_dec_ref_known(v_ps_3899_, 2);
v_snd_3906_ = lean_ctor_get(v_head_3903_, 1);
lean_inc(v_snd_3906_);
lean_dec(v_head_3903_);
v_fn_3907_ = lean_ctor_get(v_fst_3904_, 1);
lean_inc_ref(v_fn_3907_);
lean_dec(v_fst_3904_);
lean_inc_ref(v_a_3900_);
lean_inc(v_startPos_3897_);
lean_inc(v_startLhsPrec_3896_);
lean_inc(v_left_x3f_3894_);
v___x_3908_ = l_Lean_Parser_longestMatchStep(v_left_x3f_3894_, v_startSize_3895_, v_startLhsPrec_3896_, v_startPos_3897_, v_prevPrio_3898_, v_snd_3906_, v_fn_3907_, v_a_3900_, v_a_3901_);
v_fst_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_fst_3909_);
v_snd_3910_ = lean_ctor_get(v___x_3908_, 1);
lean_inc(v_snd_3910_);
lean_dec_ref(v___x_3908_);
v_prevPrio_3898_ = v_snd_3910_;
v_ps_3899_ = v_tail_3905_;
v_a_3901_ = v_fst_3909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse___boxed(lean_object* v_left_x3f_3912_, lean_object* v_startSize_3913_, lean_object* v_startLhsPrec_3914_, lean_object* v_startPos_3915_, lean_object* v_prevPrio_3916_, lean_object* v_ps_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3912_, v_startSize_3913_, v_startLhsPrec_3914_, v_startPos_3915_, v_prevPrio_3916_, v_ps_3917_, v_a_3918_, v_a_3919_);
lean_dec(v_startSize_3913_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux(lean_object* v_left_x3f_3921_, lean_object* v_startSize_3922_, lean_object* v_startLhsPrec_3923_, lean_object* v_startPos_3924_, lean_object* v_prevPrio_3925_, lean_object* v_ps_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3921_, v_startSize_3922_, v_startLhsPrec_3923_, v_startPos_3924_, v_prevPrio_3925_, v_ps_3926_, v_a_3927_, v_a_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFnAux___boxed(lean_object* v_left_x3f_3930_, lean_object* v_startSize_3931_, lean_object* v_startLhsPrec_3932_, lean_object* v_startPos_3933_, lean_object* v_prevPrio_3934_, lean_object* v_ps_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l_Lean_Parser_longestMatchFnAux(v_left_x3f_3930_, v_startSize_3931_, v_startLhsPrec_3932_, v_startPos_3933_, v_prevPrio_3934_, v_ps_3935_, v_a_3936_, v_a_3937_);
lean_dec(v_startSize_3931_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_longestMatchFn(lean_object* v_left_x3f_3940_, lean_object* v_x_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
if (lean_obj_tag(v_x_3941_) == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
lean_dec_ref(v_a_3942_);
lean_dec(v_left_x3f_3940_);
v___x_3944_ = ((lean_object*)(l_Lean_Parser_longestMatchFn___closed__0));
v___x_3945_ = l_Lean_Parser_ParserState_mkError(v_a_3943_, v___x_3944_);
return v___x_3945_;
}
else
{
lean_object* v_tail_3946_; 
v_tail_3946_ = lean_ctor_get(v_x_3941_, 1);
if (lean_obj_tag(v_tail_3946_) == 0)
{
lean_object* v_head_3947_; lean_object* v_fst_3948_; lean_object* v_lhsPrec_3949_; lean_object* v_fn_3950_; lean_object* v___x_3951_; 
v_head_3947_ = lean_ctor_get(v_x_3941_, 0);
lean_inc(v_head_3947_);
lean_dec_ref_known(v_x_3941_, 2);
v_fst_3948_ = lean_ctor_get(v_head_3947_, 0);
lean_inc(v_fst_3948_);
lean_dec(v_head_3947_);
v_lhsPrec_3949_ = lean_ctor_get(v_a_3943_, 1);
lean_inc(v_lhsPrec_3949_);
v_fn_3950_ = lean_ctor_get(v_fst_3948_, 1);
lean_inc_ref(v_fn_3950_);
lean_dec(v_fst_3948_);
v___x_3951_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3940_, v_lhsPrec_3949_, v_fn_3950_, v_a_3942_, v_a_3943_);
return v___x_3951_;
}
else
{
lean_object* v_head_3952_; lean_object* v_fst_3953_; lean_object* v_lhsPrec_3954_; lean_object* v_pos_3955_; lean_object* v_snd_3956_; lean_object* v_fn_3957_; lean_object* v_startSize_3958_; lean_object* v_s_3959_; lean_object* v___x_3960_; 
lean_inc(v_tail_3946_);
v_head_3952_ = lean_ctor_get(v_x_3941_, 0);
lean_inc(v_head_3952_);
lean_dec_ref_known(v_x_3941_, 2);
v_fst_3953_ = lean_ctor_get(v_head_3952_, 0);
lean_inc(v_fst_3953_);
v_lhsPrec_3954_ = lean_ctor_get(v_a_3943_, 1);
lean_inc_n(v_lhsPrec_3954_, 2);
v_pos_3955_ = lean_ctor_get(v_a_3943_, 2);
lean_inc(v_pos_3955_);
v_snd_3956_ = lean_ctor_get(v_head_3952_, 1);
lean_inc(v_snd_3956_);
lean_dec(v_head_3952_);
v_fn_3957_ = lean_ctor_get(v_fst_3953_, 1);
lean_inc_ref(v_fn_3957_);
lean_dec(v_fst_3953_);
v_startSize_3958_ = l_Lean_Parser_ParserState_stackSize(v_a_3943_);
lean_inc_ref(v_a_3942_);
lean_inc(v_left_x3f_3940_);
v_s_3959_ = l_Lean_Parser_runLongestMatchParser(v_left_x3f_3940_, v_lhsPrec_3954_, v_fn_3957_, v_a_3942_, v_a_3943_);
v___x_3960_ = l___private_Lean_Parser_Basic_0__Lean_Parser_longestMatchFnAux_parse(v_left_x3f_3940_, v_startSize_3958_, v_lhsPrec_3954_, v_pos_3955_, v_snd_3956_, v_tail_3946_, v_a_3942_, v_s_3959_);
lean_dec(v_startSize_3958_);
return v___x_3960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_anyOfFn(lean_object* v_x_3962_, lean_object* v_x_3963_, lean_object* v_x_3964_){
_start:
{
if (lean_obj_tag(v_x_3962_) == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_dec_ref(v_x_3963_);
v___x_3965_ = ((lean_object*)(l_Lean_Parser_anyOfFn___closed__0));
v___x_3966_ = l_Lean_Parser_ParserState_mkError(v_x_3964_, v___x_3965_);
return v___x_3966_;
}
else
{
lean_object* v_tail_3967_; 
v_tail_3967_ = lean_ctor_get(v_x_3962_, 1);
if (lean_obj_tag(v_tail_3967_) == 0)
{
lean_object* v_head_3968_; lean_object* v_fn_3969_; lean_object* v___x_3970_; 
v_head_3968_ = lean_ctor_get(v_x_3962_, 0);
lean_inc(v_head_3968_);
lean_dec_ref_known(v_x_3962_, 2);
v_fn_3969_ = lean_ctor_get(v_head_3968_, 1);
lean_inc_ref(v_fn_3969_);
lean_dec(v_head_3968_);
v___x_3970_ = lean_apply_2(v_fn_3969_, v_x_3963_, v_x_3964_);
return v___x_3970_;
}
else
{
lean_object* v_head_3971_; lean_object* v_fn_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_inc(v_tail_3967_);
v_head_3971_ = lean_ctor_get(v_x_3962_, 0);
lean_inc(v_head_3971_);
lean_dec_ref_known(v_x_3962_, 2);
v_fn_3972_ = lean_ctor_get(v_head_3971_, 1);
lean_inc_ref(v_fn_3972_);
lean_dec(v_head_3971_);
v___x_3973_ = lean_alloc_closure((void*)(l_Lean_Parser_anyOfFn), 3, 1);
lean_closure_set(v___x_3973_, 0, v_tail_3967_);
v___x_3974_ = l_Lean_Parser_orelseFn(v_fn_3972_, v___x_3973_, v_x_3963_, v_x_3964_);
return v___x_3974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEqFn(lean_object* v_errorMsg_3975_, lean_object* v_c_3976_, lean_object* v_s_3977_){
_start:
{
lean_object* v_toCacheableParserContext_3978_; lean_object* v_savedPos_x3f_3979_; 
v_toCacheableParserContext_3978_ = lean_ctor_get(v_c_3976_, 2);
v_savedPos_x3f_3979_ = lean_ctor_get(v_toCacheableParserContext_3978_, 2);
lean_inc(v_savedPos_x3f_3979_);
if (lean_obj_tag(v_savedPos_x3f_3979_) == 0)
{
lean_dec_ref(v_c_3976_);
lean_dec_ref(v_errorMsg_3975_);
return v_s_3977_;
}
else
{
lean_object* v_toInputContext_3980_; lean_object* v_val_3981_; lean_object* v_fileMap_3982_; lean_object* v_pos_3983_; lean_object* v_savedPos_3984_; lean_object* v_pos_3985_; lean_object* v_column_3986_; lean_object* v_column_3987_; uint8_t v___x_3988_; 
v_toInputContext_3980_ = lean_ctor_get(v_c_3976_, 0);
lean_inc_ref(v_toInputContext_3980_);
lean_dec_ref(v_c_3976_);
v_val_3981_ = lean_ctor_get(v_savedPos_x3f_3979_, 0);
lean_inc(v_val_3981_);
lean_dec_ref_known(v_savedPos_x3f_3979_, 1);
v_fileMap_3982_ = lean_ctor_get(v_toInputContext_3980_, 2);
lean_inc_ref_n(v_fileMap_3982_, 2);
lean_dec_ref(v_toInputContext_3980_);
v_pos_3983_ = lean_ctor_get(v_s_3977_, 2);
v_savedPos_3984_ = l_Lean_FileMap_toPosition(v_fileMap_3982_, v_val_3981_);
lean_dec(v_val_3981_);
v_pos_3985_ = l_Lean_FileMap_toPosition(v_fileMap_3982_, v_pos_3983_);
v_column_3986_ = lean_ctor_get(v_pos_3985_, 1);
lean_inc(v_column_3986_);
lean_dec_ref(v_pos_3985_);
v_column_3987_ = lean_ctor_get(v_savedPos_3984_, 1);
lean_inc(v_column_3987_);
lean_dec_ref(v_savedPos_3984_);
v___x_3988_ = lean_nat_dec_eq(v_column_3986_, v_column_3987_);
lean_dec(v_column_3987_);
lean_dec(v_column_3986_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_Parser_ParserState_mkError(v_s_3977_, v_errorMsg_3975_);
return v___x_3989_;
}
else
{
lean_dec_ref(v_errorMsg_3975_);
return v_s_3977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColEq(lean_object* v_errorMsg_3990_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3991_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_3992_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColEqFn), 3, 1);
lean_closure_set(v___x_3992_, 0, v_errorMsg_3990_);
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3991_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1(){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__1));
v___x_4002_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___closed__2));
v___x_4003_ = l_Lean_addBuiltinDocString(v___x_4001_, v___x_4002_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1___boxed(lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColEq___regBuiltin_Lean_Parser_checkColEq_docString__1();
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGeFn(lean_object* v_errorMsg_4006_, lean_object* v_c_4007_, lean_object* v_s_4008_){
_start:
{
lean_object* v_toCacheableParserContext_4009_; lean_object* v_savedPos_x3f_4010_; 
v_toCacheableParserContext_4009_ = lean_ctor_get(v_c_4007_, 2);
v_savedPos_x3f_4010_ = lean_ctor_get(v_toCacheableParserContext_4009_, 2);
lean_inc(v_savedPos_x3f_4010_);
if (lean_obj_tag(v_savedPos_x3f_4010_) == 0)
{
lean_dec_ref(v_c_4007_);
lean_dec_ref(v_errorMsg_4006_);
return v_s_4008_;
}
else
{
lean_object* v_toInputContext_4011_; lean_object* v_val_4012_; lean_object* v_fileMap_4013_; lean_object* v_pos_4014_; lean_object* v_savedPos_4015_; lean_object* v_column_4016_; lean_object* v_pos_4017_; lean_object* v_column_4018_; uint8_t v___x_4019_; 
v_toInputContext_4011_ = lean_ctor_get(v_c_4007_, 0);
lean_inc_ref(v_toInputContext_4011_);
lean_dec_ref(v_c_4007_);
v_val_4012_ = lean_ctor_get(v_savedPos_x3f_4010_, 0);
lean_inc(v_val_4012_);
lean_dec_ref_known(v_savedPos_x3f_4010_, 1);
v_fileMap_4013_ = lean_ctor_get(v_toInputContext_4011_, 2);
lean_inc_ref_n(v_fileMap_4013_, 2);
lean_dec_ref(v_toInputContext_4011_);
v_pos_4014_ = lean_ctor_get(v_s_4008_, 2);
v_savedPos_4015_ = l_Lean_FileMap_toPosition(v_fileMap_4013_, v_val_4012_);
lean_dec(v_val_4012_);
v_column_4016_ = lean_ctor_get(v_savedPos_4015_, 1);
lean_inc(v_column_4016_);
lean_dec_ref(v_savedPos_4015_);
v_pos_4017_ = l_Lean_FileMap_toPosition(v_fileMap_4013_, v_pos_4014_);
v_column_4018_ = lean_ctor_get(v_pos_4017_, 1);
lean_inc(v_column_4018_);
lean_dec_ref(v_pos_4017_);
v___x_4019_ = lean_nat_dec_le(v_column_4016_, v_column_4018_);
lean_dec(v_column_4018_);
lean_dec(v_column_4016_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Parser_ParserState_mkError(v_s_4008_, v_errorMsg_4006_);
return v___x_4020_;
}
else
{
lean_dec_ref(v_errorMsg_4006_);
return v_s_4008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGe(lean_object* v_errorMsg_4021_){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = ((lean_object*)(l_Lean_Parser_epsilonInfo));
v___x_4023_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGeFn), 3, 1);
lean_closure_set(v___x_4023_, 0, v_errorMsg_4021_);
v___x_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4022_);
lean_ctor_set(v___x_4024_, 1, v___x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1(){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__1));
v___x_4033_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___closed__2));
v___x_4034_ = l_Lean_addBuiltinDocString(v___x_4032_, v___x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1___boxed(lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGe___regBuiltin_Lean_Parser_checkColGe_docString__1();
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGtFn(lean_object* v_errorMsg_4037_, lean_object* v_c_4038_, lean_object* v_s_4039_){
_start:
{
lean_object* v_toCacheableParserContext_4040_; lean_object* v_savedPos_x3f_4041_; 
v_toCacheableParserContext_4040_ = lean_ctor_get(v_c_4038_, 2);
v_savedPos_x3f_4041_ = lean_ctor_get(v_toCacheableParserContext_4040_, 2);
lean_inc(v_savedPos_x3f_4041_);
if (lean_obj_tag(v_savedPos_x3f_4041_) == 0)
{
lean_dec_ref(v_c_4038_);
lean_dec_ref(v_errorMsg_4037_);
return v_s_4039_;
}
else
{
lean_object* v_toInputContext_4042_; lean_object* v_val_4043_; lean_object* v_fileMap_4044_; lean_object* v_pos_4045_; lean_object* v_savedPos_4046_; lean_object* v_column_4047_; lean_object* v_pos_4048_; lean_object* v_column_4049_; uint8_t v___x_4050_; 
v_toInputContext_4042_ = lean_ctor_get(v_c_4038_, 0);
lean_inc_ref(v_toInputContext_4042_);
lean_dec_ref(v_c_4038_);
v_val_4043_ = lean_ctor_get(v_savedPos_x3f_4041_, 0);
lean_inc(v_val_4043_);
lean_dec_ref_known(v_savedPos_x3f_4041_, 1);
v_fileMap_4044_ = lean_ctor_get(v_toInputContext_4042_, 2);
lean_inc_ref_n(v_fileMap_4044_, 2);
lean_dec_ref(v_toInputContext_4042_);
v_pos_4045_ = lean_ctor_get(v_s_4039_, 2);
v_savedPos_4046_ = l_Lean_FileMap_toPosition(v_fileMap_4044_, v_val_4043_);
lean_dec(v_val_4043_);
v_column_4047_ = lean_ctor_get(v_savedPos_4046_, 1);
lean_inc(v_column_4047_);
lean_dec_ref(v_savedPos_4046_);
v_pos_4048_ = l_Lean_FileMap_toPosition(v_fileMap_4044_, v_pos_4045_);
v_column_4049_ = lean_ctor_get(v_pos_4048_, 1);
lean_inc(v_column_4049_);
lean_dec_ref(v_pos_4048_);
v___x_4050_ = lean_nat_dec_lt(v_column_4047_, v_column_4049_);
lean_dec(v_column_4049_);
lean_dec(v_column_4047_);
if (v___x_4050_ == 0)
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Lean_Parser_ParserState_mkError(v_s_4039_, v_errorMsg_4037_);
return v___x_4051_;
}
else
{
lean_dec_ref(v_errorMsg_4037_);
return v_s_4039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkColGt(lean_object* v_errorMsg_4052_){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4054_ = lean_alloc_closure((void*)(l_Lean_Parser_checkColGtFn), 3, 1);
lean_closure_set(v___x_4054_, 0, v_errorMsg_4052_);
v___x_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4053_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1(){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__1));
v___x_4064_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___closed__2));
v___x_4065_ = l_Lean_addBuiltinDocString(v___x_4063_, v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1___boxed(lean_object* v_a_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkColGt___regBuiltin_Lean_Parser_checkColGt_docString__1();
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEqFn(lean_object* v_errorMsg_4068_, lean_object* v_c_4069_, lean_object* v_s_4070_){
_start:
{
lean_object* v_toCacheableParserContext_4071_; lean_object* v_savedPos_x3f_4072_; 
v_toCacheableParserContext_4071_ = lean_ctor_get(v_c_4069_, 2);
v_savedPos_x3f_4072_ = lean_ctor_get(v_toCacheableParserContext_4071_, 2);
lean_inc(v_savedPos_x3f_4072_);
if (lean_obj_tag(v_savedPos_x3f_4072_) == 0)
{
lean_dec_ref(v_c_4069_);
lean_dec_ref(v_errorMsg_4068_);
return v_s_4070_;
}
else
{
lean_object* v_toInputContext_4073_; lean_object* v_val_4074_; lean_object* v_fileMap_4075_; lean_object* v_pos_4076_; lean_object* v_savedPos_4077_; lean_object* v_pos_4078_; lean_object* v_line_4079_; lean_object* v_line_4080_; uint8_t v___x_4081_; 
v_toInputContext_4073_ = lean_ctor_get(v_c_4069_, 0);
lean_inc_ref(v_toInputContext_4073_);
lean_dec_ref(v_c_4069_);
v_val_4074_ = lean_ctor_get(v_savedPos_x3f_4072_, 0);
lean_inc(v_val_4074_);
lean_dec_ref_known(v_savedPos_x3f_4072_, 1);
v_fileMap_4075_ = lean_ctor_get(v_toInputContext_4073_, 2);
lean_inc_ref_n(v_fileMap_4075_, 2);
lean_dec_ref(v_toInputContext_4073_);
v_pos_4076_ = lean_ctor_get(v_s_4070_, 2);
v_savedPos_4077_ = l_Lean_FileMap_toPosition(v_fileMap_4075_, v_val_4074_);
lean_dec(v_val_4074_);
v_pos_4078_ = l_Lean_FileMap_toPosition(v_fileMap_4075_, v_pos_4076_);
v_line_4079_ = lean_ctor_get(v_pos_4078_, 0);
lean_inc(v_line_4079_);
lean_dec_ref(v_pos_4078_);
v_line_4080_ = lean_ctor_get(v_savedPos_4077_, 0);
lean_inc(v_line_4080_);
lean_dec_ref(v_savedPos_4077_);
v___x_4081_ = lean_nat_dec_eq(v_line_4079_, v_line_4080_);
lean_dec(v_line_4080_);
lean_dec(v_line_4079_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_Parser_ParserState_mkError(v_s_4070_, v_errorMsg_4068_);
return v___x_4082_;
}
else
{
lean_dec_ref(v_errorMsg_4068_);
return v_s_4070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkLineEq(lean_object* v_errorMsg_4083_){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4085_ = lean_alloc_closure((void*)(l_Lean_Parser_checkLineEqFn), 3, 1);
lean_closure_set(v___x_4085_, 0, v_errorMsg_4083_);
v___x_4086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4084_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1(){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__1));
v___x_4095_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___closed__2));
v___x_4096_ = l_Lean_addBuiltinDocString(v___x_4094_, v___x_4095_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1___boxed(lean_object* v_a_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkLineEq___regBuiltin_Lean_Parser_checkLineEq_docString__1();
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0(lean_object* v___y_4099_, lean_object* v_x_4100_){
_start:
{
lean_object* v_prec_4101_; lean_object* v_quotDepth_4102_; uint8_t v_suppressInsideQuot_4103_; lean_object* v_forbiddenTks_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4113_; 
v_prec_4101_ = lean_ctor_get(v_x_4100_, 0);
v_quotDepth_4102_ = lean_ctor_get(v_x_4100_, 1);
v_suppressInsideQuot_4103_ = lean_ctor_get_uint8(v_x_4100_, sizeof(void*)*4);
v_forbiddenTks_4104_ = lean_ctor_get(v_x_4100_, 3);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_x_4100_);
if (v_isSharedCheck_4113_ == 0)
{
lean_object* v_unused_4114_; 
v_unused_4114_ = lean_ctor_get(v_x_4100_, 2);
lean_dec(v_unused_4114_);
v___x_4106_ = v_x_4100_;
v_isShared_4107_ = v_isSharedCheck_4113_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_forbiddenTks_4104_);
lean_inc(v_quotDepth_4102_);
lean_inc(v_prec_4101_);
lean_dec(v_x_4100_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4113_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v_pos_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
v_pos_4108_ = lean_ctor_get(v___y_4099_, 2);
lean_inc(v_pos_4108_);
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_pos_4108_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 2, v___x_4109_);
v___x_4111_ = v___x_4106_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_prec_4101_);
lean_ctor_set(v_reuseFailAlloc_4112_, 1, v_quotDepth_4102_);
lean_ctor_set(v_reuseFailAlloc_4112_, 2, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4112_, 3, v_forbiddenTks_4104_);
lean_ctor_set_uint8(v_reuseFailAlloc_4112_, sizeof(void*)*4, v_suppressInsideQuot_4103_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__0___boxed(lean_object* v___y_4115_, lean_object* v_x_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Lean_Parser_withPosition___lam__0(v___y_4115_, v_x_4116_);
lean_dec_ref(v___y_4115_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition___lam__1(lean_object* v_fn_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v___f_4121_; lean_object* v___x_4122_; 
lean_inc_ref(v___y_4120_);
v___f_4121_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4121_, 0, v___y_4120_);
v___x_4122_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4121_, v_fn_4118_, v___y_4119_, v___y_4120_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPosition(lean_object* v_p_4123_){
_start:
{
lean_object* v_info_4124_; lean_object* v_fn_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4133_; 
v_info_4124_ = lean_ctor_get(v_p_4123_, 0);
v_fn_4125_ = lean_ctor_get(v_p_4123_, 1);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_p_4123_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4127_ = v_p_4123_;
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_fn_4125_);
lean_inc(v_info_4124_);
lean_dec(v_p_4123_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4133_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___f_4129_; lean_object* v___x_4131_; 
v___f_4129_ = lean_alloc_closure((void*)(l_Lean_Parser_withPosition___lam__1), 3, 1);
lean_closure_set(v___f_4129_, 0, v_fn_4125_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 1, v___f_4129_);
v___x_4131_ = v___x_4127_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_info_4124_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___f_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1(){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4141_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__1));
v___x_4142_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___closed__2));
v___x_4143_ = l_Lean_addBuiltinDocString(v___x_4141_, v___x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1___boxed(lean_object* v_a_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withPosition___regBuiltin_Lean_Parser_withPosition_docString__1();
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0(lean_object* v_prev_4146_, lean_object* v_pos_4147_, lean_object* v_c_4148_){
_start:
{
uint8_t v___x_4149_; 
v___x_4149_ = l_Lean_Parser_checkTailLinebreak(v_prev_4146_);
if (v___x_4149_ == 0)
{
lean_dec(v_pos_4147_);
return v_c_4148_;
}
else
{
lean_object* v_prec_4150_; lean_object* v_quotDepth_4151_; uint8_t v_suppressInsideQuot_4152_; lean_object* v_forbiddenTks_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4161_; 
v_prec_4150_ = lean_ctor_get(v_c_4148_, 0);
v_quotDepth_4151_ = lean_ctor_get(v_c_4148_, 1);
v_suppressInsideQuot_4152_ = lean_ctor_get_uint8(v_c_4148_, sizeof(void*)*4);
v_forbiddenTks_4153_ = lean_ctor_get(v_c_4148_, 3);
v_isSharedCheck_4161_ = !lean_is_exclusive(v_c_4148_);
if (v_isSharedCheck_4161_ == 0)
{
lean_object* v_unused_4162_; 
v_unused_4162_ = lean_ctor_get(v_c_4148_, 2);
lean_dec(v_unused_4162_);
v___x_4155_ = v_c_4148_;
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_forbiddenTks_4153_);
lean_inc(v_quotDepth_4151_);
lean_inc(v_prec_4150_);
lean_dec(v_c_4148_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4161_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4159_; 
v___x_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4157_, 0, v_pos_4147_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 2, v___x_4157_);
v___x_4159_ = v___x_4155_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_prec_4150_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_quotDepth_4151_);
lean_ctor_set(v_reuseFailAlloc_4160_, 2, v___x_4157_);
lean_ctor_set(v_reuseFailAlloc_4160_, 3, v_forbiddenTks_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4160_, sizeof(void*)*4, v_suppressInsideQuot_4152_);
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
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed(lean_object* v_prev_4163_, lean_object* v_pos_4164_, lean_object* v_c_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Parser_withPositionAfterLinebreak___lam__0(v_prev_4163_, v_pos_4164_, v_c_4165_);
lean_dec(v_prev_4163_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak___lam__1(lean_object* v_fn_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_){
_start:
{
lean_object* v_stxStack_4170_; lean_object* v_pos_4171_; lean_object* v_prev_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; 
v_stxStack_4170_ = lean_ctor_get(v___y_4169_, 0);
v_pos_4171_ = lean_ctor_get(v___y_4169_, 2);
v_prev_4172_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_4170_);
lean_inc(v_pos_4171_);
v___f_4173_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4173_, 0, v_prev_4172_);
lean_closure_set(v___f_4173_, 1, v_pos_4171_);
v___x_4174_ = l_Lean_Parser_adaptCacheableContextFn(v___f_4173_, v_fn_4167_, v___y_4168_, v___y_4169_);
return v___x_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withPositionAfterLinebreak(lean_object* v_p_4175_){
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
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_Parser_withPositionAfterLinebreak___lam__1), 3, 1);
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
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition___lam__0(lean_object* v_x_4186_){
_start:
{
lean_object* v_prec_4187_; lean_object* v_quotDepth_4188_; uint8_t v_suppressInsideQuot_4189_; lean_object* v_forbiddenTks_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4198_; 
v_prec_4187_ = lean_ctor_get(v_x_4186_, 0);
v_quotDepth_4188_ = lean_ctor_get(v_x_4186_, 1);
v_suppressInsideQuot_4189_ = lean_ctor_get_uint8(v_x_4186_, sizeof(void*)*4);
v_forbiddenTks_4190_ = lean_ctor_get(v_x_4186_, 3);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_x_4186_);
if (v_isSharedCheck_4198_ == 0)
{
lean_object* v_unused_4199_; 
v_unused_4199_ = lean_ctor_get(v_x_4186_, 2);
lean_dec(v_unused_4199_);
v___x_4192_ = v_x_4186_;
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_forbiddenTks_4190_);
lean_inc(v_quotDepth_4188_);
lean_inc(v_prec_4187_);
lean_dec(v_x_4186_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4198_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
v___x_4194_ = lean_box(0);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 2, v___x_4194_);
v___x_4196_ = v___x_4192_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_prec_4187_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_quotDepth_4188_);
lean_ctor_set(v_reuseFailAlloc_4197_, 2, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4197_, 3, v_forbiddenTks_4190_);
lean_ctor_set_uint8(v_reuseFailAlloc_4197_, sizeof(void*)*4, v_suppressInsideQuot_4189_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutPosition(lean_object* v_p_4201_){
_start:
{
lean_object* v___f_4202_; lean_object* v___x_4203_; 
v___f_4202_ = ((lean_object*)(l_Lean_Parser_withoutPosition___closed__0));
v___x_4203_ = l_Lean_Parser_adaptCacheableContext(v___f_4202_, v_p_4201_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1(){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v___x_4211_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__1));
v___x_4212_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___closed__2));
v___x_4213_ = l_Lean_addBuiltinDocString(v___x_4211_, v___x_4212_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1___boxed(lean_object* v_a_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutPosition___regBuiltin_Lean_Parser_withoutPosition_docString__1();
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden___lam__0(lean_object* v_tk_4216_, lean_object* v_c_4217_){
_start:
{
lean_object* v_prec_4218_; lean_object* v_quotDepth_4219_; uint8_t v_suppressInsideQuot_4220_; lean_object* v_savedPos_x3f_4221_; lean_object* v_forbiddenTks_4222_; uint8_t v___x_4223_; 
v_prec_4218_ = lean_ctor_get(v_c_4217_, 0);
v_quotDepth_4219_ = lean_ctor_get(v_c_4217_, 1);
v_suppressInsideQuot_4220_ = lean_ctor_get_uint8(v_c_4217_, sizeof(void*)*4);
v_savedPos_x3f_4221_ = lean_ctor_get(v_c_4217_, 2);
v_forbiddenTks_4222_ = lean_ctor_get(v_c_4217_, 3);
v___x_4223_ = l_Array_contains___at___00Lean_Parser_mkTokenAndFixPos_spec__0(v_forbiddenTks_4222_, v_tk_4216_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4231_; 
lean_inc_ref(v_forbiddenTks_4222_);
lean_inc(v_savedPos_x3f_4221_);
lean_inc(v_quotDepth_4219_);
lean_inc(v_prec_4218_);
v_isSharedCheck_4231_ = !lean_is_exclusive(v_c_4217_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; lean_object* v_unused_4233_; lean_object* v_unused_4234_; lean_object* v_unused_4235_; 
v_unused_4232_ = lean_ctor_get(v_c_4217_, 3);
lean_dec(v_unused_4232_);
v_unused_4233_ = lean_ctor_get(v_c_4217_, 2);
lean_dec(v_unused_4233_);
v_unused_4234_ = lean_ctor_get(v_c_4217_, 1);
lean_dec(v_unused_4234_);
v_unused_4235_ = lean_ctor_get(v_c_4217_, 0);
lean_dec(v_unused_4235_);
v___x_4225_ = v_c_4217_;
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
else
{
lean_dec(v_c_4217_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4227_; lean_object* v___x_4229_; 
v___x_4227_ = lean_array_push(v_forbiddenTks_4222_, v_tk_4216_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 3, v___x_4227_);
v___x_4229_ = v___x_4225_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_prec_4218_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v_quotDepth_4219_);
lean_ctor_set(v_reuseFailAlloc_4230_, 2, v_savedPos_x3f_4221_);
lean_ctor_set(v_reuseFailAlloc_4230_, 3, v___x_4227_);
lean_ctor_set_uint8(v_reuseFailAlloc_4230_, sizeof(void*)*4, v_suppressInsideQuot_4220_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
else
{
lean_dec_ref(v_tk_4216_);
return v_c_4217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbidden(lean_object* v_tk_4236_, lean_object* v_p_4237_){
_start:
{
lean_object* v___f_4238_; lean_object* v___x_4239_; 
v___f_4238_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbidden___lam__0), 2, 1);
lean_closure_set(v___f_4238_, 0, v_tk_4236_);
v___x_4239_ = l_Lean_Parser_adaptCacheableContext(v___f_4238_, v_p_4237_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1(){
_start:
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v___x_4247_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__1));
v___x_4248_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___closed__2));
v___x_4249_ = l_Lean_addBuiltinDocString(v___x_4247_, v___x_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1___boxed(lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbidden___regBuiltin_Lean_Parser_withForbidden_docString__1();
return v_res_4251_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(lean_object* v_a_4252_, lean_object* v_as_4253_, size_t v_i_4254_, size_t v_stop_4255_){
_start:
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_usize_dec_eq(v_i_4254_, v_stop_4255_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4257_; uint8_t v___x_4258_; 
v___x_4257_ = lean_array_uget_borrowed(v_as_4253_, v_i_4254_);
v___x_4258_ = lean_string_dec_eq(v___x_4257_, v_a_4252_);
if (v___x_4258_ == 0)
{
size_t v___x_4259_; size_t v___x_4260_; 
v___x_4259_ = ((size_t)1ULL);
v___x_4260_ = lean_usize_add(v_i_4254_, v___x_4259_);
v_i_4254_ = v___x_4260_;
goto _start;
}
else
{
return v___x_4258_;
}
}
else
{
uint8_t v___x_4262_; 
v___x_4262_ = 0;
return v___x_4262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0___boxed(lean_object* v_a_4263_, lean_object* v_as_4264_, lean_object* v_i_4265_, lean_object* v_stop_4266_){
_start:
{
size_t v_i_boxed_4267_; size_t v_stop_boxed_4268_; uint8_t v_res_4269_; lean_object* v_r_4270_; 
v_i_boxed_4267_ = lean_unbox_usize(v_i_4265_);
lean_dec(v_i_4265_);
v_stop_boxed_4268_ = lean_unbox_usize(v_stop_4266_);
lean_dec(v_stop_4266_);
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4263_, v_as_4264_, v_i_boxed_4267_, v_stop_boxed_4268_);
lean_dec_ref(v_as_4264_);
lean_dec_ref(v_a_4263_);
v_r_4270_ = lean_box(v_res_4269_);
return v_r_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(lean_object* v_size_4271_, lean_object* v_as_4272_, size_t v_sz_4273_, size_t v_i_4274_, lean_object* v_b_4275_){
_start:
{
lean_object* v_a_4277_; uint8_t v___x_4281_; 
v___x_4281_ = lean_usize_dec_lt(v_i_4274_, v_sz_4273_);
if (v___x_4281_ == 0)
{
lean_dec(v_size_4271_);
return v_b_4275_;
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4285_; lean_object* v___y_4287_; uint8_t v___x_4292_; 
v_a_4282_ = lean_array_uget_borrowed(v_as_4272_, v_i_4274_);
v___x_4285_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_nat_dec_lt(v___x_4285_, v_size_4271_);
if (v___x_4292_ == 0)
{
goto v___jp_4283_;
}
else
{
lean_object* v___x_4293_; uint8_t v___x_4294_; 
v___x_4293_ = lean_array_get_size(v_b_4275_);
v___x_4294_ = lean_nat_dec_le(v_size_4271_, v___x_4293_);
if (v___x_4294_ == 0)
{
v___y_4287_ = v___x_4293_;
goto v___jp_4286_;
}
else
{
lean_inc(v_size_4271_);
v___y_4287_ = v_size_4271_;
goto v___jp_4286_;
}
}
v___jp_4283_:
{
lean_object* v___x_4284_; 
lean_inc(v_a_4282_);
v___x_4284_ = lean_array_push(v_b_4275_, v_a_4282_);
v_a_4277_ = v___x_4284_;
goto v___jp_4276_;
}
v___jp_4286_:
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_nat_dec_lt(v___x_4285_, v___y_4287_);
if (v___x_4288_ == 0)
{
lean_dec(v___y_4287_);
goto v___jp_4283_;
}
else
{
size_t v___x_4289_; size_t v___x_4290_; uint8_t v___x_4291_; 
v___x_4289_ = ((size_t)0ULL);
v___x_4290_ = lean_usize_of_nat(v___y_4287_);
lean_dec(v___y_4287_);
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__0(v_a_4282_, v_b_4275_, v___x_4289_, v___x_4290_);
if (v___x_4291_ == 0)
{
goto v___jp_4283_;
}
else
{
v_a_4277_ = v_b_4275_;
goto v___jp_4276_;
}
}
}
}
v___jp_4276_:
{
size_t v___x_4278_; size_t v___x_4279_; 
v___x_4278_ = ((size_t)1ULL);
v___x_4279_ = lean_usize_add(v_i_4274_, v___x_4278_);
v_i_4274_ = v___x_4279_;
v_b_4275_ = v_a_4277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1___boxed(lean_object* v_size_4295_, lean_object* v_as_4296_, lean_object* v_sz_4297_, lean_object* v_i_4298_, lean_object* v_b_4299_){
_start:
{
size_t v_sz_boxed_4300_; size_t v_i_boxed_4301_; lean_object* v_res_4302_; 
v_sz_boxed_4300_ = lean_unbox_usize(v_sz_4297_);
lean_dec(v_sz_4297_);
v_i_boxed_4301_ = lean_unbox_usize(v_i_4298_);
lean_dec(v_i_4298_);
v_res_4302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4295_, v_as_4296_, v_sz_boxed_4300_, v_i_boxed_4301_, v_b_4299_);
lean_dec_ref(v_as_4296_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(lean_object* v_init_4303_, lean_object* v_tks_4304_){
_start:
{
lean_object* v_size_4305_; size_t v_sz_4306_; size_t v___x_4307_; lean_object* v___x_4308_; 
v_size_4305_ = lean_array_get_size(v_init_4303_);
v_sz_4306_ = lean_array_size(v_tks_4304_);
v___x_4307_ = ((size_t)0ULL);
v___x_4308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks_spec__1(v_size_4305_, v_tks_4304_, v_sz_4306_, v___x_4307_, v_init_4303_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks___boxed(lean_object* v_init_4309_, lean_object* v_tks_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_init_4309_, v_tks_4310_);
lean_dec_ref(v_tks_4310_);
return v_res_4311_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__8(void){
_start:
{
lean_object* v___x_4333_; lean_object* v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__6));
v___x_4334_ = l_Lean_mkAtom(v___x_4333_);
return v___x_4334_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__9(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4335_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__8, &l_Lean_Parser_withForbiddens___auto__1___closed__8_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__8);
v___x_4336_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4337_ = lean_array_push(v___x_4336_, v___x_4335_);
return v___x_4337_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__13(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_4349_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4350_ = lean_array_push(v___x_4349_, v___x_4348_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__14(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4351_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__13, &l_Lean_Parser_withForbiddens___auto__1___closed__13_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__13);
v___x_4352_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__11));
v___x_4353_ = lean_box(2);
v___x_4354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
lean_ctor_set(v___x_4354_, 1, v___x_4352_);
lean_ctor_set(v___x_4354_, 2, v___x_4351_);
return v___x_4354_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__15(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4355_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__14, &l_Lean_Parser_withForbiddens___auto__1___closed__14_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__14);
v___x_4356_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__9, &l_Lean_Parser_withForbiddens___auto__1___closed__9_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__9);
v___x_4357_ = lean_array_push(v___x_4356_, v___x_4355_);
return v___x_4357_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4358_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__15, &l_Lean_Parser_withForbiddens___auto__1___closed__15_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__15);
v___x_4359_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__7));
v___x_4360_ = lean_box(2);
v___x_4361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4360_);
lean_ctor_set(v___x_4361_, 1, v___x_4359_);
lean_ctor_set(v___x_4361_, 2, v___x_4358_);
return v___x_4361_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__16, &l_Lean_Parser_withForbiddens___auto__1___closed__16_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__16);
v___x_4363_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4364_ = lean_array_push(v___x_4363_, v___x_4362_);
return v___x_4364_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4365_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__17, &l_Lean_Parser_withForbiddens___auto__1___closed__17_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__17);
v___x_4366_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_4367_ = lean_box(2);
v___x_4368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
lean_ctor_set(v___x_4368_, 1, v___x_4366_);
lean_ctor_set(v___x_4368_, 2, v___x_4365_);
return v___x_4368_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__19(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__18, &l_Lean_Parser_withForbiddens___auto__1___closed__18_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__18);
v___x_4370_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4371_ = lean_array_push(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__20(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4372_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__19, &l_Lean_Parser_withForbiddens___auto__1___closed__19_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__19);
v___x_4373_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__5));
v___x_4374_ = lean_box(2);
v___x_4375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
lean_ctor_set(v___x_4375_, 1, v___x_4373_);
lean_ctor_set(v___x_4375_, 2, v___x_4372_);
return v___x_4375_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__21(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4376_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__20, &l_Lean_Parser_withForbiddens___auto__1___closed__20_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__20);
v___x_4377_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__3));
v___x_4378_ = lean_array_push(v___x_4377_, v___x_4376_);
return v___x_4378_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1___closed__22(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4379_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__21, &l_Lean_Parser_withForbiddens___auto__1___closed__21_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__21);
v___x_4380_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__2));
v___x_4381_ = lean_box(2);
v___x_4382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4382_, 0, v___x_4381_);
lean_ctor_set(v___x_4382_, 1, v___x_4380_);
lean_ctor_set(v___x_4382_, 2, v___x_4379_);
return v___x_4382_;
}
}
static lean_object* _init_l_Lean_Parser_withForbiddens___auto__1(void){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = lean_obj_once(&l_Lean_Parser_withForbiddens___auto__1___closed__22, &l_Lean_Parser_withForbiddens___auto__1___closed__22_once, _init_l_Lean_Parser_withForbiddens___auto__1___closed__22);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg___lam__0(lean_object* v_tks_4384_, lean_object* v_c_4385_){
_start:
{
lean_object* v_prec_4386_; lean_object* v_quotDepth_4387_; uint8_t v_suppressInsideQuot_4388_; lean_object* v_savedPos_x3f_4389_; lean_object* v_forbiddenTks_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4404_; 
v_prec_4386_ = lean_ctor_get(v_c_4385_, 0);
v_quotDepth_4387_ = lean_ctor_get(v_c_4385_, 1);
v_suppressInsideQuot_4388_ = lean_ctor_get_uint8(v_c_4385_, sizeof(void*)*4);
v_savedPos_x3f_4389_ = lean_ctor_get(v_c_4385_, 2);
v_forbiddenTks_4390_ = lean_ctor_get(v_c_4385_, 3);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_c_4385_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4392_ = v_c_4385_;
v_isShared_4393_ = v_isSharedCheck_4404_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_forbiddenTks_4390_);
lean_inc(v_savedPos_x3f_4389_);
lean_inc(v_quotDepth_4387_);
lean_inc(v_prec_4386_);
lean_dec(v_c_4385_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4404_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; 
v___x_4394_ = lean_array_get_size(v_forbiddenTks_4390_);
v___x_4395_ = lean_unsigned_to_nat(0u);
v___x_4396_ = lean_nat_dec_eq(v___x_4394_, v___x_4395_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; lean_object* v___x_4399_; 
v___x_4397_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mergeForbiddenTks(v_forbiddenTks_4390_, v_tks_4384_);
lean_dec_ref(v_tks_4384_);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 3, v___x_4397_);
v___x_4399_ = v___x_4392_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_prec_4386_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v_quotDepth_4387_);
lean_ctor_set(v_reuseFailAlloc_4400_, 2, v_savedPos_x3f_4389_);
lean_ctor_set(v_reuseFailAlloc_4400_, 3, v___x_4397_);
lean_ctor_set_uint8(v_reuseFailAlloc_4400_, sizeof(void*)*4, v_suppressInsideQuot_4388_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
else
{
lean_object* v___x_4402_; 
lean_dec_ref(v_forbiddenTks_4390_);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 3, v_tks_4384_);
v___x_4402_ = v___x_4392_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_prec_4386_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_quotDepth_4387_);
lean_ctor_set(v_reuseFailAlloc_4403_, 2, v_savedPos_x3f_4389_);
lean_ctor_set(v_reuseFailAlloc_4403_, 3, v_tks_4384_);
lean_ctor_set_uint8(v_reuseFailAlloc_4403_, sizeof(void*)*4, v_suppressInsideQuot_4388_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens___redArg(lean_object* v_tks_4405_, lean_object* v_p_4406_){
_start:
{
lean_object* v___f_4407_; lean_object* v___x_4408_; 
v___f_4407_ = lean_alloc_closure((void*)(l_Lean_Parser_withForbiddens___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4407_, 0, v_tks_4405_);
v___x_4408_ = l_Lean_Parser_adaptCacheableContext(v___f_4407_, v_p_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withForbiddens(lean_object* v_tks_4409_, lean_object* v_p_4410_, lean_object* v___h_4411_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Lean_Parser_withForbiddens___redArg(v_tks_4409_, v_p_4410_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1(){
_start:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4420_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__1));
v___x_4421_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___closed__2));
v___x_4422_ = l_Lean_addBuiltinDocString(v___x_4420_, v___x_4421_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1___boxed(lean_object* v_a_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withForbiddens___regBuiltin_Lean_Parser_withForbiddens_docString__1();
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden___lam__0(lean_object* v_x_4427_){
_start:
{
lean_object* v_prec_4428_; lean_object* v_quotDepth_4429_; uint8_t v_suppressInsideQuot_4430_; lean_object* v_savedPos_x3f_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4439_; 
v_prec_4428_ = lean_ctor_get(v_x_4427_, 0);
v_quotDepth_4429_ = lean_ctor_get(v_x_4427_, 1);
v_suppressInsideQuot_4430_ = lean_ctor_get_uint8(v_x_4427_, sizeof(void*)*4);
v_savedPos_x3f_4431_ = lean_ctor_get(v_x_4427_, 2);
v_isSharedCheck_4439_ = !lean_is_exclusive(v_x_4427_);
if (v_isSharedCheck_4439_ == 0)
{
lean_object* v_unused_4440_; 
v_unused_4440_ = lean_ctor_get(v_x_4427_, 3);
lean_dec(v_unused_4440_);
v___x_4433_ = v_x_4427_;
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_savedPos_x3f_4431_);
lean_inc(v_quotDepth_4429_);
lean_inc(v_prec_4428_);
lean_dec(v_x_4427_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4439_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4435_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___lam__0___closed__0));
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 3, v___x_4435_);
v___x_4437_ = v___x_4433_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_prec_4428_);
lean_ctor_set(v_reuseFailAlloc_4438_, 1, v_quotDepth_4429_);
lean_ctor_set(v_reuseFailAlloc_4438_, 2, v_savedPos_x3f_4431_);
lean_ctor_set(v_reuseFailAlloc_4438_, 3, v___x_4435_);
lean_ctor_set_uint8(v_reuseFailAlloc_4438_, sizeof(void*)*4, v_suppressInsideQuot_4430_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutForbidden(lean_object* v_p_4442_){
_start:
{
lean_object* v___f_4443_; lean_object* v___x_4444_; 
v___f_4443_ = ((lean_object*)(l_Lean_Parser_withoutForbidden___closed__0));
v___x_4444_ = l_Lean_Parser_adaptCacheableContext(v___f_4443_, v_p_4442_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1(){
_start:
{
lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4452_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__1));
v___x_4453_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___closed__2));
v___x_4454_ = l_Lean_addBuiltinDocString(v___x_4452_, v___x_4453_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1___boxed(lean_object* v_a_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withoutForbidden___regBuiltin_Lean_Parser_withoutForbidden_docString__1();
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn(lean_object* v_c_4458_, lean_object* v_s_4459_){
_start:
{
lean_object* v_pos_4460_; lean_object* v_toInputContext_4461_; uint8_t v___x_4462_; 
v_pos_4460_ = lean_ctor_get(v_s_4459_, 2);
v_toInputContext_4461_ = lean_ctor_get(v_c_4458_, 0);
v___x_4462_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_4461_, v_pos_4460_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = ((lean_object*)(l_Lean_Parser_eoiFn___closed__0));
v___x_4464_ = l_Lean_Parser_ParserState_mkError(v_s_4459_, v___x_4463_);
return v___x_4464_;
}
else
{
return v_s_4459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_eoiFn___boxed(lean_object* v_c_4465_, lean_object* v_s_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l_Lean_Parser_eoiFn(v_c_4465_, v_s_4466_);
lean_dec_ref(v_c_4465_);
return v_res_4467_;
}
}
static lean_object* _init_l_Lean_Parser_eoi___closed__0(void){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4468_ = lean_alloc_closure((void*)(l_Lean_Parser_eoiFn___boxed), 2, 0);
v___x_4469_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
lean_ctor_set(v___x_4470_, 1, v___x_4468_);
return v___x_4470_;
}
}
static lean_object* _init_l_Lean_Parser_eoi(void){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = lean_obj_once(&l_Lean_Parser_eoi___closed__0, &l_Lean_Parser_eoi___closed__0_once, _init_l_Lean_Parser_eoi___closed__0);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(lean_object* v_k_4472_, lean_object* v_v_4473_, lean_object* v_t_4474_){
_start:
{
if (lean_obj_tag(v_t_4474_) == 0)
{
lean_object* v_size_4475_; lean_object* v_k_4476_; lean_object* v_v_4477_; lean_object* v_l_4478_; lean_object* v_r_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4759_; 
v_size_4475_ = lean_ctor_get(v_t_4474_, 0);
v_k_4476_ = lean_ctor_get(v_t_4474_, 1);
v_v_4477_ = lean_ctor_get(v_t_4474_, 2);
v_l_4478_ = lean_ctor_get(v_t_4474_, 3);
v_r_4479_ = lean_ctor_get(v_t_4474_, 4);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_t_4474_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4481_ = v_t_4474_;
v_isShared_4482_ = v_isSharedCheck_4759_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_r_4479_);
lean_inc(v_l_4478_);
lean_inc(v_v_4477_);
lean_inc(v_k_4476_);
lean_inc(v_size_4475_);
lean_dec(v_t_4474_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4759_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
uint8_t v___x_4483_; 
v___x_4483_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4472_, v_k_4476_);
switch(v___x_4483_)
{
case 0:
{
lean_object* v_impl_4484_; lean_object* v___x_4485_; 
lean_dec(v_size_4475_);
v_impl_4484_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4472_, v_v_4473_, v_l_4478_);
v___x_4485_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4479_) == 0)
{
lean_object* v_size_4486_; lean_object* v_size_4487_; lean_object* v_k_4488_; lean_object* v_v_4489_; lean_object* v_l_4490_; lean_object* v_r_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; uint8_t v___x_4494_; 
v_size_4486_ = lean_ctor_get(v_r_4479_, 0);
v_size_4487_ = lean_ctor_get(v_impl_4484_, 0);
v_k_4488_ = lean_ctor_get(v_impl_4484_, 1);
v_v_4489_ = lean_ctor_get(v_impl_4484_, 2);
v_l_4490_ = lean_ctor_get(v_impl_4484_, 3);
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
v___x_4495_ = lean_nat_add(v___x_4485_, v_size_4487_);
v___x_4496_ = lean_nat_add(v___x_4495_, v_size_4486_);
lean_dec(v___x_4495_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 3, v_impl_4484_);
lean_ctor_set(v___x_4481_, 0, v___x_4496_);
v___x_4498_ = v___x_4481_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
lean_ctor_set(v_reuseFailAlloc_4499_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4499_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4499_, 3, v_impl_4484_);
lean_ctor_set(v_reuseFailAlloc_4499_, 4, v_r_4479_);
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
lean_object* v___x_4501_; uint8_t v_isShared_4502_; uint8_t v_isSharedCheck_4565_; 
lean_inc(v_l_4490_);
lean_inc(v_v_4489_);
lean_inc(v_k_4488_);
lean_inc(v_size_4487_);
v_isSharedCheck_4565_ = !lean_is_exclusive(v_impl_4484_);
if (v_isSharedCheck_4565_ == 0)
{
lean_object* v_unused_4566_; lean_object* v_unused_4567_; lean_object* v_unused_4568_; lean_object* v_unused_4569_; lean_object* v_unused_4570_; 
v_unused_4566_ = lean_ctor_get(v_impl_4484_, 4);
lean_dec(v_unused_4566_);
v_unused_4567_ = lean_ctor_get(v_impl_4484_, 3);
lean_dec(v_unused_4567_);
v_unused_4568_ = lean_ctor_get(v_impl_4484_, 2);
lean_dec(v_unused_4568_);
v_unused_4569_ = lean_ctor_get(v_impl_4484_, 1);
lean_dec(v_unused_4569_);
v_unused_4570_ = lean_ctor_get(v_impl_4484_, 0);
lean_dec(v_unused_4570_);
v___x_4501_ = v_impl_4484_;
v_isShared_4502_ = v_isSharedCheck_4565_;
goto v_resetjp_4500_;
}
else
{
lean_dec(v_impl_4484_);
v___x_4501_ = lean_box(0);
v_isShared_4502_ = v_isSharedCheck_4565_;
goto v_resetjp_4500_;
}
v_resetjp_4500_:
{
lean_object* v_size_4503_; lean_object* v_size_4504_; lean_object* v_k_4505_; lean_object* v_v_4506_; lean_object* v_l_4507_; lean_object* v_r_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; uint8_t v___x_4511_; 
v_size_4503_ = lean_ctor_get(v_l_4490_, 0);
v_size_4504_ = lean_ctor_get(v_r_4491_, 0);
v_k_4505_ = lean_ctor_get(v_r_4491_, 1);
v_v_4506_ = lean_ctor_get(v_r_4491_, 2);
v_l_4507_ = lean_ctor_get(v_r_4491_, 3);
v_r_4508_ = lean_ctor_get(v_r_4491_, 4);
v___x_4509_ = lean_unsigned_to_nat(2u);
v___x_4510_ = lean_nat_mul(v___x_4509_, v_size_4503_);
v___x_4511_ = lean_nat_dec_lt(v_size_4504_, v___x_4510_);
lean_dec(v___x_4510_);
if (v___x_4511_ == 0)
{
lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4540_; 
lean_inc(v_r_4508_);
lean_inc(v_l_4507_);
lean_inc(v_v_4506_);
lean_inc(v_k_4505_);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_r_4491_);
if (v_isSharedCheck_4540_ == 0)
{
lean_object* v_unused_4541_; lean_object* v_unused_4542_; lean_object* v_unused_4543_; lean_object* v_unused_4544_; lean_object* v_unused_4545_; 
v_unused_4541_ = lean_ctor_get(v_r_4491_, 4);
lean_dec(v_unused_4541_);
v_unused_4542_ = lean_ctor_get(v_r_4491_, 3);
lean_dec(v_unused_4542_);
v_unused_4543_ = lean_ctor_get(v_r_4491_, 2);
lean_dec(v_unused_4543_);
v_unused_4544_ = lean_ctor_get(v_r_4491_, 1);
lean_dec(v_unused_4544_);
v_unused_4545_ = lean_ctor_get(v_r_4491_, 0);
lean_dec(v_unused_4545_);
v___x_4513_ = v_r_4491_;
v_isShared_4514_ = v_isSharedCheck_4540_;
goto v_resetjp_4512_;
}
else
{
lean_dec(v_r_4491_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4540_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___x_4528_; lean_object* v___y_4530_; 
v___x_4515_ = lean_nat_add(v___x_4485_, v_size_4487_);
lean_dec(v_size_4487_);
v___x_4516_ = lean_nat_add(v___x_4515_, v_size_4486_);
lean_dec(v___x_4515_);
v___x_4528_ = lean_nat_add(v___x_4485_, v_size_4503_);
if (lean_obj_tag(v_l_4507_) == 0)
{
lean_object* v_size_4538_; 
v_size_4538_ = lean_ctor_get(v_l_4507_, 0);
lean_inc(v_size_4538_);
v___y_4530_ = v_size_4538_;
goto v___jp_4529_;
}
else
{
lean_object* v___x_4539_; 
v___x_4539_ = lean_unsigned_to_nat(0u);
v___y_4530_ = v___x_4539_;
goto v___jp_4529_;
}
v___jp_4517_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = lean_nat_add(v___y_4518_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec(v___y_4518_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 4, v_r_4479_);
lean_ctor_set(v___x_4513_, 3, v_r_4508_);
lean_ctor_set(v___x_4513_, 2, v_v_4477_);
lean_ctor_set(v___x_4513_, 1, v_k_4476_);
lean_ctor_set(v___x_4513_, 0, v___x_4521_);
v___x_4523_ = v___x_4513_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v___x_4521_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4527_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4527_, 3, v_r_4508_);
lean_ctor_set(v_reuseFailAlloc_4527_, 4, v_r_4479_);
v___x_4523_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4525_; 
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 4, v___x_4523_);
lean_ctor_set(v___x_4501_, 3, v___y_4519_);
lean_ctor_set(v___x_4501_, 2, v_v_4506_);
lean_ctor_set(v___x_4501_, 1, v_k_4505_);
lean_ctor_set(v___x_4501_, 0, v___x_4516_);
v___x_4525_ = v___x_4501_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4516_);
lean_ctor_set(v_reuseFailAlloc_4526_, 1, v_k_4505_);
lean_ctor_set(v_reuseFailAlloc_4526_, 2, v_v_4506_);
lean_ctor_set(v_reuseFailAlloc_4526_, 3, v___y_4519_);
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
v___jp_4529_:
{
lean_object* v___x_4531_; lean_object* v___x_4533_; 
v___x_4531_ = lean_nat_add(v___x_4528_, v___y_4530_);
lean_dec(v___y_4530_);
lean_dec(v___x_4528_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v_l_4507_);
lean_ctor_set(v___x_4481_, 3, v_l_4490_);
lean_ctor_set(v___x_4481_, 2, v_v_4489_);
lean_ctor_set(v___x_4481_, 1, v_k_4488_);
lean_ctor_set(v___x_4481_, 0, v___x_4531_);
v___x_4533_ = v___x_4481_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4531_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_k_4488_);
lean_ctor_set(v_reuseFailAlloc_4537_, 2, v_v_4489_);
lean_ctor_set(v_reuseFailAlloc_4537_, 3, v_l_4490_);
lean_ctor_set(v_reuseFailAlloc_4537_, 4, v_l_4507_);
v___x_4533_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; 
v___x_4534_ = lean_nat_add(v___x_4485_, v_size_4486_);
if (lean_obj_tag(v_r_4508_) == 0)
{
lean_object* v_size_4535_; 
v_size_4535_ = lean_ctor_get(v_r_4508_, 0);
lean_inc(v_size_4535_);
v___y_4518_ = v___x_4534_;
v___y_4519_ = v___x_4533_;
v___y_4520_ = v_size_4535_;
goto v___jp_4517_;
}
else
{
lean_object* v___x_4536_; 
v___x_4536_ = lean_unsigned_to_nat(0u);
v___y_4518_ = v___x_4534_;
v___y_4519_ = v___x_4533_;
v___y_4520_ = v___x_4536_;
goto v___jp_4517_;
}
}
}
}
}
else
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4551_; 
lean_del_object(v___x_4481_);
v___x_4546_ = lean_nat_add(v___x_4485_, v_size_4487_);
lean_dec(v_size_4487_);
v___x_4547_ = lean_nat_add(v___x_4546_, v_size_4486_);
lean_dec(v___x_4546_);
v___x_4548_ = lean_nat_add(v___x_4485_, v_size_4486_);
v___x_4549_ = lean_nat_add(v___x_4548_, v_size_4504_);
lean_dec(v___x_4548_);
lean_inc_ref(v_r_4479_);
if (v_isShared_4502_ == 0)
{
lean_ctor_set(v___x_4501_, 4, v_r_4479_);
lean_ctor_set(v___x_4501_, 3, v_r_4491_);
lean_ctor_set(v___x_4501_, 2, v_v_4477_);
lean_ctor_set(v___x_4501_, 1, v_k_4476_);
lean_ctor_set(v___x_4501_, 0, v___x_4549_);
v___x_4551_ = v___x_4501_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4549_);
lean_ctor_set(v_reuseFailAlloc_4564_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4564_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4564_, 3, v_r_4491_);
lean_ctor_set(v_reuseFailAlloc_4564_, 4, v_r_4479_);
v___x_4551_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
v_isSharedCheck_4558_ = !lean_is_exclusive(v_r_4479_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; lean_object* v_unused_4560_; lean_object* v_unused_4561_; lean_object* v_unused_4562_; lean_object* v_unused_4563_; 
v_unused_4559_ = lean_ctor_get(v_r_4479_, 4);
lean_dec(v_unused_4559_);
v_unused_4560_ = lean_ctor_get(v_r_4479_, 3);
lean_dec(v_unused_4560_);
v_unused_4561_ = lean_ctor_get(v_r_4479_, 2);
lean_dec(v_unused_4561_);
v_unused_4562_ = lean_ctor_get(v_r_4479_, 1);
lean_dec(v_unused_4562_);
v_unused_4563_ = lean_ctor_get(v_r_4479_, 0);
lean_dec(v_unused_4563_);
v___x_4553_ = v_r_4479_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_dec(v_r_4479_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 4, v___x_4551_);
lean_ctor_set(v___x_4553_, 3, v_l_4490_);
lean_ctor_set(v___x_4553_, 2, v_v_4489_);
lean_ctor_set(v___x_4553_, 1, v_k_4488_);
lean_ctor_set(v___x_4553_, 0, v___x_4547_);
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4547_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_k_4488_);
lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_v_4489_);
lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_l_4490_);
lean_ctor_set(v_reuseFailAlloc_4557_, 4, v___x_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4571_; 
v_l_4571_ = lean_ctor_get(v_impl_4484_, 3);
if (lean_obj_tag(v_l_4571_) == 0)
{
lean_object* v_r_4572_; lean_object* v_k_4573_; lean_object* v_v_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4585_; 
lean_inc_ref(v_l_4571_);
v_r_4572_ = lean_ctor_get(v_impl_4484_, 4);
v_k_4573_ = lean_ctor_get(v_impl_4484_, 1);
v_v_4574_ = lean_ctor_get(v_impl_4484_, 2);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_impl_4484_);
if (v_isSharedCheck_4585_ == 0)
{
lean_object* v_unused_4586_; lean_object* v_unused_4587_; 
v_unused_4586_ = lean_ctor_get(v_impl_4484_, 3);
lean_dec(v_unused_4586_);
v_unused_4587_ = lean_ctor_get(v_impl_4484_, 0);
lean_dec(v_unused_4587_);
v___x_4576_ = v_impl_4484_;
v_isShared_4577_ = v_isSharedCheck_4585_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_r_4572_);
lean_inc(v_v_4574_);
lean_inc(v_k_4573_);
lean_dec(v_impl_4484_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4585_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4578_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4572_);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 3, v_r_4572_);
lean_ctor_set(v___x_4576_, 2, v_v_4477_);
lean_ctor_set(v___x_4576_, 1, v_k_4476_);
lean_ctor_set(v___x_4576_, 0, v___x_4485_);
v___x_4580_ = v___x_4576_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4584_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4584_, 3, v_r_4572_);
lean_ctor_set(v_reuseFailAlloc_4584_, 4, v_r_4572_);
v___x_4580_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4582_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v___x_4580_);
lean_ctor_set(v___x_4481_, 3, v_l_4571_);
lean_ctor_set(v___x_4481_, 2, v_v_4574_);
lean_ctor_set(v___x_4481_, 1, v_k_4573_);
lean_ctor_set(v___x_4481_, 0, v___x_4578_);
v___x_4582_ = v___x_4481_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4583_, 1, v_k_4573_);
lean_ctor_set(v_reuseFailAlloc_4583_, 2, v_v_4574_);
lean_ctor_set(v_reuseFailAlloc_4583_, 3, v_l_4571_);
lean_ctor_set(v_reuseFailAlloc_4583_, 4, v___x_4580_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
else
{
lean_object* v_r_4588_; 
v_r_4588_ = lean_ctor_get(v_impl_4484_, 4);
lean_inc(v_r_4588_);
if (lean_obj_tag(v_r_4588_) == 0)
{
lean_object* v_k_4589_; lean_object* v_v_4590_; lean_object* v___x_4592_; uint8_t v_isShared_4593_; uint8_t v_isSharedCheck_4613_; 
lean_inc(v_l_4571_);
v_k_4589_ = lean_ctor_get(v_impl_4484_, 1);
v_v_4590_ = lean_ctor_get(v_impl_4484_, 2);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_impl_4484_);
if (v_isSharedCheck_4613_ == 0)
{
lean_object* v_unused_4614_; lean_object* v_unused_4615_; lean_object* v_unused_4616_; 
v_unused_4614_ = lean_ctor_get(v_impl_4484_, 4);
lean_dec(v_unused_4614_);
v_unused_4615_ = lean_ctor_get(v_impl_4484_, 3);
lean_dec(v_unused_4615_);
v_unused_4616_ = lean_ctor_get(v_impl_4484_, 0);
lean_dec(v_unused_4616_);
v___x_4592_ = v_impl_4484_;
v_isShared_4593_ = v_isSharedCheck_4613_;
goto v_resetjp_4591_;
}
else
{
lean_inc(v_v_4590_);
lean_inc(v_k_4589_);
lean_dec(v_impl_4484_);
v___x_4592_ = lean_box(0);
v_isShared_4593_ = v_isSharedCheck_4613_;
goto v_resetjp_4591_;
}
v_resetjp_4591_:
{
lean_object* v_k_4594_; lean_object* v_v_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4609_; 
v_k_4594_ = lean_ctor_get(v_r_4588_, 1);
v_v_4595_ = lean_ctor_get(v_r_4588_, 2);
v_isSharedCheck_4609_ = !lean_is_exclusive(v_r_4588_);
if (v_isSharedCheck_4609_ == 0)
{
lean_object* v_unused_4610_; lean_object* v_unused_4611_; lean_object* v_unused_4612_; 
v_unused_4610_ = lean_ctor_get(v_r_4588_, 4);
lean_dec(v_unused_4610_);
v_unused_4611_ = lean_ctor_get(v_r_4588_, 3);
lean_dec(v_unused_4611_);
v_unused_4612_ = lean_ctor_get(v_r_4588_, 0);
lean_dec(v_unused_4612_);
v___x_4597_ = v_r_4588_;
v_isShared_4598_ = v_isSharedCheck_4609_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_v_4595_);
lean_inc(v_k_4594_);
lean_dec(v_r_4588_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4609_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4599_; lean_object* v___x_4601_; 
v___x_4599_ = lean_unsigned_to_nat(3u);
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 4, v_l_4571_);
lean_ctor_set(v___x_4597_, 3, v_l_4571_);
lean_ctor_set(v___x_4597_, 2, v_v_4590_);
lean_ctor_set(v___x_4597_, 1, v_k_4589_);
lean_ctor_set(v___x_4597_, 0, v___x_4485_);
v___x_4601_ = v___x_4597_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v_k_4589_);
lean_ctor_set(v_reuseFailAlloc_4608_, 2, v_v_4590_);
lean_ctor_set(v_reuseFailAlloc_4608_, 3, v_l_4571_);
lean_ctor_set(v_reuseFailAlloc_4608_, 4, v_l_4571_);
v___x_4601_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
lean_object* v___x_4603_; 
if (v_isShared_4593_ == 0)
{
lean_ctor_set(v___x_4592_, 4, v_l_4571_);
lean_ctor_set(v___x_4592_, 2, v_v_4477_);
lean_ctor_set(v___x_4592_, 1, v_k_4476_);
lean_ctor_set(v___x_4592_, 0, v___x_4485_);
v___x_4603_ = v___x_4592_;
goto v_reusejp_4602_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4607_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4607_, 3, v_l_4571_);
lean_ctor_set(v_reuseFailAlloc_4607_, 4, v_l_4571_);
v___x_4603_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4602_;
}
v_reusejp_4602_:
{
lean_object* v___x_4605_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v___x_4603_);
lean_ctor_set(v___x_4481_, 3, v___x_4601_);
lean_ctor_set(v___x_4481_, 2, v_v_4595_);
lean_ctor_set(v___x_4481_, 1, v_k_4594_);
lean_ctor_set(v___x_4481_, 0, v___x_4599_);
v___x_4605_ = v___x_4481_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4606_, 1, v_k_4594_);
lean_ctor_set(v_reuseFailAlloc_4606_, 2, v_v_4595_);
lean_ctor_set(v_reuseFailAlloc_4606_, 3, v___x_4601_);
lean_ctor_set(v_reuseFailAlloc_4606_, 4, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
}
}
else
{
lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4617_ = lean_unsigned_to_nat(2u);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v_r_4588_);
lean_ctor_set(v___x_4481_, 3, v_impl_4484_);
lean_ctor_set(v___x_4481_, 0, v___x_4617_);
v___x_4619_ = v___x_4481_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4620_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4620_, 3, v_impl_4484_);
lean_ctor_set(v_reuseFailAlloc_4620_, 4, v_r_4588_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4622_; 
lean_dec(v_v_4477_);
lean_dec(v_k_4476_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 2, v_v_4473_);
lean_ctor_set(v___x_4481_, 1, v_k_4472_);
v___x_4622_ = v___x_4481_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_size_4475_);
lean_ctor_set(v_reuseFailAlloc_4623_, 1, v_k_4472_);
lean_ctor_set(v_reuseFailAlloc_4623_, 2, v_v_4473_);
lean_ctor_set(v_reuseFailAlloc_4623_, 3, v_l_4478_);
lean_ctor_set(v_reuseFailAlloc_4623_, 4, v_r_4479_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
default: 
{
lean_object* v_impl_4624_; lean_object* v___x_4625_; 
lean_dec(v_size_4475_);
v_impl_4624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4472_, v_v_4473_, v_r_4479_);
v___x_4625_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4478_) == 0)
{
lean_object* v_size_4626_; lean_object* v_size_4627_; lean_object* v_k_4628_; lean_object* v_v_4629_; lean_object* v_l_4630_; lean_object* v_r_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v_size_4626_ = lean_ctor_get(v_l_4478_, 0);
v_size_4627_ = lean_ctor_get(v_impl_4624_, 0);
v_k_4628_ = lean_ctor_get(v_impl_4624_, 1);
v_v_4629_ = lean_ctor_get(v_impl_4624_, 2);
v_l_4630_ = lean_ctor_get(v_impl_4624_, 3);
lean_inc(v_l_4630_);
v_r_4631_ = lean_ctor_get(v_impl_4624_, 4);
v___x_4632_ = lean_unsigned_to_nat(3u);
v___x_4633_ = lean_nat_mul(v___x_4632_, v_size_4626_);
v___x_4634_ = lean_nat_dec_lt(v___x_4633_, v_size_4627_);
lean_dec(v___x_4633_);
if (v___x_4634_ == 0)
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4638_; 
lean_dec(v_l_4630_);
v___x_4635_ = lean_nat_add(v___x_4625_, v_size_4626_);
v___x_4636_ = lean_nat_add(v___x_4635_, v_size_4627_);
lean_dec(v___x_4635_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v_impl_4624_);
lean_ctor_set(v___x_4481_, 0, v___x_4636_);
v___x_4638_ = v___x_4481_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v___x_4636_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_l_4478_);
lean_ctor_set(v_reuseFailAlloc_4639_, 4, v_impl_4624_);
v___x_4638_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
return v___x_4638_;
}
}
else
{
lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4703_; 
lean_inc(v_r_4631_);
lean_inc(v_v_4629_);
lean_inc(v_k_4628_);
lean_inc(v_size_4627_);
v_isSharedCheck_4703_ = !lean_is_exclusive(v_impl_4624_);
if (v_isSharedCheck_4703_ == 0)
{
lean_object* v_unused_4704_; lean_object* v_unused_4705_; lean_object* v_unused_4706_; lean_object* v_unused_4707_; lean_object* v_unused_4708_; 
v_unused_4704_ = lean_ctor_get(v_impl_4624_, 4);
lean_dec(v_unused_4704_);
v_unused_4705_ = lean_ctor_get(v_impl_4624_, 3);
lean_dec(v_unused_4705_);
v_unused_4706_ = lean_ctor_get(v_impl_4624_, 2);
lean_dec(v_unused_4706_);
v_unused_4707_ = lean_ctor_get(v_impl_4624_, 1);
lean_dec(v_unused_4707_);
v_unused_4708_ = lean_ctor_get(v_impl_4624_, 0);
lean_dec(v_unused_4708_);
v___x_4641_ = v_impl_4624_;
v_isShared_4642_ = v_isSharedCheck_4703_;
goto v_resetjp_4640_;
}
else
{
lean_dec(v_impl_4624_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4703_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v_size_4643_; lean_object* v_k_4644_; lean_object* v_v_4645_; lean_object* v_l_4646_; lean_object* v_r_4647_; lean_object* v_size_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v_size_4643_ = lean_ctor_get(v_l_4630_, 0);
v_k_4644_ = lean_ctor_get(v_l_4630_, 1);
v_v_4645_ = lean_ctor_get(v_l_4630_, 2);
v_l_4646_ = lean_ctor_get(v_l_4630_, 3);
v_r_4647_ = lean_ctor_get(v_l_4630_, 4);
v_size_4648_ = lean_ctor_get(v_r_4631_, 0);
v___x_4649_ = lean_unsigned_to_nat(2u);
v___x_4650_ = lean_nat_mul(v___x_4649_, v_size_4648_);
v___x_4651_ = lean_nat_dec_lt(v_size_4643_, v___x_4650_);
lean_dec(v___x_4650_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4679_; 
lean_inc(v_r_4647_);
lean_inc(v_l_4646_);
lean_inc(v_v_4645_);
lean_inc(v_k_4644_);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_l_4630_);
if (v_isSharedCheck_4679_ == 0)
{
lean_object* v_unused_4680_; lean_object* v_unused_4681_; lean_object* v_unused_4682_; lean_object* v_unused_4683_; lean_object* v_unused_4684_; 
v_unused_4680_ = lean_ctor_get(v_l_4630_, 4);
lean_dec(v_unused_4680_);
v_unused_4681_ = lean_ctor_get(v_l_4630_, 3);
lean_dec(v_unused_4681_);
v_unused_4682_ = lean_ctor_get(v_l_4630_, 2);
lean_dec(v_unused_4682_);
v_unused_4683_ = lean_ctor_get(v_l_4630_, 1);
lean_dec(v_unused_4683_);
v_unused_4684_ = lean_ctor_get(v_l_4630_, 0);
lean_dec(v_unused_4684_);
v___x_4653_ = v_l_4630_;
v_isShared_4654_ = v_isSharedCheck_4679_;
goto v_resetjp_4652_;
}
else
{
lean_dec(v_l_4630_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4679_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4669_; 
v___x_4655_ = lean_nat_add(v___x_4625_, v_size_4626_);
v___x_4656_ = lean_nat_add(v___x_4655_, v_size_4627_);
lean_dec(v_size_4627_);
if (lean_obj_tag(v_l_4646_) == 0)
{
lean_object* v_size_4677_; 
v_size_4677_ = lean_ctor_get(v_l_4646_, 0);
lean_inc(v_size_4677_);
v___y_4669_ = v_size_4677_;
goto v___jp_4668_;
}
else
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_unsigned_to_nat(0u);
v___y_4669_ = v___x_4678_;
goto v___jp_4668_;
}
v___jp_4657_:
{
lean_object* v___x_4661_; lean_object* v___x_4663_; 
v___x_4661_ = lean_nat_add(v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec(v___y_4659_);
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 4, v_r_4631_);
lean_ctor_set(v___x_4653_, 3, v_r_4647_);
lean_ctor_set(v___x_4653_, 2, v_v_4629_);
lean_ctor_set(v___x_4653_, 1, v_k_4628_);
lean_ctor_set(v___x_4653_, 0, v___x_4661_);
v___x_4663_ = v___x_4653_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v___x_4661_);
lean_ctor_set(v_reuseFailAlloc_4667_, 1, v_k_4628_);
lean_ctor_set(v_reuseFailAlloc_4667_, 2, v_v_4629_);
lean_ctor_set(v_reuseFailAlloc_4667_, 3, v_r_4647_);
lean_ctor_set(v_reuseFailAlloc_4667_, 4, v_r_4631_);
v___x_4663_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
lean_object* v___x_4665_; 
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 4, v___x_4663_);
lean_ctor_set(v___x_4641_, 3, v___y_4658_);
lean_ctor_set(v___x_4641_, 2, v_v_4645_);
lean_ctor_set(v___x_4641_, 1, v_k_4644_);
lean_ctor_set(v___x_4641_, 0, v___x_4656_);
v___x_4665_ = v___x_4641_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_k_4644_);
lean_ctor_set(v_reuseFailAlloc_4666_, 2, v_v_4645_);
lean_ctor_set(v_reuseFailAlloc_4666_, 3, v___y_4658_);
lean_ctor_set(v_reuseFailAlloc_4666_, 4, v___x_4663_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
v___jp_4668_:
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = lean_nat_add(v___x_4655_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec(v___x_4655_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v_l_4646_);
lean_ctor_set(v___x_4481_, 0, v___x_4670_);
v___x_4672_ = v___x_4481_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4676_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4676_, 3, v_l_4478_);
lean_ctor_set(v_reuseFailAlloc_4676_, 4, v_l_4646_);
v___x_4672_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; 
v___x_4673_ = lean_nat_add(v___x_4625_, v_size_4648_);
if (lean_obj_tag(v_r_4647_) == 0)
{
lean_object* v_size_4674_; 
v_size_4674_ = lean_ctor_get(v_r_4647_, 0);
lean_inc(v_size_4674_);
v___y_4658_ = v___x_4672_;
v___y_4659_ = v___x_4673_;
v___y_4660_ = v_size_4674_;
goto v___jp_4657_;
}
else
{
lean_object* v___x_4675_; 
v___x_4675_ = lean_unsigned_to_nat(0u);
v___y_4658_ = v___x_4672_;
v___y_4659_ = v___x_4673_;
v___y_4660_ = v___x_4675_;
goto v___jp_4657_;
}
}
}
}
}
else
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
lean_del_object(v___x_4481_);
v___x_4685_ = lean_nat_add(v___x_4625_, v_size_4626_);
v___x_4686_ = lean_nat_add(v___x_4685_, v_size_4627_);
lean_dec(v_size_4627_);
v___x_4687_ = lean_nat_add(v___x_4685_, v_size_4643_);
lean_dec(v___x_4685_);
lean_inc_ref(v_l_4478_);
if (v_isShared_4642_ == 0)
{
lean_ctor_set(v___x_4641_, 4, v_l_4630_);
lean_ctor_set(v___x_4641_, 3, v_l_4478_);
lean_ctor_set(v___x_4641_, 2, v_v_4477_);
lean_ctor_set(v___x_4641_, 1, v_k_4476_);
lean_ctor_set(v___x_4641_, 0, v___x_4687_);
v___x_4689_ = v___x_4641_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4687_);
lean_ctor_set(v_reuseFailAlloc_4702_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4702_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4702_, 3, v_l_4478_);
lean_ctor_set(v_reuseFailAlloc_4702_, 4, v_l_4630_);
v___x_4689_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4696_; 
v_isSharedCheck_4696_ = !lean_is_exclusive(v_l_4478_);
if (v_isSharedCheck_4696_ == 0)
{
lean_object* v_unused_4697_; lean_object* v_unused_4698_; lean_object* v_unused_4699_; lean_object* v_unused_4700_; lean_object* v_unused_4701_; 
v_unused_4697_ = lean_ctor_get(v_l_4478_, 4);
lean_dec(v_unused_4697_);
v_unused_4698_ = lean_ctor_get(v_l_4478_, 3);
lean_dec(v_unused_4698_);
v_unused_4699_ = lean_ctor_get(v_l_4478_, 2);
lean_dec(v_unused_4699_);
v_unused_4700_ = lean_ctor_get(v_l_4478_, 1);
lean_dec(v_unused_4700_);
v_unused_4701_ = lean_ctor_get(v_l_4478_, 0);
lean_dec(v_unused_4701_);
v___x_4691_ = v_l_4478_;
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
else
{
lean_dec(v_l_4478_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4696_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4694_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 4, v_r_4631_);
lean_ctor_set(v___x_4691_, 3, v___x_4689_);
lean_ctor_set(v___x_4691_, 2, v_v_4629_);
lean_ctor_set(v___x_4691_, 1, v_k_4628_);
lean_ctor_set(v___x_4691_, 0, v___x_4686_);
v___x_4694_ = v___x_4691_;
goto v_reusejp_4693_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v_k_4628_);
lean_ctor_set(v_reuseFailAlloc_4695_, 2, v_v_4629_);
lean_ctor_set(v_reuseFailAlloc_4695_, 3, v___x_4689_);
lean_ctor_set(v_reuseFailAlloc_4695_, 4, v_r_4631_);
v___x_4694_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4693_;
}
v_reusejp_4693_:
{
return v___x_4694_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4709_; 
v_l_4709_ = lean_ctor_get(v_impl_4624_, 3);
lean_inc(v_l_4709_);
if (lean_obj_tag(v_l_4709_) == 0)
{
lean_object* v_r_4710_; lean_object* v_k_4711_; lean_object* v_v_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4735_; 
v_r_4710_ = lean_ctor_get(v_impl_4624_, 4);
v_k_4711_ = lean_ctor_get(v_impl_4624_, 1);
v_v_4712_ = lean_ctor_get(v_impl_4624_, 2);
v_isSharedCheck_4735_ = !lean_is_exclusive(v_impl_4624_);
if (v_isSharedCheck_4735_ == 0)
{
lean_object* v_unused_4736_; lean_object* v_unused_4737_; 
v_unused_4736_ = lean_ctor_get(v_impl_4624_, 3);
lean_dec(v_unused_4736_);
v_unused_4737_ = lean_ctor_get(v_impl_4624_, 0);
lean_dec(v_unused_4737_);
v___x_4714_ = v_impl_4624_;
v_isShared_4715_ = v_isSharedCheck_4735_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_r_4710_);
lean_inc(v_v_4712_);
lean_inc(v_k_4711_);
lean_dec(v_impl_4624_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4735_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v_k_4716_; lean_object* v_v_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4731_; 
v_k_4716_ = lean_ctor_get(v_l_4709_, 1);
v_v_4717_ = lean_ctor_get(v_l_4709_, 2);
v_isSharedCheck_4731_ = !lean_is_exclusive(v_l_4709_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; lean_object* v_unused_4733_; lean_object* v_unused_4734_; 
v_unused_4732_ = lean_ctor_get(v_l_4709_, 4);
lean_dec(v_unused_4732_);
v_unused_4733_ = lean_ctor_get(v_l_4709_, 3);
lean_dec(v_unused_4733_);
v_unused_4734_ = lean_ctor_get(v_l_4709_, 0);
lean_dec(v_unused_4734_);
v___x_4719_ = v_l_4709_;
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_v_4717_);
lean_inc(v_k_4716_);
lean_dec(v_l_4709_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4731_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4721_; lean_object* v___x_4723_; 
v___x_4721_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4710_, 2);
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 4, v_r_4710_);
lean_ctor_set(v___x_4719_, 3, v_r_4710_);
lean_ctor_set(v___x_4719_, 2, v_v_4477_);
lean_ctor_set(v___x_4719_, 1, v_k_4476_);
lean_ctor_set(v___x_4719_, 0, v___x_4625_);
v___x_4723_ = v___x_4719_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_r_4710_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_r_4710_);
v___x_4723_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4725_; 
lean_inc(v_r_4710_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 3, v_r_4710_);
lean_ctor_set(v___x_4714_, 0, v___x_4625_);
v___x_4725_ = v___x_4714_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_k_4711_);
lean_ctor_set(v_reuseFailAlloc_4729_, 2, v_v_4712_);
lean_ctor_set(v_reuseFailAlloc_4729_, 3, v_r_4710_);
lean_ctor_set(v_reuseFailAlloc_4729_, 4, v_r_4710_);
v___x_4725_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4727_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v___x_4725_);
lean_ctor_set(v___x_4481_, 3, v___x_4723_);
lean_ctor_set(v___x_4481_, 2, v_v_4717_);
lean_ctor_set(v___x_4481_, 1, v_k_4716_);
lean_ctor_set(v___x_4481_, 0, v___x_4721_);
v___x_4727_ = v___x_4481_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4721_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_k_4716_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_v_4717_);
lean_ctor_set(v_reuseFailAlloc_4728_, 3, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4728_, 4, v___x_4725_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
}
else
{
lean_object* v_r_4738_; 
v_r_4738_ = lean_ctor_get(v_impl_4624_, 4);
lean_inc(v_r_4738_);
if (lean_obj_tag(v_r_4738_) == 0)
{
lean_object* v_k_4739_; lean_object* v_v_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4751_; 
v_k_4739_ = lean_ctor_get(v_impl_4624_, 1);
v_v_4740_ = lean_ctor_get(v_impl_4624_, 2);
v_isSharedCheck_4751_ = !lean_is_exclusive(v_impl_4624_);
if (v_isSharedCheck_4751_ == 0)
{
lean_object* v_unused_4752_; lean_object* v_unused_4753_; lean_object* v_unused_4754_; 
v_unused_4752_ = lean_ctor_get(v_impl_4624_, 4);
lean_dec(v_unused_4752_);
v_unused_4753_ = lean_ctor_get(v_impl_4624_, 3);
lean_dec(v_unused_4753_);
v_unused_4754_ = lean_ctor_get(v_impl_4624_, 0);
lean_dec(v_unused_4754_);
v___x_4742_ = v_impl_4624_;
v_isShared_4743_ = v_isSharedCheck_4751_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_v_4740_);
lean_inc(v_k_4739_);
lean_dec(v_impl_4624_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4751_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4744_; lean_object* v___x_4746_; 
v___x_4744_ = lean_unsigned_to_nat(3u);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 4, v_l_4709_);
lean_ctor_set(v___x_4742_, 2, v_v_4477_);
lean_ctor_set(v___x_4742_, 1, v_k_4476_);
lean_ctor_set(v___x_4742_, 0, v___x_4625_);
v___x_4746_ = v___x_4742_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4750_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4750_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4750_, 3, v_l_4709_);
lean_ctor_set(v_reuseFailAlloc_4750_, 4, v_l_4709_);
v___x_4746_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
lean_object* v___x_4748_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v_r_4738_);
lean_ctor_set(v___x_4481_, 3, v___x_4746_);
lean_ctor_set(v___x_4481_, 2, v_v_4740_);
lean_ctor_set(v___x_4481_, 1, v_k_4739_);
lean_ctor_set(v___x_4481_, 0, v___x_4744_);
v___x_4748_ = v___x_4481_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_k_4739_);
lean_ctor_set(v_reuseFailAlloc_4749_, 2, v_v_4740_);
lean_ctor_set(v_reuseFailAlloc_4749_, 3, v___x_4746_);
lean_ctor_set(v_reuseFailAlloc_4749_, 4, v_r_4738_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
}
}
else
{
lean_object* v___x_4755_; lean_object* v___x_4757_; 
v___x_4755_ = lean_unsigned_to_nat(2u);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v_impl_4624_);
lean_ctor_set(v___x_4481_, 3, v_r_4738_);
lean_ctor_set(v___x_4481_, 0, v___x_4755_);
v___x_4757_ = v___x_4481_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4755_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_k_4476_);
lean_ctor_set(v_reuseFailAlloc_4758_, 2, v_v_4477_);
lean_ctor_set(v_reuseFailAlloc_4758_, 3, v_r_4738_);
lean_ctor_set(v_reuseFailAlloc_4758_, 4, v_impl_4624_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
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
lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4760_ = lean_unsigned_to_nat(1u);
v___x_4761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4760_);
lean_ctor_set(v___x_4761_, 1, v_k_4472_);
lean_ctor_set(v___x_4761_, 2, v_v_4473_);
lean_ctor_set(v___x_4761_, 3, v_t_4474_);
lean_ctor_set(v___x_4761_, 4, v_t_4474_);
return v___x_4761_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(lean_object* v_t_4762_, lean_object* v_k_4763_){
_start:
{
if (lean_obj_tag(v_t_4762_) == 0)
{
lean_object* v_k_4764_; lean_object* v_v_4765_; lean_object* v_l_4766_; lean_object* v_r_4767_; uint8_t v___x_4768_; 
v_k_4764_ = lean_ctor_get(v_t_4762_, 1);
v_v_4765_ = lean_ctor_get(v_t_4762_, 2);
v_l_4766_ = lean_ctor_get(v_t_4762_, 3);
v_r_4767_ = lean_ctor_get(v_t_4762_, 4);
v___x_4768_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4763_, v_k_4764_);
switch(v___x_4768_)
{
case 0:
{
v_t_4762_ = v_l_4766_;
goto _start;
}
case 1:
{
lean_object* v___x_4770_; 
lean_inc(v_v_4765_);
v___x_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4770_, 0, v_v_4765_);
return v___x_4770_;
}
default: 
{
v_t_4762_ = v_r_4767_;
goto _start;
}
}
}
else
{
lean_object* v___x_4772_; 
v___x_4772_ = lean_box(0);
return v___x_4772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg___boxed(lean_object* v_t_4773_, lean_object* v_k_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4773_, v_k_4774_);
lean_dec(v_k_4774_);
lean_dec(v_t_4773_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert___redArg(lean_object* v_map_4776_, lean_object* v_k_4777_, lean_object* v_v_4778_){
_start:
{
lean_object* v___x_4779_; 
v___x_4779_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_4776_, v_k_4777_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4780_ = lean_box(0);
v___x_4781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4781_, 0, v_v_4778_);
lean_ctor_set(v___x_4781_, 1, v___x_4780_);
v___x_4782_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4777_, v___x_4781_, v_map_4776_);
return v___x_4782_;
}
else
{
lean_object* v_val_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v_val_4783_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_val_4783_);
lean_dec_ref_known(v___x_4779_, 1);
v___x_4784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4784_, 0, v_v_4778_);
lean_ctor_set(v___x_4784_, 1, v_val_4783_);
v___x_4785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4777_, v___x_4784_, v_map_4776_);
return v___x_4785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_insert(lean_object* v_00_u03b1_4786_, lean_object* v_map_4787_, lean_object* v_k_4788_, lean_object* v_v_4789_){
_start:
{
lean_object* v___x_4790_; 
v___x_4790_ = l_Lean_Parser_TokenMap_insert___redArg(v_map_4787_, v_k_4788_, v_v_4789_);
return v___x_4790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(lean_object* v_00_u03b4_4791_, lean_object* v_t_4792_, lean_object* v_k_4793_){
_start:
{
lean_object* v___x_4794_; 
v___x_4794_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_t_4792_, v_k_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___boxed(lean_object* v_00_u03b4_4795_, lean_object* v_t_4796_, lean_object* v_k_4797_){
_start:
{
lean_object* v_res_4798_; 
v_res_4798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0(v_00_u03b4_4795_, v_t_4796_, v_k_4797_);
lean_dec(v_k_4797_);
lean_dec(v_t_4796_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1(lean_object* v_00_u03b2_4799_, lean_object* v_k_4800_, lean_object* v_v_4801_, lean_object* v_t_4802_, lean_object* v_hl_4803_){
_start:
{
lean_object* v___x_4804_; 
v___x_4804_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Parser_TokenMap_insert_spec__1___redArg(v_k_4800_, v_v_4801_, v_t_4802_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = lean_box(1);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited___redArg___boxed(lean_object* v___dummy_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Parser_TokenMap_instInhabited___redArg();
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instInhabited(lean_object* v_00_u03b1_4809_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = lean_box(1);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_4812_; 
v___x_4812_ = lean_box(1);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Parser_TokenMap_instEmptyCollection___redArg();
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instEmptyCollection(lean_object* v_00_u03b1_4815_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = lean_box(1);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0(lean_object* v_f_4817_, lean_object* v_a_4818_, lean_object* v_b_4819_, lean_object* v_c_4820_){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4821_, 0, v_a_4818_);
lean_ctor_set(v___x_4821_, 1, v_b_4819_);
v___x_4822_ = lean_apply_2(v_f_4817_, v___x_4821_, v_c_4820_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1(lean_object* v_toPure_4823_, lean_object* v_____do__lift_4824_){
_start:
{
lean_object* v_a_4825_; lean_object* v___x_4826_; 
v_a_4825_ = lean_ctor_get(v_____do__lift_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref(v_____do__lift_4824_);
v___x_4826_ = lean_apply_2(v_toPure_4823_, lean_box(0), v_a_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg(lean_object* v_inst_4827_, lean_object* v_m_4828_, lean_object* v_init_4829_, lean_object* v_f_4830_){
_start:
{
lean_object* v_toApplicative_4831_; lean_object* v_toBind_4832_; lean_object* v_toPure_4833_; lean_object* v___f_4834_; lean_object* v___x_4835_; lean_object* v___f_4836_; lean_object* v___x_4837_; 
v_toApplicative_4831_ = lean_ctor_get(v_inst_4827_, 0);
v_toBind_4832_ = lean_ctor_get(v_inst_4827_, 1);
lean_inc(v_toBind_4832_);
v_toPure_4833_ = lean_ctor_get(v_toApplicative_4831_, 1);
lean_inc(v_toPure_4833_);
v___f_4834_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4834_, 0, v_f_4830_);
v___x_4835_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4827_, v___f_4834_, v_init_4829_, v_m_4828_);
v___f_4836_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4836_, 0, v_toPure_4833_);
v___x_4837_ = lean_apply_4(v_toBind_4832_, lean_box(0), lean_box(0), v___x_4835_, v___f_4836_);
return v___x_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1(lean_object* v_m_4838_, lean_object* v_00_u03b1_4839_, lean_object* v_inst_4840_, lean_object* v_00_u03b2_4841_, lean_object* v_m_4842_, lean_object* v_init_4843_, lean_object* v_f_4844_){
_start:
{
lean_object* v_toApplicative_4845_; lean_object* v_toBind_4846_; lean_object* v_toPure_4847_; lean_object* v___f_4848_; lean_object* v___x_4849_; lean_object* v___f_4850_; lean_object* v___x_4851_; 
v_toApplicative_4845_ = lean_ctor_get(v_inst_4840_, 0);
v_toBind_4846_ = lean_ctor_get(v_inst_4840_, 1);
lean_inc(v_toBind_4846_);
v_toPure_4847_ = lean_ctor_get(v_toApplicative_4845_, 1);
lean_inc(v_toPure_4847_);
v___f_4848_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_4848_, 0, v_f_4844_);
v___x_4849_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_4840_, v___f_4848_, v_init_4843_, v_m_4842_);
v___f_4850_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4850_, 0, v_toPure_4847_);
v___x_4851_ = lean_apply_4(v_toBind_4846_, lean_box(0), lean_box(0), v___x_4849_, v___f_4850_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___redArg(lean_object* v_inst_4852_){
_start:
{
lean_object* v___x_4853_; 
v___x_4853_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4853_, 0, lean_box(0));
lean_closure_set(v___x_4853_, 1, lean_box(0));
lean_closure_set(v___x_4853_, 2, v_inst_4852_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_TokenMap_instForInProdNameListOfMonad(lean_object* v_m_4854_, lean_object* v_00_u03b1_4855_, lean_object* v_inst_4856_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = lean_alloc_closure((void*)(l_Lean_Parser_TokenMap_instForInProdNameListOfMonad___aux__1), 7, 3);
lean_closure_set(v___x_4857_, 0, lean_box(0));
lean_closure_set(v___x_4857_, 1, lean_box(0));
lean_closure_set(v___x_4857_, 2, v_inst_4856_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(uint8_t v_x_4862_){
_start:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; 
v___x_4863_ = lean_box(v_x_4862_);
v___x_4864_ = lean_obj_tag_nat(v___x_4863_);
lean_dec(v___x_4863_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl___boxed(lean_object* v_x_4865_){
_start:
{
uint8_t v_x_4__boxed_4866_; lean_object* v_res_4867_; 
v_x_4__boxed_4866_ = lean_unbox(v_x_4865_);
v_res_4867_ = l_Lean_Parser_LeadingIdentBehavior_ctorIdx___impl(v_x_4__boxed_4866_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(lean_object* v_k_4868_){
_start:
{
lean_inc(v_k_4868_);
return v_k_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg___boxed(lean_object* v_k_4869_){
_start:
{
lean_object* v_res_4870_; 
v_res_4870_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim___redArg(v_k_4869_);
lean_dec(v_k_4869_);
return v_res_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim(lean_object* v_motive_4871_, lean_object* v_ctorIdx_4872_, uint8_t v_t_4873_, lean_object* v_h_4874_, lean_object* v_k_4875_){
_start:
{
lean_inc(v_k_4875_);
return v_k_4875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_ctorElim___boxed(lean_object* v_motive_4876_, lean_object* v_ctorIdx_4877_, lean_object* v_t_4878_, lean_object* v_h_4879_, lean_object* v_k_4880_){
_start:
{
uint8_t v_t_boxed_4881_; lean_object* v_res_4882_; 
v_t_boxed_4881_ = lean_unbox(v_t_4878_);
v_res_4882_ = l_Lean_Parser_LeadingIdentBehavior_ctorElim(v_motive_4876_, v_ctorIdx_4877_, v_t_boxed_4881_, v_h_4879_, v_k_4880_);
lean_dec(v_k_4880_);
lean_dec(v_ctorIdx_4877_);
return v_res_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(lean_object* v_default_4883_){
_start:
{
lean_inc(v_default_4883_);
return v_default_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg___boxed(lean_object* v_default_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean_Parser_LeadingIdentBehavior_default_elim___redArg(v_default_4884_);
lean_dec(v_default_4884_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim(lean_object* v_motive_4886_, uint8_t v_t_4887_, lean_object* v_h_4888_, lean_object* v_default_4889_){
_start:
{
lean_inc(v_default_4889_);
return v_default_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_default_elim___boxed(lean_object* v_motive_4890_, lean_object* v_t_4891_, lean_object* v_h_4892_, lean_object* v_default_4893_){
_start:
{
uint8_t v_t_boxed_4894_; lean_object* v_res_4895_; 
v_t_boxed_4894_ = lean_unbox(v_t_4891_);
v_res_4895_ = l_Lean_Parser_LeadingIdentBehavior_default_elim(v_motive_4890_, v_t_boxed_4894_, v_h_4892_, v_default_4893_);
lean_dec(v_default_4893_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(lean_object* v_symbol_4896_){
_start:
{
lean_inc(v_symbol_4896_);
return v_symbol_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg___boxed(lean_object* v_symbol_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim___redArg(v_symbol_4897_);
lean_dec(v_symbol_4897_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim(lean_object* v_motive_4899_, uint8_t v_t_4900_, lean_object* v_h_4901_, lean_object* v_symbol_4902_){
_start:
{
lean_inc(v_symbol_4902_);
return v_symbol_4902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_symbol_elim___boxed(lean_object* v_motive_4903_, lean_object* v_t_4904_, lean_object* v_h_4905_, lean_object* v_symbol_4906_){
_start:
{
uint8_t v_t_boxed_4907_; lean_object* v_res_4908_; 
v_t_boxed_4907_ = lean_unbox(v_t_4904_);
v_res_4908_ = l_Lean_Parser_LeadingIdentBehavior_symbol_elim(v_motive_4903_, v_t_boxed_4907_, v_h_4905_, v_symbol_4906_);
lean_dec(v_symbol_4906_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(lean_object* v_both_4909_){
_start:
{
lean_inc(v_both_4909_);
return v_both_4909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg___boxed(lean_object* v_both_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Lean_Parser_LeadingIdentBehavior_both_elim___redArg(v_both_4910_);
lean_dec(v_both_4910_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim(lean_object* v_motive_4912_, uint8_t v_t_4913_, lean_object* v_h_4914_, lean_object* v_both_4915_){
_start:
{
lean_inc(v_both_4915_);
return v_both_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_LeadingIdentBehavior_both_elim___boxed(lean_object* v_motive_4916_, lean_object* v_t_4917_, lean_object* v_h_4918_, lean_object* v_both_4919_){
_start:
{
uint8_t v_t_boxed_4920_; lean_object* v_res_4921_; 
v_t_boxed_4920_ = lean_unbox(v_t_4917_);
v_res_4921_ = l_Lean_Parser_LeadingIdentBehavior_both_elim(v_motive_4916_, v_t_boxed_4920_, v_h_4918_, v_both_4919_);
lean_dec(v_both_4919_);
return v_res_4921_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior_default(void){
_start:
{
uint8_t v___x_4922_; 
v___x_4922_ = 0;
return v___x_4922_;
}
}
static uint8_t _init_l_Lean_Parser_instInhabitedLeadingIdentBehavior(void){
_start:
{
uint8_t v___x_4923_; 
v___x_4923_ = 0;
return v___x_4923_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqLeadingIdentBehavior_beq(uint8_t v_x_4924_, uint8_t v_y_4925_){
_start:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; uint8_t v___x_4930_; 
v___x_4926_ = lean_box(v_x_4924_);
v___x_4927_ = lean_obj_tag_nat(v___x_4926_);
lean_dec(v___x_4926_);
v___x_4928_ = lean_box(v_y_4925_);
v___x_4929_ = lean_obj_tag_nat(v___x_4928_);
lean_dec(v___x_4928_);
v___x_4930_ = lean_nat_dec_eq(v___x_4927_, v___x_4929_);
return v___x_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqLeadingIdentBehavior_beq___boxed(lean_object* v_x_4931_, lean_object* v_y_4932_){
_start:
{
uint8_t v_x_24__boxed_4933_; uint8_t v_y_25__boxed_4934_; uint8_t v_res_4935_; lean_object* v_r_4936_; 
v_x_24__boxed_4933_ = lean_unbox(v_x_4931_);
v_y_25__boxed_4934_ = lean_unbox(v_y_4932_);
v_res_4935_ = l_Lean_Parser_instBEqLeadingIdentBehavior_beq(v_x_24__boxed_4933_, v_y_25__boxed_4934_);
v_r_4936_ = lean_box(v_res_4935_);
return v_r_4936_;
}
}
static lean_object* _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6(void){
_start:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; 
v___x_4948_ = lean_unsigned_to_nat(2u);
v___x_4949_ = lean_nat_to_int(v___x_4948_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr(uint8_t v_x_4950_, lean_object* v_prec_4951_){
_start:
{
lean_object* v___y_4953_; lean_object* v___y_4960_; lean_object* v___y_4967_; 
switch(v_x_4950_)
{
case 0:
{
lean_object* v___x_4973_; uint8_t v___x_4974_; 
v___x_4973_ = lean_unsigned_to_nat(1024u);
v___x_4974_ = lean_nat_dec_le(v___x_4973_, v_prec_4951_);
if (v___x_4974_ == 0)
{
lean_object* v___x_4975_; 
v___x_4975_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4953_ = v___x_4975_;
goto v___jp_4952_;
}
else
{
lean_object* v___x_4976_; 
v___x_4976_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4953_ = v___x_4976_;
goto v___jp_4952_;
}
}
case 1:
{
lean_object* v___x_4977_; uint8_t v___x_4978_; 
v___x_4977_ = lean_unsigned_to_nat(1024u);
v___x_4978_ = lean_nat_dec_le(v___x_4977_, v_prec_4951_);
if (v___x_4978_ == 0)
{
lean_object* v___x_4979_; 
v___x_4979_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4960_ = v___x_4979_;
goto v___jp_4959_;
}
else
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4960_ = v___x_4980_;
goto v___jp_4959_;
}
}
default: 
{
lean_object* v___x_4981_; uint8_t v___x_4982_; 
v___x_4981_ = lean_unsigned_to_nat(1024u);
v___x_4982_ = lean_nat_dec_le(v___x_4981_, v_prec_4951_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
v___x_4983_ = lean_obj_once(&l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6, &l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6_once, _init_l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__6);
v___y_4967_ = v___x_4983_;
goto v___jp_4966_;
}
else
{
lean_object* v___x_4984_; 
v___x_4984_ = lean_obj_once(&l_Lean_Parser_incQuotDepth___closed__0, &l_Lean_Parser_incQuotDepth___closed__0_once, _init_l_Lean_Parser_incQuotDepth___closed__0);
v___y_4967_ = v___x_4984_;
goto v___jp_4966_;
}
}
}
v___jp_4952_:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; uint8_t v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4954_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__1));
lean_inc(v___y_4953_);
v___x_4955_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___y_4953_);
lean_ctor_set(v___x_4955_, 1, v___x_4954_);
v___x_4956_ = 0;
v___x_4957_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4957_, 0, v___x_4955_);
lean_ctor_set_uint8(v___x_4957_, sizeof(void*)*1, v___x_4956_);
v___x_4958_ = l_Repr_addAppParen(v___x_4957_, v_prec_4951_);
return v___x_4958_;
}
v___jp_4959_:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; uint8_t v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4961_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__3));
lean_inc(v___y_4960_);
v___x_4962_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___y_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = 0;
v___x_4964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4964_, 0, v___x_4962_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*1, v___x_4963_);
v___x_4965_ = l_Repr_addAppParen(v___x_4964_, v_prec_4951_);
return v___x_4965_;
}
v___jp_4966_:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; uint8_t v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4968_ = ((lean_object*)(l_Lean_Parser_instReprLeadingIdentBehavior_repr___closed__5));
lean_inc(v___y_4967_);
v___x_4969_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___y_4967_);
lean_ctor_set(v___x_4969_, 1, v___x_4968_);
v___x_4970_ = 0;
v___x_4971_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_4971_, 0, v___x_4969_);
lean_ctor_set_uint8(v___x_4971_, sizeof(void*)*1, v___x_4970_);
v___x_4972_ = l_Repr_addAppParen(v___x_4971_, v_prec_4951_);
return v___x_4972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instReprLeadingIdentBehavior_repr___boxed(lean_object* v_x_4985_, lean_object* v_prec_4986_){
_start:
{
uint8_t v_x_169__boxed_4987_; lean_object* v_res_4988_; 
v_x_169__boxed_4987_ = lean_unbox(v_x_4985_);
v_res_4988_ = l_Lean_Parser_instReprLeadingIdentBehavior_repr(v_x_169__boxed_4987_, v_prec_4986_);
lean_dec(v_prec_4986_);
return v_res_4988_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0(void){
_start:
{
lean_object* v___x_4991_; 
v___x_4991_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_4991_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4992_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__0, &l_Lean_Parser_instInhabitedParserCategory_default___closed__0_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__0);
v___x_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4993_, 0, v___x_4992_);
return v___x_4993_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2(void){
_start:
{
uint8_t v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4994_ = 0;
v___x_4995_ = ((lean_object*)(l_Lean_Parser_instInhabitedPrattParsingTables___closed__0));
v___x_4996_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__1, &l_Lean_Parser_instInhabitedParserCategory_default___closed__1_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__1);
v___x_4997_ = lean_box(0);
v___x_4998_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4998_, 0, v___x_4997_);
lean_ctor_set(v___x_4998_, 1, v___x_4996_);
lean_ctor_set(v___x_4998_, 2, v___x_4995_);
lean_ctor_set_uint8(v___x_4998_, sizeof(void*)*3, v___x_4994_);
return v___x_4998_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory_default(void){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserCategory_default___closed__2, &l_Lean_Parser_instInhabitedParserCategory_default___closed__2_once, _init_l_Lean_Parser_instInhabitedParserCategory_default___closed__2);
return v___x_4999_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserCategory(void){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = l_Lean_Parser_instInhabitedParserCategory_default;
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg(lean_object* v_map_5001_, lean_object* v_c_5002_, lean_object* v_s_5003_, uint8_t v_behavior_5004_){
_start:
{
lean_object* v___x_5005_; lean_object* v_fst_5006_; lean_object* v_snd_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5049_; 
v___x_5005_ = l_Lean_Parser_peekToken(v_c_5002_, v_s_5003_);
v_fst_5006_ = lean_ctor_get(v___x_5005_, 0);
v_snd_5007_ = lean_ctor_get(v___x_5005_, 1);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5009_ = v___x_5005_;
v_isShared_5010_ = v_isSharedCheck_5049_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_snd_5007_);
lean_inc(v_fst_5006_);
lean_dec(v___x_5005_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5049_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v_n_5012_; 
if (lean_obj_tag(v_snd_5007_) == 0)
{
lean_object* v_a_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
lean_del_object(v___x_5009_);
lean_dec(v_fst_5006_);
v_a_5024_ = lean_ctor_get(v_snd_5007_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v_snd_5007_, 1);
v___x_5025_ = lean_box(0);
v___x_5026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5026_, 0, v_a_5024_);
lean_ctor_set(v___x_5026_, 1, v___x_5025_);
return v___x_5026_;
}
else
{
lean_object* v_a_5027_; 
v_a_5027_ = lean_ctor_get(v_snd_5007_, 0);
lean_inc(v_a_5027_);
lean_dec_ref_known(v_snd_5007_, 1);
switch(lean_obj_tag(v_a_5027_))
{
case 2:
{
lean_object* v_val_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; 
v_val_5028_ = lean_ctor_get(v_a_5027_, 1);
lean_inc_ref(v_val_5028_);
lean_dec_ref_known(v_a_5027_, 2);
v___x_5029_ = lean_box(0);
v___x_5030_ = l_Lean_Name_str___override(v___x_5029_, v_val_5028_);
v_n_5012_ = v___x_5030_;
goto v___jp_5011_;
}
case 3:
{
switch(v_behavior_5004_)
{
case 0:
{
lean_dec_ref_known(v_a_5027_, 4);
goto v___jp_5022_;
}
case 1:
{
lean_object* v_val_5031_; lean_object* v___x_5032_; 
v_val_5031_ = lean_ctor_get(v_a_5027_, 2);
lean_inc(v_val_5031_);
lean_dec_ref_known(v_a_5027_, 4);
v___x_5032_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5001_, v_val_5031_);
lean_dec(v_val_5031_);
if (lean_obj_tag(v___x_5032_) == 0)
{
goto v___jp_5022_;
}
else
{
lean_object* v_val_5033_; lean_object* v___x_5034_; 
lean_del_object(v___x_5009_);
v_val_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_val_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v_fst_5006_);
lean_ctor_set(v___x_5034_, 1, v_val_5033_);
return v___x_5034_;
}
}
default: 
{
lean_object* v_val_5035_; lean_object* v___x_5036_; 
v_val_5035_ = lean_ctor_get(v_a_5027_, 2);
lean_inc(v_val_5035_);
lean_dec_ref_known(v_a_5027_, 4);
v___x_5036_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5001_, v_val_5035_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_dec(v_val_5035_);
goto v___jp_5022_;
}
else
{
lean_object* v_val_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
lean_del_object(v___x_5009_);
v_val_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_val_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v___x_5038_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v___x_5039_ = lean_name_eq(v_val_5035_, v___x_5038_);
lean_dec(v_val_5035_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; 
v___x_5040_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5001_, v___x_5038_);
if (lean_obj_tag(v___x_5040_) == 1)
{
lean_object* v_val_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v_val_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_val_5041_);
lean_dec_ref_known(v___x_5040_, 1);
v___x_5042_ = l_List_appendTR___redArg(v_val_5037_, v_val_5041_);
v___x_5043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5043_, 0, v_fst_5006_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
return v___x_5043_;
}
else
{
lean_object* v___x_5044_; 
lean_dec(v___x_5040_);
v___x_5044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5044_, 0, v_fst_5006_);
lean_ctor_set(v___x_5044_, 1, v_val_5037_);
return v___x_5044_;
}
}
else
{
lean_object* v___x_5045_; 
v___x_5045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5045_, 0, v_fst_5006_);
lean_ctor_set(v___x_5045_, 1, v_val_5037_);
return v___x_5045_;
}
}
}
}
}
case 1:
{
lean_object* v_kind_5046_; 
v_kind_5046_ = lean_ctor_get(v_a_5027_, 1);
lean_inc(v_kind_5046_);
lean_dec_ref_known(v_a_5027_, 3);
v_n_5012_ = v_kind_5046_;
goto v___jp_5011_;
}
default: 
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
lean_dec(v_a_5027_);
lean_del_object(v___x_5009_);
v___x_5047_ = lean_box(0);
v___x_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5048_, 0, v_fst_5006_);
lean_ctor_set(v___x_5048_, 1, v___x_5047_);
return v___x_5048_;
}
}
}
v___jp_5011_:
{
lean_object* v___x_5013_; 
v___x_5013_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Parser_TokenMap_insert_spec__0___redArg(v_map_5001_, v_n_5012_);
lean_dec(v_n_5012_);
if (lean_obj_tag(v___x_5013_) == 1)
{
lean_object* v_val_5014_; lean_object* v___x_5016_; 
v_val_5014_ = lean_ctor_get(v___x_5013_, 0);
lean_inc(v_val_5014_);
lean_dec_ref_known(v___x_5013_, 1);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 1, v_val_5014_);
v___x_5016_ = v___x_5009_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v_fst_5006_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v_val_5014_);
v___x_5016_ = v_reuseFailAlloc_5017_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
return v___x_5016_;
}
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5020_; 
lean_dec(v___x_5013_);
v___x_5018_ = lean_box(0);
if (v_isShared_5010_ == 0)
{
lean_ctor_set(v___x_5009_, 1, v___x_5018_);
v___x_5020_ = v___x_5009_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v_fst_5006_);
lean_ctor_set(v_reuseFailAlloc_5021_, 1, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
return v___x_5020_;
}
}
}
v___jp_5022_:
{
lean_object* v___x_5023_; 
v___x_5023_ = ((lean_object*)(l_Lean_Parser_identFn___closed__0));
v_n_5012_ = v___x_5023_;
goto v___jp_5011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___redArg___boxed(lean_object* v_map_5050_, lean_object* v_c_5051_, lean_object* v_s_5052_, lean_object* v_behavior_5053_){
_start:
{
uint8_t v_behavior_boxed_5054_; lean_object* v_res_5055_; 
v_behavior_boxed_5054_ = lean_unbox(v_behavior_5053_);
v_res_5055_ = l_Lean_Parser_indexed___redArg(v_map_5050_, v_c_5051_, v_s_5052_, v_behavior_boxed_5054_);
lean_dec(v_map_5050_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed(lean_object* v_00_u03b1_5056_, lean_object* v_map_5057_, lean_object* v_c_5058_, lean_object* v_s_5059_, uint8_t v_behavior_5060_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Lean_Parser_indexed___redArg(v_map_5057_, v_c_5058_, v_s_5059_, v_behavior_5060_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_indexed___boxed(lean_object* v_00_u03b1_5062_, lean_object* v_map_5063_, lean_object* v_c_5064_, lean_object* v_s_5065_, lean_object* v_behavior_5066_){
_start:
{
uint8_t v_behavior_boxed_5067_; lean_object* v_res_5068_; 
v_behavior_boxed_5067_ = lean_unbox(v_behavior_5066_);
v_res_5068_ = l_Lean_Parser_indexed(v_00_u03b1_5062_, v_map_5063_, v_c_5064_, v_s_5065_, v_behavior_boxed_5067_);
lean_dec(v_map_5063_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(lean_object* v_x_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_){
_start:
{
lean_object* v___x_5072_; 
v___x_5072_ = l_Lean_Parser_whitespace(v___y_5070_, v___y_5071_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_x_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v_res_5076_; 
v_res_5076_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(v_x_5073_, v___y_5074_, v___y_5075_);
lean_dec(v_x_5073_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___f_5079_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_));
v___x_5080_ = lean_st_mk_ref(v___f_5079_);
v___x_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5081_, 0, v___x_5080_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2____boxed(lean_object* v_a_5082_){
_start:
{
lean_object* v_res_5083_; 
v_res_5083_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_367397207____hygCtx___hyg_2_();
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(lean_object* v___x_5084_){
_start:
{
lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5086_ = lean_st_ref_get(v___x_5084_);
v___x_5087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5087_, 0, v___x_5086_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v___x_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(v___x_5088_);
lean_dec(v___x_5088_);
return v_res_5090_;
}
}
static lean_object* _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5091_; lean_object* v___f_5092_; 
v___x_5091_ = l_Lean_Parser_categoryParserFnRef;
v___f_5092_ = lean_alloc_closure((void*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5092_, 0, v___x_5091_);
return v___f_5092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; uint8_t v___x_5103_; lean_object* v___x_5104_; 
v___f_5099_ = lean_obj_once(&l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_, &l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2__once, _init_l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_);
v___x_5100_ = lean_box(0);
v___x_5101_ = lean_box(2);
v___x_5102_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_));
v___x_5103_ = 0;
v___x_5104_ = l_Lean_registerEnvExtension___redArg(v___f_5099_, v___x_5100_, v___x_5101_, v___x_5102_, v___x_5103_, v___x_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2____boxed(lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l___private_Lean_Parser_Basic_0__Lean_Parser_initFn_00___x40_Lean_Parser_Basic_281847278____hygCtx___hyg_2_();
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0(lean_object* v_a_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
lean_object* v___x_5110_; 
v___x_5110_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v___y_5108_, v___y_5109_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn___lam__0___boxed(lean_object* v_a_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Parser_categoryParserFn___lam__0(v_a_5111_, v___y_5112_, v___y_5113_);
lean_dec_ref(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec(v_a_5111_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParserFn(lean_object* v_catName_5118_, lean_object* v_ctx_5119_, lean_object* v_s_5120_){
_start:
{
lean_object* v_toParserModuleContext_5121_; lean_object* v_env_5122_; lean_object* v___x_5123_; lean_object* v_asyncMode_5124_; lean_object* v___f_5125_; lean_object* v___x_5126_; uint8_t v___x_5127_; lean_object* v___x_21__overap_5128_; lean_object* v___x_5129_; 
v_toParserModuleContext_5121_ = lean_ctor_get(v_ctx_5119_, 1);
v_env_5122_ = lean_ctor_get(v_toParserModuleContext_5121_, 0);
v___x_5123_ = l_Lean_Parser_categoryParserFnExtension;
v_asyncMode_5124_ = lean_ctor_get(v___x_5123_, 2);
v___f_5125_ = ((lean_object*)(l_Lean_Parser_categoryParserFn___closed__1));
v___x_5126_ = lean_box(0);
v___x_5127_ = 0;
lean_inc_ref(v_env_5122_);
v___x_21__overap_5128_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___f_5125_, v___x_5123_, v_env_5122_, v_asyncMode_5124_, v___x_5126_, v___x_5127_);
v___x_5129_ = lean_apply_3(v___x_21__overap_5128_, v_catName_5118_, v_ctx_5119_, v_s_5120_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser___lam__0(lean_object* v_prec_5130_, lean_object* v_x_5131_){
_start:
{
lean_object* v_quotDepth_5132_; uint8_t v_suppressInsideQuot_5133_; lean_object* v_savedPos_x3f_5134_; lean_object* v_forbiddenTks_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5142_; 
v_quotDepth_5132_ = lean_ctor_get(v_x_5131_, 1);
v_suppressInsideQuot_5133_ = lean_ctor_get_uint8(v_x_5131_, sizeof(void*)*4);
v_savedPos_x3f_5134_ = lean_ctor_get(v_x_5131_, 2);
v_forbiddenTks_5135_ = lean_ctor_get(v_x_5131_, 3);
v_isSharedCheck_5142_ = !lean_is_exclusive(v_x_5131_);
if (v_isSharedCheck_5142_ == 0)
{
lean_object* v_unused_5143_; 
v_unused_5143_ = lean_ctor_get(v_x_5131_, 0);
lean_dec(v_unused_5143_);
v___x_5137_ = v_x_5131_;
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
else
{
lean_inc(v_forbiddenTks_5135_);
lean_inc(v_savedPos_x3f_5134_);
lean_inc(v_quotDepth_5132_);
lean_dec(v_x_5131_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5142_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5140_; 
if (v_isShared_5138_ == 0)
{
lean_ctor_set(v___x_5137_, 0, v_prec_5130_);
v___x_5140_ = v___x_5137_;
goto v_reusejp_5139_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_prec_5130_);
lean_ctor_set(v_reuseFailAlloc_5141_, 1, v_quotDepth_5132_);
lean_ctor_set(v_reuseFailAlloc_5141_, 2, v_savedPos_x3f_5134_);
lean_ctor_set(v_reuseFailAlloc_5141_, 3, v_forbiddenTks_5135_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, sizeof(void*)*4, v_suppressInsideQuot_5133_);
v___x_5140_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5139_;
}
v_reusejp_5139_:
{
return v___x_5140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_categoryParser(lean_object* v_catName_5144_, lean_object* v_prec_5145_){
_start:
{
lean_object* v___f_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___f_5146_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParser___lam__0), 2, 1);
lean_closure_set(v___f_5146_, 0, v_prec_5145_);
v___x_5147_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
lean_inc(v_catName_5144_);
v___x_5148_ = lean_alloc_closure((void*)(l_Lean_Parser_categoryParserFn), 3, 1);
lean_closure_set(v___x_5148_, 0, v_catName_5144_);
v___x_5149_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_5149_, 0, v_catName_5144_);
lean_closure_set(v___x_5149_, 1, v___x_5148_);
v___x_5150_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_5150_, 0, v___f_5146_);
lean_closure_set(v___x_5150_, 1, v___x_5149_);
v___x_5151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5151_, 0, v___x_5147_);
lean_ctor_set(v___x_5151_, 1, v___x_5150_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_termParser(lean_object* v_prec_5155_){
_start:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5156_ = ((lean_object*)(l_Lean_Parser_termParser___closed__1));
v___x_5157_ = l_Lean_Parser_categoryParser(v___x_5156_, v_prec_5155_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0(lean_object* v_c_5159_, lean_object* v_s_5160_){
_start:
{
lean_object* v_stxStack_5161_; lean_object* v_pos_5162_; lean_object* v_prev_5163_; uint8_t v___x_5164_; 
v_stxStack_5161_ = lean_ctor_get(v_s_5160_, 0);
v_pos_5162_ = lean_ctor_get(v_s_5160_, 2);
v_prev_5163_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5161_);
v___x_5164_ = l_Lean_Parser_checkTailNoWs(v_prev_5163_);
lean_dec(v_prev_5163_);
if (v___x_5164_ == 0)
{
return v_s_5160_;
}
else
{
lean_object* v_toInputContext_5165_; uint8_t v___x_5166_; 
v_toInputContext_5165_ = lean_ctor_get(v_c_5159_, 0);
v___x_5166_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_5165_, v_pos_5162_);
if (v___x_5166_ == 0)
{
lean_object* v_inputString_5167_; uint32_t v_curr_5168_; uint32_t v___x_5169_; uint8_t v___x_5170_; 
v_inputString_5167_ = lean_ctor_get(v_toInputContext_5165_, 0);
v_curr_5168_ = lean_string_utf8_get_fast(v_inputString_5167_, v_pos_5162_);
v___x_5169_ = 58;
v___x_5170_ = lean_uint32_dec_eq(v_curr_5168_, v___x_5169_);
if (v___x_5170_ == 0)
{
return v_s_5160_;
}
else
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___x_5171_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon___lam__0___closed__0));
v___x_5172_ = lean_box(0);
v___x_5173_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_5160_, v___x_5171_, v___x_5172_, v___x_5170_);
return v___x_5173_;
}
}
else
{
return v_s_5160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_checkNoImmediateColon___lam__0___boxed(lean_object* v_c_5174_, lean_object* v_s_5175_){
_start:
{
lean_object* v_res_5176_; 
v_res_5176_ = l_Lean_Parser_checkNoImmediateColon___lam__0(v_c_5174_, v_s_5175_);
lean_dec_ref(v_c_5174_);
return v_res_5176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1(){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; 
v___x_5189_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__1));
v___x_5190_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___closed__2));
v___x_5191_ = l_Lean_addBuiltinDocString(v___x_5189_, v___x_5190_);
return v___x_5191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1___boxed(lean_object* v_a_5192_){
_start:
{
lean_object* v_res_5193_; 
v_res_5193_ = l___private_Lean_Parser_Basic_0__Lean_Parser_checkNoImmediateColon___regBuiltin_Lean_Parser_checkNoImmediateColon_docString__1();
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpectedFn(lean_object* v_expected_5194_, lean_object* v_p_5195_, lean_object* v_c_5196_, lean_object* v_s_5197_){
_start:
{
lean_object* v___x_5198_; lean_object* v_errorMsg_5199_; 
v___x_5198_ = lean_apply_2(v_p_5195_, v_c_5196_, v_s_5197_);
v_errorMsg_5199_ = lean_ctor_get(v___x_5198_, 4);
lean_inc(v_errorMsg_5199_);
if (lean_obj_tag(v_errorMsg_5199_) == 1)
{
lean_object* v_val_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5230_; 
v_val_5200_ = lean_ctor_get(v_errorMsg_5199_, 0);
v_isSharedCheck_5230_ = !lean_is_exclusive(v_errorMsg_5199_);
if (v_isSharedCheck_5230_ == 0)
{
v___x_5202_ = v_errorMsg_5199_;
v_isShared_5203_ = v_isSharedCheck_5230_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_val_5200_);
lean_dec(v_errorMsg_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5230_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v_stxStack_5204_; lean_object* v_lhsPrec_5205_; lean_object* v_pos_5206_; lean_object* v_cache_5207_; lean_object* v_recoveredErrors_5208_; lean_object* v___x_5210_; uint8_t v_isShared_5211_; uint8_t v_isSharedCheck_5228_; 
v_stxStack_5204_ = lean_ctor_get(v___x_5198_, 0);
v_lhsPrec_5205_ = lean_ctor_get(v___x_5198_, 1);
v_pos_5206_ = lean_ctor_get(v___x_5198_, 2);
v_cache_5207_ = lean_ctor_get(v___x_5198_, 3);
v_recoveredErrors_5208_ = lean_ctor_get(v___x_5198_, 5);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5198_);
if (v_isSharedCheck_5228_ == 0)
{
lean_object* v_unused_5229_; 
v_unused_5229_ = lean_ctor_get(v___x_5198_, 4);
lean_dec(v_unused_5229_);
v___x_5210_ = v___x_5198_;
v_isShared_5211_ = v_isSharedCheck_5228_;
goto v_resetjp_5209_;
}
else
{
lean_inc(v_recoveredErrors_5208_);
lean_inc(v_cache_5207_);
lean_inc(v_pos_5206_);
lean_inc(v_lhsPrec_5205_);
lean_inc(v_stxStack_5204_);
lean_dec(v___x_5198_);
v___x_5210_ = lean_box(0);
v_isShared_5211_ = v_isSharedCheck_5228_;
goto v_resetjp_5209_;
}
v_resetjp_5209_:
{
lean_object* v_unexpectedTk_5212_; lean_object* v_unexpected_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5226_; 
v_unexpectedTk_5212_ = lean_ctor_get(v_val_5200_, 0);
v_unexpected_5213_ = lean_ctor_get(v_val_5200_, 1);
v_isSharedCheck_5226_ = !lean_is_exclusive(v_val_5200_);
if (v_isSharedCheck_5226_ == 0)
{
lean_object* v_unused_5227_; 
v_unused_5227_ = lean_ctor_get(v_val_5200_, 2);
lean_dec(v_unused_5227_);
v___x_5215_ = v_val_5200_;
v_isShared_5216_ = v_isSharedCheck_5226_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_unexpected_5213_);
lean_inc(v_unexpectedTk_5212_);
lean_dec(v_val_5200_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5226_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
lean_ctor_set(v___x_5215_, 2, v_expected_5194_);
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_unexpectedTk_5212_);
lean_ctor_set(v_reuseFailAlloc_5225_, 1, v_unexpected_5213_);
lean_ctor_set(v_reuseFailAlloc_5225_, 2, v_expected_5194_);
v___x_5218_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5220_; 
if (v_isShared_5203_ == 0)
{
lean_ctor_set(v___x_5202_, 0, v___x_5218_);
v___x_5220_ = v___x_5202_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5218_);
v___x_5220_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5222_; 
if (v_isShared_5211_ == 0)
{
lean_ctor_set(v___x_5210_, 4, v___x_5220_);
v___x_5222_ = v___x_5210_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_stxStack_5204_);
lean_ctor_set(v_reuseFailAlloc_5223_, 1, v_lhsPrec_5205_);
lean_ctor_set(v_reuseFailAlloc_5223_, 2, v_pos_5206_);
lean_ctor_set(v_reuseFailAlloc_5223_, 3, v_cache_5207_);
lean_ctor_set(v_reuseFailAlloc_5223_, 4, v___x_5220_);
lean_ctor_set(v_reuseFailAlloc_5223_, 5, v_recoveredErrors_5208_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
}
}
}
else
{
lean_dec(v_errorMsg_5199_);
lean_dec(v_expected_5194_);
return v___x_5198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_setExpected(lean_object* v_expected_5231_, lean_object* v_p_5232_){
_start:
{
lean_object* v_info_5233_; lean_object* v_fn_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5242_; 
v_info_5233_ = lean_ctor_get(v_p_5232_, 0);
v_fn_5234_ = lean_ctor_get(v_p_5232_, 1);
v_isSharedCheck_5242_ = !lean_is_exclusive(v_p_5232_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5236_ = v_p_5232_;
v_isShared_5237_ = v_isSharedCheck_5242_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_fn_5234_);
lean_inc(v_info_5233_);
lean_dec(v_p_5232_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5242_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5238_; lean_object* v___x_5240_; 
v___x_5238_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpectedFn), 4, 2);
lean_closure_set(v___x_5238_, 0, v_expected_5231_);
lean_closure_set(v___x_5238_, 1, v_fn_5234_);
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 1, v___x_5238_);
v___x_5240_ = v___x_5236_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_info_5233_);
lean_ctor_set(v_reuseFailAlloc_5241_, 1, v___x_5238_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0(lean_object* v_x_5243_, lean_object* v_s_5244_){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5245_ = ((lean_object*)(l_Lean_Parser_withForbiddens___auto__1___closed__12));
v___x_5246_ = l_Lean_Parser_ParserState_pushSyntax(v_s_5244_, v___x_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_pushNone___lam__0___boxed(lean_object* v_x_5247_, lean_object* v_s_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_Lean_Parser_pushNone___lam__0(v_x_5247_, v_s_5248_);
lean_dec_ref(v_x_5247_);
return v_res_5249_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__3(void){
_start:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5259_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__2));
v___x_5260_ = l_Lean_Parser_symbolNoAntiquot(v___x_5259_);
return v___x_5260_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__4(void){
_start:
{
lean_object* v___x_5261_; lean_object* v___x_5262_; 
v___x_5261_ = lean_unsigned_to_nat(0u);
v___x_5262_ = l_Lean_Parser_termParser(v___x_5261_);
return v___x_5262_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__5(void){
_start:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5263_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__4, &l_Lean_Parser_antiquotNestedExpr___closed__4_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__4);
v___x_5264_ = l_Lean_Parser_decQuotDepth(v___x_5263_);
return v___x_5264_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__6(void){
_start:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; 
v___x_5265_ = ((lean_object*)(l_Lean_Parser_dbgTraceStateFn___closed__6));
v___x_5266_ = l_Lean_Parser_symbolNoAntiquot(v___x_5265_);
return v___x_5266_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__7(void){
_start:
{
lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5267_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__6, &l_Lean_Parser_antiquotNestedExpr___closed__6_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__6);
v___x_5268_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__5, &l_Lean_Parser_antiquotNestedExpr___closed__5_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__5);
v___x_5269_ = l_Lean_Parser_andthen(v___x_5268_, v___x_5267_);
return v___x_5269_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__8(void){
_start:
{
lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; 
v___x_5270_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__7, &l_Lean_Parser_antiquotNestedExpr___closed__7_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__7);
v___x_5271_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__3, &l_Lean_Parser_antiquotNestedExpr___closed__3_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__3);
v___x_5272_ = l_Lean_Parser_andthen(v___x_5271_, v___x_5270_);
return v___x_5272_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr___closed__9(void){
_start:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; 
v___x_5273_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__8, &l_Lean_Parser_antiquotNestedExpr___closed__8_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__8);
v___x_5274_ = ((lean_object*)(l_Lean_Parser_antiquotNestedExpr___closed__1));
v___x_5275_ = l_Lean_Parser_node(v___x_5274_, v___x_5273_);
return v___x_5275_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotNestedExpr(void){
_start:
{
lean_object* v___x_5276_; 
v___x_5276_ = lean_obj_once(&l_Lean_Parser_antiquotNestedExpr___closed__9, &l_Lean_Parser_antiquotNestedExpr___closed__9_once, _init_l_Lean_Parser_antiquotNestedExpr___closed__9);
return v___x_5276_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__1(void){
_start:
{
lean_object* v___x_5278_; lean_object* v___x_5279_; 
v___x_5278_ = ((lean_object*)(l_Lean_Parser_antiquotExpr___closed__0));
v___x_5279_ = l_Lean_Parser_symbolNoAntiquot(v___x_5278_);
return v___x_5279_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__2(void){
_start:
{
lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5280_ = l_Lean_Parser_antiquotNestedExpr;
v___x_5281_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__1, &l_Lean_Parser_antiquotExpr___closed__1_once, _init_l_Lean_Parser_antiquotExpr___closed__1);
v___x_5282_ = l_Lean_Parser_orelse(v___x_5281_, v___x_5280_);
return v___x_5282_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr___closed__3(void){
_start:
{
lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; 
v___x_5283_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__2, &l_Lean_Parser_antiquotExpr___closed__2_once, _init_l_Lean_Parser_antiquotExpr___closed__2);
v___x_5284_ = l_Lean_Parser_identNoAntiquot;
v___x_5285_ = l_Lean_Parser_orelse(v___x_5284_, v___x_5283_);
return v___x_5285_;
}
}
static lean_object* _init_l_Lean_Parser_antiquotExpr(void){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = lean_obj_once(&l_Lean_Parser_antiquotExpr___closed__3, &l_Lean_Parser_antiquotExpr___closed__3_once, _init_l_Lean_Parser_antiquotExpr___closed__3);
return v___x_5286_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__1(void){
_start:
{
lean_object* v___x_5288_; lean_object* v___x_5289_; 
v___x_5288_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__0));
v___x_5289_ = l_Lean_Parser_checkNoWsBefore(v___x_5288_);
return v___x_5289_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__3(void){
_start:
{
lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5291_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__2));
v___x_5292_ = l_Lean_Parser_symbolNoAntiquot(v___x_5291_);
return v___x_5292_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__5(void){
_start:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; 
v___x_5294_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5295_ = l_Lean_Parser_symbolNoAntiquot(v___x_5294_);
return v___x_5295_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__6(void){
_start:
{
lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5296_ = l_Lean_Parser_antiquotExpr;
v___x_5297_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5298_ = l_Lean_Parser_andthen(v___x_5297_, v___x_5296_);
return v___x_5298_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__7(void){
_start:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5299_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__6, &l_Lean_Parser_tokenAntiquotFn___closed__6_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__6);
v___x_5300_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__5, &l_Lean_Parser_tokenAntiquotFn___closed__5_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__5);
v___x_5301_ = l_Lean_Parser_andthen(v___x_5300_, v___x_5299_);
return v___x_5301_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__8(void){
_start:
{
lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5302_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__7, &l_Lean_Parser_tokenAntiquotFn___closed__7_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__7);
v___x_5303_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__3, &l_Lean_Parser_tokenAntiquotFn___closed__3_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__3);
v___x_5304_ = l_Lean_Parser_andthen(v___x_5303_, v___x_5302_);
return v___x_5304_;
}
}
static lean_object* _init_l_Lean_Parser_tokenAntiquotFn___closed__9(void){
_start:
{
lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5305_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__8, &l_Lean_Parser_tokenAntiquotFn___closed__8_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__8);
v___x_5306_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__1, &l_Lean_Parser_tokenAntiquotFn___closed__1_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__1);
v___x_5307_ = l_Lean_Parser_andthen(v___x_5306_, v___x_5305_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenAntiquotFn(lean_object* v_c_5311_, lean_object* v_s_5312_){
_start:
{
lean_object* v_pos_5313_; lean_object* v_errorMsg_5314_; lean_object* v___x_5315_; uint8_t v___x_5316_; 
v_pos_5313_ = lean_ctor_get(v_s_5312_, 2);
v_errorMsg_5314_ = lean_ctor_get(v_s_5312_, 4);
v___x_5315_ = lean_box(0);
v___x_5316_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5314_, v___x_5315_);
if (v___x_5316_ == 0)
{
lean_dec_ref(v_c_5311_);
return v_s_5312_;
}
else
{
lean_object* v___x_5317_; lean_object* v_fn_5318_; lean_object* v_iniSz_5319_; lean_object* v_s_5320_; lean_object* v_errorMsg_5321_; uint8_t v___x_5322_; 
lean_inc(v_pos_5313_);
v___x_5317_ = lean_obj_once(&l_Lean_Parser_tokenAntiquotFn___closed__9, &l_Lean_Parser_tokenAntiquotFn___closed__9_once, _init_l_Lean_Parser_tokenAntiquotFn___closed__9);
v_fn_5318_ = lean_ctor_get(v___x_5317_, 1);
v_iniSz_5319_ = l_Lean_Parser_ParserState_stackSize(v_s_5312_);
lean_inc_ref(v_fn_5318_);
v_s_5320_ = lean_apply_2(v_fn_5318_, v_c_5311_, v_s_5312_);
v_errorMsg_5321_ = lean_ctor_get(v_s_5320_, 4);
lean_inc(v_errorMsg_5321_);
v___x_5322_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5321_, v___x_5315_);
lean_dec(v_errorMsg_5321_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
v___x_5323_ = l_Lean_Parser_ParserState_restore(v_s_5320_, v_iniSz_5319_, v_pos_5313_);
lean_dec(v_iniSz_5319_);
return v___x_5323_;
}
else
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; 
lean_dec(v_pos_5313_);
v___x_5324_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__11));
v___x_5325_ = lean_unsigned_to_nat(1u);
v___x_5326_ = lean_nat_sub(v_iniSz_5319_, v___x_5325_);
lean_dec(v_iniSz_5319_);
v___x_5327_ = l_Lean_Parser_ParserState_mkNode(v_s_5320_, v___x_5324_, v___x_5326_);
lean_dec(v___x_5326_);
return v___x_5327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot___lam__0(lean_object* v_fn_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v_toInputContext_5331_; lean_object* v_s_5332_; lean_object* v_pos_5333_; lean_object* v_inputString_5334_; uint32_t v___x_5335_; uint32_t v___x_5336_; uint8_t v___x_5337_; 
v_toInputContext_5331_ = lean_ctor_get(v___y_5329_, 0);
lean_inc_ref(v___y_5329_);
v_s_5332_ = lean_apply_2(v_fn_5328_, v___y_5329_, v___y_5330_);
v_pos_5333_ = lean_ctor_get(v_s_5332_, 2);
lean_inc(v_pos_5333_);
v_inputString_5334_ = lean_ctor_get(v_toInputContext_5331_, 0);
v___x_5335_ = lean_string_utf8_get(v_inputString_5334_, v_pos_5333_);
lean_dec(v_pos_5333_);
v___x_5336_ = 37;
v___x_5337_ = lean_uint32_dec_eq(v___x_5335_, v___x_5336_);
if (v___x_5337_ == 0)
{
lean_dec_ref(v___y_5329_);
return v_s_5332_;
}
else
{
lean_object* v___x_5338_; 
v___x_5338_ = l_Lean_Parser_tokenAntiquotFn(v___y_5329_, v_s_5332_);
return v___x_5338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object* v_p_5339_){
_start:
{
lean_object* v_info_5340_; lean_object* v_fn_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5349_; 
v_info_5340_ = lean_ctor_get(v_p_5339_, 0);
v_fn_5341_ = lean_ctor_get(v_p_5339_, 1);
v_isSharedCheck_5349_ = !lean_is_exclusive(v_p_5339_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5343_ = v_p_5339_;
v_isShared_5344_ = v_isSharedCheck_5349_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_fn_5341_);
lean_inc(v_info_5340_);
lean_dec(v_p_5339_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5349_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___f_5345_; lean_object* v___x_5347_; 
v___f_5345_ = lean_alloc_closure((void*)(l_Lean_Parser_tokenWithAntiquot___lam__0), 3, 1);
lean_closure_set(v___f_5345_, 0, v_fn_5341_);
if (v_isShared_5344_ == 0)
{
lean_ctor_set(v___x_5343_, 1, v___f_5345_);
v___x_5347_ = v___x_5343_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_info_5340_);
lean_ctor_set(v_reuseFailAlloc_5348_, 1, v___f_5345_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_symbol(lean_object* v_sym_5350_){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; 
v___x_5351_ = l_Lean_Parser_symbolNoAntiquot(v_sym_5350_);
v___x_5352_ = l_Lean_Parser_tokenWithAntiquot(v___x_5351_);
return v___x_5352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol(lean_object* v_sym_5355_, uint8_t v_includeIdent_5356_){
_start:
{
lean_object* v___x_5357_; lean_object* v___x_5358_; 
v___x_5357_ = l_Lean_Parser_nonReservedSymbolNoAntiquot(v_sym_5355_, v_includeIdent_5356_);
v___x_5358_ = l_Lean_Parser_tokenWithAntiquot(v___x_5357_);
return v___x_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nonReservedSymbol___boxed(lean_object* v_sym_5359_, lean_object* v_includeIdent_5360_){
_start:
{
uint8_t v_includeIdent_boxed_5361_; lean_object* v_res_5362_; 
v_includeIdent_boxed_5361_ = lean_unbox(v_includeIdent_5360_);
v_res_5362_ = l_Lean_Parser_nonReservedSymbol(v_sym_5359_, v_includeIdent_boxed_5361_);
return v_res_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___redArg(lean_object* v_sym_5363_, lean_object* v_asciiSym_5364_){
_start:
{
lean_object* v___x_5365_; lean_object* v___x_5366_; 
v___x_5365_ = l_Lean_Parser_unicodeSymbolNoAntiquot___redArg(v_sym_5363_, v_asciiSym_5364_);
v___x_5366_ = l_Lean_Parser_tokenWithAntiquot(v___x_5365_);
return v___x_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol(lean_object* v_sym_5367_, lean_object* v_asciiSym_5368_, uint8_t v_preserveForPP_5369_){
_start:
{
lean_object* v___x_5370_; 
v___x_5370_ = l_Lean_Parser_unicodeSymbol___redArg(v_sym_5367_, v_asciiSym_5368_);
return v___x_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_unicodeSymbol___boxed(lean_object* v_sym_5371_, lean_object* v_asciiSym_5372_, lean_object* v_preserveForPP_5373_){
_start:
{
uint8_t v_preserveForPP_boxed_5374_; lean_object* v_res_5375_; 
v_preserveForPP_boxed_5374_ = lean_unbox(v_preserveForPP_5373_);
v_res_5375_ = l_Lean_Parser_unicodeSymbol(v_sym_5371_, v_asciiSym_5372_, v_preserveForPP_boxed_5374_);
return v_res_5375_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__0(void){
_start:
{
lean_object* v___x_5376_; lean_object* v___x_5377_; 
v___x_5376_ = ((lean_object*)(l_Lean_Parser_tokenAntiquotFn___closed__4));
v___x_5377_ = l_Lean_Parser_symbol(v___x_5376_);
return v___x_5377_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__1(void){
_start:
{
lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; 
v___x_5378_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5379_ = lean_box(0);
v___x_5380_ = l_Lean_Parser_setExpected(v___x_5379_, v___x_5378_);
return v___x_5380_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__2(void){
_start:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; 
v___x_5381_ = ((lean_object*)(l_Lean_Parser_chFn___closed__1));
v___x_5382_ = l_Lean_Parser_checkNoWsBefore(v___x_5381_);
return v___x_5382_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__3(void){
_start:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5383_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__0, &l_Lean_Parser_mkAntiquot___closed__0_once, _init_l_Lean_Parser_mkAntiquot___closed__0);
v___x_5384_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__2, &l_Lean_Parser_mkAntiquot___closed__2_once, _init_l_Lean_Parser_mkAntiquot___closed__2);
v___x_5385_ = l_Lean_Parser_andthen(v___x_5384_, v___x_5383_);
return v___x_5385_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__4(void){
_start:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; 
v___x_5386_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__3, &l_Lean_Parser_mkAntiquot___closed__3_once, _init_l_Lean_Parser_mkAntiquot___closed__3);
v___x_5387_ = l_Lean_Parser_manyNoAntiquot(v___x_5386_);
return v___x_5387_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__6(void){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5389_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__5));
v___x_5390_ = l_Lean_Parser_checkNoWsBefore(v___x_5389_);
return v___x_5390_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__13(void){
_start:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5399_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__12));
v___x_5400_ = l_Lean_Parser_symbol(v___x_5399_);
return v___x_5400_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquot___closed__14(void){
_start:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5401_ = ((lean_object*)(l_Lean_Parser_pushNone));
v___x_5402_ = ((lean_object*)(l_Lean_Parser_checkNoImmediateColon));
v___x_5403_ = l_Lean_Parser_andthen(v___x_5402_, v___x_5401_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot(lean_object* v_name_5407_, lean_object* v_kind_5408_, uint8_t v_anonymous_5409_, uint8_t v_isPseudoKind_5410_){
_start:
{
lean_object* v___y_5412_; lean_object* v___y_5413_; lean_object* v___y_5426_; 
if (v_isPseudoKind_5410_ == 0)
{
lean_object* v___x_5444_; 
v___x_5444_ = lean_box(0);
v___y_5426_ = v___x_5444_;
goto v___jp_5425_;
}
else
{
lean_object* v___x_5445_; 
v___x_5445_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__16));
v___y_5426_ = v___x_5445_;
goto v___jp_5425_;
}
v___jp_5411_:
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; 
v___x_5414_ = l_Lean_Parser_maxPrec;
v___x_5415_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5416_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5417_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5418_ = l_Lean_Parser_antiquotExpr;
v___x_5419_ = l_Lean_Parser_andthen(v___x_5418_, v___y_5413_);
v___x_5420_ = l_Lean_Parser_andthen(v___x_5417_, v___x_5419_);
v___x_5421_ = l_Lean_Parser_andthen(v___x_5416_, v___x_5420_);
v___x_5422_ = l_Lean_Parser_andthen(v___x_5415_, v___x_5421_);
v___x_5423_ = l_Lean_Parser_atomic(v___x_5422_);
v___x_5424_ = l_Lean_Parser_leadingNode(v___y_5412_, v___x_5414_, v___x_5423_);
return v___x_5424_;
}
v___jp_5425_:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v_kind_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; uint8_t v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v_nameP_5441_; 
lean_inc(v___y_5426_);
v___x_5427_ = l_Lean_Name_append(v_kind_5408_, v___y_5426_);
v___x_5428_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__8));
v_kind_5429_ = l_Lean_Name_append(v___x_5427_, v___x_5428_);
v___x_5430_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__10));
v___x_5431_ = ((lean_object*)(l_Lean_Parser_mkAntiquot___closed__11));
v___x_5432_ = lean_string_append(v___x_5431_, v_name_5407_);
v___x_5433_ = ((lean_object*)(l_Lean_Parser_chFn___closed__0));
v___x_5434_ = lean_string_append(v___x_5432_, v___x_5433_);
v___x_5435_ = l_Lean_Parser_checkNoWsBefore(v___x_5434_);
v___x_5436_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__13, &l_Lean_Parser_mkAntiquot___closed__13_once, _init_l_Lean_Parser_mkAntiquot___closed__13);
v___x_5437_ = 0;
v___x_5438_ = l_Lean_Parser_nonReservedSymbol(v_name_5407_, v___x_5437_);
v___x_5439_ = l_Lean_Parser_andthen(v___x_5436_, v___x_5438_);
v___x_5440_ = l_Lean_Parser_andthen(v___x_5435_, v___x_5439_);
v_nameP_5441_ = l_Lean_Parser_node(v___x_5430_, v___x_5440_);
if (v_anonymous_5409_ == 0)
{
v___y_5412_ = v_kind_5429_;
v___y_5413_ = v_nameP_5441_;
goto v___jp_5411_;
}
else
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__14, &l_Lean_Parser_mkAntiquot___closed__14_once, _init_l_Lean_Parser_mkAntiquot___closed__14);
v___x_5443_ = l_Lean_Parser_orelse(v_nameP_5441_, v___x_5442_);
v___y_5412_ = v_kind_5429_;
v___y_5413_ = v___x_5443_;
goto v___jp_5411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquot___boxed(lean_object* v_name_5446_, lean_object* v_kind_5447_, lean_object* v_anonymous_5448_, lean_object* v_isPseudoKind_5449_){
_start:
{
uint8_t v_anonymous_boxed_5450_; uint8_t v_isPseudoKind_boxed_5451_; lean_object* v_res_5452_; 
v_anonymous_boxed_5450_ = lean_unbox(v_anonymous_5448_);
v_isPseudoKind_boxed_5451_ = lean_unbox(v_isPseudoKind_5449_);
v_res_5452_ = l_Lean_Parser_mkAntiquot(v_name_5446_, v_kind_5447_, v_anonymous_boxed_5450_, v_isPseudoKind_boxed_5451_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1(){
_start:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; 
v___x_5460_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__1));
v___x_5461_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___closed__2));
v___x_5462_ = l_Lean_addBuiltinDocString(v___x_5460_, v___x_5461_);
return v___x_5462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1___boxed(lean_object* v_a_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquot___regBuiltin_Lean_Parser_mkAntiquot_docString__1();
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn(lean_object* v_antiquotP_5465_, lean_object* v_p_5466_, uint8_t v_antiquotBehavior_5467_, lean_object* v_c_5468_, lean_object* v_s_5469_){
_start:
{
lean_object* v_toInputContext_5470_; lean_object* v_pos_5471_; lean_object* v_inputString_5472_; uint32_t v___x_5473_; uint32_t v___x_5474_; uint8_t v___x_5475_; 
v_toInputContext_5470_ = lean_ctor_get(v_c_5468_, 0);
v_pos_5471_ = lean_ctor_get(v_s_5469_, 2);
v_inputString_5472_ = lean_ctor_get(v_toInputContext_5470_, 0);
v___x_5473_ = lean_string_utf8_get(v_inputString_5472_, v_pos_5471_);
v___x_5474_ = 36;
v___x_5475_ = lean_uint32_dec_eq(v___x_5473_, v___x_5474_);
if (v___x_5475_ == 0)
{
lean_object* v___x_5476_; 
lean_dec_ref(v_antiquotP_5465_);
v___x_5476_ = lean_apply_2(v_p_5466_, v_c_5468_, v_s_5469_);
return v___x_5476_;
}
else
{
lean_object* v___x_5477_; 
v___x_5477_ = l_Lean_Parser_orelseFnCore(v_antiquotP_5465_, v_p_5466_, v_antiquotBehavior_5467_, v_c_5468_, v_s_5469_);
return v___x_5477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotFn___boxed(lean_object* v_antiquotP_5478_, lean_object* v_p_5479_, lean_object* v_antiquotBehavior_5480_, lean_object* v_c_5481_, lean_object* v_s_5482_){
_start:
{
uint8_t v_antiquotBehavior_boxed_5483_; lean_object* v_res_5484_; 
v_antiquotBehavior_boxed_5483_ = lean_unbox(v_antiquotBehavior_5480_);
v_res_5484_ = l_Lean_Parser_withAntiquotFn(v_antiquotP_5478_, v_p_5479_, v_antiquotBehavior_boxed_5483_, v_c_5481_, v_s_5482_);
return v_res_5484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquot(lean_object* v_antiquotP_5485_, lean_object* v_p_5486_){
_start:
{
lean_object* v_info_5487_; lean_object* v_fn_5488_; lean_object* v_info_5489_; lean_object* v_fn_5490_; lean_object* v___x_5492_; uint8_t v_isShared_5493_; uint8_t v_isSharedCheck_5501_; 
v_info_5487_ = lean_ctor_get(v_antiquotP_5485_, 0);
lean_inc_ref(v_info_5487_);
v_fn_5488_ = lean_ctor_get(v_antiquotP_5485_, 1);
lean_inc_ref(v_fn_5488_);
lean_dec_ref(v_antiquotP_5485_);
v_info_5489_ = lean_ctor_get(v_p_5486_, 0);
v_fn_5490_ = lean_ctor_get(v_p_5486_, 1);
v_isSharedCheck_5501_ = !lean_is_exclusive(v_p_5486_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5492_ = v_p_5486_;
v_isShared_5493_ = v_isSharedCheck_5501_;
goto v_resetjp_5491_;
}
else
{
lean_inc(v_fn_5490_);
lean_inc(v_info_5489_);
lean_dec(v_p_5486_);
v___x_5492_ = lean_box(0);
v_isShared_5493_ = v_isSharedCheck_5501_;
goto v_resetjp_5491_;
}
v_resetjp_5491_:
{
lean_object* v___x_5494_; uint8_t v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5499_; 
v___x_5494_ = l_Lean_Parser_orelseInfo(v_info_5487_, v_info_5489_);
v___x_5495_ = 1;
v___x_5496_ = lean_box(v___x_5495_);
v___x_5497_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5497_, 0, v_fn_5488_);
lean_closure_set(v___x_5497_, 1, v_fn_5490_);
lean_closure_set(v___x_5497_, 2, v___x_5496_);
if (v_isShared_5493_ == 0)
{
lean_ctor_set(v___x_5492_, 1, v___x_5497_);
lean_ctor_set(v___x_5492_, 0, v___x_5494_);
v___x_5499_ = v___x_5492_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v___x_5494_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v___x_5497_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1(){
_start:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5509_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__1));
v___x_5510_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___closed__2));
v___x_5511_ = l_Lean_addBuiltinDocString(v___x_5509_, v___x_5510_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1___boxed(lean_object* v_a_5512_){
_start:
{
lean_object* v_res_5513_; 
v_res_5513_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquot___regBuiltin_Lean_Parser_withAntiquot_docString__1();
return v_res_5513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotAcceptLhs(lean_object* v_antiquotP_5514_, lean_object* v_p_5515_){
_start:
{
lean_object* v_info_5516_; lean_object* v_fn_5517_; lean_object* v_info_5518_; lean_object* v_fn_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5530_; 
v_info_5516_ = lean_ctor_get(v_antiquotP_5514_, 0);
lean_inc_ref(v_info_5516_);
v_fn_5517_ = lean_ctor_get(v_antiquotP_5514_, 1);
lean_inc_ref(v_fn_5517_);
lean_dec_ref(v_antiquotP_5514_);
v_info_5518_ = lean_ctor_get(v_p_5515_, 0);
v_fn_5519_ = lean_ctor_get(v_p_5515_, 1);
v_isSharedCheck_5530_ = !lean_is_exclusive(v_p_5515_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5521_ = v_p_5515_;
v_isShared_5522_ = v_isSharedCheck_5530_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_fn_5519_);
lean_inc(v_info_5518_);
lean_dec(v_p_5515_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5530_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; uint8_t v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5528_; 
v___x_5523_ = l_Lean_Parser_orelseInfo(v_info_5516_, v_info_5518_);
v___x_5524_ = 0;
v___x_5525_ = lean_box(v___x_5524_);
v___x_5526_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotFn___boxed), 5, 3);
lean_closure_set(v___x_5526_, 0, v_fn_5517_);
lean_closure_set(v___x_5526_, 1, v_fn_5519_);
lean_closure_set(v___x_5526_, 2, v___x_5525_);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 1, v___x_5526_);
lean_ctor_set(v___x_5521_, 0, v___x_5523_);
v___x_5528_ = v___x_5521_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5523_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v___x_5526_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1(){
_start:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; 
v___x_5538_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__1));
v___x_5539_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___closed__2));
v___x_5540_ = l_Lean_addBuiltinDocString(v___x_5538_, v___x_5539_);
return v___x_5540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1___boxed(lean_object* v_a_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotAcceptLhs___regBuiltin_Lean_Parser_withAntiquotAcceptLhs_docString__1();
return v_res_5542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withoutInfo(lean_object* v_p_5543_){
_start:
{
lean_object* v_fn_5544_; lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5552_; 
v_fn_5544_ = lean_ctor_get(v_p_5543_, 1);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_p_5543_);
if (v_isSharedCheck_5552_ == 0)
{
lean_object* v_unused_5553_; 
v_unused_5553_ = lean_ctor_get(v_p_5543_, 0);
lean_dec(v_unused_5553_);
v___x_5546_ = v_p_5543_;
v_isShared_5547_ = v_isSharedCheck_5552_;
goto v_resetjp_5545_;
}
else
{
lean_inc(v_fn_5544_);
lean_dec(v_p_5543_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5552_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v___x_5548_; lean_object* v___x_5550_; 
v___x_5548_ = ((lean_object*)(l_Lean_Parser_errorAtSavedPos___closed__0));
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 0, v___x_5548_);
v___x_5550_ = v___x_5546_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_fn_5544_);
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
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__2(void){
_start:
{
lean_object* v___x_5557_; lean_object* v___x_5558_; 
v___x_5557_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__1));
v___x_5558_ = l_Lean_Parser_symbol(v___x_5557_);
return v___x_5558_;
}
}
static lean_object* _init_l_Lean_Parser_mkAntiquotSplice___closed__3(void){
_start:
{
lean_object* v___x_5559_; lean_object* v___x_5560_; 
v___x_5559_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_dbgTraceStateFn_spec__0___closed__2));
v___x_5560_ = l_Lean_Parser_symbol(v___x_5559_);
return v___x_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkAntiquotSplice(lean_object* v_kind_5561_, lean_object* v_p_5562_, lean_object* v_suffix_5563_){
_start:
{
lean_object* v___x_5564_; lean_object* v_kind_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; 
v___x_5564_ = ((lean_object*)(l_Lean_Parser_mkAntiquotSplice___closed__1));
v_kind_5565_ = l_Lean_Name_append(v_kind_5561_, v___x_5564_);
v___x_5566_ = l_Lean_Parser_maxPrec;
v___x_5567_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__1, &l_Lean_Parser_mkAntiquot___closed__1_once, _init_l_Lean_Parser_mkAntiquot___closed__1);
v___x_5568_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__4, &l_Lean_Parser_mkAntiquot___closed__4_once, _init_l_Lean_Parser_mkAntiquot___closed__4);
v___x_5569_ = lean_obj_once(&l_Lean_Parser_mkAntiquot___closed__6, &l_Lean_Parser_mkAntiquot___closed__6_once, _init_l_Lean_Parser_mkAntiquot___closed__6);
v___x_5570_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__2, &l_Lean_Parser_mkAntiquotSplice___closed__2_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__2);
v___x_5571_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5572_ = l_Lean_Parser_node(v___x_5571_, v_p_5562_);
v___x_5573_ = lean_obj_once(&l_Lean_Parser_mkAntiquotSplice___closed__3, &l_Lean_Parser_mkAntiquotSplice___closed__3_once, _init_l_Lean_Parser_mkAntiquotSplice___closed__3);
v___x_5574_ = l_Lean_Parser_andthen(v___x_5573_, v_suffix_5563_);
v___x_5575_ = l_Lean_Parser_andthen(v___x_5572_, v___x_5574_);
v___x_5576_ = l_Lean_Parser_andthen(v___x_5570_, v___x_5575_);
v___x_5577_ = l_Lean_Parser_andthen(v___x_5569_, v___x_5576_);
v___x_5578_ = l_Lean_Parser_andthen(v___x_5568_, v___x_5577_);
v___x_5579_ = l_Lean_Parser_andthen(v___x_5567_, v___x_5578_);
v___x_5580_ = l_Lean_Parser_atomic(v___x_5579_);
v___x_5581_ = l_Lean_Parser_leadingNode(v_kind_5565_, v___x_5566_, v___x_5580_);
return v___x_5581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1(){
_start:
{
lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; 
v___x_5589_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__1));
v___x_5590_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___closed__2));
v___x_5591_ = l_Lean_addBuiltinDocString(v___x_5589_, v___x_5590_);
return v___x_5591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1___boxed(lean_object* v_a_5592_){
_start:
{
lean_object* v_res_5593_; 
v_res_5593_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkAntiquotSplice___regBuiltin_Lean_Parser_mkAntiquotSplice_docString__1();
return v_res_5593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(lean_object* v_kind_5597_, lean_object* v_suffix_5598_, lean_object* v_c_5599_, lean_object* v_s_5600_){
_start:
{
lean_object* v_pos_5601_; lean_object* v_iniSz_5602_; lean_object* v_s_5603_; lean_object* v_stxStack_5604_; lean_object* v_errorMsg_5605_; lean_object* v___x_5606_; uint8_t v___x_5607_; 
v_pos_5601_ = lean_ctor_get(v_s_5600_, 2);
lean_inc(v_pos_5601_);
v_iniSz_5602_ = l_Lean_Parser_ParserState_stackSize(v_s_5600_);
v_s_5603_ = lean_apply_2(v_suffix_5598_, v_c_5599_, v_s_5600_);
v_stxStack_5604_ = lean_ctor_get(v_s_5603_, 0);
lean_inc_ref(v_stxStack_5604_);
v_errorMsg_5605_ = lean_ctor_get(v_s_5603_, 4);
lean_inc(v_errorMsg_5605_);
v___x_5606_ = lean_box(0);
v___x_5607_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5605_, v___x_5606_);
lean_dec(v_errorMsg_5605_);
if (v___x_5607_ == 0)
{
lean_object* v___x_5608_; 
lean_dec_ref(v_stxStack_5604_);
lean_dec(v_kind_5597_);
v___x_5608_ = l_Lean_Parser_ParserState_restore(v_s_5603_, v_iniSz_5602_, v_pos_5601_);
lean_dec(v_iniSz_5602_);
return v___x_5608_;
}
else
{
lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; 
lean_dec(v_iniSz_5602_);
lean_dec(v_pos_5601_);
v___x_5609_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn___closed__1));
v___x_5610_ = l_Lean_Name_append(v_kind_5597_, v___x_5609_);
v___x_5611_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_5604_);
lean_dec_ref(v_stxStack_5604_);
v___x_5612_ = lean_unsigned_to_nat(2u);
v___x_5613_ = lean_nat_sub(v___x_5611_, v___x_5612_);
lean_dec(v___x_5611_);
v___x_5614_ = l_Lean_Parser_ParserState_mkNode(v_s_5603_, v___x_5610_, v___x_5613_);
lean_dec(v___x_5613_);
return v___x_5614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice___lam__0(lean_object* v_fn_5615_, lean_object* v_kind_5616_, lean_object* v_fn_5617_, lean_object* v_c_5618_, lean_object* v_s_5619_){
_start:
{
lean_object* v_s_5620_; lean_object* v_stxStack_5621_; lean_object* v_errorMsg_5622_; lean_object* v___x_5623_; uint8_t v___x_5624_; 
lean_inc_ref(v_c_5618_);
v_s_5620_ = lean_apply_2(v_fn_5615_, v_c_5618_, v_s_5619_);
v_stxStack_5621_ = lean_ctor_get(v_s_5620_, 0);
lean_inc_ref(v_stxStack_5621_);
v_errorMsg_5622_ = lean_ctor_get(v_s_5620_, 4);
lean_inc(v_errorMsg_5622_);
v___x_5623_ = lean_box(0);
v___x_5624_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5622_, v___x_5623_);
lean_dec(v_errorMsg_5622_);
if (v___x_5624_ == 0)
{
lean_dec_ref(v_stxStack_5621_);
lean_dec_ref(v_c_5618_);
lean_dec_ref(v_fn_5617_);
lean_dec(v_kind_5616_);
return v_s_5620_;
}
else
{
lean_object* v___x_5625_; uint8_t v___x_5626_; 
v___x_5625_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5621_);
lean_dec_ref(v_stxStack_5621_);
v___x_5626_ = l_Lean_Syntax_isAntiquots(v___x_5625_);
if (v___x_5626_ == 0)
{
lean_dec_ref(v_c_5618_);
lean_dec_ref(v_fn_5617_);
lean_dec(v_kind_5616_);
return v_s_5620_;
}
else
{
lean_object* v___x_5627_; 
v___x_5627_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSpliceFn(v_kind_5616_, v_fn_5617_, v_c_5618_, v_s_5620_);
return v___x_5627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSuffixSplice(lean_object* v_kind_5628_, lean_object* v_p_5629_, lean_object* v_suffix_5630_){
_start:
{
lean_object* v_info_5631_; lean_object* v_fn_5632_; lean_object* v_info_5633_; lean_object* v_fn_5634_; lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5643_; 
v_info_5631_ = lean_ctor_get(v_p_5629_, 0);
lean_inc_ref(v_info_5631_);
v_fn_5632_ = lean_ctor_get(v_p_5629_, 1);
lean_inc_ref(v_fn_5632_);
lean_dec_ref(v_p_5629_);
v_info_5633_ = lean_ctor_get(v_suffix_5630_, 0);
v_fn_5634_ = lean_ctor_get(v_suffix_5630_, 1);
v_isSharedCheck_5643_ = !lean_is_exclusive(v_suffix_5630_);
if (v_isSharedCheck_5643_ == 0)
{
v___x_5636_ = v_suffix_5630_;
v_isShared_5637_ = v_isSharedCheck_5643_;
goto v_resetjp_5635_;
}
else
{
lean_inc(v_fn_5634_);
lean_inc(v_info_5633_);
lean_dec(v_suffix_5630_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5643_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___f_5638_; lean_object* v___x_5639_; lean_object* v___x_5641_; 
v___f_5638_ = lean_alloc_closure((void*)(l_Lean_Parser_withAntiquotSuffixSplice___lam__0), 5, 3);
lean_closure_set(v___f_5638_, 0, v_fn_5632_);
lean_closure_set(v___f_5638_, 1, v_kind_5628_);
lean_closure_set(v___f_5638_, 2, v_fn_5634_);
v___x_5639_ = l_Lean_Parser_andthenInfo(v_info_5631_, v_info_5633_);
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 1, v___f_5638_);
lean_ctor_set(v___x_5636_, 0, v___x_5639_);
v___x_5641_ = v___x_5636_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5642_; 
v_reuseFailAlloc_5642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5642_, 0, v___x_5639_);
lean_ctor_set(v_reuseFailAlloc_5642_, 1, v___f_5638_);
v___x_5641_ = v_reuseFailAlloc_5642_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
return v___x_5641_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1(){
_start:
{
lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; 
v___x_5651_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__1));
v___x_5652_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___closed__2));
v___x_5653_ = l_Lean_addBuiltinDocString(v___x_5651_, v___x_5652_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1___boxed(lean_object* v_a_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l___private_Lean_Parser_Basic_0__Lean_Parser_withAntiquotSuffixSplice___regBuiltin_Lean_Parser_withAntiquotSuffixSplice_docString__1();
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object* v_kind_5656_, lean_object* v_p_5657_, lean_object* v_suffix_5658_){
_start:
{
lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; 
lean_inc_ref(v_p_5657_);
v___x_5659_ = l_Lean_Parser_withoutInfo(v_p_5657_);
lean_inc_ref(v_suffix_5658_);
lean_inc(v_kind_5656_);
v___x_5660_ = l_Lean_Parser_mkAntiquotSplice(v_kind_5656_, v___x_5659_, v_suffix_5658_);
v___x_5661_ = l_Lean_Parser_withAntiquotSuffixSplice(v_kind_5656_, v_p_5657_, v_suffix_5658_);
v___x_5662_ = l_Lean_Parser_withAntiquot(v___x_5660_, v___x_5661_);
return v___x_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object* v_name_5663_, lean_object* v_kind_5664_, lean_object* v_p_5665_, uint8_t v_anonymous_5666_){
_start:
{
uint8_t v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; 
v___x_5667_ = 0;
lean_inc(v_kind_5664_);
v___x_5668_ = l_Lean_Parser_mkAntiquot(v_name_5663_, v_kind_5664_, v_anonymous_5666_, v___x_5667_);
v___x_5669_ = l_Lean_Parser_node(v_kind_5664_, v_p_5665_);
v___x_5670_ = l_Lean_Parser_withAntiquot(v___x_5668_, v___x_5669_);
return v___x_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_nodeWithAntiquot___boxed(lean_object* v_name_5671_, lean_object* v_kind_5672_, lean_object* v_p_5673_, lean_object* v_anonymous_5674_){
_start:
{
uint8_t v_anonymous_boxed_5675_; lean_object* v_res_5676_; 
v_anonymous_boxed_5675_ = lean_unbox(v_anonymous_5674_);
v_res_5676_ = l_Lean_Parser_nodeWithAntiquot(v_name_5671_, v_kind_5672_, v_p_5673_, v_anonymous_boxed_5675_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepByElemParser(lean_object* v_p_5681_, lean_object* v_sep_5682_){
_start:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v_str_5687_; lean_object* v_startInclusive_5688_; lean_object* v_endExclusive_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; 
v___x_5683_ = lean_unsigned_to_nat(0u);
v___x_5684_ = lean_string_utf8_byte_size(v_sep_5682_);
v___x_5685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5685_, 0, v_sep_5682_);
lean_ctor_set(v___x_5685_, 1, v___x_5683_);
lean_ctor_set(v___x_5685_, 2, v___x_5684_);
v___x_5686_ = l_String_Slice_trimAscii(v___x_5685_);
v_str_5687_ = lean_ctor_get(v___x_5686_, 0);
lean_inc_ref(v_str_5687_);
v_startInclusive_5688_ = lean_ctor_get(v___x_5686_, 1);
lean_inc(v_startInclusive_5688_);
v_endExclusive_5689_ = lean_ctor_get(v___x_5686_, 2);
lean_inc(v_endExclusive_5689_);
lean_dec_ref(v___x_5686_);
v___x_5690_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__1));
v___x_5691_ = lean_string_utf8_extract_fast(v_str_5687_, v_startInclusive_5688_, v_endExclusive_5689_);
lean_dec(v_endExclusive_5689_);
lean_dec(v_startInclusive_5688_);
lean_dec_ref(v_str_5687_);
v___x_5692_ = ((lean_object*)(l_Lean_Parser_sepByElemParser___closed__2));
v___x_5693_ = lean_string_append(v___x_5691_, v___x_5692_);
v___x_5694_ = l_Lean_Parser_symbol(v___x_5693_);
v___x_5695_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_5690_, v_p_5681_, v___x_5694_);
return v___x_5695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy(lean_object* v_p_5696_, lean_object* v_sep_5697_, lean_object* v_psep_5698_, uint8_t v_allowTrailingSep_5699_){
_start:
{
lean_object* v___x_5700_; lean_object* v___x_5701_; 
v___x_5700_ = l_Lean_Parser_sepByElemParser(v_p_5696_, v_sep_5697_);
v___x_5701_ = l_Lean_Parser_sepByNoAntiquot(v___x_5700_, v_psep_5698_, v_allowTrailingSep_5699_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy___boxed(lean_object* v_p_5702_, lean_object* v_sep_5703_, lean_object* v_psep_5704_, lean_object* v_allowTrailingSep_5705_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5706_; lean_object* v_res_5707_; 
v_allowTrailingSep_boxed_5706_ = lean_unbox(v_allowTrailingSep_5705_);
v_res_5707_ = l_Lean_Parser_sepBy(v_p_5702_, v_sep_5703_, v_psep_5704_, v_allowTrailingSep_boxed_5706_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1(lean_object* v_p_5708_, lean_object* v_sep_5709_, lean_object* v_psep_5710_, uint8_t v_allowTrailingSep_5711_){
_start:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; 
v___x_5712_ = l_Lean_Parser_sepByElemParser(v_p_5708_, v_sep_5709_);
v___x_5713_ = l_Lean_Parser_sepBy1NoAntiquot(v___x_5712_, v_psep_5710_, v_allowTrailingSep_5711_);
return v___x_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_sepBy1___boxed(lean_object* v_p_5714_, lean_object* v_sep_5715_, lean_object* v_psep_5716_, lean_object* v_allowTrailingSep_5717_){
_start:
{
uint8_t v_allowTrailingSep_boxed_5718_; lean_object* v_res_5719_; 
v_allowTrailingSep_boxed_5718_ = lean_unbox(v_allowTrailingSep_5717_);
v_res_5719_ = l_Lean_Parser_sepBy1(v_p_5714_, v_sep_5715_, v_psep_5716_, v_allowTrailingSep_boxed_5718_);
return v_res_5719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(lean_object* v_s_5720_, lean_object* v_iniSz_5721_){
_start:
{
lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; uint8_t v___x_5725_; 
v___x_5722_ = l_Lean_Parser_ParserState_stackSize(v_s_5720_);
v___x_5723_ = lean_unsigned_to_nat(1u);
v___x_5724_ = lean_nat_add(v_iniSz_5721_, v___x_5723_);
v___x_5725_ = lean_nat_dec_eq(v___x_5722_, v___x_5724_);
lean_dec(v___x_5724_);
lean_dec(v___x_5722_);
if (v___x_5725_ == 0)
{
lean_object* v___x_5726_; lean_object* v___x_5727_; 
v___x_5726_ = ((lean_object*)(l_Lean_Parser_optionalFn___closed__1));
v___x_5727_ = l_Lean_Parser_ParserState_mkNode(v_s_5720_, v___x_5726_, v_iniSz_5721_);
return v___x_5727_;
}
else
{
return v_s_5720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult___boxed(lean_object* v_s_5728_, lean_object* v_iniSz_5729_){
_start:
{
lean_object* v_res_5730_; 
v_res_5730_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5728_, v_iniSz_5729_);
lean_dec(v_iniSz_5729_);
return v_res_5730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux(lean_object* v_kind_5731_, lean_object* v_tables_5732_, uint8_t v_behavior_5733_, lean_object* v_c_5734_, lean_object* v_s_5735_){
_start:
{
lean_object* v_leadingTable_5736_; lean_object* v_leadingParsers_5737_; lean_object* v_iniSz_5738_; lean_object* v___x_5739_; lean_object* v_fst_5740_; lean_object* v_snd_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5762_; 
v_leadingTable_5736_ = lean_ctor_get(v_tables_5732_, 0);
lean_inc(v_leadingTable_5736_);
v_leadingParsers_5737_ = lean_ctor_get(v_tables_5732_, 1);
lean_inc(v_leadingParsers_5737_);
lean_dec_ref(v_tables_5732_);
v_iniSz_5738_ = l_Lean_Parser_ParserState_stackSize(v_s_5735_);
lean_inc_ref(v_c_5734_);
v___x_5739_ = l_Lean_Parser_indexed___redArg(v_leadingTable_5736_, v_c_5734_, v_s_5735_, v_behavior_5733_);
lean_dec(v_leadingTable_5736_);
v_fst_5740_ = lean_ctor_get(v___x_5739_, 0);
v_snd_5741_ = lean_ctor_get(v___x_5739_, 1);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5739_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5743_ = v___x_5739_;
v_isShared_5744_ = v_isSharedCheck_5762_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_snd_5741_);
lean_inc(v_fst_5740_);
lean_dec(v___x_5739_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5762_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v_errorMsg_5745_; lean_object* v___x_5746_; uint8_t v___x_5747_; 
v_errorMsg_5745_ = lean_ctor_get(v_fst_5740_, 4);
v___x_5746_ = lean_box(0);
v___x_5747_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5745_, v___x_5746_);
if (v___x_5747_ == 0)
{
lean_del_object(v___x_5743_);
lean_dec(v_snd_5741_);
lean_dec(v_iniSz_5738_);
lean_dec(v_leadingParsers_5737_);
lean_dec_ref(v_c_5734_);
lean_dec(v_kind_5731_);
return v_fst_5740_;
}
else
{
lean_object* v_ps_5748_; uint8_t v___x_5749_; 
v_ps_5748_ = l_List_appendTR___redArg(v_leadingParsers_5737_, v_snd_5741_);
v___x_5749_ = l_List_isEmpty___redArg(v_ps_5748_);
if (v___x_5749_ == 0)
{
lean_object* v_s_5750_; lean_object* v___x_5751_; 
lean_del_object(v___x_5743_);
lean_dec(v_kind_5731_);
v_s_5750_ = l_Lean_Parser_longestMatchFn(v___x_5746_, v_ps_5748_, v_c_5734_, v_fst_5740_);
v___x_5751_ = l___private_Lean_Parser_Basic_0__Lean_Parser_mkResult(v_s_5750_, v_iniSz_5738_);
lean_dec(v_iniSz_5738_);
return v___x_5751_;
}
else
{
lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5755_; 
lean_dec(v_ps_5748_);
lean_dec(v_iniSz_5738_);
v___x_5752_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_5731_, v___x_5749_);
v___x_5753_ = lean_box(0);
lean_inc_ref(v___x_5752_);
if (v_isShared_5744_ == 0)
{
lean_ctor_set_tag(v___x_5743_, 1);
lean_ctor_set(v___x_5743_, 1, v___x_5753_);
lean_ctor_set(v___x_5743_, 0, v___x_5752_);
v___x_5755_ = v___x_5743_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v___x_5752_);
lean_ctor_set(v_reuseFailAlloc_5761_, 1, v___x_5753_);
v___x_5755_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
lean_object* v_s_5756_; lean_object* v_errorMsg_5757_; uint8_t v___x_5758_; 
v_s_5756_ = l_Lean_Parser_tokenFn(v___x_5755_, v_c_5734_, v_fst_5740_);
v_errorMsg_5757_ = lean_ctor_get(v_s_5756_, 4);
v___x_5758_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5757_, v___x_5746_);
if (v___x_5758_ == 0)
{
lean_dec_ref(v___x_5752_);
return v_s_5756_;
}
else
{
lean_object* v___x_5759_; lean_object* v___x_5760_; 
v___x_5759_ = lean_unsigned_to_nat(0u);
v___x_5760_ = l_Lean_Parser_ParserState_mkUnexpectedTokenError(v_s_5756_, v___x_5752_, v___x_5759_);
return v___x_5760_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParserAux___boxed(lean_object* v_kind_5763_, lean_object* v_tables_5764_, lean_object* v_behavior_5765_, lean_object* v_c_5766_, lean_object* v_s_5767_){
_start:
{
uint8_t v_behavior_boxed_5768_; lean_object* v_res_5769_; 
v_behavior_boxed_5768_ = lean_unbox(v_behavior_5765_);
v_res_5769_ = l_Lean_Parser_leadingParserAux(v_kind_5763_, v_tables_5764_, v_behavior_boxed_5768_, v_c_5766_, v_s_5767_);
return v_res_5769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser(lean_object* v_kind_5770_, lean_object* v_tables_5771_, uint8_t v_behavior_5772_, lean_object* v_antiquotParser_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_){
_start:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; uint8_t v___x_5778_; lean_object* v___x_5779_; 
v___x_5776_ = lean_box(v_behavior_5772_);
v___x_5777_ = lean_alloc_closure((void*)(l_Lean_Parser_leadingParserAux___boxed), 5, 3);
lean_closure_set(v___x_5777_, 0, v_kind_5770_);
lean_closure_set(v___x_5777_, 1, v_tables_5771_);
lean_closure_set(v___x_5777_, 2, v___x_5776_);
v___x_5778_ = 0;
v___x_5779_ = l_Lean_Parser_withAntiquotFn(v_antiquotParser_5773_, v___x_5777_, v___x_5778_, v_a_5774_, v_a_5775_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_leadingParser___boxed(lean_object* v_kind_5780_, lean_object* v_tables_5781_, lean_object* v_behavior_5782_, lean_object* v_antiquotParser_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_){
_start:
{
uint8_t v_behavior_boxed_5786_; lean_object* v_res_5787_; 
v_behavior_boxed_5786_ = lean_unbox(v_behavior_5782_);
v_res_5787_ = l_Lean_Parser_leadingParser(v_kind_5780_, v_tables_5781_, v_behavior_boxed_5786_, v_antiquotParser_5783_, v_a_5784_, v_a_5785_);
return v_res_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoopStep(lean_object* v_tables_5788_, lean_object* v_left_5789_, lean_object* v_ps_5790_, lean_object* v_c_5791_, lean_object* v_s_5792_){
_start:
{
lean_object* v_trailingParsers_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; 
v_trailingParsers_5793_ = lean_ctor_get(v_tables_5788_, 3);
lean_inc(v_trailingParsers_5793_);
lean_dec_ref(v_tables_5788_);
v___x_5794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5794_, 0, v_left_5789_);
v___x_5795_ = l_List_appendTR___redArg(v_ps_5790_, v_trailingParsers_5793_);
v___x_5796_ = l_Lean_Parser_longestMatchFn(v___x_5794_, v___x_5795_, v_c_5791_, v_s_5792_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_trailingLoop(lean_object* v_tables_5797_, lean_object* v_c_5798_, lean_object* v_s_5799_){
_start:
{
lean_object* v_pos_5800_; lean_object* v_trailingTable_5801_; lean_object* v_trailingParsers_5802_; lean_object* v_iniSz_5803_; uint8_t v___x_5804_; lean_object* v___x_5805_; lean_object* v_fst_5806_; lean_object* v_snd_5807_; lean_object* v_stxStack_5808_; lean_object* v_errorMsg_5809_; lean_object* v___x_5824_; uint8_t v___x_5825_; 
v_pos_5800_ = lean_ctor_get(v_s_5799_, 2);
lean_inc(v_pos_5800_);
v_trailingTable_5801_ = lean_ctor_get(v_tables_5797_, 2);
v_trailingParsers_5802_ = lean_ctor_get(v_tables_5797_, 3);
v_iniSz_5803_ = l_Lean_Parser_ParserState_stackSize(v_s_5799_);
v___x_5804_ = 0;
lean_inc_ref(v_c_5798_);
v___x_5805_ = l_Lean_Parser_indexed___redArg(v_trailingTable_5801_, v_c_5798_, v_s_5799_, v___x_5804_);
v_fst_5806_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_fst_5806_);
v_snd_5807_ = lean_ctor_get(v___x_5805_, 1);
lean_inc(v_snd_5807_);
lean_dec_ref(v___x_5805_);
v_stxStack_5808_ = lean_ctor_get(v_fst_5806_, 0);
v_errorMsg_5809_ = lean_ctor_get(v_fst_5806_, 4);
v___x_5824_ = lean_box(0);
v___x_5825_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5809_, v___x_5824_);
if (v___x_5825_ == 0)
{
lean_object* v___x_5826_; 
lean_dec(v_snd_5807_);
lean_dec_ref(v_c_5798_);
lean_dec_ref(v_tables_5797_);
v___x_5826_ = l_Lean_Parser_ParserState_restore(v_fst_5806_, v_iniSz_5803_, v_pos_5800_);
lean_dec(v_iniSz_5803_);
return v___x_5826_;
}
else
{
uint8_t v___x_5827_; 
v___x_5827_ = l_List_isEmpty___redArg(v_snd_5807_);
if (v___x_5827_ == 0)
{
goto v___jp_5810_;
}
else
{
uint8_t v___x_5828_; 
v___x_5828_ = l_List_isEmpty___redArg(v_trailingParsers_5802_);
if (v___x_5828_ == 0)
{
goto v___jp_5810_;
}
else
{
lean_dec(v_snd_5807_);
lean_dec(v_iniSz_5803_);
lean_dec(v_pos_5800_);
lean_dec_ref(v_c_5798_);
lean_dec_ref(v_tables_5797_);
return v_fst_5806_;
}
}
}
v___jp_5810_:
{
lean_object* v_left_5811_; lean_object* v_s_5812_; lean_object* v_s_5813_; lean_object* v_pos_5814_; lean_object* v_errorMsg_5815_; lean_object* v___x_5816_; uint8_t v___x_5817_; 
v_left_5811_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_5808_);
v_s_5812_ = l_Lean_Parser_ParserState_popSyntax(v_fst_5806_);
lean_inc_ref(v_c_5798_);
lean_inc(v_left_5811_);
lean_inc_ref(v_tables_5797_);
v_s_5813_ = l_Lean_Parser_trailingLoopStep(v_tables_5797_, v_left_5811_, v_snd_5807_, v_c_5798_, v_s_5812_);
v_pos_5814_ = lean_ctor_get(v_s_5813_, 2);
v_errorMsg_5815_ = lean_ctor_get(v_s_5813_, 4);
v___x_5816_ = lean_box(0);
v___x_5817_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5815_, v___x_5816_);
if (v___x_5817_ == 0)
{
uint8_t v_decide_5818_; 
lean_dec_ref(v_c_5798_);
lean_dec_ref(v_tables_5797_);
v_decide_5818_ = lean_nat_dec_eq(v_pos_5814_, v_pos_5800_);
if (v_decide_5818_ == 0)
{
lean_dec(v_left_5811_);
lean_dec(v_iniSz_5803_);
lean_dec(v_pos_5800_);
return v_s_5813_;
}
else
{
lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5819_ = lean_unsigned_to_nat(1u);
v___x_5820_ = lean_nat_sub(v_iniSz_5803_, v___x_5819_);
lean_dec(v_iniSz_5803_);
v___x_5821_ = l_Lean_Parser_ParserState_restore(v_s_5813_, v___x_5820_, v_pos_5800_);
lean_dec(v___x_5820_);
v___x_5822_ = l_Lean_Parser_ParserState_pushSyntax(v___x_5821_, v_left_5811_);
return v___x_5822_;
}
}
else
{
lean_dec(v_left_5811_);
lean_dec(v_iniSz_5803_);
lean_dec(v_pos_5800_);
v_s_5799_ = v_s_5813_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser(lean_object* v_kind_5829_, lean_object* v_tables_5830_, uint8_t v_behavior_5831_, lean_object* v_antiquotParser_5832_, lean_object* v_c_5833_, lean_object* v_s_5834_){
_start:
{
lean_object* v_s_5835_; lean_object* v_errorMsg_5836_; lean_object* v___x_5837_; uint8_t v___x_5838_; 
lean_inc_ref(v_c_5833_);
lean_inc_ref(v_tables_5830_);
v_s_5835_ = l_Lean_Parser_leadingParser(v_kind_5829_, v_tables_5830_, v_behavior_5831_, v_antiquotParser_5832_, v_c_5833_, v_s_5834_);
v_errorMsg_5836_ = lean_ctor_get(v_s_5835_, 4);
v___x_5837_ = lean_box(0);
v___x_5838_ = l_instBEqOption_beq___at___00Lean_Parser_andthenFn_spec__0(v_errorMsg_5836_, v___x_5837_);
if (v___x_5838_ == 0)
{
lean_dec_ref(v_c_5833_);
lean_dec_ref(v_tables_5830_);
return v_s_5835_;
}
else
{
lean_object* v___x_5839_; 
v___x_5839_ = l_Lean_Parser_trailingLoop(v_tables_5830_, v_c_5833_, v_s_5835_);
return v___x_5839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_prattParser___boxed(lean_object* v_kind_5840_, lean_object* v_tables_5841_, lean_object* v_behavior_5842_, lean_object* v_antiquotParser_5843_, lean_object* v_c_5844_, lean_object* v_s_5845_){
_start:
{
uint8_t v_behavior_boxed_5846_; lean_object* v_res_5847_; 
v_behavior_boxed_5846_ = lean_unbox(v_behavior_5842_);
v_res_5847_ = l_Lean_Parser_prattParser(v_kind_5840_, v_tables_5841_, v_behavior_boxed_5846_, v_antiquotParser_5843_, v_c_5844_, v_s_5845_);
return v_res_5847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_fieldIdxFn(lean_object* v_c_5852_, lean_object* v_s_5853_){
_start:
{
lean_object* v_toInputContext_5854_; lean_object* v_pos_5855_; lean_object* v_inputString_5856_; lean_object* v_initStackSz_5857_; uint32_t v_curr_5862_; uint32_t v___x_5863_; uint8_t v___x_5864_; 
v_toInputContext_5854_ = lean_ctor_get(v_c_5852_, 0);
v_pos_5855_ = lean_ctor_get(v_s_5853_, 2);
lean_inc(v_pos_5855_);
v_inputString_5856_ = lean_ctor_get(v_toInputContext_5854_, 0);
v_initStackSz_5857_ = l_Lean_Parser_ParserState_stackSize(v_s_5853_);
v_curr_5862_ = lean_string_utf8_get(v_inputString_5856_, v_pos_5855_);
v___x_5863_ = 48;
v___x_5864_ = lean_uint32_dec_le(v___x_5863_, v_curr_5862_);
if (v___x_5864_ == 0)
{
lean_dec_ref(v_c_5852_);
goto v___jp_5858_;
}
else
{
uint32_t v___x_5865_; uint8_t v___x_5866_; 
v___x_5865_ = 57;
v___x_5866_ = lean_uint32_dec_le(v_curr_5862_, v___x_5865_);
if (v___x_5866_ == 0)
{
lean_dec_ref(v_c_5852_);
goto v___jp_5858_;
}
else
{
uint8_t v___x_5867_; 
v___x_5867_ = lean_uint32_dec_eq(v_curr_5862_, v___x_5863_);
if (v___x_5867_ == 0)
{
lean_object* v___f_5868_; lean_object* v_s_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; 
lean_dec(v_initStackSz_5857_);
v___f_5868_ = ((lean_object*)(l___private_Lean_Parser_Basic_0__Lean_Parser_decimalNumberFn_parseOptExp___closed__0));
v_s_5869_ = l_Lean_Parser_takeWhileFn(v___f_5868_, v_c_5852_, v_s_5853_);
v___x_5870_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5871_ = l_Lean_Parser_mkNodeToken(v___x_5870_, v_pos_5855_, v___x_5866_, v_c_5852_, v_s_5869_);
return v___x_5871_;
}
else
{
lean_dec_ref(v_c_5852_);
goto v___jp_5858_;
}
}
}
v___jp_5858_:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___x_5859_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__0));
v___x_5860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5860_, 0, v_initStackSz_5857_);
v___x_5861_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_5853_, v___x_5859_, v_pos_5855_, v___x_5860_);
lean_dec_ref_known(v___x_5860_, 1);
return v___x_5861_;
}
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__0(void){
_start:
{
uint8_t v___x_5872_; uint8_t v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; 
v___x_5872_ = 0;
v___x_5873_ = 1;
v___x_5874_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__2));
v___x_5875_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5876_ = l_Lean_Parser_mkAntiquot(v___x_5875_, v___x_5874_, v___x_5873_, v___x_5872_);
return v___x_5876_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__1(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5877_ = ((lean_object*)(l_Lean_Parser_fieldIdxFn___closed__1));
v___x_5878_ = l_Lean_Parser_mkAtomicInfo(v___x_5877_);
return v___x_5878_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__2(void){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; 
v___x_5879_ = lean_alloc_closure((void*)(l_Lean_Parser_fieldIdxFn), 2, 0);
v___x_5880_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__1, &l_Lean_Parser_fieldIdx___closed__1_once, _init_l_Lean_Parser_fieldIdx___closed__1);
v___x_5881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5880_);
lean_ctor_set(v___x_5881_, 1, v___x_5879_);
return v___x_5881_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx___closed__3(void){
_start:
{
lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5882_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__2, &l_Lean_Parser_fieldIdx___closed__2_once, _init_l_Lean_Parser_fieldIdx___closed__2);
v___x_5883_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__0, &l_Lean_Parser_fieldIdx___closed__0_once, _init_l_Lean_Parser_fieldIdx___closed__0);
v___x_5884_ = l_Lean_Parser_withAntiquot(v___x_5883_, v___x_5882_);
return v___x_5884_;
}
}
static lean_object* _init_l_Lean_Parser_fieldIdx(void){
_start:
{
lean_object* v___x_5885_; 
v___x_5885_ = lean_obj_once(&l_Lean_Parser_fieldIdx___closed__3, &l_Lean_Parser_fieldIdx___closed__3_once, _init_l_Lean_Parser_fieldIdx___closed__3);
return v___x_5885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0(lean_object* v_x_5886_, lean_object* v_s_5887_){
_start:
{
lean_inc_ref(v_s_5887_);
return v_s_5887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_skip___lam__0___boxed(lean_object* v_x_5888_, lean_object* v_s_5889_){
_start:
{
lean_object* v_res_5890_; 
v_res_5890_ = l_Lean_Parser_skip___lam__0(v_x_5888_, v_s_5889_);
lean_dec_ref(v_s_5889_);
lean_dec_ref(v_x_5888_);
return v_res_5890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg(lean_object* v_inst_5896_, lean_object* v_s_5897_, lean_object* v_f_5898_, lean_object* v_b_5899_){
_start:
{
lean_object* v_toApplicative_5900_; lean_object* v_toPure_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; uint8_t v___x_5905_; 
v_toApplicative_5900_ = lean_ctor_get(v_inst_5896_, 0);
v_toPure_5901_ = lean_ctor_get(v_toApplicative_5900_, 1);
v___x_5902_ = l_Lean_Syntax_getArgs(v_s_5897_);
v___x_5903_ = lean_unsigned_to_nat(0u);
v___x_5904_ = lean_array_get_size(v___x_5902_);
v___x_5905_ = lean_nat_dec_lt(v___x_5903_, v___x_5904_);
if (v___x_5905_ == 0)
{
lean_object* v___x_5906_; 
lean_inc(v_toPure_5901_);
lean_dec_ref(v___x_5902_);
lean_dec(v_f_5898_);
lean_dec_ref(v_inst_5896_);
v___x_5906_ = lean_apply_2(v_toPure_5901_, lean_box(0), v_b_5899_);
return v___x_5906_;
}
else
{
lean_object* v___x_5907_; size_t v___x_5908_; size_t v___x_5909_; lean_object* v___x_5910_; 
v___x_5907_ = lean_alloc_closure((void*)(l_flip), 6, 4);
lean_closure_set(v___x_5907_, 0, lean_box(0));
lean_closure_set(v___x_5907_, 1, lean_box(0));
lean_closure_set(v___x_5907_, 2, lean_box(0));
lean_closure_set(v___x_5907_, 3, v_f_5898_);
v___x_5908_ = ((size_t)0ULL);
v___x_5909_ = lean_usize_of_nat(v___x_5904_);
v___x_5910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_5896_, v___x_5907_, v___x_5902_, v___x_5908_, v___x_5909_, v_b_5899_);
return v___x_5910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___redArg___boxed(lean_object* v_inst_5911_, lean_object* v_s_5912_, lean_object* v_f_5913_, lean_object* v_b_5914_){
_start:
{
lean_object* v_res_5915_; 
v_res_5915_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5911_, v_s_5912_, v_f_5913_, v_b_5914_);
lean_dec(v_s_5912_);
return v_res_5915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM(lean_object* v_m_5916_, lean_object* v_inst_5917_, lean_object* v_00_u03b2_5918_, lean_object* v_s_5919_, lean_object* v_f_5920_, lean_object* v_b_5921_){
_start:
{
lean_object* v___x_5922_; 
v___x_5922_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_5917_, v_s_5919_, v_f_5920_, v_b_5921_);
return v___x_5922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___boxed(lean_object* v_m_5923_, lean_object* v_inst_5924_, lean_object* v_00_u03b2_5925_, lean_object* v_s_5926_, lean_object* v_f_5927_, lean_object* v_b_5928_){
_start:
{
lean_object* v_res_5929_; 
v_res_5929_ = l_Lean_Syntax_foldArgsM(v_m_5923_, v_inst_5924_, v_00_u03b2_5925_, v_s_5926_, v_f_5927_, v_b_5928_);
lean_dec(v_s_5926_);
return v_res_5929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___lam__0(lean_object* v_f_5930_, lean_object* v_x1_5931_, lean_object* v_x2_5932_){
_start:
{
lean_object* v___x_5933_; 
v___x_5933_ = lean_apply_2(v_f_5930_, v_x1_5931_, v_x2_5932_);
return v___x_5933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(lean_object* v_f_5934_, lean_object* v_as_5935_, size_t v_i_5936_, size_t v_stop_5937_, lean_object* v_b_5938_){
_start:
{
uint8_t v___x_5939_; 
v___x_5939_ = lean_usize_dec_eq(v_i_5936_, v_stop_5937_);
if (v___x_5939_ == 0)
{
lean_object* v___x_5940_; lean_object* v___x_5941_; size_t v___x_5942_; size_t v___x_5943_; 
v___x_5940_ = lean_array_uget_borrowed(v_as_5935_, v_i_5936_);
lean_inc(v_f_5934_);
lean_inc(v___x_5940_);
v___x_5941_ = lean_apply_2(v_f_5934_, v___x_5940_, v_b_5938_);
v___x_5942_ = ((size_t)1ULL);
v___x_5943_ = lean_usize_add(v_i_5936_, v___x_5942_);
v_i_5936_ = v___x_5943_;
v_b_5938_ = v___x_5941_;
goto _start;
}
else
{
lean_dec(v_f_5934_);
return v_b_5938_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg___boxed(lean_object* v_f_5945_, lean_object* v_as_5946_, lean_object* v_i_5947_, lean_object* v_stop_5948_, lean_object* v_b_5949_){
_start:
{
size_t v_i_boxed_5950_; size_t v_stop_boxed_5951_; lean_object* v_res_5952_; 
v_i_boxed_5950_ = lean_unbox_usize(v_i_5947_);
lean_dec(v_i_5947_);
v_stop_boxed_5951_ = lean_unbox_usize(v_stop_5948_);
lean_dec(v_stop_5948_);
v_res_5952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5945_, v_as_5946_, v_i_boxed_5950_, v_stop_boxed_5951_, v_b_5949_);
lean_dec_ref(v_as_5946_);
return v_res_5952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(lean_object* v_s_5953_, lean_object* v_f_5954_, lean_object* v_b_5955_){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; uint8_t v___x_5959_; 
v___x_5956_ = l_Lean_Syntax_getArgs(v_s_5953_);
v___x_5957_ = lean_unsigned_to_nat(0u);
v___x_5958_ = lean_array_get_size(v___x_5956_);
v___x_5959_ = lean_nat_dec_lt(v___x_5957_, v___x_5958_);
if (v___x_5959_ == 0)
{
lean_dec_ref(v___x_5956_);
lean_dec(v_f_5954_);
return v_b_5955_;
}
else
{
size_t v___x_5960_; size_t v___x_5961_; lean_object* v___x_5962_; 
v___x_5960_ = ((size_t)0ULL);
v___x_5961_ = lean_usize_of_nat(v___x_5958_);
v___x_5962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5954_, v___x_5956_, v___x_5960_, v___x_5961_, v_b_5955_);
lean_dec_ref(v___x_5956_);
return v___x_5962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg___boxed(lean_object* v_s_5963_, lean_object* v_f_5964_, lean_object* v_b_5965_){
_start:
{
lean_object* v_res_5966_; 
v_res_5966_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5963_, v_f_5964_, v_b_5965_);
lean_dec(v_s_5963_);
return v_res_5966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg(lean_object* v_s_5967_, lean_object* v_f_5968_, lean_object* v_b_5969_){
_start:
{
lean_object* v___f_5970_; lean_object* v___x_5971_; 
v___f_5970_ = lean_alloc_closure((void*)(l_Lean_Syntax_foldArgs___redArg___lam__0), 3, 1);
lean_closure_set(v___f_5970_, 0, v_f_5968_);
v___x_5971_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5967_, v___f_5970_, v_b_5969_);
return v___x_5971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___redArg___boxed(lean_object* v_s_5972_, lean_object* v_f_5973_, lean_object* v_b_5974_){
_start:
{
lean_object* v_res_5975_; 
v_res_5975_ = l_Lean_Syntax_foldArgs___redArg(v_s_5972_, v_f_5973_, v_b_5974_);
lean_dec(v_s_5972_);
return v_res_5975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs(lean_object* v_00_u03b2_5976_, lean_object* v_s_5977_, lean_object* v_f_5978_, lean_object* v_b_5979_){
_start:
{
lean_object* v___x_5980_; 
v___x_5980_ = l_Lean_Syntax_foldArgs___redArg(v_s_5977_, v_f_5978_, v_b_5979_);
return v___x_5980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgs___boxed(lean_object* v_00_u03b2_5981_, lean_object* v_s_5982_, lean_object* v_f_5983_, lean_object* v_b_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lean_Syntax_foldArgs(v_00_u03b2_5981_, v_s_5982_, v_f_5983_, v_b_5984_);
lean_dec(v_s_5982_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(lean_object* v_00_u03b2_5986_, lean_object* v_s_5987_, lean_object* v_f_5988_, lean_object* v_b_5989_){
_start:
{
lean_object* v___x_5990_; 
v___x_5990_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___redArg(v_s_5987_, v_f_5988_, v_b_5989_);
return v___x_5990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0___boxed(lean_object* v_00_u03b2_5991_, lean_object* v_s_5992_, lean_object* v_f_5993_, lean_object* v_b_5994_){
_start:
{
lean_object* v_res_5995_; 
v_res_5995_ = l_Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0(v_00_u03b2_5991_, v_s_5992_, v_f_5993_, v_b_5994_);
lean_dec(v_s_5992_);
return v_res_5995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(lean_object* v_00_u03b2_5996_, lean_object* v_f_5997_, lean_object* v_as_5998_, size_t v_i_5999_, size_t v_stop_6000_, lean_object* v_b_6001_){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___redArg(v_f_5997_, v_as_5998_, v_i_5999_, v_stop_6000_, v_b_6001_);
return v___x_6002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b2_6003_, lean_object* v_f_6004_, lean_object* v_as_6005_, lean_object* v_i_6006_, lean_object* v_stop_6007_, lean_object* v_b_6008_){
_start:
{
size_t v_i_boxed_6009_; size_t v_stop_boxed_6010_; lean_object* v_res_6011_; 
v_i_boxed_6009_ = lean_unbox_usize(v_i_6006_);
lean_dec(v_i_6006_);
v_stop_boxed_6010_ = lean_unbox_usize(v_stop_6007_);
lean_dec(v_stop_6007_);
v_res_6011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Syntax_foldArgsM___at___00Lean_Syntax_foldArgs_spec__0_spec__0(v_00_u03b2_6003_, v_f_6004_, v_as_6005_, v_i_boxed_6009_, v_stop_boxed_6010_, v_b_6008_);
lean_dec_ref(v_as_6005_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___lam__0(lean_object* v_f_6012_, lean_object* v_s_6013_, lean_object* v_x_6014_){
_start:
{
lean_object* v___x_6015_; 
v___x_6015_ = lean_apply_1(v_f_6012_, v_s_6013_);
return v___x_6015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg(lean_object* v_inst_6016_, lean_object* v_s_6017_, lean_object* v_f_6018_){
_start:
{
lean_object* v___f_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v___f_6019_ = lean_alloc_closure((void*)(l_Lean_Syntax_forArgsM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_6019_, 0, v_f_6018_);
v___x_6020_ = lean_box(0);
v___x_6021_ = l_Lean_Syntax_foldArgsM___redArg(v_inst_6016_, v_s_6017_, v___f_6019_, v___x_6020_);
return v___x_6021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___redArg___boxed(lean_object* v_inst_6022_, lean_object* v_s_6023_, lean_object* v_f_6024_){
_start:
{
lean_object* v_res_6025_; 
v_res_6025_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6022_, v_s_6023_, v_f_6024_);
lean_dec(v_s_6023_);
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM(lean_object* v_m_6026_, lean_object* v_inst_6027_, lean_object* v_s_6028_, lean_object* v_f_6029_){
_start:
{
lean_object* v___x_6030_; 
v___x_6030_ = l_Lean_Syntax_forArgsM___redArg(v_inst_6027_, v_s_6028_, v_f_6029_);
return v___x_6030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_forArgsM___boxed(lean_object* v_m_6031_, lean_object* v_inst_6032_, lean_object* v_s_6033_, lean_object* v_f_6034_){
_start:
{
lean_object* v_res_6035_; 
v_res_6035_ = l_Lean_Syntax_forArgsM(v_m_6031_, v_inst_6032_, v_s_6033_, v_f_6034_);
lean_dec(v_s_6033_);
return v_res_6035_;
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
