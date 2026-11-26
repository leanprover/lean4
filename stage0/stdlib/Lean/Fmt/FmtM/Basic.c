// Lean compiler output
// Module: Lean.Fmt.FmtM.Basic
// Imports: public import Lean.Fmt.FmtM.Layouts import Lean.Fmt.Util.RangeTree import Lean.Fmt.FmtM.Comments meta import Lean.Parser.Term.Basic import Init.Data
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
extern lean_object* l_Lean_Fmt_quantifierFmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_getValues___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Fmt_keyedFmtProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedComment_default;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Comment_render(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNl___redArg();
lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_parseComments(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getTrailing_x3f(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
extern lean_object* l_Lean_Fmt_infixFmtAttribute;
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_CommentCollector_Context_trailingComments(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_binSearchRightmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_failure;
lean_object* l_Lean_Fmt_getFmtProviders(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_markMultiLineRaw(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedError_default;
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
lean_object* l_String_Pos_Raw_offsetOfPosAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Substring_Raw_splitOn(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getLeading_x3f(lean_object*);
extern lean_object* l_instInhabitedRaw__1;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
extern uint32_t l_Lean_idEndEscape;
extern uint32_t l_Lean_idBeginEscape;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
extern lean_object* l_String_instInhabitedSlice;
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t l_Lean_Fmt_instBEqDefaultCost_beq___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_quantified(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_Lean_Fmt_conditionalFmtAttribute;
lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* l_Lean_Fmt_Layouts_conditional(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_firstSyntaxTagId;
lean_object* l___private_Init_ShareCommon_0__ShareCommon_Internal_mkStateImpl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_Range_ofSubstring(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_Range_ofSubstring___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__1;
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__2;
static lean_once_cell_t l_Lean_FmtM_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_FmtM_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_FmtM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FmtM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_FormattedWhitespace_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_getLineInfo_x21___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.FmtM.Basic"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__0 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__0_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Fmt.getLineInfo!"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__1 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__1_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "assertion violation: lineInfo.startPos <= pos && pos <= lineInfo.endPos\n  "};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__2 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_getLineInfo_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getLineInfo_x21___closed__3;
static const lean_closure_object l_Lean_Fmt_getLineInfo_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_getLineInfo_x21___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__4 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__4_value;
static const lean_closure_object l_Lean_Fmt_getLineInfo_x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_getLineInfo_x21___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__5 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__5_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__6 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__6_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__7 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__7_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__8 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__8_value;
static lean_once_cell_t l_Lean_Fmt_getLineInfo_x21___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getLineInfo_x21___closed__9;
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_getLineInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_getLineInfos___closed__0 = (const lean_object*)&l_Lean_Fmt_getLineInfos___closed__0_value;
static const lean_string_object l_Lean_Fmt_getLineInfos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Fmt.getLineInfos"};
static const lean_object* l_Lean_Fmt_getLineInfos___closed__1 = (const lean_object*)&l_Lean_Fmt_getLineInfos___closed__1_value;
static const lean_string_object l_Lean_Fmt_getLineInfos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "assertion violation: !lineInfos.isEmpty\n  "};
static const lean_object* l_Lean_Fmt_getLineInfos___closed__2 = (const lean_object*)&l_Lean_Fmt_getLineInfos___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_getLineInfos___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getLineInfos___closed__3;
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ParserDescr"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(92, 191, 134, 190, 206, 60, 55, 123)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "TrailingParserDescr"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(73, 30, 7, 95, 84, 115, 124, 250)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ws"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 198, 251, 95, 67, 81, 118, 246)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__4_value),LEAN_SCALAR_PTR_LITERAL(74, 147, 100, 44, 136, 108, 159, 66)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__8_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colEq"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(105, 155, 248, 3, 115, 223, 12, 139)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lineEq"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__12_value),LEAN_SCALAR_PTR_LITERAL(11, 222, 52, 211, 142, 186, 26, 103)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__14_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__16_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppHardSpace"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 168, 190, 83, 177, 86, 113, 221)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ppAllowUngrouped"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__20_value),LEAN_SCALAR_PTR_LITERAL(254, 56, 209, 55, 154, 125, 240, 2)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "ppHardLineUnlessUngrouped"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__22_value),LEAN_SCALAR_PTR_LITERAL(68, 165, 69, 201, 179, 176, 38, 97)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__3_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__5_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__7_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__9_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__11_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__13_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__15_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__17_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__19_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__21_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__23_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases___closed__24_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternIgnore"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__4_value),LEAN_SCALAR_PTR_LITERAL(195, 83, 213, 191, 208, 4, 123, 240)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__6_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__8_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "withoutForbidden"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__10_value),LEAN_SCALAR_PTR_LITERAL(36, 202, 249, 244, 227, 198, 135, 34)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppGroup"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__12_value),LEAN_SCALAR_PTR_LITERAL(149, 180, 65, 169, 196, 28, 141, 221)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ppRealGroup"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__14_value),LEAN_SCALAR_PTR_LITERAL(86, 184, 190, 137, 27, 87, 63, 174)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ppRealFill"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__16_value),LEAN_SCALAR_PTR_LITERAL(21, 219, 143, 167, 248, 5, 230, 49)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppIndent"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__18_value),LEAN_SCALAR_PTR_LITERAL(240, 142, 232, 190, 100, 212, 29, 41)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__20_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ppDedentIfGrouped"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__22_value),LEAN_SCALAR_PTR_LITERAL(195, 164, 225, 181, 149, 187, 81, 113)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__1_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__3_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__5_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__7_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__9_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__11_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__13_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__15_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__17_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__19_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__21_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__23_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases___closed__24_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1 = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instInhabitedQuantifierChain_default = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_instInhabitedQuantifierChain = (const lean_object*)&l_Lean_Fmt_instInhabitedQuantifierChain_default___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "_private.Lean.Fmt.FmtM.Basic.0.Lean.Fmt.quantifierChain"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRawAsInSource___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid syntax position"};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRawAsInSource___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "Input syntax to the formatter is malformed: invalid syntax position."};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__1_value;
static const lean_array_object l_Lean_Fmt_fmtRawAsInSource___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_fmtRawAsInSource___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__3;
static const lean_string_object l_Lean_Fmt_fmtRawAsInSource___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_fmtRawAsInSource___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRawAsInSource___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0;
static lean_once_cell_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_fmtPrefixOperator___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtPrefixOperator___closed__0;
static lean_once_cell_t l_Lean_Fmt_fmtPrefixOperator___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_fmtPrefixOperator___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_resolveChoiceNodes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtChoiceNode"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 97, 186, 28, 58, 175, 99, 37)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "antiquot_scope"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "antiquot_splice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "antiquot_suffix_splice"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "token_antiquot"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4_value;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtAtomic"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 89, 152, 45, 219, 206, 174, 0)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "fmtInfixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 84, 102, 146, 118, 206, 223, 209)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "fmtPostfixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__2_value),LEAN_SCALAR_PTR_LITERAL(208, 119, 87, 59, 92, 236, 3, 41)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5;
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtPrefixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 164, 120, 136, 13, 122, 50, 33)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtInfixOperator___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtConditional___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtQuantifier___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "substring is invalid and cannot be converted to a slice"};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "Input syntax to the formatter is malformed: substring is invalid and cannot be converted to a slice."};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0_value;
static const lean_array_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "missing token range"};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "Input syntax to the formatter is malformed: missing token range."};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value),((lean_object*)&l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_Range_ofSubstring(lean_object* v_s_1_){
_start:
{
lean_object* v_startPos_2_; lean_object* v_stopPos_3_; lean_object* v___x_4_; 
v_startPos_2_ = lean_ctor_get(v_s_1_, 1);
v_stopPos_3_ = lean_ctor_get(v_s_1_, 2);
lean_inc(v_stopPos_3_);
lean_inc(v_startPos_2_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_startPos_2_);
lean_ctor_set(v___x_4_, 1, v_stopPos_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_Range_ofSubstring___boxed(lean_object* v_s_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_Range_ofSubstring(v_s_5_);
lean_dec_ref(v_s_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(lean_object* v_as_7_, lean_object* v_i_8_){
_start:
{
lean_object* v_zero_9_; uint8_t v_isZero_10_; 
v_zero_9_ = lean_unsigned_to_nat(0u);
v_isZero_10_ = lean_nat_dec_eq(v_i_8_, v_zero_9_);
if (v_isZero_10_ == 1)
{
lean_object* v___x_11_; 
lean_dec(v_i_8_);
v___x_11_ = lean_box(0);
return v___x_11_;
}
else
{
lean_object* v_one_12_; lean_object* v_n_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_one_12_ = lean_unsigned_to_nat(1u);
v_n_13_ = lean_nat_sub(v_i_8_, v_one_12_);
lean_dec(v_i_8_);
v___x_14_ = lean_array_fget_borrowed(v_as_7_, v_n_13_);
lean_inc(v___x_14_);
v___x_15_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v___x_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
v_i_8_ = v_n_13_;
goto _start;
}
else
{
lean_dec(v_n_13_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(lean_object* v_stx_17_){
_start:
{
switch(lean_obj_tag(v_stx_17_))
{
case 0:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
case 1:
{
lean_object* v_args_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_args_19_ = lean_ctor_get(v_stx_17_, 2);
lean_inc_ref(v_args_19_);
lean_dec_ref_known(v_stx_17_, 3);
v___x_20_ = lean_array_get_size(v_args_19_);
v___x_21_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_args_19_, v___x_20_);
lean_dec_ref(v_args_19_);
return v___x_21_;
}
default: 
{
lean_object* v___x_22_; 
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v_stx_17_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg___boxed(lean_object* v_as_23_, lean_object* v_i_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_as_23_, v_i_24_);
lean_dec_ref(v_as_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(lean_object* v_as_26_, lean_object* v_i_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_as_26_, v_i_27_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___boxed(lean_object* v_as_30_, lean_object* v_i_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(v_as_30_, v_i_31_, v_a_32_);
lean_dec_ref(v_as_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(lean_object* v_stx_37_){
_start:
{
switch(lean_obj_tag(v_stx_37_))
{
case 0:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
case 1:
{
lean_object* v_args_39_; lean_object* v___x_40_; lean_object* v___x_41_; size_t v_sz_42_; size_t v___x_43_; lean_object* v___x_44_; lean_object* v_fst_45_; 
v_args_39_ = lean_ctor_get(v_stx_37_, 2);
lean_inc_ref(v_args_39_);
lean_dec_ref_known(v_stx_37_, 3);
v___x_40_ = lean_box(0);
v___x_41_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0));
v_sz_42_ = lean_array_size(v_args_39_);
v___x_43_ = ((size_t)0ULL);
v___x_44_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(v_args_39_, v_sz_42_, v___x_43_, v___x_41_);
lean_dec_ref(v_args_39_);
v_fst_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_fst_45_);
lean_dec_ref(v___x_44_);
if (lean_obj_tag(v_fst_45_) == 0)
{
return v___x_40_;
}
else
{
lean_object* v_val_46_; 
v_val_46_ = lean_ctor_get(v_fst_45_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v_fst_45_, 1);
return v_val_46_;
}
}
default: 
{
lean_object* v___x_47_; 
v___x_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_47_, 0, v_stx_37_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(lean_object* v_as_48_, size_t v_sz_49_, size_t v_i_50_, lean_object* v_b_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = lean_usize_dec_lt(v_i_50_, v_sz_49_);
if (v___x_52_ == 0)
{
lean_inc_ref(v_b_51_);
return v_b_51_;
}
else
{
lean_object* v___x_53_; lean_object* v_a_54_; lean_object* v___x_55_; 
v___x_53_ = lean_box(0);
v_a_54_ = lean_array_uget_borrowed(v_as_48_, v_i_50_);
lean_inc(v_a_54_);
v___x_55_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_a_54_);
if (lean_obj_tag(v___x_55_) == 1)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_53_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; size_t v___x_59_; size_t v___x_60_; 
lean_dec(v___x_55_);
v___x_58_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0));
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_50_, v___x_59_);
v_i_50_ = v___x_60_;
v_b_51_ = v___x_58_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___boxed(lean_object* v_as_62_, lean_object* v_sz_63_, lean_object* v_i_64_, lean_object* v_b_65_){
_start:
{
size_t v_sz_boxed_66_; size_t v_i_boxed_67_; lean_object* v_res_68_; 
v_sz_boxed_66_ = lean_unbox_usize(v_sz_63_);
lean_dec(v_sz_63_);
v_i_boxed_67_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_res_68_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(v_as_62_, v_sz_boxed_66_, v_i_boxed_67_, v_b_65_);
lean_dec_ref(v_b_65_);
lean_dec_ref(v_as_62_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(lean_object* v_a_69_){
_start:
{
lean_object* v_fst_70_; lean_object* v_snd_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_111_; 
v_fst_70_ = lean_ctor_get(v_a_69_, 0);
v_snd_71_ = lean_ctor_get(v_a_69_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_a_69_);
if (v_isSharedCheck_111_ == 0)
{
v___x_73_ = v_a_69_;
v_isShared_74_ = v_isSharedCheck_111_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_snd_71_);
lean_inc(v_fst_70_);
lean_dec(v_a_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_111_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
uint32_t v___y_76_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_nat_dec_lt(v___x_104_, v_snd_71_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
lean_del_object(v___x_73_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_fst_70_);
lean_ctor_set(v___x_106_, 1, v_snd_71_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = l_String_Slice_Pos_get_x3f(v_fst_70_, v___x_104_);
if (lean_obj_tag(v___x_107_) == 0)
{
uint32_t v___x_108_; 
v___x_108_ = 65;
v___y_76_ = v___x_108_;
goto v___jp_75_;
}
else
{
lean_object* v_val_109_; uint32_t v___x_110_; 
v_val_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_val_109_);
lean_dec_ref_known(v___x_107_, 1);
v___x_110_ = lean_unbox_uint32(v_val_109_);
lean_dec(v_val_109_);
v___y_76_ = v___x_110_;
goto v___jp_75_;
}
}
v___jp_75_:
{
uint32_t v___x_77_; uint8_t v___x_78_; 
v___x_77_ = 32;
v___x_78_ = lean_uint32_dec_eq(v___y_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_80_; 
if (v_isShared_74_ == 0)
{
v___x_80_ = v___x_73_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_fst_70_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_snd_71_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v_str_82_; lean_object* v_startInclusive_83_; lean_object* v_endExclusive_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_100_; 
v_str_82_ = lean_ctor_get(v_fst_70_, 0);
lean_inc_ref(v_str_82_);
v_startInclusive_83_ = lean_ctor_get(v_fst_70_, 1);
lean_inc(v_startInclusive_83_);
v_endExclusive_84_ = lean_ctor_get(v_fst_70_, 2);
lean_inc(v_endExclusive_84_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_String_Slice_Pos_nextn(v_fst_70_, v___x_86_, v___x_85_);
v_isSharedCheck_100_ = !lean_is_exclusive(v_fst_70_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; lean_object* v_unused_102_; lean_object* v_unused_103_; 
v_unused_101_ = lean_ctor_get(v_fst_70_, 2);
lean_dec(v_unused_101_);
v_unused_102_ = lean_ctor_get(v_fst_70_, 1);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_fst_70_, 0);
lean_dec(v_unused_103_);
v___x_89_ = v_fst_70_;
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_fst_70_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_100_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_nat_add(v_startInclusive_83_, v___x_87_);
lean_dec(v___x_87_);
lean_dec(v_startInclusive_83_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_str_82_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_endExclusive_84_);
v___x_93_ = v_reuseFailAlloc_99_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_94_ = lean_nat_sub(v_snd_71_, v___x_85_);
lean_dec(v_snd_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_94_);
lean_ctor_set(v___x_73_, 0, v___x_93_);
v___x_96_ = v___x_73_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_94_);
v___x_96_ = v_reuseFailAlloc_98_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
v_a_69_ = v___x_96_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(lean_object* v_line_112_, lean_object* v_numSpaces_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_fst_116_; 
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_line_112_);
lean_ctor_set(v___x_114_, 1, v_numSpaces_113_);
v___x_115_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(v___x_114_);
v_fst_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_fst_116_);
lean_dec_ref(v___x_115_);
return v_fst_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0(lean_object* v_inst_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(v_a_118_);
return v___x_119_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1));
v___x_126_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2);
v___x_129_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1));
v___x_130_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
lean_ctor_set(v___x_130_, 2, v___x_127_);
lean_ctor_set(v___x_130_, 3, v___x_127_);
return v___x_130_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg(){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___boxed(lean_object* v___dummy_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg();
return v_res_137_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0(void){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg();
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(lean_object* v_s_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___boxed(lean_object* v_s_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v_s_141_);
lean_dec_ref(v_s_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(lean_object* v_numSpaces_143_, lean_object* v_s_144_, lean_object* v___x_145_, lean_object* v___x_146_, lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
lean_object* v_it_150_; lean_object* v_startInclusive_151_; lean_object* v_endExclusive_152_; 
if (lean_obj_tag(v_a_147_) == 0)
{
lean_object* v_currPos_158_; lean_object* v_searcher_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_265_; 
v_currPos_158_ = lean_ctor_get(v_a_147_, 0);
v_searcher_159_ = lean_ctor_get(v_a_147_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_a_147_);
if (v_isSharedCheck_265_ == 0)
{
v___x_161_ = v_a_147_;
v_isShared_162_ = v_isSharedCheck_265_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_searcher_159_);
lean_inc(v_currPos_158_);
lean_dec(v_a_147_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_265_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_it_164_; lean_object* v_it_170_; lean_object* v_startPos_171_; lean_object* v_endPos_172_; 
switch(lean_obj_tag(v_searcher_159_))
{
case 0:
{
lean_object* v_pos_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_197_; 
lean_del_object(v___x_161_);
v_pos_185_ = lean_ctor_get(v_searcher_159_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_searcher_159_);
if (v_isSharedCheck_197_ == 0)
{
v___x_187_ = v_searcher_159_;
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_pos_185_);
lean_dec(v_searcher_159_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_197_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_startInclusive_189_; lean_object* v_endExclusive_190_; lean_object* v___x_191_; uint8_t v_decide_192_; 
v_startInclusive_189_ = lean_ctor_get(v___x_145_, 1);
v_endExclusive_190_ = lean_ctor_get(v___x_145_, 2);
v___x_191_ = lean_nat_sub(v_endExclusive_190_, v_startInclusive_189_);
v_decide_192_ = lean_nat_dec_eq(v_pos_185_, v___x_191_);
lean_dec(v___x_191_);
if (v_decide_192_ == 0)
{
lean_object* v___x_194_; 
lean_inc(v_pos_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
v___x_194_ = v___x_187_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_pos_185_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_inc(v_pos_185_);
v_it_170_ = v___x_194_;
v_startPos_171_ = v_pos_185_;
v_endPos_172_ = v_pos_185_;
goto v___jp_169_;
}
}
else
{
lean_object* v___x_196_; 
lean_del_object(v___x_187_);
v___x_196_ = lean_box(3);
lean_inc(v_pos_185_);
v_it_170_ = v___x_196_;
v_startPos_171_ = v_pos_185_;
v_endPos_172_ = v_pos_185_;
goto v___jp_169_;
}
}
}
case 1:
{
lean_object* v_pos_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
v_pos_198_ = lean_ctor_get(v_searcher_159_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_searcher_159_);
if (v_isSharedCheck_206_ == 0)
{
v___x_200_ = v_searcher_159_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_pos_198_);
lean_dec(v_searcher_159_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_string_utf8_next_fast(v_s_144_, v_pos_198_);
lean_dec(v_pos_198_);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 0);
lean_ctor_set(v___x_200_, 0, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
v_it_164_ = v___x_204_;
goto v___jp_163_;
}
}
}
case 2:
{
lean_object* v_needle_207_; lean_object* v_table_208_; lean_object* v_stackPos_209_; lean_object* v_needlePos_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_264_; 
v_needle_207_ = lean_ctor_get(v_searcher_159_, 0);
v_table_208_ = lean_ctor_get(v_searcher_159_, 1);
v_stackPos_209_ = lean_ctor_get(v_searcher_159_, 2);
v_needlePos_210_ = lean_ctor_get(v_searcher_159_, 3);
v_isSharedCheck_264_ = !lean_is_exclusive(v_searcher_159_);
if (v_isSharedCheck_264_ == 0)
{
v___x_212_ = v_searcher_159_;
v_isShared_213_ = v_isSharedCheck_264_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_needlePos_210_);
lean_inc(v_stackPos_209_);
lean_inc(v_table_208_);
lean_inc(v_needle_207_);
lean_dec(v_searcher_159_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_264_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_str_214_; lean_object* v_startInclusive_215_; lean_object* v_endExclusive_216_; lean_object* v_basePos_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_str_214_ = lean_ctor_get(v_needle_207_, 0);
v_startInclusive_215_ = lean_ctor_get(v_needle_207_, 1);
v_endExclusive_216_ = lean_ctor_get(v_needle_207_, 2);
v_basePos_217_ = lean_nat_sub(v_stackPos_209_, v_needlePos_210_);
v___x_218_ = lean_nat_sub(v_endExclusive_216_, v_startInclusive_215_);
v___x_219_ = lean_nat_add(v_basePos_217_, v___x_218_);
v___x_220_ = lean_nat_dec_le(v___x_219_, v___x_146_);
lean_dec(v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
lean_dec(v___x_218_);
lean_del_object(v___x_212_);
lean_dec(v_needlePos_210_);
lean_dec(v_stackPos_209_);
lean_dec_ref(v_table_208_);
lean_dec_ref(v_needle_207_);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_basePos_217_, v___x_221_);
lean_dec(v_basePos_217_);
v___x_223_ = lean_nat_dec_le(v___x_222_, v___x_146_);
lean_dec(v___x_222_);
if (v___x_223_ == 0)
{
lean_del_object(v___x_161_);
goto v___jp_183_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = lean_box(3);
v_it_164_ = v___x_224_;
goto v___jp_163_;
}
}
else
{
uint8_t v_stackByte_225_; lean_object* v___x_226_; uint8_t v_patByte_227_; uint8_t v___x_228_; 
lean_dec(v_basePos_217_);
lean_inc(v_stackPos_209_);
v_stackByte_225_ = lean_string_get_byte_fast(v_s_144_, v_stackPos_209_);
v___x_226_ = lean_nat_add(v_startInclusive_215_, v_needlePos_210_);
v_patByte_227_ = lean_string_get_byte_fast(v_str_214_, v___x_226_);
v___x_228_ = lean_uint8_dec_eq(v_stackByte_225_, v_patByte_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; uint8_t v_decide_230_; 
lean_dec(v___x_218_);
v___x_229_ = lean_unsigned_to_nat(0u);
v_decide_230_ = lean_nat_dec_eq(v_needlePos_210_, v___x_229_);
if (v_decide_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_newNeedlePos_233_; uint8_t v___x_234_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_nat_sub(v_needlePos_210_, v___x_231_);
lean_dec(v_needlePos_210_);
v_newNeedlePos_233_ = lean_array_fget_borrowed(v_table_208_, v___x_232_);
lean_dec(v___x_232_);
v___x_234_ = lean_nat_dec_eq(v_newNeedlePos_233_, v___x_229_);
if (v___x_234_ == 0)
{
lean_object* v___x_236_; 
lean_inc(v_newNeedlePos_233_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 3, v_newNeedlePos_233_);
v___x_236_ = v___x_212_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_needle_207_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_table_208_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_stackPos_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_newNeedlePos_233_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
v_it_164_ = v___x_236_;
goto v___jp_163_;
}
}
else
{
lean_object* v_nextStackPos_238_; lean_object* v___x_240_; 
v_nextStackPos_238_ = l_String_Slice_posGE___redArg(v___x_145_, v_stackPos_209_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 3, v___x_229_);
lean_ctor_set(v___x_212_, 2, v_nextStackPos_238_);
v___x_240_ = v___x_212_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_needle_207_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_table_208_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_nextStackPos_238_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v___x_229_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v_it_164_ = v___x_240_;
goto v___jp_163_;
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_nextStackPos_244_; lean_object* v___x_246_; 
lean_dec(v_needlePos_210_);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_add(v_stackPos_209_, v___x_242_);
lean_dec(v_stackPos_209_);
v_nextStackPos_244_ = l_String_Slice_posGE___redArg(v___x_145_, v___x_243_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 3, v___x_229_);
lean_ctor_set(v___x_212_, 2, v_nextStackPos_244_);
v___x_246_ = v___x_212_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_needle_207_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_table_208_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_nextStackPos_244_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v___x_229_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v_it_164_ = v___x_246_;
goto v___jp_163_;
}
}
}
else
{
lean_object* v___x_248_; lean_object* v_nextStackPos_249_; lean_object* v_nextNeedlePos_250_; uint8_t v_decide_251_; 
lean_del_object(v___x_161_);
v___x_248_ = lean_unsigned_to_nat(1u);
v_nextStackPos_249_ = lean_nat_add(v_stackPos_209_, v___x_248_);
lean_dec(v_stackPos_209_);
v_nextNeedlePos_250_ = lean_nat_add(v_needlePos_210_, v___x_248_);
lean_dec(v_needlePos_210_);
v_decide_251_ = lean_nat_dec_eq(v_nextNeedlePos_250_, v___x_218_);
lean_dec(v___x_218_);
if (v_decide_251_ == 0)
{
lean_object* v___x_253_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 3, v_nextNeedlePos_250_);
lean_ctor_set(v___x_212_, 2, v_nextStackPos_249_);
v___x_253_ = v___x_212_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_needle_207_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_table_208_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_nextStackPos_249_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_nextNeedlePos_250_);
v___x_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; 
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_currPos_158_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v_a_147_ = v___x_254_;
goto _start;
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_257_ = lean_nat_sub(v_nextStackPos_249_, v_nextNeedlePos_250_);
lean_dec(v_nextNeedlePos_250_);
v___x_258_ = l_String_Slice_pos_x21(v___x_145_, v___x_257_);
lean_dec(v___x_257_);
v___x_259_ = l_String_Slice_pos_x21(v___x_145_, v_nextStackPos_249_);
v___x_260_ = lean_unsigned_to_nat(0u);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 3, v___x_260_);
lean_ctor_set(v___x_212_, 2, v_nextStackPos_249_);
v___x_262_ = v___x_212_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_needle_207_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_table_208_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_nextStackPos_249_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
v_it_170_ = v___x_262_;
v_startPos_171_ = v___x_258_;
v_endPos_172_ = v___x_259_;
goto v___jp_169_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_161_);
goto v___jp_183_;
}
}
v___jp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v_it_164_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_currPos_158_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_it_164_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v_a_147_ = v___x_166_;
goto _start;
}
}
v___jp_169_:
{
lean_object* v_slice_173_; lean_object* v_startInclusive_174_; lean_object* v_endExclusive_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_slice_173_ = l_String_Slice_subslice_x21(v___x_145_, v_currPos_158_, v_startPos_171_);
v_startInclusive_174_ = lean_ctor_get(v_slice_173_, 0);
v_endExclusive_175_ = lean_ctor_get(v_slice_173_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v_slice_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v_slice_173_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_endExclusive_175_);
lean_inc(v_startInclusive_174_);
lean_dec(v_slice_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_nextIt_180_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v_it_170_);
lean_ctor_set(v___x_177_, 0, v_endPos_172_);
v_nextIt_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_endPos_172_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v_it_170_);
v_nextIt_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v_it_150_ = v_nextIt_180_;
v_startInclusive_151_ = v_startInclusive_174_;
v_endExclusive_152_ = v_endExclusive_175_;
goto v___jp_149_;
}
}
}
v___jp_183_:
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(1);
lean_inc(v___x_146_);
v_it_150_ = v___x_184_;
v_startInclusive_151_ = v_currPos_158_;
v_endExclusive_152_ = v___x_146_;
goto v___jp_149_;
}
}
}
else
{
lean_dec(v___x_146_);
lean_dec_ref(v_s_144_);
lean_dec(v_numSpaces_143_);
return v_b_148_;
}
v___jp_149_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_inc_ref(v_s_144_);
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v_s_144_);
lean_ctor_set(v___x_153_, 1, v_startInclusive_151_);
lean_ctor_set(v___x_153_, 2, v_endExclusive_152_);
lean_inc(v_numSpaces_143_);
v___x_154_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(v___x_153_, v_numSpaces_143_);
v___x_155_ = l_String_Slice_toString(v___x_154_);
lean_dec_ref(v___x_154_);
v___x_156_ = lean_array_push(v_b_148_, v___x_155_);
v_a_147_ = v_it_150_;
v_b_148_ = v___x_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg___boxed(lean_object* v_numSpaces_266_, lean_object* v_s_267_, lean_object* v___x_268_, lean_object* v___x_269_, lean_object* v_a_270_, lean_object* v_b_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_266_, v_s_267_, v___x_268_, v___x_269_, v_a_270_, v_b_271_);
lean_dec_ref(v___x_268_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(lean_object* v_s_275_, lean_object* v_numSpaces_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_277_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_string_utf8_byte_size(v_s_275_);
lean_inc_ref(v_s_275_);
v___x_280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_280_, 0, v_s_275_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
v___x_281_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_282_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0));
v___x_283_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_276_, v_s_275_, v___x_280_, v___x_279_, v___x_281_, v___x_282_);
lean_dec_ref_known(v___x_280_, 3);
v___x_284_ = lean_array_to_list(v___x_283_);
v___x_285_ = l_String_intercalate(v___x_277_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(lean_object* v_numSpaces_286_, lean_object* v_s_287_, lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v_inst_290_, lean_object* v_R_291_, lean_object* v_a_292_, lean_object* v_b_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_286_, v_s_287_, v___x_288_, v___x_289_, v_a_292_, v_b_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___boxed(lean_object* v_numSpaces_295_, lean_object* v_s_296_, lean_object* v___x_297_, lean_object* v___x_298_, lean_object* v_inst_299_, lean_object* v_R_300_, lean_object* v_a_301_, lean_object* v_b_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(v_numSpaces_295_, v_s_296_, v___x_297_, v___x_298_, v_inst_299_, v_R_300_, v_a_301_, v_b_302_);
lean_dec_ref(v___x_297_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState___redArg(lean_object* v_value_304_, lean_object* v_s_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_s_305_);
lean_ctor_set(v___x_306_, 1, v_value_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState(lean_object* v_00_u03b1_307_, lean_object* v_value_308_, lean_object* v_s_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_s_309_);
lean_ctor_set(v___x_310_, 1, v_value_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_unsigned_to_nat(16u);
v___x_313_ = lean_mk_array(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__0, &l_Lean_FmtM_run___redArg___closed__0_once, _init_l_Lean_FmtM_run___redArg___closed__0);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_Lean_ShareCommon_objectFactory;
v___x_318_ = l___private_Init_ShareCommon_0__ShareCommon_Internal_mkStateImpl(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = l_Lean_Fmt_firstSyntaxTagId;
v___x_320_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__2, &l_Lean_FmtM_run___redArg___closed__2_once, _init_l_Lean_FmtM_run___redArg___closed__2);
v___x_321_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__1, &l_Lean_FmtM_run___redArg___closed__1_once, _init_l_Lean_FmtM_run___redArg___closed__1);
v___x_322_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
lean_ctor_set(v___x_322_, 2, v___x_319_);
lean_ctor_set(v___x_322_, 3, v___x_321_);
lean_ctor_set(v___x_322_, 4, v___x_321_);
lean_ctor_set(v___x_322_, 5, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run___redArg(lean_object* v_ctx_323_, lean_object* v_act_324_){
_start:
{
lean_object* v___x_325_; lean_object* v_r_326_; 
v___x_325_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__3, &l_Lean_FmtM_run___redArg___closed__3_once, _init_l_Lean_FmtM_run___redArg___closed__3);
v_r_326_ = lean_apply_2(v_act_324_, v_ctx_323_, v___x_325_);
if (lean_obj_tag(v_r_326_) == 0)
{
lean_object* v_a_327_; lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_a_327_ = lean_ctor_get(v_r_326_, 0);
v_a_328_ = lean_ctor_get(v_r_326_, 1);
v_isSharedCheck_336_ = !lean_is_exclusive(v_r_326_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v_r_326_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_inc(v_a_327_);
lean_dec(v_r_326_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_a_327_);
lean_ctor_set(v___x_330_, 0, v_a_328_);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_328_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v_a_327_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_ctor_get(v_r_326_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v_r_326_, 2);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_a_337_);
return v___x_338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run(lean_object* v_00_u03b1_339_, lean_object* v_ctx_340_, lean_object* v_act_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_FmtM_run___redArg(v_ctx_340_, v_act_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(lean_object* v_00_u03b1_343_, lean_object* v_v_344_, lean_object* v_x_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_toBacktrackableState_347_; lean_object* v_shareCommonState_348_; lean_object* v_freshTagId_349_; lean_object* v_missingFormatters_350_; lean_object* v_partialFormatters_351_; lean_object* v_missingChoiceResolutions_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_370_; 
v_toBacktrackableState_347_ = lean_ctor_get(v___y_346_, 0);
v_shareCommonState_348_ = lean_ctor_get(v___y_346_, 1);
v_freshTagId_349_ = lean_ctor_get(v___y_346_, 2);
v_missingFormatters_350_ = lean_ctor_get(v___y_346_, 3);
v_partialFormatters_351_ = lean_ctor_get(v___y_346_, 4);
v_missingChoiceResolutions_352_ = lean_ctor_get(v___y_346_, 5);
v_isSharedCheck_370_ = !lean_is_exclusive(v___y_346_);
if (v_isSharedCheck_370_ == 0)
{
v___x_354_ = v___y_346_;
v_isShared_355_ = v_isSharedCheck_370_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_missingChoiceResolutions_352_);
lean_inc(v_partialFormatters_351_);
lean_inc(v_missingFormatters_350_);
lean_inc(v_freshTagId_349_);
lean_inc(v_shareCommonState_348_);
lean_inc(v_toBacktrackableState_347_);
lean_dec(v___y_346_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_370_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_369_; 
v___x_356_ = l_Lean_ShareCommon_objectFactory;
v___x_357_ = lean_state_sharecommon(v___x_356_, v_shareCommonState_348_, v_v_344_);
v_fst_358_ = lean_ctor_get(v___x_357_, 0);
v_snd_359_ = lean_ctor_get(v___x_357_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_369_ == 0)
{
v___x_361_ = v___x_357_;
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_snd_359_);
lean_inc(v_fst_358_);
lean_dec(v___x_357_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_369_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_snd_359_);
v___x_364_ = v___x_354_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_toBacktrackableState_347_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_snd_359_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_freshTagId_349_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_missingFormatters_350_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_partialFormatters_351_);
lean_ctor_set(v_reuseFailAlloc_368_, 5, v_missingChoiceResolutions_352_);
v___x_364_ = v_reuseFailAlloc_368_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_366_; 
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_fst_358_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed(lean_object* v_00_u03b1_371_, lean_object* v_v_372_, lean_object* v_x_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(v_00_u03b1_371_, v_v_372_, v_x_373_, v___y_374_);
lean_dec_ref(v_x_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_FormattedWhitespace_merge(lean_object* v_t1_378_, lean_object* v_t2_379_){
_start:
{
lean_object* v_formattedLeadingRanges_380_; lean_object* v_formattedTrailingRanges_381_; lean_object* v_formattedLeadingRanges_382_; lean_object* v_formattedTrailingRanges_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_392_; 
v_formattedLeadingRanges_380_ = lean_ctor_get(v_t1_378_, 0);
lean_inc_ref(v_formattedLeadingRanges_380_);
v_formattedTrailingRanges_381_ = lean_ctor_get(v_t1_378_, 1);
lean_inc_ref(v_formattedTrailingRanges_381_);
lean_dec_ref(v_t1_378_);
v_formattedLeadingRanges_382_ = lean_ctor_get(v_t2_379_, 0);
v_formattedTrailingRanges_383_ = lean_ctor_get(v_t2_379_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_t2_379_);
if (v_isSharedCheck_392_ == 0)
{
v___x_385_ = v_t2_379_;
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_formattedTrailingRanges_383_);
lean_inc(v_formattedLeadingRanges_382_);
lean_dec(v_t2_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_392_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = l_Array_append___redArg(v_formattedLeadingRanges_380_, v_formattedLeadingRanges_382_);
lean_dec_ref(v_formattedLeadingRanges_382_);
v___x_388_ = l_Array_append___redArg(v_formattedTrailingRanges_381_, v_formattedTrailingRanges_383_);
lean_dec_ref(v_formattedTrailingRanges_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 1, v___x_388_);
lean_ctor_set(v___x_385_, 0, v___x_387_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object* v_stx_393_, lean_object* v_i_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_arg_396_; uint8_t v___x_397_; 
v_arg_396_ = l_Lean_Syntax_getArg(v_stx_393_, v_i_394_);
v___x_397_ = l_Lean_Syntax_isMissing(v_arg_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_arg_396_);
lean_ctor_set(v___x_398_, 1, v_a_395_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v_arg_396_);
v___x_399_ = l_Lean_Fmt_Error_partialFormatter;
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_a_395_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg___boxed(lean_object* v_stx_401_, lean_object* v_i_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_401_, v_i_402_, v_a_403_);
lean_dec(v_i_402_);
lean_dec(v_stx_401_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21(lean_object* v_stx_405_, lean_object* v_i_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_405_, v_i_406_, v_a_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___boxed(lean_object* v_stx_410_, lean_object* v_i_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Fmt_getStxArg_x21(v_stx_410_, v_i_411_, v_a_412_, v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_i_411_);
lean_dec(v_stx_410_);
return v_res_414_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v___f_416_; 
v___x_415_ = l_Lean_Fmt_instInhabitedError_default;
v___f_416_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_416_, 0, v___x_415_);
return v___f_416_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___f_420_; lean_object* v___f_421_; lean_object* v___x_703__overap_422_; lean_object* v___x_423_; 
v___f_420_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_421_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_421_, 0, v___f_420_);
v___x_703__overap_422_ = lean_panic_fn_borrowed(v___f_421_, v_msg_417_);
lean_dec_ref(v___f_421_);
lean_inc_ref(v___y_418_);
v___x_423_ = lean_apply_2(v___x_703__overap_422_, v___y_418_, v___y_419_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___boxed(lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v_msg_424_, v___y_425_, v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_427_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(lean_object* v_msg_431_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0);
v___x_433_ = lean_panic_fn_borrowed(v___x_432_, v_msg_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object* v_x_434_){
_start:
{
lean_object* v_startPos_435_; 
v_startPos_435_ = lean_ctor_get(v_x_434_, 4);
lean_inc(v_startPos_435_);
return v_startPos_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Fmt_getLineInfo_x21___lam__0(v_x_436_);
lean_dec_ref(v_x_436_);
return v_res_437_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_getLineInfo_x21___lam__1(lean_object* v_x1_438_, lean_object* v_x2_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_x1_438_, v___x_440_);
v___x_442_ = lean_nat_dec_le(v___x_441_, v_x2_439_);
lean_dec(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1___boxed(lean_object* v_x1_443_, lean_object* v_x2_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Lean_Fmt_getLineInfo_x21___lam__1(v_x1_443_, v_x2_444_);
lean_dec(v_x2_444_);
lean_dec(v_x1_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__3(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__2));
v___x_451_ = lean_unsigned_to_nat(2u);
v___x_452_ = lean_unsigned_to_nat(87u);
v___x_453_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__1));
v___x_454_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_455_ = l_mkPanicMessageWithDecl(v___x_454_, v___x_453_, v___x_452_, v___x_451_, v___x_450_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__9(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_461_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__8));
v___x_462_ = lean_unsigned_to_nat(14u);
v___x_463_ = lean_unsigned_to_nat(22u);
v___x_464_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__7));
v___x_465_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__6));
v___x_466_ = l_mkPanicMessageWithDecl(v___x_465_, v___x_464_, v___x_463_, v___x_462_, v___x_461_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21(lean_object* v_pos_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___y_474_; lean_object* v_lineInfos_488_; lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___x_491_; 
v_lineInfos_488_ = lean_ctor_get(v_a_468_, 4);
v___f_489_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_490_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
lean_inc(v_pos_467_);
v___x_491_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_488_, v_pos_467_, v___f_489_, v___f_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_493_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_492_);
v___y_474_ = v___x_493_;
goto v___jp_473_;
}
else
{
lean_object* v_val_494_; 
v_val_494_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_494_);
lean_dec_ref_known(v___x_491_, 1);
v___y_474_ = v_val_494_;
goto v___jp_473_;
}
v___jp_470_:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__3, &l_Lean_Fmt_getLineInfo_x21___closed__3_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__3);
v___x_472_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v___x_471_, v_a_468_, v_a_469_);
return v___x_472_;
}
v___jp_473_:
{
lean_object* v_snd_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_486_; 
v_snd_475_ = lean_ctor_get(v___y_474_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v___y_474_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v___y_474_, 0);
lean_dec(v_unused_487_);
v___x_477_ = v___y_474_;
v_isShared_478_ = v_isSharedCheck_486_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_snd_475_);
lean_dec(v___y_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_486_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v_startPos_479_; lean_object* v_endPos_480_; uint8_t v___x_481_; 
v_startPos_479_ = lean_ctor_get(v_snd_475_, 4);
v_endPos_480_ = lean_ctor_get(v_snd_475_, 5);
v___x_481_ = lean_nat_dec_le(v_startPos_479_, v_pos_467_);
if (v___x_481_ == 0)
{
lean_del_object(v___x_477_);
lean_dec(v_snd_475_);
lean_dec(v_pos_467_);
goto v___jp_470_;
}
else
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_le(v_pos_467_, v_endPos_480_);
lean_dec(v_pos_467_);
if (v___x_482_ == 0)
{
lean_del_object(v___x_477_);
lean_dec(v_snd_475_);
goto v___jp_470_;
}
else
{
lean_object* v___x_484_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 1, v_a_469_);
lean_ctor_set(v___x_477_, 0, v_snd_475_);
v___x_484_ = v___x_477_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_snd_475_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_a_469_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___boxed(lean_object* v_pos_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Fmt_getLineInfo_x21(v_pos_495_, v_a_496_, v_a_497_);
lean_dec_ref(v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1(lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___f_502_; lean_object* v___f_503_; lean_object* v___x_1262__overap_504_; lean_object* v___x_505_; 
v___f_502_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_503_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_503_, 0, v___f_502_);
v___x_1262__overap_504_ = lean_panic_fn_borrowed(v___f_503_, v_msg_499_);
lean_dec_ref(v___f_503_);
lean_inc_ref(v___y_500_);
v___x_505_ = lean_apply_2(v___x_1262__overap_504_, v___y_500_, v___y_501_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1___boxed(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v_msg_506_, v___y_507_, v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(lean_object* v_a_510_, lean_object* v_b_511_){
_start:
{
lean_object* v_array_512_; lean_object* v_start_513_; lean_object* v_stop_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_527_; 
v_array_512_ = lean_ctor_get(v_a_510_, 0);
v_start_513_ = lean_ctor_get(v_a_510_, 1);
v_stop_514_ = lean_ctor_get(v_a_510_, 2);
v_isSharedCheck_527_ = !lean_is_exclusive(v_a_510_);
if (v_isSharedCheck_527_ == 0)
{
v___x_516_ = v_a_510_;
v_isShared_517_ = v_isSharedCheck_527_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_stop_514_);
lean_inc(v_start_513_);
lean_inc(v_array_512_);
lean_dec(v_a_510_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_527_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = lean_nat_dec_lt(v_start_513_, v_stop_514_);
if (v___x_518_ == 0)
{
lean_del_object(v___x_516_);
lean_dec(v_stop_514_);
lean_dec(v_start_513_);
lean_dec_ref(v_array_512_);
return v_b_511_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_start_513_, v___x_519_);
lean_inc_ref(v_array_512_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_520_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_array_512_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_stop_514_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_array_fget(v_array_512_, v_start_513_);
lean_dec(v_start_513_);
lean_dec_ref(v_array_512_);
v___x_524_ = lean_array_push(v_b_511_, v___x_523_);
v_a_510_ = v___x_522_;
v_b_511_ = v___x_524_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfos___closed__3(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_532_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__2));
v___x_533_ = lean_unsigned_to_nat(2u);
v___x_534_ = lean_unsigned_to_nat(95u);
v___x_535_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__1));
v___x_536_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_537_ = l_mkPanicMessageWithDecl(v___x_536_, v___x_535_, v___x_534_, v___x_533_, v___x_532_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos(lean_object* v_pos_538_, lean_object* v_tailPos_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_lineInfos_542_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___y_568_; lean_object* v___x_574_; 
v_lineInfos_542_ = lean_ctor_get(v_a_540_, 4);
v___f_565_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_566_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_574_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_542_, v_pos_538_, v___f_565_, v___f_566_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_576_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_575_);
v___y_568_ = v___x_576_;
goto v___jp_567_;
}
else
{
lean_object* v_val_577_; 
v_val_577_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_574_, 1);
v___y_568_ = v_val_577_;
goto v___jp_567_;
}
v___jp_543_:
{
lean_object* v_fst_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_563_; 
v_fst_546_ = lean_ctor_get(v___y_545_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___y_545_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v___y_545_, 1);
lean_dec(v_unused_564_);
v___x_548_ = v___y_545_;
v_isShared_549_ = v_isSharedCheck_563_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_fst_546_);
lean_dec(v___y_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_563_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_550_ = lean_unsigned_to_nat(1u);
v___x_551_ = lean_nat_add(v_fst_546_, v___x_550_);
lean_dec(v_fst_546_);
lean_inc_ref(v_lineInfos_542_);
v___x_552_ = l_Array_toSubarray___redArg(v_lineInfos_542_, v___y_544_, v___x_551_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_555_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_552_, v___x_554_);
v___x_556_ = lean_array_get_size(v___x_555_);
v___x_557_ = lean_nat_dec_eq(v___x_556_, v___x_553_);
if (v___x_557_ == 0)
{
lean_object* v___x_559_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v_a_541_);
lean_ctor_set(v___x_548_, 0, v___x_555_);
v___x_559_ = v___x_548_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_a_541_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec_ref(v___x_555_);
lean_del_object(v___x_548_);
v___x_561_ = lean_obj_once(&l_Lean_Fmt_getLineInfos___closed__3, &l_Lean_Fmt_getLineInfos___closed__3_once, _init_l_Lean_Fmt_getLineInfos___closed__3);
v___x_562_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v___x_561_, v_a_540_, v_a_541_);
return v___x_562_;
}
}
}
v___jp_567_:
{
lean_object* v_fst_569_; lean_object* v___x_570_; 
v_fst_569_ = lean_ctor_get(v___y_568_, 0);
lean_inc(v_fst_569_);
lean_dec_ref(v___y_568_);
v___x_570_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_542_, v_tailPos_539_, v___f_565_, v___f_566_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_572_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_571_);
v___y_544_ = v_fst_569_;
v___y_545_ = v___x_572_;
goto v___jp_543_;
}
else
{
lean_object* v_val_573_; 
v_val_573_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_val_573_);
lean_dec_ref_known(v___x_570_, 1);
v___y_544_ = v_fst_569_;
v___y_545_ = v_val_573_;
goto v___jp_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos___boxed(lean_object* v_pos_578_, lean_object* v_tailPos_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Fmt_getLineInfos(v_pos_578_, v_tailPos_579_, v_a_580_, v_a_581_);
lean_dec_ref(v_a_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0(lean_object* v_inst_583_, lean_object* v_R_584_, lean_object* v_a_585_, lean_object* v_b_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v_a_585_, v_b_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f(lean_object* v_pos_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_lineInfos_591_; lean_object* v___y_593_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___x_615_; 
v_lineInfos_591_ = lean_ctor_get(v_a_589_, 4);
v___f_613_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_614_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_615_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_591_, v_pos_588_, v___f_613_, v___f_614_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_617_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_616_);
v___y_593_ = v___x_617_;
goto v___jp_592_;
}
else
{
lean_object* v_val_618_; 
v_val_618_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v___x_615_, 1);
v___y_593_ = v_val_618_;
goto v___jp_592_;
}
v___jp_592_:
{
lean_object* v_fst_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_611_; 
v_fst_594_ = lean_ctor_get(v___y_593_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___y_593_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; 
v_unused_612_ = lean_ctor_get(v___y_593_, 1);
lean_dec(v_unused_612_);
v___x_596_ = v___y_593_;
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_fst_594_);
lean_dec(v___y_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_611_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_fst_594_, v___x_598_);
lean_dec(v_fst_594_);
v___x_600_ = lean_array_get_size(v_lineInfos_591_);
v___x_601_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_a_590_);
lean_ctor_set(v___x_596_, 0, v___x_602_);
v___x_604_ = v___x_596_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_a_590_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_array_fget_borrowed(v_lineInfos_591_, v___x_599_);
lean_dec(v___x_599_);
lean_inc(v___x_606_);
v___x_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v_a_590_);
lean_ctor_set(v___x_596_, 0, v___x_607_);
v___x_609_ = v___x_596_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_590_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f___boxed(lean_object* v_pos_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Fmt_getNextLineInfo_x3f(v_pos_619_, v_a_620_, v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(size_t v_sz_623_, size_t v_i_624_, lean_object* v_bs_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_bs_625_);
lean_ctor_set(v___x_628_, 1, v___y_626_);
return v___x_628_;
}
else
{
lean_object* v_v_629_; lean_object* v_fst_630_; lean_object* v_snd_631_; lean_object* v___x_632_; lean_object* v_bs_x27_633_; lean_object* v_a_635_; lean_object* v_a_636_; 
v_v_629_ = lean_array_uget_borrowed(v_bs_625_, v_i_624_);
v_fst_630_ = lean_ctor_get(v_v_629_, 0);
lean_inc(v_fst_630_);
v_snd_631_ = lean_ctor_get(v_v_629_, 1);
lean_inc(v_snd_631_);
v___x_632_ = lean_unsigned_to_nat(0u);
v_bs_x27_633_ = lean_array_uset(v_bs_625_, v_i_624_, v___x_632_);
if (lean_obj_tag(v_snd_631_) == 0)
{
v_a_635_ = v_fst_630_;
v_a_636_ = v___y_626_;
goto v___jp_634_;
}
else
{
lean_object* v_val_641_; lean_object* v_doc_642_; lean_object* v_metaData_643_; lean_object* v___x_644_; 
v_val_641_ = lean_ctor_get(v_snd_631_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_snd_631_, 1);
v_doc_642_ = lean_ctor_get(v_fst_630_, 0);
lean_inc(v_doc_642_);
v_metaData_643_ = lean_ctor_get(v_fst_630_, 1);
lean_inc(v_metaData_643_);
lean_dec(v_fst_630_);
v___x_644_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_642_, v_val_641_, v___y_626_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v_doc_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
v_a_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_644_, 2);
v_doc_647_ = lean_ctor_get(v_a_645_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_a_645_, 1);
lean_dec(v_unused_655_);
v___x_649_ = v_a_645_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_doc_647_);
lean_dec(v_a_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 1, v_metaData_643_);
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_doc_647_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_metaData_643_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
v_a_635_ = v___x_652_;
v_a_636_ = v_a_646_;
goto v___jp_634_;
}
}
}
else
{
lean_object* v_a_656_; lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_metaData_643_);
lean_dec_ref(v_bs_x27_633_);
v_a_656_ = lean_ctor_get(v___x_644_, 0);
v_a_657_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_644_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_inc(v_a_656_);
lean_dec(v___x_644_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_656_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
v___jp_634_:
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_624_, v___x_637_);
v___x_639_ = lean_array_uset(v_bs_x27_633_, v_i_624_, v_a_635_);
v_i_624_ = v___x_638_;
v_bs_625_ = v___x_639_;
v___y_626_ = v_a_636_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg___boxed(lean_object* v_sz_665_, lean_object* v_i_666_, lean_object* v_bs_667_, lean_object* v___y_668_){
_start:
{
size_t v_sz_boxed_669_; size_t v_i_boxed_670_; lean_object* v_res_671_; 
v_sz_boxed_669_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_670_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_boxed_669_, v_i_boxed_670_, v_bs_667_, v___y_668_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace(lean_object* v_stx_672_, lean_object* v_fmtLeading_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_stx_672_);
if (lean_obj_tag(v___x_676_) == 1)
{
lean_object* v_val_677_; lean_object* v___x_678_; 
v_val_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_Syntax_getLeading_x3f(v_val_677_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_680_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_678_, 1);
lean_inc_ref(v_a_674_);
v___x_680_ = lean_apply_4(v_fmtLeading_673_, v_val_677_, v_val_679_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v_a_682_; size_t v_sz_683_; size_t v___x_684_; lean_object* v___x_685_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
v_a_682_ = lean_ctor_get(v___x_680_, 1);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_680_, 2);
v_sz_683_ = lean_array_size(v_a_681_);
v___x_684_ = ((size_t)0ULL);
v___x_685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_683_, v___x_684_, v_a_681_, v_a_682_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_a_687_ = lean_ctor_get(v___x_685_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v___x_685_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = l_Lean_Fmt_TaggedDoc_join(v_a_686_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_a_687_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
v_a_696_ = lean_ctor_get(v___x_685_, 0);
v_a_697_ = lean_ctor_get(v___x_685_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_685_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_inc(v_a_696_);
lean_dec(v___x_685_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_696_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_705_ = lean_ctor_get(v___x_680_, 0);
v_a_706_ = lean_ctor_get(v___x_680_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_680_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_inc(v_a_705_);
lean_dec(v___x_680_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_705_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v___x_678_);
lean_dec(v_val_677_);
lean_dec_ref(v_fmtLeading_673_);
v___x_714_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v_a_675_);
return v___x_715_;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v___x_676_);
lean_dec_ref(v_fmtLeading_673_);
v___x_716_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_a_675_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace___boxed(lean_object* v_stx_718_, lean_object* v_fmtLeading_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_718_, v_fmtLeading_719_, v_a_720_, v_a_721_);
lean_dec_ref(v_a_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(size_t v_sz_723_, size_t v_i_724_, lean_object* v_bs_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_723_, v_i_724_, v_bs_725_, v___y_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___boxed(lean_object* v_sz_729_, lean_object* v_i_730_, lean_object* v_bs_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
size_t v_sz_boxed_734_; size_t v_i_boxed_735_; lean_object* v_res_736_; 
v_sz_boxed_734_ = lean_unbox_usize(v_sz_729_);
lean_dec(v_sz_729_);
v_i_boxed_735_ = lean_unbox_usize(v_i_730_);
lean_dec(v_i_730_);
v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(v_sz_boxed_734_, v_i_boxed_735_, v_bs_731_, v___y_732_, v___y_733_);
lean_dec_ref(v___y_732_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace(lean_object* v_stx_737_, lean_object* v_fmtTrailing_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v_stx_737_);
if (lean_obj_tag(v___x_741_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_743_; 
v_val_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_Syntax_getTrailing_x3f(v_val_742_);
if (lean_obj_tag(v___x_743_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_745_; 
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_743_, 1);
lean_inc_ref(v_a_739_);
v___x_745_ = lean_apply_4(v_fmtTrailing_738_, v_val_742_, v_val_744_, v_a_739_, v_a_740_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v_a_747_; size_t v_sz_748_; size_t v___x_749_; lean_object* v___x_750_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
v_a_747_ = lean_ctor_get(v___x_745_, 1);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_745_, 2);
v_sz_748_ = lean_array_size(v_a_746_);
v___x_749_ = ((size_t)0ULL);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_748_, v___x_749_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
v_a_752_ = lean_ctor_get(v___x_750_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v___x_750_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_inc(v_a_751_);
lean_dec(v___x_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_756_ = l_Lean_Fmt_TaggedDoc_join(v_a_751_);
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_a_752_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_761_ = lean_ctor_get(v___x_750_, 0);
v_a_762_ = lean_ctor_get(v___x_750_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_750_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_inc(v_a_761_);
lean_dec(v___x_750_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_a_762_);
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
else
{
lean_object* v_a_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
v_a_770_ = lean_ctor_get(v___x_745_, 0);
v_a_771_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_745_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_inc(v_a_770_);
lean_dec(v___x_745_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_770_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_a_771_);
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
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v___x_743_);
lean_dec(v_val_742_);
lean_dec_ref(v_fmtTrailing_738_);
v___x_779_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v_a_740_);
return v___x_780_;
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v___x_741_);
lean_dec_ref(v_fmtTrailing_738_);
v___x_781_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_a_740_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace___boxed(lean_object* v_stx_783_, lean_object* v_fmtTrailing_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_783_, v_fmtTrailing_784_, v_a_785_, v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(lean_object* v_env_788_, lean_object* v_opts_789_, lean_object* v_kind_790_){
_start:
{
uint8_t v___x_791_; lean_object* v___x_792_; 
v___x_791_ = 1;
v___x_792_ = l_Lean_Environment_evalConst___redArg(v_env_788_, v_opts_789_, v_kind_790_, v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v___x_793_; 
lean_dec_ref_known(v___x_792_, 1);
v___x_793_ = lean_box(0);
return v___x_793_;
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_792_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_792_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1___boxed(lean_object* v_env_802_, lean_object* v_opts_803_, lean_object* v_kind_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(v_env_802_, v_opts_803_, v_kind_804_);
lean_dec(v_kind_804_);
lean_dec_ref(v_opts_803_);
lean_dec_ref(v_env_802_);
return v_res_805_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_box(0);
v___x_807_ = lean_unsigned_to_nat(16u);
v___x_808_ = lean_mk_array(v___x_807_, v___x_806_);
return v___x_808_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(lean_object* v_env_823_, lean_object* v_opts_824_, lean_object* v_kind_825_){
_start:
{
uint8_t v___x_826_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___y_845_; lean_object* v___y_846_; uint8_t v___y_847_; lean_object* v___x_895_; 
v___x_826_ = 0;
lean_inc(v_kind_825_);
lean_inc_ref(v_env_823_);
v___x_895_ = l_Lean_Environment_find_x3f(v_env_823_, v_kind_825_, v___x_826_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_896_; 
lean_dec(v_kind_825_);
lean_dec_ref(v_env_823_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
else
{
lean_object* v_val_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_val_897_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_895_, 1);
v___x_898_ = l_Lean_ConstantInfo_type(v_val_897_);
lean_dec(v_val_897_);
v___x_899_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_900_ = l_Lean_Expr_isConstOf(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_902_ = l_Lean_Expr_isConstOf(v___x_898_, v___x_901_);
lean_dec_ref(v___x_898_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v_kind_825_);
lean_dec_ref(v_env_823_);
v___x_903_ = lean_box(0);
return v___x_903_;
}
else
{
goto v___jp_860_;
}
}
else
{
lean_dec_ref(v___x_898_);
goto v___jp_860_;
}
}
v___jp_827_:
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(1u);
v___x_834_ = lean_nat_add(v___y_830_, v___x_833_);
lean_dec(v___y_830_);
v___x_835_ = lean_nat_dec_eq(v___x_834_, v___y_832_);
lean_dec(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v___y_832_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
else
{
uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_eq(v___y_832_, v___y_828_);
lean_dec(v___y_828_);
lean_dec(v___y_832_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec(v___y_829_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_840_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_840_, 0, v___y_829_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*2, v___y_831_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*2 + 1, v___x_826_);
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
}
v___jp_842_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc(v___y_843_);
lean_inc(v___y_846_);
lean_inc(v___y_844_);
v___x_848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_848_, 0, v___y_844_);
lean_ctor_set(v___x_848_, 1, v___y_846_);
lean_ctor_set(v___x_848_, 2, v___y_843_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
if (v___y_847_ == 0)
{
uint8_t v___x_850_; 
v___x_850_ = lean_nat_dec_eq(v___y_844_, v___y_843_);
if (v___x_850_ == 0)
{
v___y_828_ = v___y_843_;
v___y_829_ = v___x_849_;
v___y_830_ = v___y_844_;
v___y_831_ = v___y_845_;
v___y_832_ = v___y_846_;
goto v___jp_827_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_add(v___y_843_, v___x_851_);
v___x_853_ = lean_nat_dec_eq(v___y_846_, v___x_852_);
lean_dec(v___x_852_);
if (v___x_853_ == 0)
{
v___y_828_ = v___y_843_;
v___y_829_ = v___x_849_;
v___y_830_ = v___y_844_;
v___y_831_ = v___y_845_;
v___y_832_ = v___y_846_;
goto v___jp_827_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v___y_846_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
v___x_854_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_855_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_855_, 0, v___x_849_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*2, v___x_826_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*2 + 1, v___x_826_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v___y_846_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
v___x_857_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_858_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_858_, 0, v___x_849_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*2, v___x_826_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*2 + 1, v___x_826_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
v___jp_860_:
{
uint8_t v___x_861_; lean_object* v___x_862_; 
v___x_861_ = 1;
v___x_862_ = l_Lean_Environment_evalConst___redArg(v_env_823_, v_opts_824_, v_kind_825_, v___x_861_);
lean_dec(v_kind_825_);
lean_dec_ref(v_env_823_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
lean_dec_ref_known(v___x_862_, 1);
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_a_864_; 
v_a_864_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_862_, 1);
if (lean_obj_tag(v_a_864_) == 4)
{
lean_object* v_p_865_; 
v_p_865_ = lean_ctor_get(v_a_864_, 3);
lean_inc_ref(v_p_865_);
if (lean_obj_tag(v_p_865_) == 2)
{
lean_object* v_name_866_; 
v_name_866_ = lean_ctor_get(v_p_865_, 0);
lean_inc(v_name_866_);
if (lean_obj_tag(v_name_866_) == 1)
{
lean_object* v_pre_867_; 
v_pre_867_ = lean_ctor_get(v_name_866_, 0);
if (lean_obj_tag(v_pre_867_) == 0)
{
lean_object* v_prec_868_; lean_object* v_lhsPrec_869_; lean_object* v_p_u2081_870_; lean_object* v_p_u2082_871_; lean_object* v_str_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_prec_868_ = lean_ctor_get(v_a_864_, 1);
lean_inc(v_prec_868_);
v_lhsPrec_869_ = lean_ctor_get(v_a_864_, 2);
lean_inc(v_lhsPrec_869_);
lean_dec_ref_known(v_a_864_, 4);
v_p_u2081_870_ = lean_ctor_get(v_p_865_, 1);
lean_inc_ref(v_p_u2081_870_);
v_p_u2082_871_ = lean_ctor_get(v_p_865_, 2);
lean_inc_ref(v_p_u2082_871_);
lean_dec_ref_known(v_p_865_, 3);
v_str_872_ = lean_ctor_get(v_name_866_, 1);
lean_inc_ref(v_str_872_);
lean_dec_ref_known(v_name_866_, 2);
v___x_873_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_874_ = lean_string_dec_eq(v_str_872_, v___x_873_);
lean_dec_ref(v_str_872_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
lean_dec_ref(v_p_u2082_871_);
lean_dec_ref(v_p_u2081_870_);
lean_dec(v_lhsPrec_869_);
lean_dec(v_prec_868_);
v___x_875_ = lean_box(0);
return v___x_875_;
}
else
{
if (lean_obj_tag(v_p_u2081_870_) == 5)
{
lean_dec_ref_known(v_p_u2081_870_, 1);
if (lean_obj_tag(v_p_u2082_871_) == 7)
{
lean_object* v_catName_876_; 
v_catName_876_ = lean_ctor_get(v_p_u2082_871_, 0);
lean_inc(v_catName_876_);
if (lean_obj_tag(v_catName_876_) == 1)
{
lean_object* v_pre_877_; 
v_pre_877_ = lean_ctor_get(v_catName_876_, 0);
if (lean_obj_tag(v_pre_877_) == 0)
{
lean_object* v_rbp_878_; lean_object* v_str_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_rbp_878_ = lean_ctor_get(v_p_u2082_871_, 1);
lean_inc(v_rbp_878_);
lean_dec_ref_known(v_p_u2082_871_, 2);
v_str_879_ = lean_ctor_get(v_catName_876_, 1);
lean_inc_ref(v_str_879_);
lean_dec_ref_known(v_catName_876_, 2);
v___x_880_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_881_ = lean_string_dec_eq(v_str_879_, v___x_880_);
lean_dec_ref(v_str_879_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
lean_dec(v_rbp_878_);
lean_dec(v_lhsPrec_869_);
lean_dec(v_prec_868_);
v___x_882_ = lean_box(0);
return v___x_882_;
}
else
{
uint8_t v___x_883_; 
v___x_883_ = lean_nat_dec_eq(v_prec_868_, v_lhsPrec_869_);
if (v___x_883_ == 0)
{
v___y_843_ = v_rbp_878_;
v___y_844_ = v_prec_868_;
v___y_845_ = v___x_881_;
v___y_846_ = v_lhsPrec_869_;
v___y_847_ = v___x_826_;
goto v___jp_842_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_lhsPrec_869_, v___x_884_);
v___x_886_ = lean_nat_dec_eq(v___x_885_, v_rbp_878_);
lean_dec(v___x_885_);
v___y_843_ = v_rbp_878_;
v___y_844_ = v_prec_868_;
v___y_845_ = v___x_881_;
v___y_846_ = v_lhsPrec_869_;
v___y_847_ = v___x_886_;
goto v___jp_842_;
}
}
}
else
{
lean_object* v___x_887_; 
lean_dec_ref_known(v_catName_876_, 2);
lean_dec_ref_known(v_p_u2082_871_, 2);
lean_dec(v_lhsPrec_869_);
lean_dec(v_prec_868_);
v___x_887_ = lean_box(0);
return v___x_887_;
}
}
else
{
lean_object* v___x_888_; 
lean_dec_ref_known(v_p_u2082_871_, 2);
lean_dec(v_catName_876_);
lean_dec(v_lhsPrec_869_);
lean_dec(v_prec_868_);
v___x_888_ = lean_box(0);
return v___x_888_;
}
}
else
{
lean_object* v___x_889_; 
lean_dec_ref(v_p_u2082_871_);
lean_dec(v_lhsPrec_869_);
lean_dec(v_prec_868_);
v___x_889_ = lean_box(0);
return v___x_889_;
}
}
else
{
lean_object* v___x_890_; 
lean_dec_ref(v_p_u2082_871_);
lean_dec_ref(v_p_u2081_870_);
lean_dec(v_lhsPrec_869_);
lean_dec(v_prec_868_);
v___x_890_ = lean_box(0);
return v___x_890_;
}
}
}
else
{
lean_object* v___x_891_; 
lean_dec_ref_known(v_name_866_, 2);
lean_dec_ref_known(v_p_865_, 3);
lean_dec_ref_known(v_a_864_, 4);
v___x_891_ = lean_box(0);
return v___x_891_;
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v_name_866_);
lean_dec_ref_known(v_p_865_, 3);
lean_dec_ref_known(v_a_864_, 4);
v___x_892_ = lean_box(0);
return v___x_892_;
}
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v_p_865_);
lean_dec_ref_known(v_a_864_, 4);
v___x_893_ = lean_box(0);
return v___x_893_;
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v_a_864_);
v___x_894_ = lean_box(0);
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___boxed(lean_object* v_env_904_, lean_object* v_opts_905_, lean_object* v_kind_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_904_, v_opts_905_, v_kind_906_);
lean_dec_ref(v_opts_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(lean_object* v_env_908_, lean_object* v_opts_909_, lean_object* v_kind_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = l_Lean_Fmt_infixFmtAttribute;
lean_inc_ref(v_env_908_);
v___x_912_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_911_, v_env_908_, v_kind_910_);
v___x_913_ = l_List_head_x3f___redArg(v___x_912_);
lean_dec(v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v___x_914_; 
v___x_914_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_908_, v_opts_909_, v_kind_910_);
return v___x_914_;
}
else
{
lean_dec(v_kind_910_);
lean_dec_ref(v_env_908_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f___boxed(lean_object* v_env_915_, lean_object* v_opts_916_, lean_object* v_kind_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_915_, v_opts_916_, v_kind_917_);
lean_dec_ref(v_opts_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(lean_object* v_env_919_, lean_object* v_opts_920_, lean_object* v_kind_921_){
_start:
{
uint8_t v___x_922_; lean_object* v___x_923_; 
v___x_922_ = 1;
v___x_923_ = l_Lean_Environment_evalConst___redArg(v_env_919_, v_opts_920_, v_kind_921_, v___x_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v___x_924_; 
lean_dec_ref_known(v___x_923_, 1);
v___x_924_ = lean_box(0);
return v___x_924_;
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_925_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_923_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1___boxed(lean_object* v_env_933_, lean_object* v_opts_934_, lean_object* v_kind_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(v_env_933_, v_opts_934_, v_kind_935_);
lean_dec(v_kind_935_);
lean_dec_ref(v_opts_934_);
lean_dec_ref(v_env_933_);
return v_res_936_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(lean_object* v_env_937_, lean_object* v_opts_938_, lean_object* v_kind_939_){
_start:
{
uint8_t v___x_940_; lean_object* v___x_941_; 
v___x_940_ = 0;
lean_inc(v_kind_939_);
lean_inc_ref(v_env_937_);
v___x_941_ = l_Lean_Environment_find_x3f(v_env_937_, v_kind_939_, v___x_940_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_dec(v_kind_939_);
lean_dec_ref(v_env_937_);
return v___x_940_;
}
else
{
lean_object* v_val_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_val_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_val_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = l_Lean_ConstantInfo_type(v_val_942_);
lean_dec(v_val_942_);
v___x_944_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_945_ = l_Lean_Expr_isConstOf(v___x_943_, v___x_944_);
lean_dec_ref(v___x_943_);
if (v___x_945_ == 0)
{
lean_dec(v_kind_939_);
lean_dec_ref(v_env_937_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Environment_evalConst___redArg(v_env_937_, v_opts_938_, v_kind_939_, v___x_945_);
lean_dec(v_kind_939_);
lean_dec_ref(v_env_937_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_dec_ref_known(v___x_946_, 1);
return v___x_940_;
}
else
{
lean_object* v_a_947_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
if (lean_obj_tag(v_a_947_) == 3)
{
lean_object* v_p_948_; 
v_p_948_ = lean_ctor_get(v_a_947_, 2);
lean_inc_ref(v_p_948_);
if (lean_obj_tag(v_p_948_) == 2)
{
lean_object* v_name_949_; 
v_name_949_ = lean_ctor_get(v_p_948_, 0);
lean_inc(v_name_949_);
if (lean_obj_tag(v_name_949_) == 1)
{
lean_object* v_pre_950_; 
v_pre_950_ = lean_ctor_get(v_name_949_, 0);
if (lean_obj_tag(v_pre_950_) == 0)
{
lean_object* v_prec_951_; lean_object* v_p_u2081_952_; lean_object* v_p_u2082_953_; lean_object* v_str_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_prec_951_ = lean_ctor_get(v_a_947_, 1);
lean_inc(v_prec_951_);
lean_dec_ref_known(v_a_947_, 3);
v_p_u2081_952_ = lean_ctor_get(v_p_948_, 1);
lean_inc_ref(v_p_u2081_952_);
v_p_u2082_953_ = lean_ctor_get(v_p_948_, 2);
lean_inc_ref(v_p_u2082_953_);
lean_dec_ref_known(v_p_948_, 3);
v_str_954_ = lean_ctor_get(v_name_949_, 1);
lean_inc_ref(v_str_954_);
lean_dec_ref_known(v_name_949_, 2);
v___x_955_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_956_ = lean_string_dec_eq(v_str_954_, v___x_955_);
lean_dec_ref(v_str_954_);
if (v___x_956_ == 0)
{
lean_dec_ref(v_p_u2082_953_);
lean_dec_ref(v_p_u2081_952_);
lean_dec(v_prec_951_);
return v___x_956_;
}
else
{
if (lean_obj_tag(v_p_u2081_952_) == 5)
{
lean_dec_ref_known(v_p_u2081_952_, 1);
if (lean_obj_tag(v_p_u2082_953_) == 7)
{
lean_object* v_catName_957_; 
v_catName_957_ = lean_ctor_get(v_p_u2082_953_, 0);
lean_inc(v_catName_957_);
if (lean_obj_tag(v_catName_957_) == 1)
{
lean_object* v_pre_958_; 
v_pre_958_ = lean_ctor_get(v_catName_957_, 0);
if (lean_obj_tag(v_pre_958_) == 0)
{
lean_object* v_rbp_959_; lean_object* v_str_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_rbp_959_ = lean_ctor_get(v_p_u2082_953_, 1);
lean_inc(v_rbp_959_);
lean_dec_ref_known(v_p_u2082_953_, 2);
v_str_960_ = lean_ctor_get(v_catName_957_, 1);
lean_inc_ref(v_str_960_);
lean_dec_ref_known(v_catName_957_, 2);
v___x_961_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_962_ = lean_string_dec_eq(v_str_960_, v___x_961_);
lean_dec_ref(v_str_960_);
if (v___x_962_ == 0)
{
lean_dec(v_rbp_959_);
lean_dec(v_prec_951_);
return v___x_962_;
}
else
{
uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_eq(v_prec_951_, v_rbp_959_);
lean_dec(v_rbp_959_);
lean_dec(v_prec_951_);
return v___x_963_;
}
}
else
{
lean_dec_ref_known(v_catName_957_, 2);
lean_dec_ref_known(v_p_u2082_953_, 2);
lean_dec(v_prec_951_);
return v___x_940_;
}
}
else
{
lean_dec_ref_known(v_p_u2082_953_, 2);
lean_dec(v_catName_957_);
lean_dec(v_prec_951_);
return v___x_940_;
}
}
else
{
lean_dec_ref(v_p_u2082_953_);
lean_dec(v_prec_951_);
return v___x_940_;
}
}
else
{
lean_dec_ref(v_p_u2082_953_);
lean_dec_ref(v_p_u2081_952_);
lean_dec(v_prec_951_);
return v___x_940_;
}
}
}
else
{
lean_dec_ref_known(v_name_949_, 2);
lean_dec_ref_known(v_p_948_, 3);
lean_dec_ref_known(v_a_947_, 3);
return v___x_940_;
}
}
else
{
lean_dec_ref_known(v_p_948_, 3);
lean_dec(v_name_949_);
lean_dec_ref_known(v_a_947_, 3);
return v___x_940_;
}
}
else
{
lean_dec_ref_known(v_a_947_, 3);
lean_dec_ref(v_p_948_);
return v___x_940_;
}
}
else
{
lean_dec(v_a_947_);
return v___x_940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter___boxed(lean_object* v_env_964_, lean_object* v_opts_965_, lean_object* v_kind_966_){
_start:
{
uint8_t v_res_967_; lean_object* v_r_968_; 
v_res_967_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_964_, v_opts_965_, v_kind_966_);
lean_dec_ref(v_opts_965_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(lean_object* v_env_969_, lean_object* v_opts_970_, lean_object* v_kind_971_){
_start:
{
uint8_t v___x_972_; lean_object* v___x_973_; 
v___x_972_ = 1;
v___x_973_ = l_Lean_Environment_evalConst___redArg(v_env_969_, v_opts_970_, v_kind_971_, v___x_972_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_974_; 
lean_dec_ref_known(v___x_973_, 1);
v___x_974_ = lean_box(0);
return v___x_974_;
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_a_975_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_973_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_973_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1___boxed(lean_object* v_env_983_, lean_object* v_opts_984_, lean_object* v_kind_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(v_env_983_, v_opts_984_, v_kind_985_);
lean_dec(v_kind_985_);
lean_dec_ref(v_opts_984_);
lean_dec_ref(v_env_983_);
return v_res_986_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(lean_object* v_env_987_, lean_object* v_opts_988_, lean_object* v_kind_989_){
_start:
{
uint8_t v___x_990_; lean_object* v___x_991_; 
v___x_990_ = 0;
lean_inc(v_kind_989_);
lean_inc_ref(v_env_987_);
v___x_991_ = l_Lean_Environment_find_x3f(v_env_987_, v_kind_989_, v___x_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_dec(v_kind_989_);
lean_dec_ref(v_env_987_);
return v___x_990_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_val_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = l_Lean_ConstantInfo_type(v_val_992_);
lean_dec(v_val_992_);
v___x_994_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_995_ = l_Lean_Expr_isConstOf(v___x_993_, v___x_994_);
lean_dec_ref(v___x_993_);
if (v___x_995_ == 0)
{
lean_dec(v_kind_989_);
lean_dec_ref(v_env_987_);
return v___x_995_;
}
else
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Environment_evalConst___redArg(v_env_987_, v_opts_988_, v_kind_989_, v___x_995_);
lean_dec(v_kind_989_);
lean_dec_ref(v_env_987_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_dec_ref_known(v___x_996_, 1);
return v___x_990_;
}
else
{
lean_object* v_a_997_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
if (lean_obj_tag(v_a_997_) == 4)
{
lean_object* v_p_998_; 
v_p_998_ = lean_ctor_get(v_a_997_, 3);
if (lean_obj_tag(v_p_998_) == 5)
{
lean_object* v_prec_999_; lean_object* v_lhsPrec_1000_; uint8_t v___x_1001_; 
v_prec_999_ = lean_ctor_get(v_a_997_, 1);
lean_inc(v_prec_999_);
v_lhsPrec_1000_ = lean_ctor_get(v_a_997_, 2);
lean_inc(v_lhsPrec_1000_);
lean_dec_ref_known(v_a_997_, 4);
v___x_1001_ = lean_nat_dec_eq(v_prec_999_, v_lhsPrec_1000_);
lean_dec(v_lhsPrec_1000_);
lean_dec(v_prec_999_);
return v___x_1001_;
}
else
{
lean_dec_ref_known(v_a_997_, 4);
return v___x_990_;
}
}
else
{
lean_dec(v_a_997_);
return v___x_990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter___boxed(lean_object* v_env_1002_, lean_object* v_opts_1003_, lean_object* v_kind_1004_){
_start:
{
uint8_t v_res_1005_; lean_object* v_r_1006_; 
v_res_1005_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_1002_, v_opts_1003_, v_kind_1004_);
lean_dec_ref(v_opts_1003_);
v_r_1006_ = lean_box(v_res_1005_);
return v_r_1006_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(lean_object* v_a_1133_, lean_object* v_as_1134_, size_t v_i_1135_, size_t v_stop_1136_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_usize_dec_eq(v_i_1135_, v_stop_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_array_uget_borrowed(v_as_1134_, v_i_1135_);
v___x_1139_ = lean_name_eq(v_a_1133_, v___x_1138_);
if (v___x_1139_ == 0)
{
size_t v___x_1140_; size_t v___x_1141_; 
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_add(v_i_1135_, v___x_1140_);
v_i_1135_ = v___x_1141_;
goto _start;
}
else
{
return v___x_1139_;
}
}
else
{
uint8_t v___x_1143_; 
v___x_1143_ = 0;
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0___boxed(lean_object* v_a_1144_, lean_object* v_as_1145_, lean_object* v_i_1146_, lean_object* v_stop_1147_){
_start:
{
size_t v_i_boxed_1148_; size_t v_stop_boxed_1149_; uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_i_boxed_1148_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_stop_boxed_1149_ = lean_unbox_usize(v_stop_1147_);
lean_dec(v_stop_1147_);
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1144_, v_as_1145_, v_i_boxed_1148_, v_stop_boxed_1149_);
lean_dec_ref(v_as_1145_);
lean_dec(v_a_1144_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(lean_object* v_as_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_array_get_size(v_as_1152_);
v___x_1156_ = lean_nat_dec_lt(v___x_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
return v___x_1156_;
}
else
{
size_t v___x_1157_; size_t v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = ((size_t)0ULL);
v___x_1158_ = lean_usize_of_nat(v___x_1155_);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1153_, v_as_1152_, v___x_1157_, v___x_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0___boxed(lean_object* v_as_1160_, lean_object* v_a_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v_as_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_as_1160_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(lean_object* v_x_1169_){
_start:
{
switch(lean_obj_tag(v_x_1169_))
{
case 5:
{
uint8_t v___x_1170_; 
v___x_1170_ = 1;
return v___x_1170_;
}
case 6:
{
uint8_t v___x_1171_; 
v___x_1171_ = 1;
return v___x_1171_;
}
case 12:
{
uint8_t v___x_1172_; 
v___x_1172_ = 1;
return v___x_1172_;
}
case 0:
{
lean_object* v_name_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_name_1173_ = lean_ctor_get(v_x_1169_, 0);
v___x_1174_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases));
v___x_1175_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1174_, v_name_1173_);
return v___x_1175_;
}
case 1:
{
lean_object* v_name_1176_; lean_object* v_p_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_name_1176_ = lean_ctor_get(v_x_1169_, 0);
v_p_1177_ = lean_ctor_get(v_x_1169_, 1);
v___x_1178_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases));
v___x_1179_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1178_, v_name_1176_);
if (v___x_1179_ == 0)
{
return v___x_1179_;
}
else
{
v_x_1169_ = v_p_1177_;
goto _start;
}
}
case 2:
{
lean_object* v_name_1181_; lean_object* v_p_u2081_1182_; lean_object* v_p_u2082_1183_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v_name_1181_ = lean_ctor_get(v_x_1169_, 0);
v_p_u2081_1182_ = lean_ctor_get(v_x_1169_, 1);
v_p_u2082_1183_ = lean_ctor_get(v_x_1169_, 2);
v___x_1187_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0));
v___x_1188_ = lean_name_eq(v_name_1181_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2));
v___x_1190_ = lean_name_eq(v_name_1181_, v___x_1189_);
if (v___x_1190_ == 0)
{
return v___x_1190_;
}
else
{
goto v___jp_1184_;
}
}
else
{
goto v___jp_1184_;
}
v___jp_1184_:
{
uint8_t v___x_1185_; 
v___x_1185_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_p_u2081_1182_);
if (v___x_1185_ == 0)
{
return v___x_1185_;
}
else
{
v_x_1169_ = v_p_u2082_1183_;
goto _start;
}
}
}
case 3:
{
lean_object* v_p_1191_; 
v_p_1191_ = lean_ctor_get(v_x_1169_, 2);
v_x_1169_ = v_p_1191_;
goto _start;
}
case 9:
{
lean_object* v_p_1193_; 
v_p_1193_ = lean_ctor_get(v_x_1169_, 2);
v_x_1169_ = v_p_1193_;
goto _start;
}
default: 
{
uint8_t v___x_1195_; 
v___x_1195_ = 0;
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___boxed(lean_object* v_x_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_x_1196_);
lean_dec_ref(v_x_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(lean_object* v_env_1199_, lean_object* v_opts_1200_, lean_object* v_kind_1201_){
_start:
{
uint8_t v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = 1;
v___x_1203_ = l_Lean_Environment_evalConst___redArg(v_env_1199_, v_opts_1200_, v_kind_1201_, v___x_1202_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v___x_1204_; 
lean_dec_ref_known(v___x_1203_, 1);
v___x_1204_ = lean_box(0);
return v___x_1204_;
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1203_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1203_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1___boxed(lean_object* v_env_1213_, lean_object* v_opts_1214_, lean_object* v_kind_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(v_env_1213_, v_opts_1214_, v_kind_1215_);
lean_dec(v_kind_1215_);
lean_dec_ref(v_opts_1214_);
lean_dec_ref(v_env_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(lean_object* v_env_1217_, lean_object* v_opts_1218_, lean_object* v_kind_1219_){
_start:
{
uint8_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = 0;
lean_inc(v_kind_1219_);
lean_inc_ref(v_env_1217_);
v___x_1221_ = l_Lean_Environment_find_x3f(v_env_1217_, v_kind_1219_, v___x_1220_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_dec(v_kind_1219_);
lean_dec_ref(v_env_1217_);
return v___x_1220_;
}
else
{
lean_object* v_val_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v_val_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = l_Lean_ConstantInfo_type(v_val_1222_);
lean_dec(v_val_1222_);
v___x_1224_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_1225_ = l_Lean_Expr_isConstOf(v___x_1223_, v___x_1224_);
lean_dec_ref(v___x_1223_);
if (v___x_1225_ == 0)
{
lean_dec(v_kind_1219_);
lean_dec_ref(v_env_1217_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Environment_evalConst___redArg(v_env_1217_, v_opts_1218_, v_kind_1219_, v___x_1225_);
lean_dec(v_kind_1219_);
lean_dec_ref(v_env_1217_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_dec_ref_known(v___x_1226_, 1);
return v___x_1220_;
}
else
{
lean_object* v_a_1227_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
if (lean_obj_tag(v_a_1227_) == 4)
{
lean_dec_ref_known(v_a_1227_, 4);
return v___x_1220_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_a_1227_);
lean_dec(v_a_1227_);
return v___x_1228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter___boxed(lean_object* v_env_1229_, lean_object* v_opts_1230_, lean_object* v_kind_1231_){
_start:
{
uint8_t v_res_1232_; lean_object* v_r_1233_; 
v_res_1232_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_1229_, v_opts_1230_, v_kind_1231_);
lean_dec_ref(v_opts_1230_);
v_r_1233_ = lean_box(v_res_1232_);
return v_r_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f(lean_object* v_env_1234_, lean_object* v_kind_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1237_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1236_, v_env_1234_, v_kind_1235_);
v___x_1238_ = l_List_head_x3f___redArg(v___x_1237_);
lean_dec(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f___boxed(lean_object* v_env_1239_, lean_object* v_kind_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Fmt_getConditionalFormatter_x3f(v_env_1239_, v_kind_1240_);
lean_dec(v_kind_1240_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f(lean_object* v_env_1242_, lean_object* v_kind_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_1245_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1244_, v_env_1242_, v_kind_1243_);
v___x_1246_ = l_List_head_x3f___redArg(v___x_1245_);
lean_dec(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f___boxed(lean_object* v_env_1247_, lean_object* v_kind_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1247_, v_kind_1248_);
lean_dec(v_kind_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(lean_object* v_msg_1264_){
_start:
{
lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___f_1265_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0));
v___f_1266_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1));
v___f_1267_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2));
v___f_1268_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3));
v___f_1269_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4));
v___f_1270_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5));
v___f_1271_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6));
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___f_1265_);
lean_ctor_set(v___x_1272_, 1, v___f_1266_);
v___x_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___f_1267_);
lean_ctor_set(v___x_1273_, 2, v___f_1268_);
lean_ctor_set(v___x_1273_, 3, v___f_1269_);
lean_ctor_set(v___x_1273_, 4, v___f_1270_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___f_1271_);
v___x_1275_ = ((lean_object*)(l_Lean_Fmt_instInhabitedQuantifierChain_default));
v___x_1276_ = l_instInhabitedOfMonad___redArg(v___x_1274_, v___x_1275_);
v___x_1277_ = lean_panic_fn_borrowed(v___x_1276_, v_msg_1264_);
lean_dec(v___x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(lean_object* v_env_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_snd_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1343_; 
v_snd_1280_ = lean_ctor_get(v_a_1279_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_a_1279_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v_a_1279_, 0);
lean_dec(v_unused_1344_);
v___x_1282_ = v_a_1279_;
v_isShared_1283_ = v_isSharedCheck_1343_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_snd_1280_);
lean_dec(v_a_1279_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1343_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v_snd_1284_; lean_object* v_fst_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1342_; 
v_snd_1284_ = lean_ctor_get(v_snd_1280_, 1);
v_fst_1285_ = lean_ctor_get(v_snd_1280_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_snd_1280_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1287_ = v_snd_1280_;
v_isShared_1288_ = v_isSharedCheck_1342_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_snd_1284_);
lean_inc(v_fst_1285_);
lean_dec(v_snd_1280_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1342_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
if (lean_obj_tag(v_fst_1285_) == 1)
{
lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1324_; 
v_fst_1289_ = lean_ctor_get(v_snd_1284_, 0);
v_snd_1290_ = lean_ctor_get(v_snd_1284_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_snd_1284_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1292_ = v_snd_1284_;
v_isShared_1293_ = v_isSharedCheck_1324_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snd_1290_);
lean_inc(v_fst_1289_);
lean_dec(v_snd_1284_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1324_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_val_1294_; lean_object* v___x_1295_; 
v_val_1294_ = lean_ctor_get(v_fst_1285_, 0);
lean_inc(v_val_1294_);
lean_inc(v_fst_1289_);
v___x_1295_ = lean_apply_1(v_val_1294_, v_fst_1289_);
if (lean_obj_tag(v___x_1295_) == 1)
{
lean_object* v_val_1296_; lean_object* v_toQuantifierHeadComponents_1297_; lean_object* v_body_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_dec_ref_known(v_fst_1285_, 1);
lean_dec(v_fst_1289_);
v_val_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v_toQuantifierHeadComponents_1297_ = lean_ctor_get(v_val_1296_, 0);
lean_inc_ref(v_toQuantifierHeadComponents_1297_);
v_body_1298_ = lean_ctor_get(v_val_1296_, 1);
lean_inc_n(v_body_1298_, 2);
lean_dec(v_val_1296_);
v___x_1299_ = lean_box(0);
v___x_1300_ = lean_array_push(v_snd_1290_, v_toQuantifierHeadComponents_1297_);
v___x_1301_ = l_Lean_Syntax_getKind(v_body_1298_);
lean_inc_ref(v_env_1278_);
v___x_1302_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1278_, v___x_1301_);
lean_dec(v___x_1301_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___x_1300_);
lean_ctor_set(v___x_1292_, 0, v_body_1298_);
v___x_1304_ = v___x_1292_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_body_1298_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1300_);
v___x_1304_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1304_);
lean_ctor_set(v___x_1287_, 0, v___x_1302_);
v___x_1306_ = v___x_1287_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1306_);
lean_ctor_set(v___x_1282_, 0, v___x_1299_);
v___x_1308_ = v___x_1282_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v_a_1279_ = v___x_1308_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v___x_1295_);
lean_dec_ref(v_env_1278_);
lean_inc(v_fst_1289_);
lean_inc(v_snd_1290_);
v___x_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_snd_1290_);
lean_ctor_set(v___x_1313_, 1, v_fst_1289_);
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
if (v_isShared_1293_ == 0)
{
v___x_1316_ = v___x_1292_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_fst_1289_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_snd_1290_);
v___x_1316_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1318_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1316_);
v___x_1318_ = v___x_1287_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1320_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1318_);
lean_ctor_set(v___x_1282_, 0, v___x_1314_);
v___x_1320_ = v___x_1282_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1325_; lean_object* v_snd_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v_env_1278_);
v_fst_1325_ = lean_ctor_get(v_snd_1284_, 0);
v_snd_1326_ = lean_ctor_get(v_snd_1284_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_snd_1284_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1328_ = v_snd_1284_;
v_isShared_1329_ = v_isSharedCheck_1341_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_snd_1326_);
lean_inc(v_fst_1325_);
lean_dec(v_snd_1284_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1341_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
lean_inc(v_fst_1325_);
lean_inc(v_snd_1326_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_snd_1326_);
lean_ctor_set(v___x_1330_, 1, v_fst_1325_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
if (v_isShared_1329_ == 0)
{
v___x_1333_ = v___x_1328_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_fst_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_snd_1326_);
v___x_1333_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1333_);
v___x_1335_ = v___x_1287_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1335_);
lean_ctor_set(v___x_1282_, 0, v___x_1331_);
v___x_1337_ = v___x_1282_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3(void){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1349_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2));
v___x_1350_ = lean_unsigned_to_nat(2u);
v___x_1351_ = lean_unsigned_to_nat(248u);
v___x_1352_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1));
v___x_1353_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_1354_ = l_mkPanicMessageWithDecl(v___x_1353_, v___x_1352_, v___x_1351_, v___x_1350_, v___x_1349_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(lean_object* v_env_1355_, lean_object* v_deconstructQuantifier_x3f_1356_, lean_object* v_stx_1357_){
_start:
{
lean_object* v_deconstructQuantifier_x3f_1358_; lean_object* v_quantifiers_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_fst_1365_; 
v_deconstructQuantifier_x3f_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_deconstructQuantifier_x3f_1358_, 0, v_deconstructQuantifier_x3f_1356_);
v_quantifiers_1359_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0));
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_stx_1357_);
lean_ctor_set(v___x_1361_, 1, v_quantifiers_1359_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_deconstructQuantifier_x3f_1358_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1360_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1355_, v___x_1363_);
v_fst_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_fst_1365_);
lean_dec_ref(v___x_1364_);
if (lean_obj_tag(v_fst_1365_) == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3);
v___x_1367_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; 
v_val_1368_ = lean_ctor_get(v_fst_1365_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v_fst_1365_, 1);
return v_val_1368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0(lean_object* v_env_1369_, lean_object* v_inst_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1369_, v_a_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
if (lean_obj_tag(v_x_1374_) == 0)
{
uint8_t v___x_1375_; 
v___x_1375_ = 1;
return v___x_1375_;
}
else
{
uint8_t v___x_1376_; 
v___x_1376_ = 0;
return v___x_1376_;
}
}
else
{
if (lean_obj_tag(v_x_1374_) == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = 0;
return v___x_1377_;
}
else
{
lean_object* v_val_1378_; lean_object* v_val_1379_; uint8_t v___x_1380_; 
v_val_1378_ = lean_ctor_get(v_x_1373_, 0);
v_val_1379_ = lean_ctor_get(v_x_1374_, 0);
v___x_1380_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_1378_, v_val_1379_);
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1___boxed(lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_x_1381_, v_x_1382_);
lean_dec(v_x_1382_);
lean_dec(v_x_1381_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(lean_object* v_a_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1386_) == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = 0;
return v___x_1387_;
}
else
{
lean_object* v_key_1388_; lean_object* v_tail_1389_; uint8_t v___x_1390_; 
v_key_1388_ = lean_ctor_get(v_x_1386_, 0);
v_tail_1389_ = lean_ctor_get(v_x_1386_, 2);
v___x_1390_ = lean_name_eq(v_key_1388_, v_a_1385_);
if (v___x_1390_ == 0)
{
v_x_1386_ = v_tail_1389_;
goto _start;
}
else
{
return v___x_1390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg___boxed(lean_object* v_a_1392_, lean_object* v_x_1393_){
_start:
{
uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_res_1394_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1392_, v_x_1393_);
lean_dec(v_x_1393_);
lean_dec(v_a_1392_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(lean_object* v_m_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_buckets_1398_; lean_object* v___x_1399_; uint64_t v___y_1401_; 
v_buckets_1398_ = lean_ctor_get(v_m_1396_, 1);
v___x_1399_ = lean_array_get_size(v_buckets_1398_);
if (lean_obj_tag(v_a_1397_) == 0)
{
uint64_t v___x_1415_; 
v___x_1415_ = 1723ULL;
v___y_1401_ = v___x_1415_;
goto v___jp_1400_;
}
else
{
uint64_t v_hash_1416_; 
v_hash_1416_ = lean_ctor_get_uint64(v_a_1397_, sizeof(void*)*2);
v___y_1401_ = v_hash_1416_;
goto v___jp_1400_;
}
v___jp_1400_:
{
uint64_t v___x_1402_; uint64_t v___x_1403_; uint64_t v_fold_1404_; uint64_t v___x_1405_; uint64_t v___x_1406_; uint64_t v___x_1407_; size_t v___x_1408_; size_t v___x_1409_; size_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1402_ = 32ULL;
v___x_1403_ = lean_uint64_shift_right(v___y_1401_, v___x_1402_);
v_fold_1404_ = lean_uint64_xor(v___y_1401_, v___x_1403_);
v___x_1405_ = 16ULL;
v___x_1406_ = lean_uint64_shift_right(v_fold_1404_, v___x_1405_);
v___x_1407_ = lean_uint64_xor(v_fold_1404_, v___x_1406_);
v___x_1408_ = lean_uint64_to_usize(v___x_1407_);
v___x_1409_ = lean_usize_of_nat(v___x_1399_);
v___x_1410_ = ((size_t)1ULL);
v___x_1411_ = lean_usize_sub(v___x_1409_, v___x_1410_);
v___x_1412_ = lean_usize_land(v___x_1408_, v___x_1411_);
v___x_1413_ = lean_array_uget_borrowed(v_buckets_1398_, v___x_1412_);
v___x_1414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1397_, v___x_1413_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg___boxed(lean_object* v_m_1417_, lean_object* v_a_1418_){
_start:
{
uint8_t v_res_1419_; lean_object* v_r_1420_; 
v_res_1419_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1417_, v_a_1418_);
lean_dec(v_a_1418_);
lean_dec_ref(v_m_1417_);
v_r_1420_ = lean_box(v_res_1419_);
return v_r_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(lean_object* v_env_1421_, lean_object* v_opts_1422_, lean_object* v_op_1423_, lean_object* v_stx_1424_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1441_ = l_Lean_Syntax_getNumArgs(v_stx_1424_);
v___x_1442_ = lean_unsigned_to_nat(3u);
v___x_1443_ = lean_nat_dec_eq(v___x_1441_, v___x_1442_);
lean_dec(v___x_1441_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_env_1421_);
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = lean_mk_empty_array_with_capacity(v___x_1444_);
v___x_1446_ = lean_array_push(v___x_1445_, v_stx_1424_);
return v___x_1446_;
}
else
{
lean_object* v_precs_x3f_1447_; lean_object* v_extendedChainKinds_1448_; lean_object* v___x_1449_; 
v_precs_x3f_1447_ = lean_ctor_get(v_op_1423_, 0);
v_extendedChainKinds_1448_ = lean_ctor_get(v_op_1423_, 1);
lean_inc(v_stx_1424_);
v___x_1449_ = l_Lean_Syntax_getKind(v_stx_1424_);
if (lean_obj_tag(v_precs_x3f_1447_) == 0)
{
goto v___jp_1450_;
}
else
{
lean_object* v_op_x27_x3f_1455_; 
lean_inc(v___x_1449_);
lean_inc_ref(v_env_1421_);
v_op_x27_x3f_1455_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_1421_, v_opts_1422_, v___x_1449_);
if (lean_obj_tag(v_op_x27_x3f_1455_) == 0)
{
goto v___jp_1450_;
}
else
{
lean_object* v_val_1456_; lean_object* v_precs_x3f_1457_; uint8_t v___x_1458_; 
v_val_1456_ = lean_ctor_get(v_op_x27_x3f_1455_, 0);
lean_inc(v_val_1456_);
lean_dec_ref_known(v_op_x27_x3f_1455_, 1);
v_precs_x3f_1457_ = lean_ctor_get(v_val_1456_, 0);
lean_inc(v_precs_x3f_1457_);
lean_dec(v_val_1456_);
v___x_1458_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_precs_x3f_1457_, v_precs_x3f_1447_);
lean_dec(v_precs_x3f_1457_);
if (v___x_1458_ == 0)
{
goto v___jp_1450_;
}
else
{
lean_dec(v___x_1449_);
goto v___jp_1425_;
}
}
}
v___jp_1450_:
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_extendedChainKinds_1448_, v___x_1449_);
lean_dec(v___x_1449_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec_ref(v_env_1421_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_mk_empty_array_with_capacity(v___x_1452_);
v___x_1454_ = lean_array_push(v___x_1453_, v_stx_1424_);
return v___x_1454_;
}
else
{
goto v___jp_1425_;
}
}
}
v___jp_1425_:
{
lean_object* v___x_1426_; lean_object* v_op_1427_; uint8_t v___x_1428_; 
v___x_1426_ = lean_unsigned_to_nat(1u);
v_op_1427_ = l_Lean_Syntax_getArg(v_stx_1424_, v___x_1426_);
v___x_1428_ = l_Lean_Syntax_isAtom(v_op_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec(v_op_1427_);
lean_dec_ref(v_env_1421_);
v___x_1429_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___x_1430_ = lean_array_push(v___x_1429_, v_stx_1424_);
return v___x_1430_;
}
else
{
lean_object* v___x_1431_; lean_object* v_left_1432_; lean_object* v___x_1433_; lean_object* v_right_1434_; lean_object* v_leftChain_1435_; lean_object* v_rightChain_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v_left_1432_ = l_Lean_Syntax_getArg(v_stx_1424_, v___x_1431_);
v___x_1433_ = lean_unsigned_to_nat(2u);
v_right_1434_ = l_Lean_Syntax_getArg(v_stx_1424_, v___x_1433_);
lean_dec(v_stx_1424_);
lean_inc_ref(v_env_1421_);
v_leftChain_1435_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1421_, v_opts_1422_, v_op_1423_, v_left_1432_);
v_rightChain_1436_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1421_, v_opts_1422_, v_op_1423_, v_right_1434_);
v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___x_1438_ = lean_array_push(v___x_1437_, v_op_1427_);
v___x_1439_ = l_Array_append___redArg(v_leftChain_1435_, v___x_1438_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = l_Array_append___redArg(v___x_1439_, v_rightChain_1436_);
lean_dec_ref(v_rightChain_1436_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain___boxed(lean_object* v_env_1459_, lean_object* v_opts_1460_, lean_object* v_op_1461_, lean_object* v_stx_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1459_, v_opts_1460_, v_op_1461_, v_stx_1462_);
lean_dec_ref(v_op_1461_);
lean_dec_ref(v_opts_1460_);
return v_res_1463_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(lean_object* v_00_u03b2_1464_, lean_object* v_m_1465_, lean_object* v_a_1466_){
_start:
{
uint8_t v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1465_, v_a_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___boxed(lean_object* v_00_u03b2_1468_, lean_object* v_m_1469_, lean_object* v_a_1470_){
_start:
{
uint8_t v_res_1471_; lean_object* v_r_1472_; 
v_res_1471_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(v_00_u03b2_1468_, v_m_1469_, v_a_1470_);
lean_dec(v_a_1470_);
lean_dec_ref(v_m_1469_);
v_r_1472_ = lean_box(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(lean_object* v_00_u03b2_1473_, lean_object* v_a_1474_, lean_object* v_x_1475_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1474_, v_x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_a_1478_, lean_object* v_x_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(v_00_u03b2_1477_, v_a_1478_, v_x_1479_);
lean_dec(v_x_1479_);
lean_dec(v_a_1478_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v___x_1484_, lean_object* v_a_1485_, lean_object* v_b_1486_){
_start:
{
lean_object* v_it_1488_; lean_object* v_startInclusive_1489_; lean_object* v_endExclusive_1490_; 
if (lean_obj_tag(v_a_1485_) == 0)
{
lean_object* v_currPos_1496_; lean_object* v_searcher_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1603_; 
v_currPos_1496_ = lean_ctor_get(v_a_1485_, 0);
v_searcher_1497_ = lean_ctor_get(v_a_1485_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_a_1485_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1499_ = v_a_1485_;
v_isShared_1500_ = v_isSharedCheck_1603_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_searcher_1497_);
lean_inc(v_currPos_1496_);
lean_dec(v_a_1485_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1603_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_it_1502_; lean_object* v_it_1508_; lean_object* v_startPos_1509_; lean_object* v_endPos_1510_; 
switch(lean_obj_tag(v_searcher_1497_))
{
case 0:
{
lean_object* v_pos_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1535_; 
lean_del_object(v___x_1499_);
v_pos_1523_ = lean_ctor_get(v_searcher_1497_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_searcher_1497_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1525_ = v_searcher_1497_;
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_pos_1523_);
lean_dec(v_searcher_1497_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1535_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_startInclusive_1527_; lean_object* v_endExclusive_1528_; lean_object* v___x_1529_; uint8_t v_decide_1530_; 
v_startInclusive_1527_ = lean_ctor_get(v___x_1483_, 1);
v_endExclusive_1528_ = lean_ctor_get(v___x_1483_, 2);
v___x_1529_ = lean_nat_sub(v_endExclusive_1528_, v_startInclusive_1527_);
v_decide_1530_ = lean_nat_dec_eq(v_pos_1523_, v___x_1529_);
lean_dec(v___x_1529_);
if (v_decide_1530_ == 0)
{
lean_object* v___x_1532_; 
lean_inc(v_pos_1523_);
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 1);
v___x_1532_ = v___x_1525_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_pos_1523_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_inc(v_pos_1523_);
v_it_1508_ = v___x_1532_;
v_startPos_1509_ = v_pos_1523_;
v_endPos_1510_ = v_pos_1523_;
goto v___jp_1507_;
}
}
else
{
lean_object* v___x_1534_; 
lean_del_object(v___x_1525_);
v___x_1534_ = lean_box(3);
lean_inc(v_pos_1523_);
v_it_1508_ = v___x_1534_;
v_startPos_1509_ = v_pos_1523_;
v_endPos_1510_ = v_pos_1523_;
goto v___jp_1507_;
}
}
}
case 1:
{
lean_object* v_pos_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1544_; 
v_pos_1536_ = lean_ctor_get(v_searcher_1497_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_searcher_1497_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1538_ = v_searcher_1497_;
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_pos_1536_);
lean_dec(v_searcher_1497_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_string_utf8_next_fast(v___x_1482_, v_pos_1536_);
lean_dec(v_pos_1536_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1540_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
v_it_1502_ = v___x_1542_;
goto v___jp_1501_;
}
}
}
case 2:
{
lean_object* v_needle_1545_; lean_object* v_table_1546_; lean_object* v_stackPos_1547_; lean_object* v_needlePos_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1602_; 
v_needle_1545_ = lean_ctor_get(v_searcher_1497_, 0);
v_table_1546_ = lean_ctor_get(v_searcher_1497_, 1);
v_stackPos_1547_ = lean_ctor_get(v_searcher_1497_, 2);
v_needlePos_1548_ = lean_ctor_get(v_searcher_1497_, 3);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_searcher_1497_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1550_ = v_searcher_1497_;
v_isShared_1551_ = v_isSharedCheck_1602_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_needlePos_1548_);
lean_inc(v_stackPos_1547_);
lean_inc(v_table_1546_);
lean_inc(v_needle_1545_);
lean_dec(v_searcher_1497_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1602_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_str_1552_; lean_object* v_startInclusive_1553_; lean_object* v_endExclusive_1554_; lean_object* v_basePos_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_str_1552_ = lean_ctor_get(v_needle_1545_, 0);
v_startInclusive_1553_ = lean_ctor_get(v_needle_1545_, 1);
v_endExclusive_1554_ = lean_ctor_get(v_needle_1545_, 2);
v_basePos_1555_ = lean_nat_sub(v_stackPos_1547_, v_needlePos_1548_);
v___x_1556_ = lean_nat_sub(v_endExclusive_1554_, v_startInclusive_1553_);
v___x_1557_ = lean_nat_add(v_basePos_1555_, v___x_1556_);
v___x_1558_ = lean_nat_dec_le(v___x_1557_, v___x_1484_);
lean_dec(v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
lean_dec(v___x_1556_);
lean_del_object(v___x_1550_);
lean_dec(v_needlePos_1548_);
lean_dec(v_stackPos_1547_);
lean_dec_ref(v_table_1546_);
lean_dec_ref(v_needle_1545_);
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_add(v_basePos_1555_, v___x_1559_);
lean_dec(v_basePos_1555_);
v___x_1561_ = lean_nat_dec_le(v___x_1560_, v___x_1484_);
lean_dec(v___x_1560_);
if (v___x_1561_ == 0)
{
lean_del_object(v___x_1499_);
goto v___jp_1521_;
}
else
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_box(3);
v_it_1502_ = v___x_1562_;
goto v___jp_1501_;
}
}
else
{
uint8_t v_stackByte_1563_; lean_object* v___x_1564_; uint8_t v_patByte_1565_; uint8_t v___x_1566_; 
lean_dec(v_basePos_1555_);
lean_inc(v_stackPos_1547_);
v_stackByte_1563_ = lean_string_get_byte_fast(v___x_1482_, v_stackPos_1547_);
v___x_1564_ = lean_nat_add(v_startInclusive_1553_, v_needlePos_1548_);
v_patByte_1565_ = lean_string_get_byte_fast(v_str_1552_, v___x_1564_);
v___x_1566_ = lean_uint8_dec_eq(v_stackByte_1563_, v_patByte_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; uint8_t v_decide_1568_; 
lean_dec(v___x_1556_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v_decide_1568_ = lean_nat_dec_eq(v_needlePos_1548_, v___x_1567_);
if (v_decide_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_newNeedlePos_1571_; uint8_t v___x_1572_; 
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_nat_sub(v_needlePos_1548_, v___x_1569_);
lean_dec(v_needlePos_1548_);
v_newNeedlePos_1571_ = lean_array_fget_borrowed(v_table_1546_, v___x_1570_);
lean_dec(v___x_1570_);
v___x_1572_ = lean_nat_dec_eq(v_newNeedlePos_1571_, v___x_1567_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1574_; 
lean_inc(v_newNeedlePos_1571_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v_newNeedlePos_1571_);
v___x_1574_ = v___x_1550_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_needle_1545_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_table_1546_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_stackPos_1547_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_newNeedlePos_1571_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
v_it_1502_ = v___x_1574_;
goto v___jp_1501_;
}
}
else
{
lean_object* v_nextStackPos_1576_; lean_object* v___x_1578_; 
v_nextStackPos_1576_ = l_String_Slice_posGE___redArg(v___x_1483_, v_stackPos_1547_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v___x_1567_);
lean_ctor_set(v___x_1550_, 2, v_nextStackPos_1576_);
v___x_1578_ = v___x_1550_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_needle_1545_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_table_1546_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_nextStackPos_1576_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v___x_1567_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v_it_1502_ = v___x_1578_;
goto v___jp_1501_;
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_nextStackPos_1582_; lean_object* v___x_1584_; 
lean_dec(v_needlePos_1548_);
v___x_1580_ = lean_unsigned_to_nat(1u);
v___x_1581_ = lean_nat_add(v_stackPos_1547_, v___x_1580_);
lean_dec(v_stackPos_1547_);
v_nextStackPos_1582_ = l_String_Slice_posGE___redArg(v___x_1483_, v___x_1581_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v___x_1567_);
lean_ctor_set(v___x_1550_, 2, v_nextStackPos_1582_);
v___x_1584_ = v___x_1550_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_needle_1545_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_table_1546_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_nextStackPos_1582_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v___x_1567_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
v_it_1502_ = v___x_1584_;
goto v___jp_1501_;
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v_nextStackPos_1587_; lean_object* v_nextNeedlePos_1588_; uint8_t v_decide_1589_; 
lean_del_object(v___x_1499_);
v___x_1586_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1587_ = lean_nat_add(v_stackPos_1547_, v___x_1586_);
lean_dec(v_stackPos_1547_);
v_nextNeedlePos_1588_ = lean_nat_add(v_needlePos_1548_, v___x_1586_);
lean_dec(v_needlePos_1548_);
v_decide_1589_ = lean_nat_dec_eq(v_nextNeedlePos_1588_, v___x_1556_);
lean_dec(v___x_1556_);
if (v_decide_1589_ == 0)
{
lean_object* v___x_1591_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v_nextNeedlePos_1588_);
lean_ctor_set(v___x_1550_, 2, v_nextStackPos_1587_);
v___x_1591_ = v___x_1550_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_needle_1545_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_table_1546_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_nextStackPos_1587_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_nextNeedlePos_1588_);
v___x_1591_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_currPos_1496_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v_a_1485_ = v___x_1592_;
goto _start;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1595_ = lean_nat_sub(v_nextStackPos_1587_, v_nextNeedlePos_1588_);
lean_dec(v_nextNeedlePos_1588_);
v___x_1596_ = l_String_Slice_pos_x21(v___x_1483_, v___x_1595_);
lean_dec(v___x_1595_);
v___x_1597_ = l_String_Slice_pos_x21(v___x_1483_, v_nextStackPos_1587_);
v___x_1598_ = lean_unsigned_to_nat(0u);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v___x_1598_);
lean_ctor_set(v___x_1550_, 2, v_nextStackPos_1587_);
v___x_1600_ = v___x_1550_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_needle_1545_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_table_1546_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_nextStackPos_1587_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
v_it_1508_ = v___x_1600_;
v_startPos_1509_ = v___x_1596_;
v_endPos_1510_ = v___x_1597_;
goto v___jp_1507_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_1499_);
goto v___jp_1521_;
}
}
v___jp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v_it_1502_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_currPos_1496_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_it_1502_);
v___x_1504_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
v_a_1485_ = v___x_1504_;
goto _start;
}
}
v___jp_1507_:
{
lean_object* v_slice_1511_; lean_object* v_startInclusive_1512_; lean_object* v_endExclusive_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_slice_1511_ = l_String_Slice_subslice_x21(v___x_1483_, v_currPos_1496_, v_startPos_1509_);
v_startInclusive_1512_ = lean_ctor_get(v_slice_1511_, 0);
v_endExclusive_1513_ = lean_ctor_get(v_slice_1511_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_slice_1511_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v_slice_1511_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_endExclusive_1513_);
lean_inc(v_startInclusive_1512_);
lean_dec(v_slice_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_nextIt_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v_it_1508_);
lean_ctor_set(v___x_1515_, 0, v_endPos_1510_);
v_nextIt_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_endPos_1510_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_it_1508_);
v_nextIt_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
v_it_1488_ = v_nextIt_1518_;
v_startInclusive_1489_ = v_startInclusive_1512_;
v_endExclusive_1490_ = v_endExclusive_1513_;
goto v___jp_1487_;
}
}
}
v___jp_1521_:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_box(1);
lean_inc(v___x_1484_);
v_it_1488_ = v___x_1522_;
v_startInclusive_1489_ = v_currPos_1496_;
v_endExclusive_1490_ = v___x_1484_;
goto v___jp_1487_;
}
}
}
else
{
lean_dec(v___x_1484_);
lean_dec_ref(v___x_1482_);
return v_b_1486_;
}
v___jp_1487_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_inc_ref(v___x_1482_);
v___x_1491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1482_);
lean_ctor_set(v___x_1491_, 1, v_startInclusive_1489_);
lean_ctor_set(v___x_1491_, 2, v_endExclusive_1490_);
v___x_1492_ = l_String_Slice_toString(v___x_1491_);
lean_dec_ref_known(v___x_1491_, 3);
v___x_1493_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_1492_);
v___x_1494_ = lean_array_push(v_b_1486_, v___x_1493_);
v_a_1485_ = v_it_1488_;
v_b_1486_ = v___x_1494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg___boxed(lean_object* v___x_1604_, lean_object* v___x_1605_, lean_object* v___x_1606_, lean_object* v_a_1607_, lean_object* v_b_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1604_, v___x_1605_, v___x_1606_, v_a_1607_, v_b_1608_);
lean_dec_ref(v___x_1605_);
return v_res_1609_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtRawAsInSource___closed__3(void){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource(uint8_t v_isFallback_1616_, lean_object* v_stx_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
uint8_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = 0;
v___x_1621_ = l_Lean_Syntax_getPos_x3f(v_stx_1617_, v___x_1620_);
if (lean_obj_tag(v___x_1621_) == 1)
{
lean_object* v_val_1622_; lean_object* v___x_1623_; 
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v___x_1623_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1617_, v___x_1620_);
if (lean_obj_tag(v___x_1623_) == 1)
{
lean_object* v_text_1624_; lean_object* v_val_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1675_; 
v_text_1624_ = lean_ctor_get(v_a_1618_, 1);
v_val_1625_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1627_ = v___x_1623_;
v_isShared_1628_ = v_isSharedCheck_1675_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_val_1625_);
lean_dec(v___x_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1675_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_source_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v_source_1629_ = lean_ctor_get(v_text_1624_, 0);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_string_utf8_byte_size(v_source_1629_);
lean_inc_ref(v_source_1629_);
v___x_1632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1632_, 0, v_source_1629_);
lean_ctor_set(v___x_1632_, 1, v___x_1630_);
lean_ctor_set(v___x_1632_, 2, v___x_1631_);
v___x_1633_ = l_String_Slice_pos_x3f(v___x_1632_, v_val_1622_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_dec_ref_known(v___x_1632_, 3);
lean_dec(v_val_1625_);
v___x_1634_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1635_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1636_, 0, v_stx_1617_);
lean_ctor_set(v___x_1636_, 1, v___x_1634_);
lean_ctor_set(v___x_1636_, 2, v___x_1635_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set_tag(v___x_1627_, 2);
lean_ctor_set(v___x_1627_, 0, v___x_1636_);
v___x_1638_ = v___x_1627_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_a_1619_);
return v___x_1639_;
}
}
else
{
lean_object* v_val_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1674_; 
lean_del_object(v___x_1627_);
v_val_1641_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1643_ = v___x_1633_;
v_isShared_1644_ = v_isSharedCheck_1674_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_val_1641_);
lean_dec(v___x_1633_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1674_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_String_Slice_pos_x3f(v___x_1632_, v_val_1625_);
lean_dec_ref_known(v___x_1632_, 3);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
lean_dec(v_val_1641_);
v___x_1646_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1647_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1648_, 0, v_stx_1617_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
lean_ctor_set(v___x_1648_, 2, v___x_1647_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 2);
lean_ctor_set(v___x_1643_, 0, v___x_1648_);
v___x_1650_ = v___x_1643_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
lean_ctor_set(v___x_1651_, 1, v_a_1619_);
return v___x_1651_;
}
}
else
{
lean_object* v_val_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
lean_del_object(v___x_1643_);
v_val_1653_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1654_ = lean_string_utf8_extract_fast(v_source_1629_, v_val_1641_, v_val_1653_);
lean_dec(v_val_1653_);
lean_dec(v_val_1641_);
v___x_1655_ = lean_string_utf8_byte_size(v___x_1654_);
lean_inc_ref(v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1630_);
lean_ctor_set(v___x_1656_, 2, v___x_1655_);
v___x_1657_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1658_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1659_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1654_, v___x_1656_, v___x_1655_, v___x_1657_, v___x_1658_);
lean_dec_ref_known(v___x_1656_, 3);
v___x_1660_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1661_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1660_, v___x_1659_);
v___x_1662_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1620_, v___x_1661_);
v___x_1663_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___x_1662_, v_stx_1617_, v_a_1619_);
lean_dec(v_stx_1617_);
if (lean_obj_tag(v___x_1663_) == 0)
{
if (v_isFallback_1616_ == 0)
{
return v___x_1663_;
}
else
{
lean_object* v_a_1664_; lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_a_1665_ = lean_ctor_get(v___x_1663_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1667_ = v___x_1663_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_1664_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1665_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
return v___x_1663_;
}
}
}
}
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v___x_1623_);
lean_dec(v_val_1622_);
v___x_1676_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1677_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1676_, v_stx_1617_, v_a_1619_);
lean_dec(v_stx_1617_);
return v___x_1677_;
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1621_);
v___x_1678_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1679_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1678_, v_stx_1617_, v_a_1619_);
lean_dec(v_stx_1617_);
return v___x_1679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource___boxed(lean_object* v_isFallback_1680_, lean_object* v_stx_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
uint8_t v_isFallback_boxed_1684_; lean_object* v_res_1685_; 
v_isFallback_boxed_1684_ = lean_unbox(v_isFallback_1680_);
v_res_1685_ = l_Lean_Fmt_fmtRawAsInSource(v_isFallback_boxed_1684_, v_stx_1681_, v_a_1682_, v_a_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(lean_object* v___x_1686_, lean_object* v___x_1687_, lean_object* v___x_1688_, lean_object* v_inst_1689_, lean_object* v_R_1690_, lean_object* v_a_1691_, lean_object* v_b_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1686_, v___x_1687_, v___x_1688_, v_a_1691_, v_b_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___boxed(lean_object* v___x_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v_inst_1697_, lean_object* v_R_1698_, lean_object* v_a_1699_, lean_object* v_b_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(v___x_1694_, v___x_1695_, v___x_1696_, v_inst_1697_, v_R_1698_, v_a_1699_, v_b_1700_);
lean_dec_ref(v___x_1695_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(lean_object* v_token_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v_lines_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_string_utf8_byte_size(v_token_1702_);
lean_inc_ref(v_token_1702_);
v___x_1705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1705_, 0, v_token_1702_);
lean_ctor_set(v___x_1705_, 1, v___x_1703_);
lean_ctor_set(v___x_1705_, 2, v___x_1704_);
v___x_1706_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1707_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_lines_1708_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_token_1702_, v___x_1705_, v___x_1704_, v___x_1706_, v___x_1707_);
lean_dec_ref_known(v___x_1705_, 3);
v___x_1709_ = lean_array_get_size(v_lines_1708_);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_dec_eq(v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1713_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1712_, v_lines_1708_);
v___x_1714_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1711_, v___x_1713_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = lean_array_get(v___x_1715_, v_lines_1708_, v___x_1703_);
lean_dec_ref(v_lines_1708_);
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(size_t v_sz_1717_, size_t v_i_1718_, lean_object* v_bs_1719_){
_start:
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_usize_dec_lt(v_i_1718_, v_sz_1717_);
if (v___x_1720_ == 0)
{
return v_bs_1719_;
}
else
{
lean_object* v_v_1721_; lean_object* v___x_1722_; lean_object* v_bs_x27_1723_; lean_object* v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v_v_1721_ = lean_array_uget(v_bs_1719_, v_i_1718_);
v___x_1722_ = lean_unsigned_to_nat(0u);
v_bs_x27_1723_ = lean_array_uset(v_bs_1719_, v_i_1718_, v___x_1722_);
v___x_1724_ = l_Lean_Fmt_Doc_text___override___redArg(v_v_1721_);
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_i_1718_, v___x_1725_);
v___x_1727_ = lean_array_uset(v_bs_x27_1723_, v_i_1718_, v___x_1724_);
v_i_1718_ = v___x_1726_;
v_bs_1719_ = v___x_1727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2___boxed(lean_object* v_sz_1729_, lean_object* v_i_1730_, lean_object* v_bs_1731_){
_start:
{
size_t v_sz_boxed_1732_; size_t v_i_boxed_1733_; lean_object* v_res_1734_; 
v_sz_boxed_1732_ = lean_unbox_usize(v_sz_1729_);
lean_dec(v_sz_1729_);
v_i_boxed_1733_ = lean_unbox_usize(v_i_1730_);
lean_dec(v_i_1730_);
v_res_1734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_boxed_1732_, v_i_boxed_1733_, v_bs_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(lean_object* v_ctx_1735_, size_t v_sz_1736_, size_t v_i_1737_, lean_object* v_bs_1738_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_lt(v_i_1737_, v_sz_1736_);
if (v___x_1739_ == 0)
{
lean_dec_ref(v_ctx_1735_);
return v_bs_1738_;
}
else
{
lean_object* v_v_1740_; lean_object* v_str_1741_; lean_object* v_startPos_1742_; lean_object* v_stopPos_1743_; lean_object* v_anchorColumnPos_1744_; lean_object* v___x_1745_; lean_object* v_bs_x27_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v_v_1740_ = lean_array_uget_borrowed(v_bs_1738_, v_i_1737_);
v_str_1741_ = lean_ctor_get(v_v_1740_, 0);
lean_inc_ref(v_str_1741_);
v_startPos_1742_ = lean_ctor_get(v_v_1740_, 1);
lean_inc(v_startPos_1742_);
v_stopPos_1743_ = lean_ctor_get(v_v_1740_, 2);
lean_inc(v_stopPos_1743_);
v_anchorColumnPos_1744_ = lean_ctor_get(v_ctx_1735_, 0);
v___x_1745_ = lean_unsigned_to_nat(0u);
v_bs_x27_1746_ = lean_array_uset(v_bs_1738_, v_i_1737_, v___x_1745_);
v___x_1747_ = lean_string_utf8_extract(v_str_1741_, v_startPos_1742_, v_stopPos_1743_);
lean_dec(v_stopPos_1743_);
lean_dec(v_startPos_1742_);
lean_dec_ref(v_str_1741_);
lean_inc(v_anchorColumnPos_1744_);
v___x_1748_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(v___x_1747_, v_anchorColumnPos_1744_);
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1737_, v___x_1749_);
v___x_1751_ = lean_array_uset(v_bs_x27_1746_, v_i_1737_, v___x_1748_);
v_i_1737_ = v___x_1750_;
v_bs_1738_ = v___x_1751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1___boxed(lean_object* v_ctx_1753_, lean_object* v_sz_1754_, lean_object* v_i_1755_, lean_object* v_bs_1756_){
_start:
{
size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1753_, v_sz_boxed_1757_, v_i_boxed_1758_, v_bs_1756_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(lean_object* v_a_1760_, lean_object* v_b_1761_){
_start:
{
lean_object* v_array_1762_; lean_object* v_start_1763_; lean_object* v_stop_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1777_; 
v_array_1762_ = lean_ctor_get(v_a_1760_, 0);
v_start_1763_ = lean_ctor_get(v_a_1760_, 1);
v_stop_1764_ = lean_ctor_get(v_a_1760_, 2);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_a_1760_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1766_ = v_a_1760_;
v_isShared_1767_ = v_isSharedCheck_1777_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_stop_1764_);
lean_inc(v_start_1763_);
lean_inc(v_array_1762_);
lean_dec(v_a_1760_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1777_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_lt(v_start_1763_, v_stop_1764_);
if (v___x_1768_ == 0)
{
lean_del_object(v___x_1766_);
lean_dec(v_stop_1764_);
lean_dec(v_start_1763_);
lean_dec_ref(v_array_1762_);
return v_b_1761_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_add(v_start_1763_, v___x_1769_);
lean_inc_ref(v_array_1762_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 1, v___x_1770_);
v___x_1772_ = v___x_1766_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_array_1762_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v_stop_1764_);
v___x_1772_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = lean_array_fget(v_array_1762_, v_start_1763_);
lean_dec(v_start_1763_);
lean_dec_ref(v_array_1762_);
v___x_1774_ = lean_array_push(v_b_1761_, v___x_1773_);
v_a_1760_ = v___x_1772_;
v_b_1761_ = v___x_1774_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(lean_object* v_ctx_1782_, lean_object* v_trailing_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_lastTokenTailPos_1785_; lean_object* v_startPos_1786_; uint8_t v___x_1787_; 
v_lastTokenTailPos_1785_ = lean_ctor_get(v_ctx_1782_, 2);
v_startPos_1786_ = lean_ctor_get(v_trailing_1783_, 1);
v___x_1787_ = lean_nat_dec_le(v_lastTokenTailPos_1785_, v_startPos_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v_lines_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_str_1794_; lean_object* v_startPos_1795_; lean_object* v_stopPos_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; size_t v_sz_1805_; size_t v___x_1806_; lean_object* v___x_1807_; lean_object* v_newLines_1808_; size_t v_sz_1809_; lean_object* v_formatted_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1788_ = l_instInhabitedRaw__1;
v___x_1789_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_trailing_1783_);
v___x_1790_ = l_Substring_Raw_splitOn(v_trailing_1783_, v___x_1789_);
v_lines_1791_ = lean_array_mk(v___x_1790_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_array_get_borrowed(v___x_1788_, v_lines_1791_, v___x_1792_);
v_str_1794_ = lean_ctor_get(v___x_1793_, 0);
v_startPos_1795_ = lean_ctor_get(v___x_1793_, 1);
v_stopPos_1796_ = lean_ctor_get(v___x_1793_, 2);
v___x_1797_ = lean_string_utf8_extract(v_str_1794_, v_startPos_1795_, v_stopPos_1796_);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_mk_empty_array_with_capacity(v___x_1798_);
lean_inc_ref(v___x_1799_);
v___x_1800_ = lean_array_push(v___x_1799_, v___x_1797_);
v___x_1801_ = lean_array_get_size(v_lines_1791_);
v___x_1802_ = l_Array_toSubarray___redArg(v_lines_1791_, v___x_1798_, v___x_1801_);
v___x_1803_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0));
v___x_1804_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v___x_1802_, v___x_1803_);
v_sz_1805_ = lean_array_size(v___x_1804_);
v___x_1806_ = ((size_t)0ULL);
v___x_1807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1782_, v_sz_1805_, v___x_1806_, v___x_1804_);
v_newLines_1808_ = l_Array_append___redArg(v___x_1800_, v___x_1807_);
lean_dec_ref(v___x_1807_);
v_sz_1809_ = lean_array_size(v_newLines_1808_);
v_formatted_1810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1809_, v___x_1806_, v_newLines_1808_);
v___x_1811_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1812_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1811_, v_formatted_1810_);
v___x_1813_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1812_);
v___x_1814_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_Range_ofSubstring(v_trailing_1783_);
lean_dec_ref(v_trailing_1783_);
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1813_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_array_push(v___x_1799_, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v_a_1784_);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref(v_trailing_1783_);
lean_dec_ref(v_ctx_1782_);
v___x_1819_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v_a_1784_);
return v___x_1820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(lean_object* v_ctx_1821_, lean_object* v___trailingTk_1822_, lean_object* v_trailing_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(v_ctx_1821_, v_trailing_1823_, v_a_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed(lean_object* v_ctx_1827_, lean_object* v___trailingTk_1828_, lean_object* v_trailing_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(v_ctx_1827_, v___trailingTk_1828_, v_trailing_1829_, v_a_1830_, v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v___trailingTk_1828_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0(lean_object* v_inst_1833_, lean_object* v_R_1834_, lean_object* v_a_1835_, lean_object* v_b_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v_a_1835_, v_b_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(lean_object* v_ctx_1838_, lean_object* v_leading_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_stopPos_1841_; lean_object* v_firstTokenPos_1842_; uint8_t v___x_1843_; 
v_stopPos_1841_ = lean_ctor_get(v_leading_1839_, 2);
v_firstTokenPos_1842_ = lean_ctor_get(v_ctx_1838_, 1);
v___x_1843_ = lean_nat_dec_le(v_stopPos_1841_, v_firstTokenPos_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v_lines_1846_; size_t v_sz_1847_; size_t v___x_1848_; lean_object* v_newLines_1849_; size_t v_sz_1850_; lean_object* v_formatted_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1844_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_leading_1839_);
v___x_1845_ = l_Substring_Raw_splitOn(v_leading_1839_, v___x_1844_);
v_lines_1846_ = lean_array_mk(v___x_1845_);
v_sz_1847_ = lean_array_size(v_lines_1846_);
v___x_1848_ = ((size_t)0ULL);
v_newLines_1849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1838_, v_sz_1847_, v___x_1848_, v_lines_1846_);
v_sz_1850_ = lean_array_size(v_newLines_1849_);
v_formatted_1851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1850_, v___x_1848_, v_newLines_1849_);
v___x_1852_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1853_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1852_, v_formatted_1851_);
v___x_1854_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1853_);
v___x_1855_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_Range_ofSubstring(v_leading_1839_);
lean_dec_ref(v_leading_1839_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1854_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_mk_empty_array_with_capacity(v___x_1858_);
v___x_1860_ = lean_array_push(v___x_1859_, v___x_1857_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v_a_1840_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec_ref(v_leading_1839_);
lean_dec_ref(v_ctx_1838_);
v___x_1862_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_a_1840_);
return v___x_1863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(lean_object* v_ctx_1864_, lean_object* v___leadingTk_1865_, lean_object* v_leading_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(v_ctx_1864_, v_leading_1866_, v_a_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed(lean_object* v_ctx_1870_, lean_object* v___leadingTk_1871_, lean_object* v_leading_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(v_ctx_1870_, v___leadingTk_1871_, v_leading_1872_, v_a_1873_, v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v___leadingTk_1871_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(lean_object* v_stx_1876_, lean_object* v_token_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_inc_ref(v_a_1878_);
v___x_1881_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed), 5, 1);
lean_closure_set(v___x_1881_, 0, v_a_1878_);
lean_inc(v_stx_1876_);
v___x_1882_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_1876_, v___x_1881_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
v_a_1884_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1882_, 2);
lean_inc_ref(v_a_1878_);
v___x_1885_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed), 5, 1);
lean_closure_set(v___x_1885_, 0, v_a_1878_);
lean_inc(v_stx_1876_);
v___x_1886_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_1876_, v___x_1885_, v_a_1879_, v_a_1884_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
v_a_1888_ = lean_ctor_get(v___x_1886_, 1);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1886_, 2);
v___x_1889_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(v_token_1877_);
v___x_1890_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_1889_, v_stx_1876_, v_a_1888_);
lean_dec(v_stx_1876_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1933_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_a_1892_ = lean_ctor_get(v___x_1890_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1894_ = v___x_1890_;
v_isShared_1895_ = v_isSharedCheck_1933_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1933_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___y_1897_; uint8_t v___x_1923_; 
v___x_1923_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1883_);
if (v___x_1923_ == 0)
{
uint8_t v___x_1924_; 
v___x_1924_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1891_);
if (v___x_1924_ == 0)
{
lean_object* v_doc_1925_; lean_object* v_doc_1926_; uint8_t v___x_1927_; 
v_doc_1925_ = lean_ctor_get(v_a_1883_, 0);
lean_inc(v_doc_1925_);
lean_dec(v_a_1883_);
v_doc_1926_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_doc_1926_);
lean_dec(v_a_1891_);
v___x_1927_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1925_);
if (v___x_1927_ == 0)
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1926_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1925_, v_doc_1926_);
v___x_1930_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1929_);
v___y_1897_ = v___x_1930_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1931_; 
lean_dec(v_doc_1926_);
v___x_1931_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1925_);
v___y_1897_ = v___x_1931_;
goto v___jp_1896_;
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_doc_1925_);
v___x_1932_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1926_);
v___y_1897_ = v___x_1932_;
goto v___jp_1896_;
}
}
else
{
lean_dec(v_a_1891_);
v___y_1897_ = v_a_1883_;
goto v___jp_1896_;
}
}
else
{
lean_dec(v_a_1883_);
v___y_1897_ = v_a_1891_;
goto v___jp_1896_;
}
v___jp_1896_:
{
uint8_t v___x_1898_; 
v___x_1898_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1897_);
if (v___x_1898_ == 0)
{
uint8_t v___x_1899_; 
v___x_1899_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1887_);
if (v___x_1899_ == 0)
{
lean_object* v_doc_1900_; lean_object* v_doc_1901_; uint8_t v___x_1902_; 
v_doc_1900_ = lean_ctor_get(v___y_1897_, 0);
lean_inc(v_doc_1900_);
lean_dec_ref(v___y_1897_);
v_doc_1901_ = lean_ctor_get(v_a_1887_, 0);
lean_inc(v_doc_1901_);
lean_dec(v_a_1887_);
v___x_1902_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1900_);
if (v___x_1902_ == 0)
{
uint8_t v___x_1903_; 
v___x_1903_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1901_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1904_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1900_, v_doc_1901_);
v___x_1905_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1904_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1905_);
v___x_1907_ = v___x_1894_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1892_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec(v_doc_1901_);
v___x_1909_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1900_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1909_);
v___x_1911_ = v___x_1894_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_a_1892_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_doc_1900_);
v___x_1913_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1901_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1913_);
v___x_1915_ = v___x_1894_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1892_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
else
{
lean_object* v___x_1918_; 
lean_dec(v_a_1887_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___y_1897_);
v___x_1918_ = v___x_1894_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___y_1897_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_a_1892_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v___x_1921_; 
lean_dec_ref(v___y_1897_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_a_1887_);
v___x_1921_ = v___x_1894_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1887_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_a_1892_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
else
{
lean_dec(v_a_1887_);
lean_dec(v_a_1883_);
return v___x_1890_;
}
}
else
{
lean_dec(v_a_1883_);
lean_dec_ref(v_token_1877_);
lean_dec(v_stx_1876_);
return v___x_1886_;
}
}
else
{
lean_dec_ref(v_token_1877_);
lean_dec(v_stx_1876_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___boxed(lean_object* v_stx_1934_, lean_object* v_token_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1934_, v_token_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec_ref(v_a_1936_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object* v_stx_1943_, uint8_t v_isRoot_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_){
_start:
{
switch(lean_obj_tag(v_stx_1943_))
{
case 0:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v_a_1947_);
return v___x_1949_;
}
case 1:
{
lean_object* v_kind_1950_; lean_object* v_args_1951_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_kind_1950_ = lean_ctor_get(v_stx_1943_, 1);
v_args_1951_ = lean_ctor_get(v_stx_1943_, 2);
v___x_1999_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_2000_ = lean_name_eq(v_kind_1950_, v___x_1999_);
if (v___x_2000_ == 0)
{
v___y_1953_ = v_a_1945_;
v___y_1954_ = v_a_1946_;
v___y_1955_ = v_a_1947_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = lean_unsigned_to_nat(0u);
v___x_2002_ = lean_array_get_size(v_args_1951_);
v___x_2003_ = lean_nat_dec_lt(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
v___y_1953_ = v_a_1945_;
v___y_1954_ = v_a_1946_;
v___y_1955_ = v_a_1947_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_2004_; 
lean_inc_ref(v_args_1951_);
lean_dec_ref_known(v_stx_1943_, 3);
v___x_2004_ = lean_array_fget(v_args_1951_, v___x_2001_);
lean_dec_ref(v_args_1951_);
v_stx_1943_ = v___x_2004_;
goto _start;
}
}
v___jp_1952_:
{
size_t v_sz_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
v_sz_1956_ = lean_array_size(v_args_1951_);
v___x_1957_ = ((size_t)0ULL);
lean_inc_ref(v_args_1951_);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_1956_, v___x_1957_, v_args_1951_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1989_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_a_1960_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1962_ = v___x_1958_;
v_isShared_1963_ = v_isSharedCheck_1989_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1989_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Fmt_TaggedDoc_join(v_a_1959_);
if (v_isRoot_1944_ == 0)
{
lean_object* v_doc_1965_; lean_object* v_metaData_1966_; lean_object* v___x_1967_; 
lean_del_object(v___x_1962_);
v_doc_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_doc_1965_);
v_metaData_1966_ = lean_ctor_get(v___x_1964_, 1);
lean_inc(v_metaData_1966_);
lean_dec_ref(v___x_1964_);
v___x_1967_ = l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(v_doc_1965_, v_stx_1943_, v_a_1960_);
lean_dec_ref_known(v_stx_1943_, 3);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1985_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_a_1969_ = lean_ctor_get(v___x_1967_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1971_ = v___x_1967_;
v_isShared_1972_ = v_isSharedCheck_1985_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1985_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v_doc_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1983_; 
v_doc_1973_ = lean_ctor_get(v_a_1968_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_a_1968_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v_a_1968_, 1);
lean_dec(v_unused_1984_);
v___x_1975_ = v_a_1968_;
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_doc_1973_);
lean_dec(v_a_1968_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v_metaData_1966_);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_doc_1973_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_metaData_1966_);
v___x_1978_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1980_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_1978_);
v___x_1980_ = v___x_1971_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_a_1969_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
else
{
lean_dec(v_metaData_1966_);
return v___x_1967_;
}
}
else
{
lean_object* v___x_1987_; 
lean_dec_ref_known(v_stx_1943_, 3);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1964_);
v___x_1987_ = v___x_1962_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_a_1960_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref_known(v_stx_1943_, 3);
v_a_1990_ = lean_ctor_get(v___x_1958_, 0);
v_a_1991_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1958_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_inc(v_a_1990_);
lean_dec(v___x_1958_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1990_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
case 2:
{
lean_object* v_val_2006_; lean_object* v___x_2007_; 
v_val_2006_ = lean_ctor_get(v_stx_1943_, 1);
lean_inc_ref(v_val_2006_);
v___x_2007_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1943_, v_val_2006_, v_a_1945_, v_a_1946_, v_a_1947_);
return v___x_2007_;
}
default: 
{
lean_object* v_rawVal_2008_; lean_object* v_str_2009_; lean_object* v_startPos_2010_; lean_object* v_stopPos_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_rawVal_2008_ = lean_ctor_get(v_stx_1943_, 1);
v_str_2009_ = lean_ctor_get(v_rawVal_2008_, 0);
v_startPos_2010_ = lean_ctor_get(v_rawVal_2008_, 1);
v_stopPos_2011_ = lean_ctor_get(v_rawVal_2008_, 2);
v___x_2012_ = lean_string_utf8_extract(v_str_2009_, v_startPos_2010_, v_stopPos_2011_);
v___x_2013_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1943_, v___x_2012_, v_a_1945_, v_a_1946_, v_a_1947_);
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t v_sz_2014_, size_t v_i_2015_, lean_object* v_bs_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_lt(v_i_2015_, v_sz_2014_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_bs_2016_);
lean_ctor_set(v___x_2021_, 1, v___y_2019_);
return v___x_2021_;
}
else
{
lean_object* v_v_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; 
v_v_2022_ = lean_array_uget_borrowed(v_bs_2016_, v_i_2015_);
v___x_2023_ = 0;
lean_inc(v_v_2022_);
v___x_2024_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_v_2022_, v___x_2023_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v_bs_x27_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
v_a_2026_ = lean_ctor_get(v___x_2024_, 1);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2024_, 2);
v___x_2027_ = lean_unsigned_to_nat(0u);
v_bs_x27_2028_ = lean_array_uset(v_bs_2016_, v_i_2015_, v___x_2027_);
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_add(v_i_2015_, v___x_2029_);
v___x_2031_ = lean_array_uset(v_bs_x27_2028_, v_i_2015_, v_a_2025_);
v_i_2015_ = v___x_2030_;
v_bs_2016_ = v___x_2031_;
v___y_2019_ = v_a_2026_;
goto _start;
}
else
{
lean_object* v_a_2033_; lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_bs_2016_);
v_a_2033_ = lean_ctor_get(v___x_2024_, 0);
v_a_2034_ = lean_ctor_get(v___x_2024_, 1);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2024_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_inc(v_a_2033_);
lean_dec(v___x_2024_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2033_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object* v_sz_2042_, lean_object* v_i_2043_, lean_object* v_bs_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
size_t v_sz_boxed_2048_; size_t v_i_boxed_2049_; lean_object* v_res_2050_; 
v_sz_boxed_2048_ = lean_unbox_usize(v_sz_2042_);
lean_dec(v_sz_2042_);
v_i_boxed_2049_ = lean_unbox_usize(v_i_2043_);
lean_dec(v_i_2043_);
v_res_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_boxed_2048_, v_i_boxed_2049_, v_bs_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object* v_stx_2051_, lean_object* v_isRoot_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
uint8_t v_isRoot_boxed_2056_; lean_object* v_res_2057_; 
v_isRoot_boxed_2056_ = lean_unbox(v_isRoot_2052_);
v_res_2057_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2051_, v_isRoot_boxed_2056_, v_a_2053_, v_a_2054_, v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object* v_stx_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
uint8_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = 0;
v___x_2062_ = l_Lean_Syntax_getPos_x3f(v_stx_2058_, v___x_2061_);
if (lean_obj_tag(v___x_2062_) == 1)
{
lean_object* v_val_2063_; lean_object* v___x_2064_; 
v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2064_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2058_, v___x_2061_);
if (lean_obj_tag(v___x_2064_) == 1)
{
lean_object* v_val_2065_; lean_object* v___x_2066_; 
v_val_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = l_Lean_Fmt_getLineInfos(v_val_2063_, v_val_2065_, v_a_2059_, v_a_2060_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2079_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_a_2068_ = lean_ctor_get(v___x_2066_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2070_ = v___x_2066_;
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2079_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_array_get_size(v_a_2067_);
lean_dec(v_a_2067_);
v___x_2074_ = lean_nat_dec_lt(v___x_2072_, v___x_2073_);
v___x_2075_ = lean_box(v___x_2074_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 0, v___x_2075_);
v___x_2077_ = v___x_2070_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_a_2068_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2080_ = lean_ctor_get(v___x_2066_, 0);
v_a_2081_ = lean_ctor_get(v___x_2066_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2066_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_inc(v_a_2080_);
lean_dec(v___x_2066_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2080_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v___x_2064_);
lean_dec(v_val_2063_);
v___x_2089_ = lean_box(v___x_2061_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_a_2060_);
return v___x_2090_;
}
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_dec(v___x_2062_);
v___x_2091_ = lean_box(v___x_2061_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_a_2060_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object* v_stx_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_2093_, v_a_2094_, v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_stx_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object* v_msg_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = lean_panic_fn_borrowed(v___x_2098_, v_msg_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object* v_x2_2100_, lean_object* v_as_2101_, size_t v_i_2102_, size_t v_stop_2103_){
_start:
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_usize_dec_eq(v_i_2102_, v_stop_2103_);
if (v___x_2104_ == 0)
{
lean_object* v_startPos_2105_; lean_object* v___x_2106_; lean_object* v_start_2107_; uint8_t v___x_2108_; 
v_startPos_2105_ = lean_ctor_get(v_x2_2100_, 4);
v___x_2106_ = lean_array_uget_borrowed(v_as_2101_, v_i_2102_);
v_start_2107_ = lean_ctor_get(v___x_2106_, 0);
v___x_2108_ = lean_nat_dec_le(v_startPos_2105_, v_start_2107_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2109_; 
v___x_2109_ = 1;
return v___x_2109_;
}
else
{
size_t v___x_2110_; size_t v___x_2111_; 
v___x_2110_ = ((size_t)1ULL);
v___x_2111_ = lean_usize_add(v_i_2102_, v___x_2110_);
v_i_2102_ = v___x_2111_;
goto _start;
}
}
else
{
uint8_t v___x_2113_; 
v___x_2113_ = 0;
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object* v_x2_2114_, lean_object* v_as_2115_, lean_object* v_i_2116_, lean_object* v_stop_2117_){
_start:
{
size_t v_i_boxed_2118_; size_t v_stop_boxed_2119_; uint8_t v_res_2120_; lean_object* v_r_2121_; 
v_i_boxed_2118_ = lean_unbox_usize(v_i_2116_);
lean_dec(v_i_2116_);
v_stop_boxed_2119_ = lean_unbox_usize(v_stop_2117_);
lean_dec(v_stop_2117_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v_x2_2114_, v_as_2115_, v_i_boxed_2118_, v_stop_boxed_2119_);
lean_dec_ref(v_as_2115_);
lean_dec_ref(v_x2_2114_);
v_r_2121_ = lean_box(v_res_2120_);
return v_r_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object* v_as_2122_, size_t v_i_2123_, size_t v_stop_2124_, lean_object* v_b_2125_){
_start:
{
lean_object* v___y_2127_; uint8_t v___x_2131_; 
v___x_2131_ = lean_usize_dec_eq(v_i_2123_, v_stop_2124_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v_length_2133_; lean_object* v_indentation_2134_; lean_object* v_tokenRanges_2135_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2132_ = lean_array_uget_borrowed(v_as_2122_, v_i_2123_);
v_length_2133_ = lean_ctor_get(v___x_2132_, 0);
v_indentation_2134_ = lean_ctor_get(v___x_2132_, 1);
v_tokenRanges_2135_ = lean_ctor_get(v___x_2132_, 3);
v___x_2139_ = lean_unsigned_to_nat(0u);
v___x_2140_ = lean_array_get_size(v_tokenRanges_2135_);
v___x_2141_ = lean_nat_dec_lt(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
goto v___jp_2136_;
}
else
{
if (v___x_2141_ == 0)
{
goto v___jp_2136_;
}
else
{
size_t v___x_2142_; size_t v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = ((size_t)0ULL);
v___x_2143_ = lean_usize_of_nat(v___x_2140_);
v___x_2144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v___x_2132_, v_tokenRanges_2135_, v___x_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
goto v___jp_2136_;
}
else
{
v___y_2127_ = v_b_2125_;
goto v___jp_2126_;
}
}
}
v___jp_2136_:
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_nat_dec_lt(v_indentation_2134_, v_length_2133_);
if (v___x_2137_ == 0)
{
v___y_2127_ = v_b_2125_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2138_; 
lean_inc(v___x_2132_);
v___x_2138_ = lean_array_push(v_b_2125_, v___x_2132_);
v___y_2127_ = v___x_2138_;
goto v___jp_2126_;
}
}
}
else
{
return v_b_2125_;
}
v___jp_2126_:
{
size_t v___x_2128_; size_t v___x_2129_; 
v___x_2128_ = ((size_t)1ULL);
v___x_2129_ = lean_usize_add(v_i_2123_, v___x_2128_);
v_i_2123_ = v___x_2129_;
v_b_2125_ = v___y_2127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object* v_as_2145_, lean_object* v_i_2146_, lean_object* v_stop_2147_, lean_object* v_b_2148_){
_start:
{
size_t v_i_boxed_2149_; size_t v_stop_boxed_2150_; lean_object* v_res_2151_; 
v_i_boxed_2149_ = lean_unbox_usize(v_i_2146_);
lean_dec(v_i_2146_);
v_stop_boxed_2150_ = lean_unbox_usize(v_stop_2147_);
lean_dec(v_stop_2147_);
v_res_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v_as_2145_, v_i_boxed_2149_, v_stop_boxed_2150_, v_b_2148_);
lean_dec_ref(v_as_2145_);
return v_res_2151_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object* v___x_2152_, lean_object* v___x_2153_, lean_object* v___x_2154_, lean_object* v_as_2155_, size_t v_i_2156_, size_t v_stop_2157_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = lean_usize_dec_eq(v_i_2156_, v_stop_2157_);
if (v___x_2158_ == 0)
{
uint8_t v___x_2159_; uint8_t v___y_2161_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2159_ = 1;
v___x_2165_ = lean_array_uget_borrowed(v_as_2155_, v_i_2156_);
v___x_2166_ = lean_nat_dec_le(v___x_2152_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_nat_dec_lt(v___x_2167_, v___x_2153_);
v___y_2161_ = v___x_2168_;
goto v___jp_2160_;
}
else
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_nat_dec_le(v___x_2152_, v___x_2154_);
v___y_2161_ = v___x_2169_;
goto v___jp_2160_;
}
v___jp_2160_:
{
if (v___y_2161_ == 0)
{
size_t v___x_2162_; size_t v___x_2163_; 
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2156_, v___x_2162_);
v_i_2156_ = v___x_2163_;
goto _start;
}
else
{
return v___x_2159_;
}
}
}
else
{
uint8_t v___x_2170_; 
v___x_2170_ = 0;
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object* v___x_2171_, lean_object* v___x_2172_, lean_object* v___x_2173_, lean_object* v_as_2174_, lean_object* v_i_2175_, lean_object* v_stop_2176_){
_start:
{
size_t v_i_boxed_2177_; size_t v_stop_boxed_2178_; uint8_t v_res_2179_; lean_object* v_r_2180_; 
v_i_boxed_2177_ = lean_unbox_usize(v_i_2175_);
lean_dec(v_i_2175_);
v_stop_boxed_2178_ = lean_unbox_usize(v_stop_2176_);
lean_dec(v_stop_2176_);
v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2171_, v___x_2172_, v___x_2173_, v_as_2174_, v_i_boxed_2177_, v_stop_boxed_2178_);
lean_dec_ref(v_as_2174_);
lean_dec(v___x_2173_);
lean_dec(v___x_2172_);
lean_dec(v___x_2171_);
v_r_2180_ = lean_box(v_res_2179_);
return v_r_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t v_sz_2181_, size_t v_i_2182_, lean_object* v_bs_2183_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_usize_dec_lt(v_i_2182_, v_sz_2181_);
if (v___x_2184_ == 0)
{
return v_bs_2183_;
}
else
{
lean_object* v_v_2185_; lean_object* v_indentation_2186_; lean_object* v___x_2187_; lean_object* v_bs_x27_2188_; size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v_v_2185_ = lean_array_uget_borrowed(v_bs_2183_, v_i_2182_);
v_indentation_2186_ = lean_ctor_get(v_v_2185_, 1);
lean_inc(v_indentation_2186_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v_bs_x27_2188_ = lean_array_uset(v_bs_2183_, v_i_2182_, v___x_2187_);
v___x_2189_ = ((size_t)1ULL);
v___x_2190_ = lean_usize_add(v_i_2182_, v___x_2189_);
v___x_2191_ = lean_array_uset(v_bs_x27_2188_, v_i_2182_, v_indentation_2186_);
v_i_2182_ = v___x_2190_;
v_bs_2183_ = v___x_2191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object* v_sz_2193_, lean_object* v_i_2194_, lean_object* v_bs_2195_){
_start:
{
size_t v_sz_boxed_2196_; size_t v_i_boxed_2197_; lean_object* v_res_2198_; 
v_sz_boxed_2196_ = lean_unbox_usize(v_sz_2193_);
lean_dec(v_sz_2193_);
v_i_boxed_2197_ = lean_unbox_usize(v_i_2194_);
lean_dec(v_i_2194_);
v_res_2198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_boxed_2196_, v_i_boxed_2197_, v_bs_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object* v_as_2199_, size_t v_i_2200_, size_t v_stop_2201_, lean_object* v_b_2202_){
_start:
{
lean_object* v___y_2204_; uint8_t v___x_2208_; 
v___x_2208_ = lean_usize_dec_eq(v_i_2200_, v_stop_2201_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = lean_array_uget_borrowed(v_as_2199_, v_i_2200_);
v___x_2210_ = lean_nat_dec_le(v_b_2202_, v___x_2209_);
if (v___x_2210_ == 0)
{
v___y_2204_ = v___x_2209_;
goto v___jp_2203_;
}
else
{
v___y_2204_ = v_b_2202_;
goto v___jp_2203_;
}
}
else
{
lean_inc(v_b_2202_);
return v_b_2202_;
}
v___jp_2203_:
{
size_t v___x_2205_; size_t v___x_2206_; 
v___x_2205_ = ((size_t)1ULL);
v___x_2206_ = lean_usize_add(v_i_2200_, v___x_2205_);
v_i_2200_ = v___x_2206_;
v_b_2202_ = v___y_2204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object* v_as_2211_, lean_object* v_i_2212_, lean_object* v_stop_2213_, lean_object* v_b_2214_){
_start:
{
size_t v_i_boxed_2215_; size_t v_stop_boxed_2216_; lean_object* v_res_2217_; 
v_i_boxed_2215_ = lean_unbox_usize(v_i_2212_);
lean_dec(v_i_2212_);
v_stop_boxed_2216_ = lean_unbox_usize(v_stop_2213_);
lean_dec(v_stop_2213_);
v_res_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_as_2211_, v_i_boxed_2215_, v_stop_boxed_2216_, v_b_2214_);
lean_dec(v_b_2214_);
lean_dec_ref(v_as_2211_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object* v_arr_2218_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; 
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = lean_array_fget_borrowed(v_arr_2218_, v___x_2219_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_array_get_size(v_arr_2218_);
v___x_2223_ = lean_nat_dec_lt(v___x_2221_, v___x_2222_);
if (v___x_2223_ == 0)
{
lean_inc(v___x_2220_);
return v___x_2220_;
}
else
{
size_t v___x_2224_; size_t v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = ((size_t)1ULL);
v___x_2225_ = lean_usize_of_nat(v___x_2222_);
v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_arr_2218_, v___x_2224_, v___x_2225_, v___x_2220_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object* v_arr_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2227_);
lean_dec_ref(v_arr_2227_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object* v_arr_2229_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2230_ = lean_array_get_size(v_arr_2229_);
v___x_2231_ = lean_unsigned_to_nat(0u);
v___x_2232_ = lean_nat_dec_eq(v___x_2230_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2229_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_box(0);
return v___x_2235_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object* v_arr_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v_arr_2236_);
lean_dec_ref(v_arr_2236_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t v_isFallback_2238_, lean_object* v_stx_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_rawDoc_2243_; lean_object* v___y_2244_; uint8_t v___y_2249_; lean_object* v_rawDoc_2250_; lean_object* v___y_2251_; lean_object* v___y_2268_; uint8_t v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2275_; uint8_t v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = 0;
v___x_2280_ = l_Lean_Syntax_getPos_x3f(v_stx_2239_, v___x_2279_);
if (lean_obj_tag(v___x_2280_) == 1)
{
lean_object* v_val_2281_; lean_object* v___x_2282_; 
v_val_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2239_, v___x_2279_);
if (lean_obj_tag(v___x_2282_) == 1)
{
lean_object* v_val_2283_; lean_object* v___x_2284_; 
v_val_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc_n(v_val_2283_, 2);
lean_dec_ref_known(v___x_2282_, 1);
lean_inc(v_val_2281_);
v___x_2284_ = l_Lean_Fmt_getLineInfos(v_val_2281_, v_val_2283_, v_a_2240_, v_a_2241_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v_a_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_indentation_2290_; lean_object* v_line_2291_; lean_object* v_startPos_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___y_2297_; size_t v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2313_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_n(v_a_2285_, 2);
v_a_2286_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2284_, 2);
v___x_2287_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_array_get_borrowed(v___x_2287_, v_a_2285_, v___x_2288_);
v_indentation_2290_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_indentation_2290_);
v_line_2291_ = lean_ctor_get(v___x_2289_, 2);
v_startPos_2292_ = lean_ctor_get(v___x_2289_, 4);
v___x_2293_ = lean_nat_sub(v_val_2281_, v_startPos_2292_);
v___x_2294_ = l_String_Pos_Raw_offsetOfPosAux(v_line_2291_, v___x_2293_, v___x_2288_, v___x_2288_);
lean_dec(v___x_2293_);
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2324_ = lean_array_get_size(v_a_2285_);
v___x_2325_ = l_Array_toSubarray___redArg(v_a_2285_, v___x_2295_, v___x_2324_);
v___x_2326_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_2327_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_2325_, v___x_2326_);
v___x_2328_ = lean_array_get_size(v___x_2327_);
v___x_2329_ = lean_nat_dec_lt(v___x_2288_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec_ref(v___x_2327_);
v___y_2313_ = v___x_2326_;
goto v___jp_2312_;
}
else
{
size_t v___x_2330_; size_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = lean_usize_of_nat(v___x_2328_);
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2327_, v___x_2330_, v___x_2331_, v___x_2326_);
lean_dec_ref(v___x_2327_);
v___y_2313_ = v___x_2332_;
goto v___jp_2312_;
}
v___jp_2296_:
{
uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = 1;
v___x_2301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2301_, 0, v___y_2299_);
lean_ctor_set(v___x_2301_, 1, v_val_2281_);
lean_ctor_set(v___x_2301_, 2, v_val_2283_);
lean_inc(v_stx_2239_);
v___x_2302_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2239_, v___x_2300_, v___x_2301_, v_a_2240_, v_a_2286_);
lean_dec_ref_known(v___x_2301_, 3);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_a_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
v_a_2304_ = lean_ctor_get(v___x_2302_, 1);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2302_, 2);
v___x_2305_ = lean_array_get_size(v_a_2285_);
lean_dec(v_a_2285_);
v___x_2306_ = lean_nat_dec_lt(v___x_2295_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_dec_ref(v___y_2297_);
lean_dec(v___x_2294_);
lean_dec(v_indentation_2290_);
v___y_2268_ = v_a_2303_;
v___y_2269_ = v___x_2306_;
v___y_2270_ = v_a_2304_;
goto v___jp_2267_;
}
else
{
uint8_t v___x_2307_; 
v___x_2307_ = lean_nat_dec_le(v___x_2294_, v_indentation_2290_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = lean_array_get_size(v___y_2297_);
v___x_2309_ = lean_nat_dec_lt(v___x_2288_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_dec_ref(v___y_2297_);
lean_dec(v___x_2294_);
lean_dec(v_indentation_2290_);
v___y_2273_ = v_a_2303_;
v___y_2274_ = v___x_2306_;
v___y_2275_ = v_a_2304_;
goto v___jp_2272_;
}
else
{
if (v___x_2309_ == 0)
{
lean_dec_ref(v___y_2297_);
lean_dec(v___x_2294_);
lean_dec(v_indentation_2290_);
v___y_2273_ = v_a_2303_;
v___y_2274_ = v___x_2306_;
v___y_2275_ = v_a_2304_;
goto v___jp_2272_;
}
else
{
size_t v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = lean_usize_of_nat(v___x_2308_);
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2294_, v___x_2305_, v_indentation_2290_, v___y_2297_, v___y_2298_, v___x_2310_);
lean_dec_ref(v___y_2297_);
lean_dec(v_indentation_2290_);
lean_dec(v___x_2294_);
if (v___x_2311_ == 0)
{
v___y_2273_ = v_a_2303_;
v___y_2274_ = v___x_2306_;
v___y_2275_ = v_a_2304_;
goto v___jp_2272_;
}
else
{
v___y_2268_ = v_a_2303_;
v___y_2269_ = v___x_2306_;
v___y_2270_ = v_a_2304_;
goto v___jp_2267_;
}
}
}
}
else
{
lean_dec_ref(v___y_2297_);
lean_dec(v___x_2294_);
lean_dec(v_indentation_2290_);
v___y_2273_ = v_a_2303_;
v___y_2274_ = v___x_2306_;
v___y_2275_ = v_a_2304_;
goto v___jp_2272_;
}
}
}
else
{
lean_dec_ref(v___y_2297_);
lean_dec(v___x_2294_);
lean_dec(v_indentation_2290_);
lean_dec(v_a_2285_);
lean_dec(v_stx_2239_);
return v___x_2302_;
}
}
v___jp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; size_t v_sz_2316_; size_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2314_ = lean_mk_empty_array_with_capacity(v___x_2295_);
lean_inc(v___x_2294_);
v___x_2315_ = lean_array_push(v___x_2314_, v___x_2294_);
v_sz_2316_ = lean_array_size(v___y_2313_);
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_2316_, v___x_2317_, v___y_2313_);
v___x_2319_ = l_Array_append___redArg(v___x_2315_, v___x_2318_);
v___x_2320_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v___x_2319_);
lean_dec_ref(v___x_2319_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_2322_ = l_panic___at___00Lean_Fmt_fmtRaw_spec__4(v___x_2321_);
v___y_2297_ = v___x_2318_;
v___y_2298_ = v___x_2317_;
v___y_2299_ = v___x_2322_;
goto v___jp_2296_;
}
else
{
lean_object* v_val_2323_; 
v_val_2323_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_val_2323_);
lean_dec_ref_known(v___x_2320_, 1);
v___y_2297_ = v___x_2318_;
v___y_2298_ = v___x_2317_;
v___y_2299_ = v_val_2323_;
goto v___jp_2296_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_val_2283_);
lean_dec(v_val_2281_);
lean_dec(v_stx_2239_);
v_a_2333_ = lean_ctor_get(v___x_2284_, 0);
v_a_2334_ = lean_ctor_get(v___x_2284_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2284_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_inc(v_a_2333_);
lean_dec(v___x_2284_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2333_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec(v___x_2282_);
lean_dec(v_val_2281_);
v___x_2342_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2343_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2342_, v_stx_2239_, v_a_2241_);
lean_dec(v_stx_2239_);
return v___x_2343_;
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v___x_2280_);
v___x_2344_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2345_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2344_, v_stx_2239_, v_a_2241_);
lean_dec(v_stx_2239_);
return v___x_2345_;
}
v___jp_2242_:
{
if (v_isFallback_2238_ == 0)
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v_rawDoc_2243_);
lean_ctor_set(v___x_2245_, 1, v___y_2244_);
return v___x_2245_;
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2246_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_rawDoc_2243_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___y_2244_);
return v___x_2247_;
}
}
v___jp_2248_:
{
lean_object* v_doc_2252_; lean_object* v_metaData_2253_; lean_object* v___x_2254_; 
v_doc_2252_ = lean_ctor_get(v_rawDoc_2250_, 0);
lean_inc(v_doc_2252_);
v_metaData_2253_ = lean_ctor_get(v_rawDoc_2250_, 1);
lean_inc(v_metaData_2253_);
lean_dec_ref(v_rawDoc_2250_);
v___x_2254_ = l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(v_doc_2252_, v_stx_2239_, v___y_2251_);
lean_dec(v_stx_2239_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v_a_2256_; lean_object* v_doc_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2265_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
v_a_2256_ = lean_ctor_get(v___x_2254_, 1);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2254_, 2);
v_doc_2257_ = lean_ctor_get(v_a_2255_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_a_2255_);
if (v_isSharedCheck_2265_ == 0)
{
lean_object* v_unused_2266_; 
v_unused_2266_ = lean_ctor_get(v_a_2255_, 1);
lean_dec(v_unused_2266_);
v___x_2259_ = v_a_2255_;
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_doc_2257_);
lean_dec(v_a_2255_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2265_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v_metaData_2253_);
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_doc_2257_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_metaData_2253_);
v___x_2262_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
if (v___y_2249_ == 0)
{
v_rawDoc_2243_ = v___x_2262_;
v___y_2244_ = v_a_2256_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_Fmt_TaggedDoc_markMultiLineRaw(v___x_2262_);
v_rawDoc_2243_ = v___x_2263_;
v___y_2244_ = v_a_2256_;
goto v___jp_2242_;
}
}
}
}
else
{
lean_dec(v_metaData_2253_);
return v___x_2254_;
}
}
v___jp_2267_:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2268_);
v___y_2249_ = v___y_2269_;
v_rawDoc_2250_ = v___x_2271_;
v___y_2251_ = v___y_2270_;
goto v___jp_2248_;
}
v___jp_2272_:
{
lean_object* v_doc_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v_doc_2276_ = lean_ctor_get(v___y_2273_, 0);
lean_inc(v_doc_2276_);
lean_dec_ref(v___y_2273_);
v___x_2277_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_2276_);
v___x_2278_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2277_);
v___y_2249_ = v___y_2274_;
v_rawDoc_2250_ = v___x_2278_;
v___y_2251_ = v___y_2275_;
goto v___jp_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object* v_isFallback_2346_, lean_object* v_stx_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
uint8_t v_isFallback_boxed_2350_; lean_object* v_res_2351_; 
v_isFallback_boxed_2350_ = lean_unbox(v_isFallback_2346_);
v_res_2351_ = l_Lean_Fmt_fmtRaw(v_isFallback_boxed_2350_, v_stx_2347_, v_a_2348_, v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object* v_arr_2352_, lean_object* v_h_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object* v_arr_2355_, lean_object* v_h_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(v_arr_2355_, v_h_2356_);
lean_dec_ref(v_arr_2355_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object* v_a_2358_, lean_object* v_____r_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_a_2358_);
v___x_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___y_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object* v_a_2364_, lean_object* v_____r_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2364_, v_____r_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v___y_2366_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object* v_a_2369_, lean_object* v_b_2370_, lean_object* v_x_2371_){
_start:
{
if (lean_obj_tag(v_x_2371_) == 0)
{
lean_dec(v_b_2370_);
lean_dec_ref(v_a_2369_);
return v_x_2371_;
}
else
{
lean_object* v_key_2372_; lean_object* v_value_2373_; lean_object* v_tail_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2386_; 
v_key_2372_ = lean_ctor_get(v_x_2371_, 0);
v_value_2373_ = lean_ctor_get(v_x_2371_, 1);
v_tail_2374_ = lean_ctor_get(v_x_2371_, 2);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_x_2371_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2376_ = v_x_2371_;
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_tail_2374_);
lean_inc(v_value_2373_);
lean_inc(v_key_2372_);
lean_dec(v_x_2371_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_Syntax_instBEqRange_beq(v_key_2372_, v_a_2369_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
v___x_2379_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2369_, v_b_2370_, v_tail_2374_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 2, v___x_2379_);
v___x_2381_ = v___x_2376_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_key_2372_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_value_2373_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v___x_2379_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
else
{
lean_object* v___x_2384_; 
lean_dec(v_value_2373_);
lean_dec(v_key_2372_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v_b_2370_);
lean_ctor_set(v___x_2376_, 0, v_a_2369_);
v___x_2384_ = v___x_2376_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2369_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_b_2370_);
lean_ctor_set(v_reuseFailAlloc_2385_, 2, v_tail_2374_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2387_, lean_object* v_x_2388_){
_start:
{
if (lean_obj_tag(v_x_2388_) == 0)
{
return v_x_2387_;
}
else
{
lean_object* v_key_2389_; lean_object* v_value_2390_; lean_object* v_tail_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2414_; 
v_key_2389_ = lean_ctor_get(v_x_2388_, 0);
v_value_2390_ = lean_ctor_get(v_x_2388_, 1);
v_tail_2391_ = lean_ctor_get(v_x_2388_, 2);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_x_2388_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2393_ = v_x_2388_;
v_isShared_2394_ = v_isSharedCheck_2414_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_tail_2391_);
lean_inc(v_value_2390_);
lean_inc(v_key_2389_);
lean_dec(v_x_2388_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2414_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; uint64_t v___x_2396_; uint64_t v___x_2397_; uint64_t v___x_2398_; uint64_t v_fold_2399_; uint64_t v___x_2400_; uint64_t v___x_2401_; uint64_t v___x_2402_; size_t v___x_2403_; size_t v___x_2404_; size_t v___x_2405_; size_t v___x_2406_; size_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2395_ = lean_array_get_size(v_x_2387_);
v___x_2396_ = l_Lean_Syntax_instHashableRange_hash(v_key_2389_);
v___x_2397_ = 32ULL;
v___x_2398_ = lean_uint64_shift_right(v___x_2396_, v___x_2397_);
v_fold_2399_ = lean_uint64_xor(v___x_2396_, v___x_2398_);
v___x_2400_ = 16ULL;
v___x_2401_ = lean_uint64_shift_right(v_fold_2399_, v___x_2400_);
v___x_2402_ = lean_uint64_xor(v_fold_2399_, v___x_2401_);
v___x_2403_ = lean_uint64_to_usize(v___x_2402_);
v___x_2404_ = lean_usize_of_nat(v___x_2395_);
v___x_2405_ = ((size_t)1ULL);
v___x_2406_ = lean_usize_sub(v___x_2404_, v___x_2405_);
v___x_2407_ = lean_usize_land(v___x_2403_, v___x_2406_);
v___x_2408_ = lean_array_uget_borrowed(v_x_2387_, v___x_2407_);
lean_inc(v___x_2408_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 2, v___x_2408_);
v___x_2410_ = v___x_2393_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_key_2389_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v_value_2390_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_array_uset(v_x_2387_, v___x_2407_, v___x_2410_);
v_x_2387_ = v___x_2411_;
v_x_2388_ = v_tail_2391_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2415_, lean_object* v_source_2416_, lean_object* v_target_2417_){
_start:
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2418_ = lean_array_get_size(v_source_2416_);
v___x_2419_ = lean_nat_dec_lt(v_i_2415_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_dec_ref(v_source_2416_);
lean_dec(v_i_2415_);
return v_target_2417_;
}
else
{
lean_object* v_es_2420_; lean_object* v___x_2421_; lean_object* v_source_2422_; lean_object* v_target_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_es_2420_ = lean_array_fget(v_source_2416_, v_i_2415_);
v___x_2421_ = lean_box(0);
v_source_2422_ = lean_array_fset(v_source_2416_, v_i_2415_, v___x_2421_);
v_target_2423_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2417_, v_es_2420_);
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = lean_nat_add(v_i_2415_, v___x_2424_);
lean_dec(v_i_2415_);
v_i_2415_ = v___x_2425_;
v_source_2416_ = v_source_2422_;
v_target_2417_ = v_target_2423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object* v_data_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_nbuckets_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2428_ = lean_array_get_size(v_data_2427_);
v___x_2429_ = lean_unsigned_to_nat(2u);
v_nbuckets_2430_ = lean_nat_mul(v___x_2428_, v___x_2429_);
v___x_2431_ = lean_unsigned_to_nat(0u);
v___x_2432_ = lean_box(0);
v___x_2433_ = lean_mk_array(v_nbuckets_2430_, v___x_2432_);
v___x_2434_ = lean_array_propagate_mark(v_data_2427_, v___x_2433_);
v___x_2435_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v___x_2431_, v_data_2427_, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object* v_a_2436_, lean_object* v_x_2437_){
_start:
{
if (lean_obj_tag(v_x_2437_) == 0)
{
uint8_t v___x_2438_; 
v___x_2438_ = 0;
return v___x_2438_;
}
else
{
lean_object* v_key_2439_; lean_object* v_tail_2440_; uint8_t v___x_2441_; 
v_key_2439_ = lean_ctor_get(v_x_2437_, 0);
v_tail_2440_ = lean_ctor_get(v_x_2437_, 2);
v___x_2441_ = l_Lean_Syntax_instBEqRange_beq(v_key_2439_, v_a_2436_);
if (v___x_2441_ == 0)
{
v_x_2437_ = v_tail_2440_;
goto _start;
}
else
{
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object* v_a_2443_, lean_object* v_x_2444_){
_start:
{
uint8_t v_res_2445_; lean_object* v_r_2446_; 
v_res_2445_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2443_, v_x_2444_);
lean_dec(v_x_2444_);
lean_dec_ref(v_a_2443_);
v_r_2446_ = lean_box(v_res_2445_);
return v_r_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object* v_m_2447_, lean_object* v_a_2448_, lean_object* v_b_2449_){
_start:
{
lean_object* v_size_2450_; lean_object* v_buckets_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2494_; 
v_size_2450_ = lean_ctor_get(v_m_2447_, 0);
v_buckets_2451_ = lean_ctor_get(v_m_2447_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_m_2447_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2453_ = v_m_2447_;
v_isShared_2454_ = v_isSharedCheck_2494_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_buckets_2451_);
lean_inc(v_size_2450_);
lean_dec(v_m_2447_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2494_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; uint64_t v___x_2456_; uint64_t v___x_2457_; uint64_t v___x_2458_; uint64_t v_fold_2459_; uint64_t v___x_2460_; uint64_t v___x_2461_; uint64_t v___x_2462_; size_t v___x_2463_; size_t v___x_2464_; size_t v___x_2465_; size_t v___x_2466_; size_t v___x_2467_; lean_object* v_bkt_2468_; uint8_t v___x_2469_; 
v___x_2455_ = lean_array_get_size(v_buckets_2451_);
v___x_2456_ = l_Lean_Syntax_instHashableRange_hash(v_a_2448_);
v___x_2457_ = 32ULL;
v___x_2458_ = lean_uint64_shift_right(v___x_2456_, v___x_2457_);
v_fold_2459_ = lean_uint64_xor(v___x_2456_, v___x_2458_);
v___x_2460_ = 16ULL;
v___x_2461_ = lean_uint64_shift_right(v_fold_2459_, v___x_2460_);
v___x_2462_ = lean_uint64_xor(v_fold_2459_, v___x_2461_);
v___x_2463_ = lean_uint64_to_usize(v___x_2462_);
v___x_2464_ = lean_usize_of_nat(v___x_2455_);
v___x_2465_ = ((size_t)1ULL);
v___x_2466_ = lean_usize_sub(v___x_2464_, v___x_2465_);
v___x_2467_ = lean_usize_land(v___x_2463_, v___x_2466_);
v_bkt_2468_ = lean_array_uget_borrowed(v_buckets_2451_, v___x_2467_);
v___x_2469_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2448_, v_bkt_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v_size_x27_2471_; lean_object* v___x_2472_; lean_object* v_buckets_x27_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2470_ = lean_unsigned_to_nat(1u);
v_size_x27_2471_ = lean_nat_add(v_size_2450_, v___x_2470_);
lean_dec(v_size_2450_);
lean_inc(v_bkt_2468_);
v___x_2472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2472_, 0, v_a_2448_);
lean_ctor_set(v___x_2472_, 1, v_b_2449_);
lean_ctor_set(v___x_2472_, 2, v_bkt_2468_);
v_buckets_x27_2473_ = lean_array_uset(v_buckets_2451_, v___x_2467_, v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(4u);
v___x_2475_ = lean_nat_mul(v_size_x27_2471_, v___x_2474_);
v___x_2476_ = lean_unsigned_to_nat(3u);
v___x_2477_ = lean_nat_div(v___x_2475_, v___x_2476_);
lean_dec(v___x_2475_);
v___x_2478_ = lean_array_get_size(v_buckets_x27_2473_);
v___x_2479_ = lean_nat_dec_le(v___x_2477_, v___x_2478_);
lean_dec(v___x_2477_);
if (v___x_2479_ == 0)
{
lean_object* v_val_2480_; lean_object* v___x_2482_; 
v_val_2480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_buckets_x27_2473_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v_val_2480_);
lean_ctor_set(v___x_2453_, 0, v_size_x27_2471_);
v___x_2482_ = v___x_2453_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_size_x27_2471_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_val_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
else
{
lean_object* v___x_2485_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v_buckets_x27_2473_);
lean_ctor_set(v___x_2453_, 0, v_size_x27_2471_);
v___x_2485_ = v___x_2453_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_size_x27_2471_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_buckets_x27_2473_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
else
{
lean_object* v___x_2487_; lean_object* v_buckets_x27_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_inc(v_bkt_2468_);
v___x_2487_ = lean_box(0);
v_buckets_x27_2488_ = lean_array_uset(v_buckets_2451_, v___x_2467_, v___x_2487_);
v___x_2489_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2448_, v_b_2449_, v_bkt_2468_);
v___x_2490_ = lean_array_uset(v_buckets_x27_2488_, v___x_2467_, v___x_2489_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v___x_2490_);
v___x_2492_ = v___x_2453_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_size_2450_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object* v_f_2495_, lean_object* v_formatterName_2496_, lean_object* v_stx_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v___y_2501_; lean_object* v_a_2513_; lean_object* v_a_2514_; lean_object* v___x_2550_; 
lean_inc_ref(v_a_2498_);
lean_inc(v_stx_2497_);
v___x_2550_ = lean_apply_3(v_f_2495_, v_stx_2497_, v_a_2498_, v_a_2499_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v_a_2552_; lean_object* v___x_2553_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
v_a_2552_ = lean_ctor_get(v___x_2550_, 1);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2550_, 2);
v___x_2553_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_a_2551_, v_stx_2497_, v_a_2552_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_stx_2497_);
lean_dec(v_formatterName_2496_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 1);
v_a_2555_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2557_ = v___x_2553_;
v_isShared_2558_ = v_isSharedCheck_2579_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2554_);
lean_inc(v_a_2555_);
lean_dec(v___x_2553_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2579_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v_toBacktrackableState_2559_; lean_object* v_shareCommonState_2560_; lean_object* v_freshTagId_2561_; lean_object* v_missingFormatters_2562_; lean_object* v_partialFormatters_2563_; lean_object* v_missingChoiceResolutions_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2578_; 
v_toBacktrackableState_2559_ = lean_ctor_get(v_a_2554_, 0);
v_shareCommonState_2560_ = lean_ctor_get(v_a_2554_, 1);
v_freshTagId_2561_ = lean_ctor_get(v_a_2554_, 2);
v_missingFormatters_2562_ = lean_ctor_get(v_a_2554_, 3);
v_partialFormatters_2563_ = lean_ctor_get(v_a_2554_, 4);
v_missingChoiceResolutions_2564_ = lean_ctor_get(v_a_2554_, 5);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_a_2554_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2566_ = v_a_2554_;
v_isShared_2567_ = v_isSharedCheck_2578_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_missingChoiceResolutions_2564_);
lean_inc(v_partialFormatters_2563_);
lean_inc(v_missingFormatters_2562_);
lean_inc(v_freshTagId_2561_);
lean_inc(v_shareCommonState_2560_);
lean_inc(v_toBacktrackableState_2559_);
lean_dec(v_a_2554_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2578_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2573_; 
v___x_2568_ = l_Lean_ShareCommon_objectFactory;
v___x_2569_ = lean_state_sharecommon(v___x_2568_, v_shareCommonState_2560_, v_a_2555_);
v_fst_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_fst_2570_);
v_snd_2571_ = lean_ctor_get(v___x_2569_, 1);
lean_inc(v_snd_2571_);
lean_dec_ref(v___x_2569_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 1, v_snd_2571_);
v___x_2573_ = v___x_2566_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_toBacktrackableState_2559_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_snd_2571_);
lean_ctor_set(v_reuseFailAlloc_2577_, 2, v_freshTagId_2561_);
lean_ctor_set(v_reuseFailAlloc_2577_, 3, v_missingFormatters_2562_);
lean_ctor_set(v_reuseFailAlloc_2577_, 4, v_partialFormatters_2563_);
lean_ctor_set(v_reuseFailAlloc_2577_, 5, v_missingChoiceResolutions_2564_);
v___x_2573_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2575_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 1, v___x_2573_);
lean_ctor_set(v___x_2557_, 0, v_fst_2570_);
v___x_2575_ = v___x_2557_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_fst_2570_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
else
{
lean_object* v_a_2580_; lean_object* v_a_2581_; 
v_a_2580_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2580_);
v_a_2581_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2553_, 2);
v_a_2513_ = v_a_2580_;
v_a_2514_ = v_a_2581_;
goto v___jp_2512_;
}
}
else
{
lean_object* v_a_2582_; lean_object* v_a_2583_; 
v_a_2582_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2582_);
v_a_2583_ = lean_ctor_get(v___x_2550_, 1);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2550_, 2);
v_a_2513_ = v_a_2582_;
v_a_2514_ = v_a_2583_;
goto v___jp_2512_;
}
v___jp_2500_:
{
lean_object* v_a_2502_; lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2511_; 
v_a_2502_ = lean_ctor_get(v___y_2501_, 0);
v_a_2503_ = lean_ctor_get(v___y_2501_, 1);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___y_2501_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2505_ = v___y_2501_;
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_inc(v_a_2502_);
lean_dec(v___y_2501_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2511_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v_a_2507_; lean_object* v___x_2509_; 
v_a_2507_ = lean_ctor_get(v_a_2502_, 0);
lean_inc(v_a_2507_);
lean_dec(v_a_2502_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v_a_2507_);
v___x_2509_ = v___x_2505_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2507_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_a_2503_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
v___jp_2512_:
{
if (lean_obj_tag(v_a_2513_) == 0)
{
uint8_t v_err_2515_; 
v_err_2515_ = lean_ctor_get_uint8(v_a_2513_, 0);
if (v_err_2515_ == 0)
{
uint8_t v___x_2516_; lean_object* v___x_2517_; 
lean_dec_ref_known(v_a_2513_, 0);
v___x_2516_ = 1;
lean_inc(v_stx_2497_);
v___x_2517_ = l_Lean_Fmt_fmtRaw(v___x_2516_, v_stx_2497_, v_a_2498_, v_a_2514_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2547_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_a_2519_ = lean_ctor_get(v___x_2517_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2521_ = v___x_2517_;
v_isShared_2522_ = v_isSharedCheck_2547_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2547_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
uint8_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = 0;
v___x_2524_ = l_Lean_Syntax_getRange_x3f(v_stx_2497_, v___x_2523_);
if (lean_obj_tag(v___x_2524_) == 1)
{
lean_object* v_val_2525_; lean_object* v_toBacktrackableState_2526_; lean_object* v_shareCommonState_2527_; lean_object* v_freshTagId_2528_; lean_object* v_missingFormatters_2529_; lean_object* v_partialFormatters_2530_; lean_object* v_missingChoiceResolutions_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2544_; 
v_val_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v_toBacktrackableState_2526_ = lean_ctor_get(v_a_2519_, 0);
v_shareCommonState_2527_ = lean_ctor_get(v_a_2519_, 1);
v_freshTagId_2528_ = lean_ctor_get(v_a_2519_, 2);
v_missingFormatters_2529_ = lean_ctor_get(v_a_2519_, 3);
v_partialFormatters_2530_ = lean_ctor_get(v_a_2519_, 4);
v_missingChoiceResolutions_2531_ = lean_ctor_get(v_a_2519_, 5);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_a_2519_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2533_ = v_a_2519_;
v_isShared_2534_ = v_isSharedCheck_2544_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_missingChoiceResolutions_2531_);
lean_inc(v_partialFormatters_2530_);
lean_inc(v_missingFormatters_2529_);
lean_inc(v_freshTagId_2528_);
lean_inc(v_shareCommonState_2527_);
lean_inc(v_toBacktrackableState_2526_);
lean_dec(v_a_2519_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2544_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
v___x_2535_ = lean_box(0);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v_formatterName_2496_);
lean_ctor_set(v___x_2521_, 0, v_stx_2497_);
v___x_2537_ = v___x_2521_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_stx_2497_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_formatterName_2496_);
v___x_2537_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_partialFormatters_2530_, v_val_2525_, v___x_2537_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 4, v___x_2538_);
v___x_2540_ = v___x_2533_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_toBacktrackableState_2526_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_shareCommonState_2527_);
lean_ctor_set(v_reuseFailAlloc_2542_, 2, v_freshTagId_2528_);
lean_ctor_set(v_reuseFailAlloc_2542_, 3, v_missingFormatters_2529_);
lean_ctor_set(v_reuseFailAlloc_2542_, 4, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2542_, 5, v_missingChoiceResolutions_2531_);
v___x_2540_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2518_, v___x_2535_, v_a_2498_, v___x_2540_);
v___y_2501_ = v___x_2541_;
goto v___jp_2500_;
}
}
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec(v___x_2524_);
lean_del_object(v___x_2521_);
lean_dec(v_stx_2497_);
lean_dec(v_formatterName_2496_);
v___x_2545_ = lean_box(0);
v___x_2546_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2518_, v___x_2545_, v_a_2498_, v_a_2519_);
v___y_2501_ = v___x_2546_;
goto v___jp_2500_;
}
}
}
else
{
lean_dec(v_stx_2497_);
lean_dec(v_formatterName_2496_);
return v___x_2517_;
}
}
else
{
lean_object* v___x_2548_; 
lean_dec(v_stx_2497_);
lean_dec(v_formatterName_2496_);
v___x_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2548_, 0, v_a_2513_);
lean_ctor_set(v___x_2548_, 1, v_a_2514_);
return v___x_2548_;
}
}
else
{
lean_object* v___x_2549_; 
lean_dec(v_stx_2497_);
lean_dec(v_formatterName_2496_);
v___x_2549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_a_2513_);
lean_ctor_set(v___x_2549_, 1, v_a_2514_);
return v___x_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object* v_f_2584_, lean_object* v_formatterName_2585_, lean_object* v_stx_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Fmt_fmtWith(v_f_2584_, v_formatterName_2585_, v_stx_2586_, v_a_2587_, v_a_2588_);
lean_dec_ref(v_a_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object* v_00_u03b2_2590_, lean_object* v_m_2591_, lean_object* v_a_2592_, lean_object* v_b_2593_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_m_2591_, v_a_2592_, v_b_2593_);
return v___x_2594_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object* v_00_u03b2_2595_, lean_object* v_a_2596_, lean_object* v_x_2597_){
_start:
{
uint8_t v___x_2598_; 
v___x_2598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2596_, v_x_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2599_, lean_object* v_a_2600_, lean_object* v_x_2601_){
_start:
{
uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_res_2602_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(v_00_u03b2_2599_, v_a_2600_, v_x_2601_);
lean_dec(v_x_2601_);
lean_dec_ref(v_a_2600_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object* v_00_u03b2_2604_, lean_object* v_data_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_data_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object* v_00_u03b2_2607_, lean_object* v_a_2608_, lean_object* v_b_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2608_, v_b_2609_, v_x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2612_, lean_object* v_i_2613_, lean_object* v_source_2614_, lean_object* v_target_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v_i_2613_, v_source_2614_, v_target_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2618_, v_x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object* v_a_2624_, lean_object* v_kind_2625_, lean_object* v_as_2626_, size_t v_sz_2627_, size_t v_i_2628_, lean_object* v_b_2629_){
_start:
{
uint8_t v___x_2630_; 
v___x_2630_ = lean_usize_dec_lt(v_i_2628_, v_sz_2627_);
if (v___x_2630_ == 0)
{
lean_dec(v_kind_2625_);
lean_inc_ref(v_b_2629_);
return v_b_2629_;
}
else
{
lean_object* v_a_2631_; lean_object* v_provider_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2648_; 
v_a_2631_ = lean_array_uget(v_as_2626_, v_i_2628_);
v_provider_2632_ = lean_ctor_get(v_a_2631_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_a_2631_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v_a_2631_, 0);
lean_dec(v_unused_2649_);
v___x_2634_ = v_a_2631_;
v_isShared_2635_ = v_isSharedCheck_2648_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_provider_2632_);
lean_dec(v_a_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2648_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_env_2636_; lean_object* v_opts_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_env_2636_ = lean_ctor_get(v_a_2624_, 0);
v_opts_2637_ = lean_ctor_get(v_a_2624_, 3);
v___x_2638_ = lean_box(0);
lean_inc(v_kind_2625_);
lean_inc_ref(v_opts_2637_);
lean_inc_ref(v_env_2636_);
v___x_2639_ = lean_apply_3(v_provider_2632_, v_env_2636_, v_opts_2637_, v_kind_2625_);
if (lean_obj_tag(v___x_2639_) == 1)
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
lean_dec(v_kind_2625_);
v___x_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 1, v___x_2638_);
lean_ctor_set(v___x_2634_, 0, v___x_2640_);
v___x_2642_ = v___x_2634_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v___x_2638_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
else
{
lean_object* v___x_2644_; size_t v___x_2645_; size_t v___x_2646_; 
lean_dec(v___x_2639_);
lean_del_object(v___x_2634_);
v___x_2644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2628_, v___x_2645_);
v_i_2628_ = v___x_2646_;
v_b_2629_ = v___x_2644_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object* v_a_2650_, lean_object* v_kind_2651_, lean_object* v_as_2652_, lean_object* v_sz_2653_, lean_object* v_i_2654_, lean_object* v_b_2655_){
_start:
{
size_t v_sz_boxed_2656_; size_t v_i_boxed_2657_; lean_object* v_res_2658_; 
v_sz_boxed_2656_ = lean_unbox_usize(v_sz_2653_);
lean_dec(v_sz_2653_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2650_, v_kind_2651_, v_as_2652_, v_sz_boxed_2656_, v_i_boxed_2657_, v_b_2655_);
lean_dec_ref(v_b_2655_);
lean_dec_ref(v_as_2652_);
lean_dec_ref(v_a_2650_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object* v_kind_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_env_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; size_t v_sz_2666_; size_t v___x_2667_; lean_object* v___x_2668_; lean_object* v_fst_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2680_; 
v_env_2662_ = lean_ctor_get(v_a_2660_, 0);
lean_inc_ref(v_env_2662_);
v___x_2663_ = l_Lean_Fmt_getFmtProviders(v_env_2662_);
v___x_2664_ = lean_box(0);
v___x_2665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v_sz_2666_ = lean_array_size(v___x_2663_);
v___x_2667_ = ((size_t)0ULL);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2660_, v_kind_2659_, v___x_2663_, v_sz_2666_, v___x_2667_, v___x_2665_);
lean_dec_ref(v___x_2663_);
v_fst_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2680_ == 0)
{
lean_object* v_unused_2681_; 
v_unused_2681_ = lean_ctor_get(v___x_2668_, 1);
lean_dec(v_unused_2681_);
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_fst_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
if (lean_obj_tag(v_fst_2669_) == 0)
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v_a_2661_);
lean_ctor_set(v___x_2671_, 0, v___x_2664_);
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_a_2661_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
else
{
lean_object* v_val_2676_; lean_object* v___x_2678_; 
v_val_2676_ = lean_ctor_get(v_fst_2669_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v_fst_2669_, 1);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v_a_2661_);
lean_ctor_set(v___x_2671_, 0, v_val_2676_);
v___x_2678_ = v___x_2671_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_val_2676_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_a_2661_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object* v_kind_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2682_, v_a_2683_, v_a_2684_);
lean_dec_ref(v_a_2683_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object* v_stx_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
switch(lean_obj_tag(v_stx_2686_))
{
case 0:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_a_2688_);
return v___x_2690_;
}
case 1:
{
lean_object* v_kind_2691_; lean_object* v___x_2692_; lean_object* v_a_2693_; 
lean_inc_ref(v_stx_2686_);
v_kind_2691_ = l_Lean_Syntax_getKind(v_stx_2686_);
lean_inc(v_kind_2691_);
v___x_2692_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2691_, v_a_2687_, v_a_2688_);
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
if (lean_obj_tag(v_a_2693_) == 1)
{
lean_object* v_val_2694_; lean_object* v_a_2695_; lean_object* v_fst_2696_; lean_object* v_snd_2697_; lean_object* v___x_2698_; 
lean_dec(v_kind_2691_);
v_val_2694_ = lean_ctor_get(v_a_2693_, 0);
lean_inc(v_val_2694_);
v_a_2695_ = lean_ctor_get(v___x_2692_, 1);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2692_);
v_fst_2696_ = lean_ctor_get(v_val_2694_, 0);
lean_inc(v_fst_2696_);
v_snd_2697_ = lean_ctor_get(v_val_2694_, 1);
lean_inc(v_snd_2697_);
lean_dec(v_val_2694_);
v___x_2698_ = l_Lean_Fmt_fmtWith(v_snd_2697_, v_fst_2696_, v_stx_2686_, v_a_2687_, v_a_2695_);
return v___x_2698_;
}
else
{
lean_object* v_a_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; 
v_a_2699_ = lean_ctor_get(v___x_2692_, 1);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2692_);
v___x_2700_ = 1;
lean_inc_ref(v_stx_2686_);
v___x_2701_ = l_Lean_Fmt_fmtRaw(v___x_2700_, v_stx_2686_, v_a_2687_, v_a_2699_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v_a_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_a_2703_ = lean_ctor_get(v___x_2701_, 1);
lean_inc(v_a_2703_);
v___x_2704_ = 0;
v___x_2705_ = l_Lean_Syntax_getRange_x3f(v_stx_2686_, v___x_2704_);
lean_dec_ref_known(v_stx_2686_, 3);
if (lean_obj_tag(v___x_2705_) == 1)
{
lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2727_; 
lean_inc(v_a_2702_);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; lean_object* v_unused_2729_; 
v_unused_2728_ = lean_ctor_get(v___x_2701_, 1);
lean_dec(v_unused_2728_);
v_unused_2729_ = lean_ctor_get(v___x_2701_, 0);
lean_dec(v_unused_2729_);
v___x_2707_ = v___x_2701_;
v_isShared_2708_ = v_isSharedCheck_2727_;
goto v_resetjp_2706_;
}
else
{
lean_dec(v___x_2701_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2727_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v_val_2709_; lean_object* v_toBacktrackableState_2710_; lean_object* v_shareCommonState_2711_; lean_object* v_freshTagId_2712_; lean_object* v_missingFormatters_2713_; lean_object* v_partialFormatters_2714_; lean_object* v_missingChoiceResolutions_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2726_; 
v_val_2709_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_val_2709_);
lean_dec_ref_known(v___x_2705_, 1);
v_toBacktrackableState_2710_ = lean_ctor_get(v_a_2703_, 0);
v_shareCommonState_2711_ = lean_ctor_get(v_a_2703_, 1);
v_freshTagId_2712_ = lean_ctor_get(v_a_2703_, 2);
v_missingFormatters_2713_ = lean_ctor_get(v_a_2703_, 3);
v_partialFormatters_2714_ = lean_ctor_get(v_a_2703_, 4);
v_missingChoiceResolutions_2715_ = lean_ctor_get(v_a_2703_, 5);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_a_2703_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2717_ = v_a_2703_;
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_missingChoiceResolutions_2715_);
lean_inc(v_partialFormatters_2714_);
lean_inc(v_missingFormatters_2713_);
lean_inc(v_freshTagId_2712_);
lean_inc(v_shareCommonState_2711_);
lean_inc(v_toBacktrackableState_2710_);
lean_dec(v_a_2703_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2726_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2719_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingFormatters_2713_, v_val_2709_, v_kind_2691_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 3, v___x_2719_);
v___x_2721_ = v___x_2717_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_toBacktrackableState_2710_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_shareCommonState_2711_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_freshTagId_2712_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_partialFormatters_2714_);
lean_ctor_set(v_reuseFailAlloc_2725_, 5, v_missingChoiceResolutions_2715_);
v___x_2721_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2723_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v___x_2721_);
v___x_2723_ = v___x_2707_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2702_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
else
{
lean_dec(v___x_2705_);
lean_dec(v_a_2703_);
lean_dec(v_kind_2691_);
return v___x_2701_;
}
}
else
{
lean_dec(v_kind_2691_);
lean_dec_ref_known(v_stx_2686_, 3);
return v___x_2701_;
}
}
}
case 2:
{
lean_object* v_val_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_val_2730_ = lean_ctor_get(v_stx_2686_, 1);
lean_inc_ref(v_val_2730_);
v___x_2731_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(v_val_2730_);
v___x_2732_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_2731_, v_stx_2686_, v_a_2688_);
lean_dec_ref_known(v_stx_2686_, 2);
return v___x_2732_;
}
default: 
{
lean_object* v_rawVal_2733_; lean_object* v_str_2734_; lean_object* v_startPos_2735_; lean_object* v_stopPos_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_rawVal_2733_ = lean_ctor_get(v_stx_2686_, 1);
v_str_2734_ = lean_ctor_get(v_rawVal_2733_, 0);
v_startPos_2735_ = lean_ctor_get(v_rawVal_2733_, 1);
v_stopPos_2736_ = lean_ctor_get(v_rawVal_2733_, 2);
v___x_2737_ = lean_string_utf8_extract(v_str_2734_, v_startPos_2735_, v_stopPos_2736_);
v___x_2738_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(v___x_2737_);
v___x_2739_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_2738_, v_stx_2686_, v_a_2688_);
lean_dec_ref_known(v_stx_2686_, 4);
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object* v_stx_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Fmt_fmt(v_stx_2740_, v_a_2741_, v_a_2742_);
lean_dec_ref(v_a_2741_);
return v_res_2743_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(lean_object* v_x_2744_){
_start:
{
lean_object* v_aPtr_2745_; lean_object* v_bPtr_2746_; size_t v_ptr_2747_; size_t v_ptr_2748_; uint64_t v___x_2749_; uint64_t v___x_2750_; uint64_t v___x_2751_; uint64_t v___x_2752_; uint64_t v___x_2753_; 
v_aPtr_2745_ = lean_ctor_get(v_x_2744_, 0);
v_bPtr_2746_ = lean_ctor_get(v_x_2744_, 1);
v_ptr_2747_ = lean_ctor_get_usize(v_aPtr_2745_, 1);
v_ptr_2748_ = lean_ctor_get_usize(v_bPtr_2746_, 1);
v___x_2749_ = 0ULL;
v___x_2750_ = lean_usize_to_uint64(v_ptr_2747_);
v___x_2751_ = lean_uint64_mix_hash(v___x_2749_, v___x_2750_);
v___x_2752_ = lean_usize_to_uint64(v_ptr_2748_);
v___x_2753_ = lean_uint64_mix_hash(v___x_2751_, v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8___boxed(lean_object* v_x_2754_){
_start:
{
uint64_t v_res_2755_; lean_object* v_r_2756_; 
v_res_2755_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_x_2754_);
lean_dec_ref(v_x_2754_);
v_r_2756_ = lean_box_uint64(v_res_2755_);
return v_r_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16___redArg(lean_object* v_x_2757_, lean_object* v_x_2758_){
_start:
{
if (lean_obj_tag(v_x_2758_) == 0)
{
return v_x_2757_;
}
else
{
lean_object* v_key_2759_; lean_object* v_value_2760_; lean_object* v_tail_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2784_; 
v_key_2759_ = lean_ctor_get(v_x_2758_, 0);
v_value_2760_ = lean_ctor_get(v_x_2758_, 1);
v_tail_2761_ = lean_ctor_get(v_x_2758_, 2);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_x_2758_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2763_ = v_x_2758_;
v_isShared_2764_ = v_isSharedCheck_2784_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_tail_2761_);
lean_inc(v_value_2760_);
lean_inc(v_key_2759_);
lean_dec(v_x_2758_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2784_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; uint64_t v___x_2766_; uint64_t v___x_2767_; uint64_t v___x_2768_; uint64_t v_fold_2769_; uint64_t v___x_2770_; uint64_t v___x_2771_; uint64_t v___x_2772_; size_t v___x_2773_; size_t v___x_2774_; size_t v___x_2775_; size_t v___x_2776_; size_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2765_ = lean_array_get_size(v_x_2757_);
v___x_2766_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_key_2759_);
v___x_2767_ = 32ULL;
v___x_2768_ = lean_uint64_shift_right(v___x_2766_, v___x_2767_);
v_fold_2769_ = lean_uint64_xor(v___x_2766_, v___x_2768_);
v___x_2770_ = 16ULL;
v___x_2771_ = lean_uint64_shift_right(v_fold_2769_, v___x_2770_);
v___x_2772_ = lean_uint64_xor(v_fold_2769_, v___x_2771_);
v___x_2773_ = lean_uint64_to_usize(v___x_2772_);
v___x_2774_ = lean_usize_of_nat(v___x_2765_);
v___x_2775_ = ((size_t)1ULL);
v___x_2776_ = lean_usize_sub(v___x_2774_, v___x_2775_);
v___x_2777_ = lean_usize_land(v___x_2773_, v___x_2776_);
v___x_2778_ = lean_array_uget_borrowed(v_x_2757_, v___x_2777_);
lean_inc(v___x_2778_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 2, v___x_2778_);
v___x_2780_ = v___x_2763_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_key_2759_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_value_2760_);
lean_ctor_set(v_reuseFailAlloc_2783_, 2, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_array_uset(v_x_2757_, v___x_2777_, v___x_2780_);
v_x_2757_ = v___x_2781_;
v_x_2758_ = v_tail_2761_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15___redArg(lean_object* v_i_2785_, lean_object* v_source_2786_, lean_object* v_target_2787_){
_start:
{
lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2788_ = lean_array_get_size(v_source_2786_);
v___x_2789_ = lean_nat_dec_lt(v_i_2785_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_dec_ref(v_source_2786_);
lean_dec(v_i_2785_);
return v_target_2787_;
}
else
{
lean_object* v_es_2790_; lean_object* v___x_2791_; lean_object* v_source_2792_; lean_object* v_target_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_es_2790_ = lean_array_fget(v_source_2786_, v_i_2785_);
v___x_2791_ = lean_box(0);
v_source_2792_ = lean_array_fset(v_source_2786_, v_i_2785_, v___x_2791_);
v_target_2793_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16___redArg(v_target_2787_, v_es_2790_);
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_nat_add(v_i_2785_, v___x_2794_);
lean_dec(v_i_2785_);
v_i_2785_ = v___x_2795_;
v_source_2786_ = v_source_2792_;
v_target_2787_ = v_target_2793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13___redArg(lean_object* v_data_2797_){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v_nbuckets_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2798_ = lean_array_get_size(v_data_2797_);
v___x_2799_ = lean_unsigned_to_nat(2u);
v_nbuckets_2800_ = lean_nat_mul(v___x_2798_, v___x_2799_);
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_mk_array(v_nbuckets_2800_, v___x_2802_);
v___x_2804_ = lean_array_propagate_mark(v_data_2797_, v___x_2803_);
v___x_2805_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15___redArg(v___x_2801_, v_data_2797_, v___x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(lean_object* v_x_2806_, lean_object* v_x_2807_){
_start:
{
lean_object* v_aPtr_2808_; lean_object* v_aPtr_2809_; lean_object* v_bPtr_2810_; lean_object* v_bPtr_2811_; size_t v_ptr_2812_; size_t v_ptr_2813_; uint8_t v___x_2814_; 
v_aPtr_2808_ = lean_ctor_get(v_x_2806_, 0);
v_aPtr_2809_ = lean_ctor_get(v_x_2807_, 0);
v_bPtr_2810_ = lean_ctor_get(v_x_2806_, 1);
v_bPtr_2811_ = lean_ctor_get(v_x_2807_, 1);
v_ptr_2812_ = lean_ctor_get_usize(v_aPtr_2808_, 1);
v_ptr_2813_ = lean_ctor_get_usize(v_aPtr_2809_, 1);
v___x_2814_ = lean_usize_dec_eq(v_ptr_2812_, v_ptr_2813_);
if (v___x_2814_ == 0)
{
return v___x_2814_;
}
else
{
size_t v_ptr_2815_; size_t v_ptr_2816_; uint8_t v___x_2817_; 
v_ptr_2815_ = lean_ctor_get_usize(v_bPtr_2810_, 1);
v_ptr_2816_ = lean_ctor_get_usize(v_bPtr_2811_, 1);
v___x_2817_ = lean_usize_dec_eq(v_ptr_2815_, v_ptr_2816_);
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10___boxed(lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
uint8_t v_res_2820_; lean_object* v_r_2821_; 
v_res_2820_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_x_2818_, v_x_2819_);
lean_dec_ref(v_x_2819_);
lean_dec_ref(v_x_2818_);
v_r_2821_ = lean_box(v_res_2820_);
return v_r_2821_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_a_2822_, lean_object* v_x_2823_){
_start:
{
if (lean_obj_tag(v_x_2823_) == 0)
{
uint8_t v___x_2824_; 
v___x_2824_ = 0;
return v___x_2824_;
}
else
{
lean_object* v_key_2825_; lean_object* v_tail_2826_; uint8_t v___x_2827_; 
v_key_2825_ = lean_ctor_get(v_x_2823_, 0);
v_tail_2826_ = lean_ctor_get(v_x_2823_, 2);
v___x_2827_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_key_2825_, v_a_2822_);
if (v___x_2827_ == 0)
{
v_x_2823_ = v_tail_2826_;
goto _start;
}
else
{
return v___x_2827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg___boxed(lean_object* v_a_2829_, lean_object* v_x_2830_){
_start:
{
uint8_t v_res_2831_; lean_object* v_r_2832_; 
v_res_2831_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(v_a_2829_, v_x_2830_);
lean_dec(v_x_2830_);
lean_dec_ref(v_a_2829_);
v_r_2832_ = lean_box(v_res_2831_);
return v_r_2832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(lean_object* v_a_2833_, lean_object* v_b_2834_, lean_object* v_x_2835_){
_start:
{
if (lean_obj_tag(v_x_2835_) == 0)
{
lean_dec(v_b_2834_);
lean_dec_ref(v_a_2833_);
return v_x_2835_;
}
else
{
lean_object* v_key_2836_; lean_object* v_value_2837_; lean_object* v_tail_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2850_; 
v_key_2836_ = lean_ctor_get(v_x_2835_, 0);
v_value_2837_ = lean_ctor_get(v_x_2835_, 1);
v_tail_2838_ = lean_ctor_get(v_x_2835_, 2);
v_isSharedCheck_2850_ = !lean_is_exclusive(v_x_2835_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2840_ = v_x_2835_;
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_tail_2838_);
lean_inc(v_value_2837_);
lean_inc(v_key_2836_);
lean_dec(v_x_2835_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2850_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
uint8_t v___x_2842_; 
v___x_2842_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_key_2836_, v_a_2833_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(v_a_2833_, v_b_2834_, v_tail_2838_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 2, v___x_2843_);
v___x_2845_ = v___x_2840_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_key_2836_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_value_2837_);
lean_ctor_set(v_reuseFailAlloc_2846_, 2, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
else
{
lean_object* v___x_2848_; 
lean_dec(v_value_2837_);
lean_dec(v_key_2836_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v_b_2834_);
lean_ctor_set(v___x_2840_, 0, v_a_2833_);
v___x_2848_ = v___x_2840_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2833_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_b_2834_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_tail_2838_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2851_, lean_object* v_a_2852_, lean_object* v_b_2853_){
_start:
{
lean_object* v_size_2854_; lean_object* v_buckets_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2898_; 
v_size_2854_ = lean_ctor_get(v_m_2851_, 0);
v_buckets_2855_ = lean_ctor_get(v_m_2851_, 1);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_m_2851_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2857_ = v_m_2851_;
v_isShared_2858_ = v_isSharedCheck_2898_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_buckets_2855_);
lean_inc(v_size_2854_);
lean_dec(v_m_2851_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2898_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; uint64_t v___x_2860_; uint64_t v___x_2861_; uint64_t v___x_2862_; uint64_t v_fold_2863_; uint64_t v___x_2864_; uint64_t v___x_2865_; uint64_t v___x_2866_; size_t v___x_2867_; size_t v___x_2868_; size_t v___x_2869_; size_t v___x_2870_; size_t v___x_2871_; lean_object* v_bkt_2872_; uint8_t v___x_2873_; 
v___x_2859_ = lean_array_get_size(v_buckets_2855_);
v___x_2860_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_a_2852_);
v___x_2861_ = 32ULL;
v___x_2862_ = lean_uint64_shift_right(v___x_2860_, v___x_2861_);
v_fold_2863_ = lean_uint64_xor(v___x_2860_, v___x_2862_);
v___x_2864_ = 16ULL;
v___x_2865_ = lean_uint64_shift_right(v_fold_2863_, v___x_2864_);
v___x_2866_ = lean_uint64_xor(v_fold_2863_, v___x_2865_);
v___x_2867_ = lean_uint64_to_usize(v___x_2866_);
v___x_2868_ = lean_usize_of_nat(v___x_2859_);
v___x_2869_ = ((size_t)1ULL);
v___x_2870_ = lean_usize_sub(v___x_2868_, v___x_2869_);
v___x_2871_ = lean_usize_land(v___x_2867_, v___x_2870_);
v_bkt_2872_ = lean_array_uget_borrowed(v_buckets_2855_, v___x_2871_);
v___x_2873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(v_a_2852_, v_bkt_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v_size_x27_2875_; lean_object* v___x_2876_; lean_object* v_buckets_x27_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2874_ = lean_unsigned_to_nat(1u);
v_size_x27_2875_ = lean_nat_add(v_size_2854_, v___x_2874_);
lean_dec(v_size_2854_);
lean_inc(v_bkt_2872_);
v___x_2876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2876_, 0, v_a_2852_);
lean_ctor_set(v___x_2876_, 1, v_b_2853_);
lean_ctor_set(v___x_2876_, 2, v_bkt_2872_);
v_buckets_x27_2877_ = lean_array_uset(v_buckets_2855_, v___x_2871_, v___x_2876_);
v___x_2878_ = lean_unsigned_to_nat(4u);
v___x_2879_ = lean_nat_mul(v_size_x27_2875_, v___x_2878_);
v___x_2880_ = lean_unsigned_to_nat(3u);
v___x_2881_ = lean_nat_div(v___x_2879_, v___x_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_array_get_size(v_buckets_x27_2877_);
v___x_2883_ = lean_nat_dec_le(v___x_2881_, v___x_2882_);
lean_dec(v___x_2881_);
if (v___x_2883_ == 0)
{
lean_object* v_val_2884_; lean_object* v___x_2886_; 
v_val_2884_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13___redArg(v_buckets_x27_2877_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v_val_2884_);
lean_ctor_set(v___x_2857_, 0, v_size_x27_2875_);
v___x_2886_ = v___x_2857_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_size_x27_2875_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_val_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
else
{
lean_object* v___x_2889_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v_buckets_x27_2877_);
lean_ctor_set(v___x_2857_, 0, v_size_x27_2875_);
v___x_2889_ = v___x_2857_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_size_x27_2875_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_buckets_x27_2877_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
else
{
lean_object* v___x_2891_; lean_object* v_buckets_x27_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_inc(v_bkt_2872_);
v___x_2891_ = lean_box(0);
v_buckets_x27_2892_ = lean_array_uset(v_buckets_2855_, v___x_2871_, v___x_2891_);
v___x_2893_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(v_a_2852_, v_b_2853_, v_bkt_2872_);
v___x_2894_ = lean_array_uset(v_buckets_x27_2892_, v___x_2871_, v___x_2893_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v___x_2894_);
v___x_2896_ = v___x_2857_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_size_2854_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(lean_object* v_a_2899_, lean_object* v_x_2900_){
_start:
{
if (lean_obj_tag(v_x_2900_) == 0)
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_box(0);
return v___x_2901_;
}
else
{
lean_object* v_key_2902_; lean_object* v_value_2903_; lean_object* v_tail_2904_; uint8_t v___x_2905_; 
v_key_2902_ = lean_ctor_get(v_x_2900_, 0);
v_value_2903_ = lean_ctor_get(v_x_2900_, 1);
v_tail_2904_ = lean_ctor_get(v_x_2900_, 2);
v___x_2905_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_key_2902_, v_a_2899_);
if (v___x_2905_ == 0)
{
v_x_2900_ = v_tail_2904_;
goto _start;
}
else
{
lean_object* v___x_2907_; 
lean_inc(v_value_2903_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_value_2903_);
return v___x_2907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg___boxed(lean_object* v_a_2908_, lean_object* v_x_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(v_a_2908_, v_x_2909_);
lean_dec(v_x_2909_);
lean_dec_ref(v_a_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(lean_object* v_m_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_buckets_2913_; lean_object* v___x_2914_; uint64_t v___x_2915_; uint64_t v___x_2916_; uint64_t v___x_2917_; uint64_t v_fold_2918_; uint64_t v___x_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_buckets_2913_ = lean_ctor_get(v_m_2911_, 1);
v___x_2914_ = lean_array_get_size(v_buckets_2913_);
v___x_2915_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_a_2912_);
v___x_2916_ = 32ULL;
v___x_2917_ = lean_uint64_shift_right(v___x_2915_, v___x_2916_);
v_fold_2918_ = lean_uint64_xor(v___x_2915_, v___x_2917_);
v___x_2919_ = 16ULL;
v___x_2920_ = lean_uint64_shift_right(v_fold_2918_, v___x_2919_);
v___x_2921_ = lean_uint64_xor(v_fold_2918_, v___x_2920_);
v___x_2922_ = lean_uint64_to_usize(v___x_2921_);
v___x_2923_ = lean_usize_of_nat(v___x_2914_);
v___x_2924_ = ((size_t)1ULL);
v___x_2925_ = lean_usize_sub(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_usize_land(v___x_2922_, v___x_2925_);
v___x_2927_ = lean_array_uget_borrowed(v_buckets_2913_, v___x_2926_);
v___x_2928_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(v_a_2912_, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(v_m_2929_, v_a_2930_);
lean_dec_ref(v_a_2930_);
lean_dec_ref(v_m_2929_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object* v_a_2932_, lean_object* v_b_2933_, lean_object* v_a_2934_){
_start:
{
lean_object* v___y_2936_; lean_object* v_da1_2941_; lean_object* v_da2_2942_; lean_object* v_db1_2943_; lean_object* v_db2_2944_; lean_object* v___y_2945_; lean_object* v_sa_2952_; lean_object* v_sb_2953_; lean_object* v___y_2954_; 
switch(lean_obj_tag(v_a_2932_))
{
case 0:
{
if (lean_obj_tag(v_b_2933_) == 0)
{
uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = 1;
v___x_2963_ = lean_box(v___x_2962_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v_a_2934_);
return v___x_2964_;
}
else
{
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 1:
{
if (lean_obj_tag(v_b_2933_) == 1)
{
lean_object* v_f_2965_; lean_object* v_f_2966_; 
v_f_2965_ = lean_ctor_get(v_a_2932_, 1);
lean_inc_ref(v_f_2965_);
lean_dec_ref_known(v_a_2932_, 2);
v_f_2966_ = lean_ctor_get(v_b_2933_, 1);
lean_inc_ref(v_f_2966_);
lean_dec_ref_known(v_b_2933_, 2);
v_sa_2952_ = v_f_2965_;
v_sb_2953_ = v_f_2966_;
v___y_2954_ = v_a_2934_;
goto v___jp_2951_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 2:
{
if (lean_obj_tag(v_b_2933_) == 2)
{
lean_object* v_s_2967_; lean_object* v_s_2968_; 
v_s_2967_ = lean_ctor_get(v_a_2932_, 1);
lean_inc_ref(v_s_2967_);
lean_dec_ref_known(v_a_2932_, 2);
v_s_2968_ = lean_ctor_get(v_b_2933_, 1);
lean_inc_ref(v_s_2968_);
lean_dec_ref_known(v_b_2933_, 2);
v_sa_2952_ = v_s_2967_;
v_sb_2953_ = v_s_2968_;
v___y_2954_ = v_a_2934_;
goto v___jp_2951_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 3:
{
if (lean_obj_tag(v_b_2933_) == 3)
{
lean_object* v_id_2969_; lean_object* v_d_2970_; lean_object* v_id_2971_; lean_object* v_d_2972_; uint8_t v___x_2973_; 
v_id_2969_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_id_2969_);
v_d_2970_ = lean_ctor_get(v_a_2932_, 2);
lean_inc(v_d_2970_);
lean_dec_ref_known(v_a_2932_, 3);
v_id_2971_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_id_2971_);
v_d_2972_ = lean_ctor_get(v_b_2933_, 2);
lean_inc(v_d_2972_);
lean_dec_ref_known(v_b_2933_, 3);
v___x_2973_ = lean_nat_dec_eq(v_id_2969_, v_id_2971_);
lean_dec(v_id_2971_);
lean_dec(v_id_2969_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v_d_2972_);
lean_dec(v_d_2970_);
v___x_2974_ = lean_box(v___x_2973_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v_a_2934_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; 
v___x_2976_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2970_, v_d_2972_, v_a_2934_);
return v___x_2976_;
}
}
else
{
lean_dec_ref_known(v_a_2932_, 3);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 4:
{
if (lean_obj_tag(v_b_2933_) == 4)
{
lean_object* v_d_2977_; lean_object* v_d_2978_; lean_object* v___x_2979_; 
v_d_2977_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_2977_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_2978_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_2978_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_2979_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2977_, v_d_2978_, v_a_2934_);
return v___x_2979_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 5:
{
if (lean_obj_tag(v_b_2933_) == 5)
{
lean_object* v_d_2980_; lean_object* v_d_2981_; lean_object* v___x_2982_; 
v_d_2980_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_2980_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_2981_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_2981_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_2982_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2980_, v_d_2981_, v_a_2934_);
return v___x_2982_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 6:
{
if (lean_obj_tag(v_b_2933_) == 6)
{
lean_object* v_n_2983_; uint8_t v_isCumulative_2984_; lean_object* v_d_2985_; lean_object* v_n_2986_; uint8_t v_isCumulative_2987_; lean_object* v_d_2988_; uint8_t v___x_2989_; 
v_n_2983_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_n_2983_);
v_isCumulative_2984_ = lean_ctor_get_uint8(v_a_2932_, sizeof(void*)*3 + 8);
v_d_2985_ = lean_ctor_get(v_a_2932_, 2);
lean_inc(v_d_2985_);
lean_dec_ref_known(v_a_2932_, 3);
v_n_2986_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_n_2986_);
v_isCumulative_2987_ = lean_ctor_get_uint8(v_b_2933_, sizeof(void*)*3 + 8);
v_d_2988_ = lean_ctor_get(v_b_2933_, 2);
lean_inc(v_d_2988_);
lean_dec_ref_known(v_b_2933_, 3);
v___x_2989_ = lean_nat_dec_eq(v_n_2983_, v_n_2986_);
lean_dec(v_n_2986_);
lean_dec(v_n_2983_);
if (v___x_2989_ == 0)
{
lean_dec(v_d_2988_);
lean_dec(v_d_2985_);
goto v___jp_2958_;
}
else
{
if (v_isCumulative_2987_ == 0)
{
if (v_isCumulative_2984_ == 0)
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2985_, v_d_2988_, v_a_2934_);
return v___x_2990_;
}
else
{
lean_dec(v_d_2988_);
lean_dec(v_d_2985_);
goto v___jp_2958_;
}
}
else
{
if (v_isCumulative_2984_ == 0)
{
lean_dec(v_d_2988_);
lean_dec(v_d_2985_);
goto v___jp_2958_;
}
else
{
lean_object* v___x_2991_; 
v___x_2991_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2985_, v_d_2988_, v_a_2934_);
return v___x_2991_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2932_, 3);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 7:
{
if (lean_obj_tag(v_b_2933_) == 7)
{
lean_object* v_d_2992_; lean_object* v_d_2993_; lean_object* v___x_2994_; 
v_d_2992_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_2992_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_2993_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_2993_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_2994_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2992_, v_d_2993_, v_a_2934_);
return v___x_2994_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 8:
{
if (lean_obj_tag(v_b_2933_) == 8)
{
uint8_t v_onlyNonCumulative_2995_; 
v_onlyNonCumulative_2995_ = lean_ctor_get_uint8(v_b_2933_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_2995_ == 0)
{
uint8_t v_onlyNonCumulative_2996_; 
v_onlyNonCumulative_2996_ = lean_ctor_get_uint8(v_a_2932_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_2996_ == 0)
{
lean_object* v_d_2997_; lean_object* v_d_2998_; lean_object* v___x_2999_; 
v_d_2997_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_2997_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_2998_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_2998_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_2999_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2997_, v_d_2998_, v_a_2934_);
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec_ref_known(v_b_2933_, 2);
lean_dec_ref_known(v_a_2932_, 2);
v___x_3000_ = lean_box(v_onlyNonCumulative_2995_);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v_a_2934_);
return v___x_3001_;
}
}
else
{
uint8_t v_onlyNonCumulative_3002_; 
v_onlyNonCumulative_3002_ = lean_ctor_get_uint8(v_a_2932_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec_ref_known(v_b_2933_, 2);
lean_dec_ref_known(v_a_2932_, 2);
v___x_3003_ = lean_box(v_onlyNonCumulative_3002_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set(v___x_3004_, 1, v_a_2934_);
return v___x_3004_;
}
else
{
lean_object* v_d_3005_; lean_object* v_d_3006_; lean_object* v___x_3007_; 
v_d_3005_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_3005_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_3006_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_3006_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_3007_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3005_, v_d_3006_, v_a_2934_);
return v___x_3007_;
}
}
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 9:
{
if (lean_obj_tag(v_b_2933_) == 9)
{
lean_object* v_d_3008_; lean_object* v_d_3009_; lean_object* v___x_3010_; 
v_d_3008_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_3008_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_3009_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_3009_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_3010_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3008_, v_d_3009_, v_a_2934_);
return v___x_3010_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 10:
{
if (lean_obj_tag(v_b_2933_) == 10)
{
lean_object* v_d_3011_; lean_object* v_d_3012_; lean_object* v___x_3013_; 
v_d_3011_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_3011_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_3012_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_3012_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_3013_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3011_, v_d_3012_, v_a_2934_);
return v___x_3013_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 11:
{
if (lean_obj_tag(v_b_2933_) == 11)
{
lean_object* v_d_3014_; lean_object* v_d_3015_; lean_object* v___x_3016_; 
v_d_3014_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_d_3014_);
lean_dec_ref_known(v_a_2932_, 2);
v_d_3015_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_d_3015_);
lean_dec_ref_known(v_b_2933_, 2);
v___x_3016_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3014_, v_d_3015_, v_a_2934_);
return v___x_3016_;
}
else
{
lean_dec_ref_known(v_a_2932_, 2);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 12:
{
if (lean_obj_tag(v_b_2933_) == 12)
{
lean_object* v_p_3017_; lean_object* v_p_3018_; lean_object* v_d_3019_; lean_object* v_d_3020_; lean_object* v_id_3021_; lean_object* v_id_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3032_; 
v_p_3017_ = lean_ctor_get(v_a_2932_, 1);
lean_inc_ref(v_p_3017_);
v_p_3018_ = lean_ctor_get(v_b_2933_, 1);
lean_inc_ref(v_p_3018_);
v_d_3019_ = lean_ctor_get(v_a_2932_, 2);
lean_inc(v_d_3019_);
lean_dec_ref_known(v_a_2932_, 3);
v_d_3020_ = lean_ctor_get(v_b_2933_, 2);
lean_inc(v_d_3020_);
lean_dec_ref_known(v_b_2933_, 3);
v_id_3021_ = lean_ctor_get(v_p_3017_, 1);
lean_inc(v_id_3021_);
lean_dec_ref(v_p_3017_);
v_id_3022_ = lean_ctor_get(v_p_3018_, 1);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_p_3018_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v_p_3018_, 0);
lean_dec(v_unused_3033_);
v___x_3024_ = v_p_3018_;
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_id_3022_);
lean_dec(v_p_3018_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3032_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_name_eq(v_id_3021_, v_id_3022_);
lean_dec(v_id_3022_);
lean_dec(v_id_3021_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
lean_dec(v_d_3020_);
lean_dec(v_d_3019_);
v___x_3027_ = lean_box(v___x_3026_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v_a_2934_);
lean_ctor_set(v___x_3024_, 0, v___x_3027_);
v___x_3029_ = v___x_3024_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_a_2934_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
else
{
lean_object* v___x_3031_; 
lean_del_object(v___x_3024_);
v___x_3031_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3019_, v_d_3020_, v_a_2934_);
return v___x_3031_;
}
}
}
else
{
lean_dec_ref_known(v_a_2932_, 3);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 13:
{
if (lean_obj_tag(v_b_2933_) == 13)
{
lean_object* v_cost_3034_; lean_object* v_d_3035_; lean_object* v_cost_3036_; lean_object* v_d_3037_; uint8_t v___x_3038_; 
v_cost_3034_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_cost_3034_);
v_d_3035_ = lean_ctor_get(v_a_2932_, 2);
lean_inc(v_d_3035_);
lean_dec_ref_known(v_a_2932_, 3);
v_cost_3036_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_cost_3036_);
v_d_3037_ = lean_ctor_get(v_b_2933_, 2);
lean_inc(v_d_3037_);
lean_dec_ref_known(v_b_2933_, 3);
v___x_3038_ = l_Lean_Fmt_instBEqDefaultCost_beq___redArg(v_cost_3034_, v_cost_3036_);
lean_dec(v_cost_3036_);
lean_dec(v_cost_3034_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec(v_d_3037_);
lean_dec(v_d_3035_);
v___x_3039_ = lean_box(v___x_3038_);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v_a_2934_);
return v___x_3040_;
}
else
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3035_, v_d_3037_, v_a_2934_);
return v___x_3041_;
}
}
else
{
lean_dec_ref_known(v_a_2932_, 3);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
case 14:
{
if (lean_obj_tag(v_b_2933_) == 14)
{
lean_object* v_a_3042_; lean_object* v_b_3043_; lean_object* v_a_3044_; lean_object* v_b_3045_; 
v_a_3042_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_a_3042_);
v_b_3043_ = lean_ctor_get(v_a_2932_, 2);
lean_inc(v_b_3043_);
lean_dec_ref_known(v_a_2932_, 3);
v_a_3044_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_a_3044_);
v_b_3045_ = lean_ctor_get(v_b_2933_, 2);
lean_inc(v_b_3045_);
lean_dec_ref_known(v_b_2933_, 3);
v_da1_2941_ = v_a_3042_;
v_da2_2942_ = v_b_3043_;
v_db1_2943_ = v_a_3044_;
v_db2_2944_ = v_b_3045_;
v___y_2945_ = v_a_2934_;
goto v___jp_2940_;
}
else
{
lean_dec_ref_known(v_a_2932_, 3);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
default: 
{
if (lean_obj_tag(v_b_2933_) == 15)
{
lean_object* v_a_3046_; lean_object* v_b_3047_; lean_object* v_a_3048_; lean_object* v_b_3049_; 
v_a_3046_ = lean_ctor_get(v_a_2932_, 1);
lean_inc(v_a_3046_);
v_b_3047_ = lean_ctor_get(v_a_2932_, 2);
lean_inc(v_b_3047_);
lean_dec_ref_known(v_a_2932_, 3);
v_a_3048_ = lean_ctor_get(v_b_2933_, 1);
lean_inc(v_a_3048_);
v_b_3049_ = lean_ctor_get(v_b_2933_, 2);
lean_inc(v_b_3049_);
lean_dec_ref_known(v_b_2933_, 3);
v_da1_2941_ = v_a_3046_;
v_da2_2942_ = v_b_3047_;
v_db1_2943_ = v_a_3048_;
v_db2_2944_ = v_b_3049_;
v___y_2945_ = v_a_2934_;
goto v___jp_2940_;
}
else
{
lean_dec_ref_known(v_a_2932_, 3);
lean_dec(v_b_2933_);
v___y_2936_ = v_a_2934_;
goto v___jp_2935_;
}
}
}
v___jp_2935_:
{
uint8_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = 0;
v___x_2938_ = lean_box(v___x_2937_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v___y_2936_);
return v___x_2939_;
}
v___jp_2940_:
{
lean_object* v___x_2946_; lean_object* v_fst_2947_; uint8_t v___x_2948_; 
v___x_2946_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da1_2941_, v_db1_2943_, v___y_2945_);
v_fst_2947_ = lean_ctor_get(v___x_2946_, 0);
v___x_2948_ = lean_unbox(v_fst_2947_);
if (v___x_2948_ == 0)
{
lean_dec(v_db2_2944_);
lean_dec(v_da2_2942_);
return v___x_2946_;
}
else
{
lean_object* v_snd_2949_; lean_object* v___x_2950_; 
v_snd_2949_ = lean_ctor_get(v___x_2946_, 1);
lean_inc(v_snd_2949_);
lean_dec_ref(v___x_2946_);
v___x_2950_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da2_2942_, v_db2_2944_, v_snd_2949_);
return v___x_2950_;
}
}
v___jp_2951_:
{
uint8_t v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = lean_string_dec_eq(v_sa_2952_, v_sb_2953_);
lean_dec_ref(v_sb_2953_);
lean_dec_ref(v_sa_2952_);
v___x_2956_ = lean_box(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
lean_ctor_set(v___x_2957_, 1, v___y_2954_);
return v___x_2957_;
}
v___jp_2958_:
{
uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = 0;
v___x_2960_ = lean_box(v___x_2959_);
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v_a_2934_);
return v___x_2961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object* v_a_3050_, lean_object* v_b_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v_cacheKey_3055_; lean_object* v___x_3056_; 
lean_inc(v_a_3050_);
v___x_3053_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3050_);
lean_inc(v_b_3051_);
v___x_3054_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3051_);
v_cacheKey_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3055_, 0, v___x_3053_);
lean_ctor_set(v_cacheKey_3055_, 1, v___x_3054_);
v___x_3056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(v_a_3052_, v_cacheKey_3055_);
if (lean_obj_tag(v___x_3056_) == 1)
{
lean_object* v_val_3057_; lean_object* v___x_3058_; 
lean_dec_ref_known(v_cacheKey_3055_, 2);
lean_dec(v_b_3051_);
lean_dec(v_a_3050_);
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_val_3057_);
lean_ctor_set(v___x_3058_, 1, v_a_3052_);
return v___x_3058_;
}
else
{
lean_object* v___x_3059_; lean_object* v_fst_3060_; lean_object* v_snd_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v___x_3056_);
v___x_3059_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(v_a_3050_, v_b_3051_, v_a_3052_);
v_fst_3060_ = lean_ctor_get(v___x_3059_, 0);
v_snd_3061_ = lean_ctor_get(v___x_3059_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3063_ = v___x_3059_;
v_isShared_3064_ = v_isSharedCheck_3069_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_snd_3061_);
lean_inc(v_fst_3060_);
lean_dec(v___x_3059_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3069_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3067_; 
lean_inc(v_fst_3060_);
v___x_3065_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3___redArg(v_snd_3061_, v_cacheKey_3055_, v_fst_3060_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 1, v___x_3065_);
v___x_3067_ = v___x_3063_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_fst_3060_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_unsigned_to_nat(16u);
v___x_3072_ = lean_mk_array(v___x_3071_, v___x_3070_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0);
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
return v___x_3075_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object* v_a_3076_, lean_object* v_b_3077_){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v_fst_3080_; uint8_t v___x_3081_; 
v___x_3078_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1);
v___x_3079_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_a_3076_, v_b_3077_, v___x_3078_);
v_fst_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_fst_3080_);
lean_dec_ref(v___x_3079_);
v___x_3081_ = lean_unbox(v_fst_3080_);
lean_dec(v_fst_3080_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object* v_a_3082_, lean_object* v_b_3083_){
_start:
{
uint8_t v_res_3084_; lean_object* v_r_3085_; 
v_res_3084_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_a_3082_, v_b_3083_);
v_r_3085_ = lean_box(v_res_3084_);
return v_r_3085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__3(lean_object* v_x_3086_, lean_object* v_x_3087_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 0)
{
return v_x_3086_;
}
else
{
lean_object* v_key_3088_; lean_object* v_value_3089_; lean_object* v_tail_3090_; lean_object* v___x_3091_; 
v_key_3088_ = lean_ctor_get(v_x_3087_, 0);
lean_inc(v_key_3088_);
v_value_3089_ = lean_ctor_get(v_x_3087_, 1);
lean_inc(v_value_3089_);
v_tail_3090_ = lean_ctor_get(v_x_3087_, 2);
lean_inc(v_tail_3090_);
lean_dec_ref_known(v_x_3087_, 3);
v___x_3091_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_x_3086_, v_key_3088_, v_value_3089_);
v_x_3086_ = v___x_3091_;
v_x_3087_ = v_tail_3090_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4(lean_object* v_as_3093_, size_t v_i_3094_, size_t v_stop_3095_, lean_object* v_b_3096_){
_start:
{
uint8_t v___x_3097_; 
v___x_3097_ = lean_usize_dec_eq(v_i_3094_, v_stop_3095_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; size_t v___x_3100_; size_t v___x_3101_; 
v___x_3098_ = lean_array_uget_borrowed(v_as_3093_, v_i_3094_);
lean_inc(v___x_3098_);
v___x_3099_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__3(v_b_3096_, v___x_3098_);
v___x_3100_ = ((size_t)1ULL);
v___x_3101_ = lean_usize_add(v_i_3094_, v___x_3100_);
v_i_3094_ = v___x_3101_;
v_b_3096_ = v___x_3099_;
goto _start;
}
else
{
return v_b_3096_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4___boxed(lean_object* v_as_3103_, lean_object* v_i_3104_, lean_object* v_stop_3105_, lean_object* v_b_3106_){
_start:
{
size_t v_i_boxed_3107_; size_t v_stop_boxed_3108_; lean_object* v_res_3109_; 
v_i_boxed_3107_ = lean_unbox_usize(v_i_3104_);
lean_dec(v_i_3104_);
v_stop_boxed_3108_ = lean_unbox_usize(v_stop_3105_);
lean_dec(v_stop_3105_);
v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4(v_as_3103_, v_i_boxed_3107_, v_stop_boxed_3108_, v_b_3106_);
lean_dec_ref(v_as_3103_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object* v_x_3110_, lean_object* v_x_3111_){
_start:
{
if (lean_obj_tag(v_x_3111_) == 0)
{
return v_x_3110_;
}
else
{
lean_object* v_key_3112_; lean_object* v_value_3113_; lean_object* v_tail_3114_; lean_object* v___x_3115_; 
v_key_3112_ = lean_ctor_get(v_x_3111_, 0);
lean_inc(v_key_3112_);
v_value_3113_ = lean_ctor_get(v_x_3111_, 1);
lean_inc(v_value_3113_);
v_tail_3114_ = lean_ctor_get(v_x_3111_, 2);
lean_inc(v_tail_3114_);
lean_dec_ref_known(v_x_3111_, 3);
v___x_3115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_x_3110_, v_key_3112_, v_value_3113_);
v_x_3110_ = v___x_3115_;
v_x_3111_ = v_tail_3114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object* v_as_3117_, size_t v_i_3118_, size_t v_stop_3119_, lean_object* v_b_3120_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_usize_dec_eq(v_i_3118_, v_stop_3119_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3123_; size_t v___x_3124_; size_t v___x_3125_; 
v___x_3122_ = lean_array_uget_borrowed(v_as_3117_, v_i_3118_);
lean_inc(v___x_3122_);
v___x_3123_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_b_3120_, v___x_3122_);
v___x_3124_ = ((size_t)1ULL);
v___x_3125_ = lean_usize_add(v_i_3118_, v___x_3124_);
v_i_3118_ = v___x_3125_;
v_b_3120_ = v___x_3123_;
goto _start;
}
else
{
return v_b_3120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___boxed(lean_object* v_as_3127_, lean_object* v_i_3128_, lean_object* v_stop_3129_, lean_object* v_b_3130_){
_start:
{
size_t v_i_boxed_3131_; size_t v_stop_boxed_3132_; lean_object* v_res_3133_; 
v_i_boxed_3131_ = lean_unbox_usize(v_i_3128_);
lean_dec(v_i_3128_);
v_stop_boxed_3132_ = lean_unbox_usize(v_stop_3129_);
lean_dec(v_stop_3129_);
v_res_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v_as_3127_, v_i_boxed_3131_, v_stop_boxed_3132_, v_b_3130_);
lean_dec_ref(v_as_3127_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5(lean_object* v_a_3134_, lean_object* v___x_3135_, lean_object* v_as_3136_, size_t v_sz_3137_, size_t v_i_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_a_3143_; lean_object* v_a_3144_; uint8_t v___x_3148_; 
v___x_3148_ = lean_usize_dec_lt(v_i_3138_, v_sz_3137_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; 
lean_dec_ref(v_a_3134_);
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v_b_3139_);
lean_ctor_set(v___x_3149_, 1, v___y_3141_);
return v___x_3149_;
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3151_; 
lean_dec_ref(v___y_3141_);
v_a_3150_ = lean_array_uget_borrowed(v_as_3136_, v_i_3138_);
lean_inc_ref(v_a_3134_);
lean_inc(v_a_3150_);
v___x_3151_ = l_Lean_Fmt_fmt(v_a_3150_, v___y_3140_, v_a_3134_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_snd_3152_; lean_object* v_snd_3153_; lean_object* v_a_3154_; lean_object* v_missingFormatters_3155_; lean_object* v_a_3156_; lean_object* v_fst_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3251_; 
v_snd_3152_ = lean_ctor_get(v_b_3139_, 1);
lean_inc(v_snd_3152_);
v_snd_3153_ = lean_ctor_get(v_snd_3152_, 1);
lean_inc(v_snd_3153_);
v_a_3154_ = lean_ctor_get(v___x_3151_, 1);
lean_inc(v_a_3154_);
v_missingFormatters_3155_ = lean_ctor_get(v_a_3154_, 3);
lean_inc_ref(v_missingFormatters_3155_);
v_a_3156_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3151_, 2);
v_fst_3157_ = lean_ctor_get(v_b_3139_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_b_3139_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v_b_3139_, 1);
lean_dec(v_unused_3252_);
v___x_3159_ = v_b_3139_;
v_isShared_3160_ = v_isSharedCheck_3251_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_fst_3157_);
lean_dec(v_b_3139_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3251_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v_fst_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3249_; 
v_fst_3161_ = lean_ctor_get(v_snd_3152_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_snd_3152_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v_snd_3152_, 1);
lean_dec(v_unused_3250_);
v___x_3163_ = v_snd_3152_;
v_isShared_3164_ = v_isSharedCheck_3249_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_fst_3161_);
lean_dec(v_snd_3152_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3249_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v_fst_3165_; lean_object* v_snd_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3248_; 
v_fst_3165_ = lean_ctor_get(v_snd_3153_, 0);
v_snd_3166_ = lean_ctor_get(v_snd_3153_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_snd_3153_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3168_ = v_snd_3153_;
v_isShared_3169_ = v_isSharedCheck_3248_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_snd_3166_);
lean_inc(v_fst_3165_);
lean_dec(v_snd_3153_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3248_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v_partialFormatters_3170_; lean_object* v_buckets_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3246_; 
v_partialFormatters_3170_ = lean_ctor_get(v_a_3154_, 4);
v_buckets_3171_ = lean_ctor_get(v_missingFormatters_3155_, 1);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_missingFormatters_3155_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v_missingFormatters_3155_, 0);
lean_dec(v_unused_3247_);
v___x_3173_ = v_missingFormatters_3155_;
v_isShared_3174_ = v_isSharedCheck_3246_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_buckets_3171_);
lean_dec(v_missingFormatters_3155_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3246_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; uint8_t v_areFormattedAlike_3176_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3234_; lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3175_ = lean_unsigned_to_nat(0u);
v_areFormattedAlike_3176_ = lean_nat_dec_eq(v___x_3135_, v___x_3175_);
v___x_3241_ = lean_array_get_size(v_buckets_3171_);
v___x_3242_ = lean_nat_dec_lt(v___x_3175_, v___x_3241_);
if (v___x_3242_ == 0)
{
lean_dec_ref(v_buckets_3171_);
v___y_3234_ = v_fst_3165_;
goto v___jp_3233_;
}
else
{
size_t v___x_3243_; size_t v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = ((size_t)0ULL);
v___x_3244_ = lean_usize_of_nat(v___x_3241_);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4(v_buckets_3171_, v___x_3243_, v___x_3244_, v_fst_3165_);
lean_dec_ref(v_buckets_3171_);
v___y_3234_ = v___x_3245_;
goto v___jp_3233_;
}
v___jp_3177_:
{
uint8_t v___x_3180_; 
lean_inc(v_a_3156_);
v___x_3180_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_a_3156_);
if (v___x_3180_ == 0)
{
if (lean_obj_tag(v_fst_3157_) == 1)
{
lean_object* v_val_3181_; lean_object* v_fst_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3173_);
lean_del_object(v___x_3159_);
v_val_3181_ = lean_ctor_get(v_fst_3157_, 0);
lean_inc(v_val_3181_);
v_fst_3182_ = lean_ctor_get(v_val_3181_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_val_3181_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_val_3181_, 1);
lean_dec(v_unused_3209_);
v___x_3184_ = v_val_3181_;
v_isShared_3185_ = v_isSharedCheck_3208_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_fst_3182_);
lean_dec(v_val_3181_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3208_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_doc_3186_; lean_object* v_doc_3187_; uint8_t v___x_3188_; 
v_doc_3186_ = lean_ctor_get(v_a_3156_, 0);
lean_inc(v_doc_3186_);
lean_dec(v_a_3156_);
v_doc_3187_ = lean_ctor_get(v_fst_3182_, 0);
lean_inc(v_doc_3187_);
lean_dec(v_fst_3182_);
v___x_3188_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_doc_3186_, v_doc_3187_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3190_; 
lean_dec(v_fst_3161_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 1, v___y_3179_);
lean_ctor_set(v___x_3184_, 0, v___y_3178_);
v___x_3190_ = v___x_3184_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___y_3178_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___y_3179_);
v___x_3190_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3191_ = lean_box(v___x_3180_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___x_3190_);
lean_ctor_set(v___x_3168_, 0, v___x_3191_);
v___x_3193_ = v___x_3168_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3190_);
v___x_3193_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3193_);
lean_ctor_set(v___x_3163_, 0, v_fst_3157_);
v___x_3195_ = v___x_3163_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_fst_3157_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
v_a_3143_ = v___x_3195_;
v_a_3144_ = v_a_3154_;
goto v___jp_3142_;
}
}
}
}
else
{
lean_object* v___x_3200_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 1, v___y_3179_);
lean_ctor_set(v___x_3184_, 0, v___y_3178_);
v___x_3200_ = v___x_3184_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___y_3178_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___y_3179_);
v___x_3200_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___x_3200_);
lean_ctor_set(v___x_3168_, 0, v_fst_3161_);
v___x_3202_ = v___x_3168_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_fst_3161_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3204_; 
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3202_);
lean_ctor_set(v___x_3163_, 0, v_fst_3157_);
v___x_3204_ = v___x_3163_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_fst_3157_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_3202_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
v_a_3143_ = v___x_3204_;
v_a_3144_ = v_a_3154_;
goto v___jp_3142_;
}
}
}
}
}
}
else
{
lean_object* v___x_3211_; 
lean_dec(v_fst_3157_);
lean_inc(v_a_3154_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v_a_3154_);
lean_ctor_set(v___x_3168_, 0, v_a_3156_);
v___x_3211_ = v___x_3168_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3156_);
lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_a_3154_);
v___x_3211_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___y_3179_);
lean_ctor_set(v___x_3163_, 0, v___y_3178_);
v___x_3214_ = v___x_3163_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___y_3178_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___y_3179_);
v___x_3214_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 1, v___x_3214_);
lean_ctor_set(v___x_3159_, 0, v_fst_3161_);
v___x_3216_ = v___x_3159_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_fst_3161_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3218_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___x_3216_);
lean_ctor_set(v___x_3173_, 0, v___x_3212_);
v___x_3218_ = v___x_3173_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
v_a_3143_ = v___x_3218_;
v_a_3144_ = v_a_3154_;
goto v___jp_3142_;
}
}
}
}
}
}
else
{
lean_object* v___x_3224_; 
lean_del_object(v___x_3173_);
lean_dec(v_fst_3161_);
lean_dec(v_a_3156_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___y_3179_);
lean_ctor_set(v___x_3168_, 0, v___y_3178_);
v___x_3224_ = v___x_3168_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___y_3178_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v___y_3179_);
v___x_3224_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3225_ = lean_box(v_areFormattedAlike_3176_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 1, v___x_3224_);
lean_ctor_set(v___x_3163_, 0, v___x_3225_);
v___x_3227_ = v___x_3163_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3224_);
v___x_3227_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3229_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 1, v___x_3227_);
v___x_3229_ = v___x_3159_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_fst_3157_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
v_a_3143_ = v___x_3229_;
v_a_3144_ = v_a_3154_;
goto v___jp_3142_;
}
}
}
}
}
v___jp_3233_:
{
lean_object* v_buckets_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v_buckets_3235_ = lean_ctor_get(v_partialFormatters_3170_, 1);
v___x_3236_ = lean_array_get_size(v_buckets_3235_);
v___x_3237_ = lean_nat_dec_lt(v___x_3175_, v___x_3236_);
if (v___x_3237_ == 0)
{
v___y_3178_ = v___y_3234_;
v___y_3179_ = v_snd_3166_;
goto v___jp_3177_;
}
else
{
size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = ((size_t)0ULL);
v___x_3239_ = lean_usize_of_nat(v___x_3236_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v_buckets_3235_, v___x_3238_, v___x_3239_, v_snd_3166_);
v___y_3178_ = v___y_3234_;
v___y_3179_ = v___x_3240_;
goto v___jp_3177_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v_b_3139_);
lean_dec_ref(v_a_3134_);
v_a_3253_ = lean_ctor_get(v___x_3151_, 0);
v_a_3254_ = lean_ctor_get(v___x_3151_, 1);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3151_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_inc(v_a_3253_);
lean_dec(v___x_3151_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3253_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
v___jp_3142_:
{
size_t v___x_3145_; size_t v___x_3146_; 
v___x_3145_ = ((size_t)1ULL);
v___x_3146_ = lean_usize_add(v_i_3138_, v___x_3145_);
v_i_3138_ = v___x_3146_;
v_b_3139_ = v_a_3143_;
v___y_3141_ = v_a_3144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5___boxed(lean_object* v_a_3262_, lean_object* v___x_3263_, lean_object* v_as_3264_, lean_object* v_sz_3265_, lean_object* v_i_3266_, lean_object* v_b_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
size_t v_sz_boxed_3270_; size_t v_i_boxed_3271_; lean_object* v_res_3272_; 
v_sz_boxed_3270_ = lean_unbox_usize(v_sz_3265_);
lean_dec(v_sz_3265_);
v_i_boxed_3271_ = lean_unbox_usize(v_i_3266_);
lean_dec(v_i_3266_);
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5(v_a_3262_, v___x_3263_, v_as_3264_, v_sz_boxed_3270_, v_i_boxed_3271_, v_b_3267_, v___y_3268_, v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v_as_3264_);
lean_dec(v___x_3263_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6(size_t v_sz_3273_, size_t v_i_3274_, lean_object* v_bs_3275_){
_start:
{
uint8_t v___x_3276_; 
v___x_3276_ = lean_usize_dec_lt(v_i_3274_, v_sz_3273_);
if (v___x_3276_ == 0)
{
return v_bs_3275_;
}
else
{
lean_object* v_v_3277_; lean_object* v___x_3278_; lean_object* v_bs_x27_3279_; lean_object* v___x_3280_; size_t v___x_3281_; size_t v___x_3282_; lean_object* v___x_3283_; 
v_v_3277_ = lean_array_uget(v_bs_3275_, v_i_3274_);
v___x_3278_ = lean_unsigned_to_nat(0u);
v_bs_x27_3279_ = lean_array_uset(v_bs_3275_, v_i_3274_, v___x_3278_);
v___x_3280_ = l_Lean_Syntax_getKind(v_v_3277_);
v___x_3281_ = ((size_t)1ULL);
v___x_3282_ = lean_usize_add(v_i_3274_, v___x_3281_);
v___x_3283_ = lean_array_uset(v_bs_x27_3279_, v_i_3274_, v___x_3280_);
v_i_3274_ = v___x_3282_;
v_bs_3275_ = v___x_3283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6___boxed(lean_object* v_sz_3285_, lean_object* v_i_3286_, lean_object* v_bs_3287_){
_start:
{
size_t v_sz_boxed_3288_; size_t v_i_boxed_3289_; lean_object* v_res_3290_; 
v_sz_boxed_3288_ = lean_unbox_usize(v_sz_3285_);
lean_dec(v_sz_3285_);
v_i_boxed_3289_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_res_3290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6(v_sz_boxed_3288_, v_i_boxed_3289_, v_bs_3287_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object* v_choiceStx_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v_areFormattedAlike_3296_; 
v___x_3294_ = l_Lean_Syntax_getNumArgs(v_choiceStx_3291_);
v___x_3295_ = lean_unsigned_to_nat(0u);
v_areFormattedAlike_3296_ = lean_nat_dec_eq(v___x_3294_, v___x_3295_);
if (v_areFormattedAlike_3296_ == 0)
{
lean_object* v_toBacktrackableState_3297_; lean_object* v_shareCommonState_3298_; lean_object* v_freshTagId_3299_; lean_object* v_missingFormatters_3300_; lean_object* v_partialFormatters_3301_; lean_object* v_missingChoiceResolutions_3302_; uint8_t v_areFormattedAlike_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; size_t v_sz_3310_; size_t v___x_3311_; lean_object* v___x_3312_; 
v_toBacktrackableState_3297_ = lean_ctor_get(v_a_3293_, 0);
lean_inc_ref(v_toBacktrackableState_3297_);
v_shareCommonState_3298_ = lean_ctor_get(v_a_3293_, 1);
lean_inc(v_shareCommonState_3298_);
v_freshTagId_3299_ = lean_ctor_get(v_a_3293_, 2);
lean_inc(v_freshTagId_3299_);
v_missingFormatters_3300_ = lean_ctor_get(v_a_3293_, 3);
v_partialFormatters_3301_ = lean_ctor_get(v_a_3293_, 4);
v_missingChoiceResolutions_3302_ = lean_ctor_get(v_a_3293_, 5);
lean_inc_ref(v_missingChoiceResolutions_3302_);
v_areFormattedAlike_3303_ = 1;
v___x_3304_ = lean_box(0);
v___x_3305_ = l_Lean_Syntax_getArgs(v_choiceStx_3291_);
lean_inc_ref(v_partialFormatters_3301_);
lean_inc_ref(v_missingFormatters_3300_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_missingFormatters_3300_);
lean_ctor_set(v___x_3306_, 1, v_partialFormatters_3301_);
v___x_3307_ = lean_box(v_areFormattedAlike_3303_);
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
lean_ctor_set(v___x_3308_, 1, v___x_3306_);
v___x_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3304_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v_sz_3310_ = lean_array_size(v___x_3305_);
v___x_3311_ = ((size_t)0ULL);
lean_inc_ref(v_a_3293_);
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5(v_a_3293_, v___x_3294_, v___x_3305_, v_sz_3310_, v___x_3311_, v___x_3309_, v_a_3292_, v_a_3293_);
lean_dec(v___x_3294_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3362_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v___x_3312_, 1);
lean_dec(v_unused_3363_);
v___x_3315_ = v___x_3312_;
v_isShared_3316_ = v_isSharedCheck_3362_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3312_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3362_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v_snd_3317_; lean_object* v_snd_3318_; lean_object* v_fst_3319_; lean_object* v_fst_3320_; lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___y_3324_; uint8_t v___x_3355_; 
v_snd_3317_ = lean_ctor_get(v_a_3313_, 1);
lean_inc(v_snd_3317_);
v_snd_3318_ = lean_ctor_get(v_snd_3317_, 1);
lean_inc(v_snd_3318_);
v_fst_3319_ = lean_ctor_get(v_a_3313_, 0);
lean_inc(v_fst_3319_);
lean_dec(v_a_3313_);
v_fst_3320_ = lean_ctor_get(v_snd_3317_, 0);
lean_inc(v_fst_3320_);
lean_dec(v_snd_3317_);
v_fst_3321_ = lean_ctor_get(v_snd_3318_, 0);
lean_inc(v_fst_3321_);
v_snd_3322_ = lean_ctor_get(v_snd_3318_, 1);
lean_inc(v_snd_3322_);
lean_dec(v_snd_3318_);
v___x_3355_ = lean_unbox(v_fst_3320_);
lean_dec(v_fst_3320_);
if (v___x_3355_ == 0)
{
lean_dec(v_fst_3319_);
lean_del_object(v___x_3315_);
v___y_3324_ = v_a_3292_;
goto v___jp_3323_;
}
else
{
if (lean_obj_tag(v_fst_3319_) == 1)
{
lean_object* v_val_3356_; lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3360_; 
lean_dec(v_snd_3322_);
lean_dec(v_fst_3321_);
lean_dec_ref(v___x_3305_);
lean_dec_ref(v_missingChoiceResolutions_3302_);
lean_dec(v_freshTagId_3299_);
lean_dec(v_shareCommonState_3298_);
lean_dec_ref(v_toBacktrackableState_3297_);
lean_dec(v_choiceStx_3291_);
v_val_3356_ = lean_ctor_get(v_fst_3319_, 0);
lean_inc(v_val_3356_);
lean_dec_ref_known(v_fst_3319_, 1);
v_fst_3357_ = lean_ctor_get(v_val_3356_, 0);
lean_inc(v_fst_3357_);
v_snd_3358_ = lean_ctor_get(v_val_3356_, 1);
lean_inc(v_snd_3358_);
lean_dec(v_val_3356_);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 1, v_snd_3358_);
lean_ctor_set(v___x_3315_, 0, v_fst_3357_);
v___x_3360_ = v___x_3315_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_fst_3357_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_snd_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
else
{
lean_dec(v_fst_3319_);
lean_del_object(v___x_3315_);
v___y_3324_ = v_a_3292_;
goto v___jp_3323_;
}
}
v___jp_3323_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3325_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3325_, 0, v_toBacktrackableState_3297_);
lean_ctor_set(v___x_3325_, 1, v_shareCommonState_3298_);
lean_ctor_set(v___x_3325_, 2, v_freshTagId_3299_);
lean_ctor_set(v___x_3325_, 3, v_fst_3321_);
lean_ctor_set(v___x_3325_, 4, v_snd_3322_);
lean_ctor_set(v___x_3325_, 5, v_missingChoiceResolutions_3302_);
lean_inc(v_choiceStx_3291_);
v___x_3326_ = l_Lean_Fmt_fmtRaw(v_areFormattedAlike_3303_, v_choiceStx_3291_, v___y_3324_, v___x_3325_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v_a_3328_; lean_object* v___x_3329_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_a_3328_ = lean_ctor_get(v___x_3326_, 1);
lean_inc(v_a_3328_);
v___x_3329_ = l_Lean_Syntax_getRange_x3f(v_choiceStx_3291_, v_areFormattedAlike_3296_);
lean_dec(v_choiceStx_3291_);
if (lean_obj_tag(v___x_3329_) == 1)
{
lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3352_; 
lean_inc(v_a_3327_);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; lean_object* v_unused_3354_; 
v_unused_3353_ = lean_ctor_get(v___x_3326_, 1);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v___x_3326_, 0);
lean_dec(v_unused_3354_);
v___x_3331_ = v___x_3326_;
v_isShared_3332_ = v_isSharedCheck_3352_;
goto v_resetjp_3330_;
}
else
{
lean_dec(v___x_3326_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3352_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v_val_3333_; lean_object* v_toBacktrackableState_3334_; lean_object* v_shareCommonState_3335_; lean_object* v_freshTagId_3336_; lean_object* v_missingFormatters_3337_; lean_object* v_partialFormatters_3338_; lean_object* v_missingChoiceResolutions_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3351_; 
v_val_3333_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3333_);
lean_dec_ref_known(v___x_3329_, 1);
v_toBacktrackableState_3334_ = lean_ctor_get(v_a_3328_, 0);
v_shareCommonState_3335_ = lean_ctor_get(v_a_3328_, 1);
v_freshTagId_3336_ = lean_ctor_get(v_a_3328_, 2);
v_missingFormatters_3337_ = lean_ctor_get(v_a_3328_, 3);
v_partialFormatters_3338_ = lean_ctor_get(v_a_3328_, 4);
v_missingChoiceResolutions_3339_ = lean_ctor_get(v_a_3328_, 5);
v_isSharedCheck_3351_ = !lean_is_exclusive(v_a_3328_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3341_ = v_a_3328_;
v_isShared_3342_ = v_isSharedCheck_3351_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_missingChoiceResolutions_3339_);
lean_inc(v_partialFormatters_3338_);
lean_inc(v_missingFormatters_3337_);
lean_inc(v_freshTagId_3336_);
lean_inc(v_shareCommonState_3335_);
lean_inc(v_toBacktrackableState_3334_);
lean_dec(v_a_3328_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3351_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6(v_sz_3310_, v___x_3311_, v___x_3305_);
v___x_3344_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingChoiceResolutions_3339_, v_val_3333_, v___x_3343_);
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 5, v___x_3344_);
v___x_3346_ = v___x_3341_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_toBacktrackableState_3334_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_shareCommonState_3335_);
lean_ctor_set(v_reuseFailAlloc_3350_, 2, v_freshTagId_3336_);
lean_ctor_set(v_reuseFailAlloc_3350_, 3, v_missingFormatters_3337_);
lean_ctor_set(v_reuseFailAlloc_3350_, 4, v_partialFormatters_3338_);
lean_ctor_set(v_reuseFailAlloc_3350_, 5, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3348_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 1, v___x_3346_);
v___x_3348_ = v___x_3331_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3327_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
else
{
lean_dec(v___x_3329_);
lean_dec(v_a_3328_);
lean_dec_ref(v___x_3305_);
return v___x_3326_;
}
}
else
{
lean_dec_ref(v___x_3305_);
lean_dec(v_choiceStx_3291_);
return v___x_3326_;
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v___x_3305_);
lean_dec_ref(v_missingChoiceResolutions_3302_);
lean_dec(v_freshTagId_3299_);
lean_dec(v_shareCommonState_3298_);
lean_dec_ref(v_toBacktrackableState_3297_);
lean_dec(v_choiceStx_3291_);
v_a_3364_ = lean_ctor_get(v___x_3312_, 0);
v_a_3365_ = lean_ctor_get(v___x_3312_, 1);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3312_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_inc(v_a_3364_);
lean_dec(v___x_3312_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3364_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec(v___x_3294_);
v___x_3373_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3374_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_3373_, v_choiceStx_3291_, v_a_3293_);
lean_dec(v_choiceStx_3291_);
return v___x_3374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object* v_choiceStx_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(v_choiceStx_3375_, v_a_3376_, v_a_3377_);
lean_dec_ref(v_a_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3379_, lean_object* v_m_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(v_m_3380_, v_a_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3383_, lean_object* v_m_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1(v_00_u03b2_3383_, v_m_3384_, v_a_3385_);
lean_dec_ref(v_a_3385_);
lean_dec_ref(v_m_3384_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_3387_, lean_object* v_m_3388_, lean_object* v_a_3389_, lean_object* v_b_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3___redArg(v_m_3388_, v_a_3389_, v_b_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9(lean_object* v_00_u03b2_3392_, lean_object* v_a_3393_, lean_object* v_x_3394_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(v_a_3393_, v_x_3394_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3396_, lean_object* v_a_3397_, lean_object* v_x_3398_){
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9(v_00_u03b2_3396_, v_a_3397_, v_x_3398_);
lean_dec(v_x_3398_);
lean_dec_ref(v_a_3397_);
return v_res_3399_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_3400_, lean_object* v_a_3401_, lean_object* v_x_3402_){
_start:
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(v_a_3401_, v_x_3402_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___boxed(lean_object* v_00_u03b2_3404_, lean_object* v_a_3405_, lean_object* v_x_3406_){
_start:
{
uint8_t v_res_3407_; lean_object* v_r_3408_; 
v_res_3407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12(v_00_u03b2_3404_, v_a_3405_, v_x_3406_);
lean_dec(v_x_3406_);
lean_dec_ref(v_a_3405_);
v_r_3408_ = lean_box(v_res_3407_);
return v_r_3408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13(lean_object* v_00_u03b2_3409_, lean_object* v_data_3410_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13___redArg(v_data_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14(lean_object* v_00_u03b2_3412_, lean_object* v_a_3413_, lean_object* v_b_3414_, lean_object* v_x_3415_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(v_a_3413_, v_b_3414_, v_x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15(lean_object* v_00_u03b2_3417_, lean_object* v_i_3418_, lean_object* v_source_3419_, lean_object* v_target_3420_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15___redArg(v_i_3418_, v_source_3419_, v_target_3420_);
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16(lean_object* v_00_u03b2_3422_, lean_object* v_x_3423_, lean_object* v_x_3424_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16___redArg(v_x_3423_, v_x_3424_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(size_t v_sz_3426_, size_t v_i_3427_, lean_object* v_bs_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_usize_dec_lt(v_i_3427_, v_sz_3426_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; 
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v_bs_3428_);
lean_ctor_set(v___x_3432_, 1, v___y_3430_);
return v___x_3432_;
}
else
{
lean_object* v_v_3433_; lean_object* v___x_3434_; 
v_v_3433_ = lean_array_uget_borrowed(v_bs_3428_, v_i_3427_);
lean_inc(v_v_3433_);
v___x_3434_ = l_Lean_Fmt_fmt(v_v_3433_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v_a_3436_; lean_object* v___x_3437_; lean_object* v_bs_x27_3438_; size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
v_a_3436_ = lean_ctor_get(v___x_3434_, 1);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3434_, 2);
v___x_3437_ = lean_unsigned_to_nat(0u);
v_bs_x27_3438_ = lean_array_uset(v_bs_3428_, v_i_3427_, v___x_3437_);
v___x_3439_ = ((size_t)1ULL);
v___x_3440_ = lean_usize_add(v_i_3427_, v___x_3439_);
v___x_3441_ = lean_array_uset(v_bs_x27_3438_, v_i_3427_, v_a_3435_);
v_i_3427_ = v___x_3440_;
v_bs_3428_ = v___x_3441_;
v___y_3430_ = v_a_3436_;
goto _start;
}
else
{
lean_object* v_a_3443_; lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref(v_bs_3428_);
v_a_3443_ = lean_ctor_get(v___x_3434_, 0);
v_a_3444_ = lean_ctor_get(v___x_3434_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3434_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_inc(v_a_3443_);
lean_dec(v___x_3434_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3443_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1___boxed(lean_object* v_sz_3452_, lean_object* v_i_3453_, lean_object* v_bs_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
size_t v_sz_boxed_3457_; size_t v_i_boxed_3458_; lean_object* v_res_3459_; 
v_sz_boxed_3457_ = lean_unbox_usize(v_sz_3452_);
lean_dec(v_sz_3452_);
v_i_boxed_3458_ = lean_unbox_usize(v_i_3453_);
lean_dec(v_i_3453_);
v_res_3459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_boxed_3457_, v_i_boxed_3458_, v_bs_3454_, v___y_3455_, v___y_3456_);
lean_dec_ref(v___y_3455_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3460_, lean_object* v_x_3461_){
_start:
{
if (lean_obj_tag(v_x_3461_) == 0)
{
return v_x_3460_;
}
else
{
lean_object* v_key_3462_; lean_object* v_value_3463_; lean_object* v_tail_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3490_; 
v_key_3462_ = lean_ctor_get(v_x_3461_, 0);
v_value_3463_ = lean_ctor_get(v_x_3461_, 1);
v_tail_3464_ = lean_ctor_get(v_x_3461_, 2);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_x_3461_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3466_ = v_x_3461_;
v_isShared_3467_ = v_isSharedCheck_3490_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_tail_3464_);
lean_inc(v_value_3463_);
lean_inc(v_key_3462_);
lean_dec(v_x_3461_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3490_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; uint64_t v___y_3470_; 
v___x_3468_ = lean_array_get_size(v_x_3460_);
if (lean_obj_tag(v_key_3462_) == 0)
{
uint64_t v___x_3488_; 
v___x_3488_ = 1723ULL;
v___y_3470_ = v___x_3488_;
goto v___jp_3469_;
}
else
{
uint64_t v_hash_3489_; 
v_hash_3489_ = lean_ctor_get_uint64(v_key_3462_, sizeof(void*)*2);
v___y_3470_ = v_hash_3489_;
goto v___jp_3469_;
}
v___jp_3469_:
{
uint64_t v___x_3471_; uint64_t v___x_3472_; uint64_t v_fold_3473_; uint64_t v___x_3474_; uint64_t v___x_3475_; uint64_t v___x_3476_; size_t v___x_3477_; size_t v___x_3478_; size_t v___x_3479_; size_t v___x_3480_; size_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3471_ = 32ULL;
v___x_3472_ = lean_uint64_shift_right(v___y_3470_, v___x_3471_);
v_fold_3473_ = lean_uint64_xor(v___y_3470_, v___x_3472_);
v___x_3474_ = 16ULL;
v___x_3475_ = lean_uint64_shift_right(v_fold_3473_, v___x_3474_);
v___x_3476_ = lean_uint64_xor(v_fold_3473_, v___x_3475_);
v___x_3477_ = lean_uint64_to_usize(v___x_3476_);
v___x_3478_ = lean_usize_of_nat(v___x_3468_);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_sub(v___x_3478_, v___x_3479_);
v___x_3481_ = lean_usize_land(v___x_3477_, v___x_3480_);
v___x_3482_ = lean_array_uget_borrowed(v_x_3460_, v___x_3481_);
lean_inc(v___x_3482_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 2, v___x_3482_);
v___x_3484_ = v___x_3466_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_key_3462_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_value_3463_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_array_uset(v_x_3460_, v___x_3481_, v___x_3484_);
v_x_3460_ = v___x_3485_;
v_x_3461_ = v_tail_3464_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(lean_object* v_i_3491_, lean_object* v_source_3492_, lean_object* v_target_3493_){
_start:
{
lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3494_ = lean_array_get_size(v_source_3492_);
v___x_3495_ = lean_nat_dec_lt(v_i_3491_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_dec_ref(v_source_3492_);
lean_dec(v_i_3491_);
return v_target_3493_;
}
else
{
lean_object* v_es_3496_; lean_object* v___x_3497_; lean_object* v_source_3498_; lean_object* v_target_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v_es_3496_ = lean_array_fget(v_source_3492_, v_i_3491_);
v___x_3497_ = lean_box(0);
v_source_3498_ = lean_array_fset(v_source_3492_, v_i_3491_, v___x_3497_);
v_target_3499_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_target_3493_, v_es_3496_);
v___x_3500_ = lean_unsigned_to_nat(1u);
v___x_3501_ = lean_nat_add(v_i_3491_, v___x_3500_);
lean_dec(v_i_3491_);
v_i_3491_ = v___x_3501_;
v_source_3492_ = v_source_3498_;
v_target_3493_ = v_target_3499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(lean_object* v_data_3503_){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v_nbuckets_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3504_ = lean_array_get_size(v_data_3503_);
v___x_3505_ = lean_unsigned_to_nat(2u);
v_nbuckets_3506_ = lean_nat_mul(v___x_3504_, v___x_3505_);
v___x_3507_ = lean_unsigned_to_nat(0u);
v___x_3508_ = lean_box(0);
v___x_3509_ = lean_mk_array(v_nbuckets_3506_, v___x_3508_);
v___x_3510_ = lean_array_propagate_mark(v_data_3503_, v___x_3509_);
v___x_3511_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v___x_3507_, v_data_3503_, v___x_3510_);
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(lean_object* v_m_3512_, lean_object* v_a_3513_, lean_object* v_b_3514_){
_start:
{
lean_object* v_size_3515_; lean_object* v_buckets_3516_; lean_object* v___x_3517_; uint64_t v___y_3519_; 
v_size_3515_ = lean_ctor_get(v_m_3512_, 0);
v_buckets_3516_ = lean_ctor_get(v_m_3512_, 1);
v___x_3517_ = lean_array_get_size(v_buckets_3516_);
if (lean_obj_tag(v_a_3513_) == 0)
{
uint64_t v___x_3556_; 
v___x_3556_ = 1723ULL;
v___y_3519_ = v___x_3556_;
goto v___jp_3518_;
}
else
{
uint64_t v_hash_3557_; 
v_hash_3557_ = lean_ctor_get_uint64(v_a_3513_, sizeof(void*)*2);
v___y_3519_ = v_hash_3557_;
goto v___jp_3518_;
}
v___jp_3518_:
{
uint64_t v___x_3520_; uint64_t v___x_3521_; uint64_t v_fold_3522_; uint64_t v___x_3523_; uint64_t v___x_3524_; uint64_t v___x_3525_; size_t v___x_3526_; size_t v___x_3527_; size_t v___x_3528_; size_t v___x_3529_; size_t v___x_3530_; lean_object* v_bkt_3531_; uint8_t v___x_3532_; 
v___x_3520_ = 32ULL;
v___x_3521_ = lean_uint64_shift_right(v___y_3519_, v___x_3520_);
v_fold_3522_ = lean_uint64_xor(v___y_3519_, v___x_3521_);
v___x_3523_ = 16ULL;
v___x_3524_ = lean_uint64_shift_right(v_fold_3522_, v___x_3523_);
v___x_3525_ = lean_uint64_xor(v_fold_3522_, v___x_3524_);
v___x_3526_ = lean_uint64_to_usize(v___x_3525_);
v___x_3527_ = lean_usize_of_nat(v___x_3517_);
v___x_3528_ = ((size_t)1ULL);
v___x_3529_ = lean_usize_sub(v___x_3527_, v___x_3528_);
v___x_3530_ = lean_usize_land(v___x_3526_, v___x_3529_);
v_bkt_3531_ = lean_array_uget_borrowed(v_buckets_3516_, v___x_3530_);
v___x_3532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_3513_, v_bkt_3531_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3553_; 
lean_inc_ref(v_buckets_3516_);
lean_inc(v_size_3515_);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_m_3512_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; lean_object* v_unused_3555_; 
v_unused_3554_ = lean_ctor_get(v_m_3512_, 1);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_m_3512_, 0);
lean_dec(v_unused_3555_);
v___x_3534_ = v_m_3512_;
v_isShared_3535_ = v_isSharedCheck_3553_;
goto v_resetjp_3533_;
}
else
{
lean_dec(v_m_3512_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3553_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v_size_x27_3537_; lean_object* v___x_3538_; lean_object* v_buckets_x27_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3536_ = lean_unsigned_to_nat(1u);
v_size_x27_3537_ = lean_nat_add(v_size_3515_, v___x_3536_);
lean_dec(v_size_3515_);
lean_inc(v_bkt_3531_);
v___x_3538_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3538_, 0, v_a_3513_);
lean_ctor_set(v___x_3538_, 1, v_b_3514_);
lean_ctor_set(v___x_3538_, 2, v_bkt_3531_);
v_buckets_x27_3539_ = lean_array_uset(v_buckets_3516_, v___x_3530_, v___x_3538_);
v___x_3540_ = lean_unsigned_to_nat(4u);
v___x_3541_ = lean_nat_mul(v_size_x27_3537_, v___x_3540_);
v___x_3542_ = lean_unsigned_to_nat(3u);
v___x_3543_ = lean_nat_div(v___x_3541_, v___x_3542_);
lean_dec(v___x_3541_);
v___x_3544_ = lean_array_get_size(v_buckets_x27_3539_);
v___x_3545_ = lean_nat_dec_le(v___x_3543_, v___x_3544_);
lean_dec(v___x_3543_);
if (v___x_3545_ == 0)
{
lean_object* v_val_3546_; lean_object* v___x_3548_; 
v_val_3546_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_buckets_x27_3539_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 1, v_val_3546_);
lean_ctor_set(v___x_3534_, 0, v_size_x27_3537_);
v___x_3548_ = v___x_3534_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_size_x27_3537_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_val_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
else
{
lean_object* v___x_3551_; 
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 1, v_buckets_x27_3539_);
lean_ctor_set(v___x_3534_, 0, v_size_x27_3537_);
v___x_3551_ = v___x_3534_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_size_x27_3537_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_buckets_x27_3539_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_dec(v_b_3514_);
lean_dec(v_a_3513_);
return v_m_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object* v_op_3558_, lean_object* v_stx_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
uint8_t v_sparse_3562_; uint8_t v_separateFinalOperand_3563_; lean_object* v_precs_x3f_3564_; lean_object* v_extendedChainKinds_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3606_; 
v_sparse_3562_ = lean_ctor_get_uint8(v_op_3558_, sizeof(void*)*2);
v_separateFinalOperand_3563_ = lean_ctor_get_uint8(v_op_3558_, sizeof(void*)*2 + 1);
v_precs_x3f_3564_ = lean_ctor_get(v_op_3558_, 0);
v_extendedChainKinds_3565_ = lean_ctor_get(v_op_3558_, 1);
v_isSharedCheck_3606_ = !lean_is_exclusive(v_op_3558_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3567_ = v_op_3558_;
v_isShared_3568_ = v_isSharedCheck_3606_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_extendedChainKinds_3565_);
lean_inc(v_precs_x3f_3564_);
lean_dec(v_op_3558_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3606_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v_env_3569_; lean_object* v_opts_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v_env_3569_ = lean_ctor_get(v_a_3560_, 0);
v_opts_3570_ = lean_ctor_get(v_a_3560_, 3);
lean_inc(v_stx_3559_);
v___x_3571_ = l_Lean_Syntax_getKind(v_stx_3559_);
v___x_3572_ = lean_box(0);
v___x_3573_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_extendedChainKinds_3565_, v___x_3571_, v___x_3572_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 1, v___x_3573_);
v___x_3575_ = v___x_3567_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_precs_x3f_3564_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3605_, sizeof(void*)*2, v_sparse_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3605_, sizeof(void*)*2 + 1, v_separateFinalOperand_3563_);
v___x_3575_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; size_t v_sz_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
lean_inc_ref(v_env_3569_);
v___x_3576_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_3569_, v_opts_3570_, v___x_3575_, v_stx_3559_);
lean_dec_ref(v___x_3575_);
v_sz_3577_ = lean_array_size(v___x_3576_);
v___x_3578_ = ((size_t)0ULL);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_3577_, v___x_3578_, v___x_3576_, v_a_3560_, v_a_3561_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3595_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_a_3581_ = lean_ctor_get(v___x_3579_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3583_ = v___x_3579_;
v_isShared_3584_ = v_isSharedCheck_3595_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3595_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___y_3586_; uint8_t v___x_3591_; 
v___x_3591_ = 1;
if (v_sparse_3562_ == 0)
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3592_, 0, v___x_3591_);
lean_ctor_set_uint8(v___x_3592_, 1, v_sparse_3562_);
lean_ctor_set_uint8(v___x_3592_, 2, v___x_3591_);
lean_ctor_set_uint8(v___x_3592_, 3, v___x_3591_);
v___y_3586_ = v___x_3592_;
goto v___jp_3585_;
}
else
{
uint8_t v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = 0;
v___x_3594_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_3594_, 0, v___x_3591_);
lean_ctor_set_uint8(v___x_3594_, 1, v___x_3593_);
lean_ctor_set_uint8(v___x_3594_, 2, v___x_3591_);
lean_ctor_set_uint8(v___x_3594_, 3, v___x_3593_);
lean_ctor_set_uint8(v___x_3594_, 4, v_separateFinalOperand_3563_);
v___y_3586_ = v___x_3594_;
goto v___jp_3585_;
}
v___jp_3585_:
{
lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3587_ = l_Lean_Fmt_Layouts_infixOperator(v_a_3580_, v___y_3586_);
lean_dec_ref(v___y_3586_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3587_);
v___x_3589_ = v___x_3583_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_a_3581_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
v_a_3596_ = lean_ctor_get(v___x_3579_, 0);
v_a_3597_ = lean_ctor_get(v___x_3579_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3579_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_inc(v_a_3596_);
lean_dec(v___x_3579_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3596_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object* v_op_3607_, lean_object* v_stx_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Fmt_fmtInfixOperator(v_op_3607_, v_stx_3608_, v_a_3609_, v_a_3610_);
lean_dec_ref(v_a_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0(lean_object* v_00_u03b2_3612_, lean_object* v_m_3613_, lean_object* v_a_3614_, lean_object* v_b_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_m_3613_, v_a_3614_, v_b_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0(lean_object* v_00_u03b2_3617_, lean_object* v_data_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_data_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3620_, lean_object* v_i_3621_, lean_object* v_source_3622_, lean_object* v_target_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v_i_3621_, v_source_3622_, v_target_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3625_, lean_object* v_x_3626_, lean_object* v_x_3627_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3626_, v_x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(lean_object* v_x_3629_, lean_object* v_x_3630_){
_start:
{
if (lean_obj_tag(v_x_3629_) == 0)
{
if (lean_obj_tag(v_x_3630_) == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = 1;
return v___x_3631_;
}
else
{
uint8_t v___x_3632_; 
v___x_3632_ = 0;
return v___x_3632_;
}
}
else
{
if (lean_obj_tag(v_x_3630_) == 0)
{
uint8_t v___x_3633_; 
v___x_3633_ = 0;
return v___x_3633_;
}
else
{
lean_object* v_val_3634_; lean_object* v_val_3635_; uint8_t v___x_3636_; 
v_val_3634_ = lean_ctor_get(v_x_3629_, 0);
v_val_3635_ = lean_ctor_get(v_x_3630_, 0);
v___x_3636_ = lean_string_dec_eq(v_val_3634_, v_val_3635_);
return v___x_3636_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0___boxed(lean_object* v_x_3637_, lean_object* v_x_3638_){
_start:
{
uint8_t v_res_3639_; lean_object* v_r_3640_; 
v_res_3639_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v_x_3637_, v_x_3638_);
lean_dec(v_x_3638_);
lean_dec(v_x_3637_);
v_r_3640_ = lean_box(v_res_3639_);
return v_r_3640_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(lean_object* v_msg_3641_){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = l_String_instInhabitedSlice;
v___x_3643_ = lean_panic_fn_borrowed(v___x_3642_, v_msg_3641_);
return v___x_3643_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(lean_object* v_s_3644_, lean_object* v_a_3645_, uint8_t v_b_3646_){
_start:
{
lean_object* v_str_3647_; lean_object* v_startInclusive_3648_; lean_object* v_endExclusive_3649_; lean_object* v___x_3650_; uint8_t v_decide_3651_; 
v_str_3647_ = lean_ctor_get(v_s_3644_, 0);
v_startInclusive_3648_ = lean_ctor_get(v_s_3644_, 1);
v_endExclusive_3649_ = lean_ctor_get(v_s_3644_, 2);
v___x_3650_ = lean_nat_sub(v_endExclusive_3649_, v_startInclusive_3648_);
v_decide_3651_ = lean_nat_dec_eq(v_a_3645_, v___x_3650_);
lean_dec(v___x_3650_);
if (v_decide_3651_ == 0)
{
lean_object* v___x_3652_; uint32_t v___x_3653_; uint32_t v___x_3654_; uint8_t v___x_3655_; 
v___x_3652_ = lean_nat_add(v_startInclusive_3648_, v_a_3645_);
lean_dec(v_a_3645_);
v___x_3653_ = lean_string_utf8_get_fast(v_str_3647_, v___x_3652_);
v___x_3654_ = l_Lean_idEndEscape;
v___x_3655_ = lean_uint32_dec_eq(v___x_3653_, v___x_3654_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3656_ = lean_string_utf8_next_fast(v_str_3647_, v___x_3652_);
lean_dec(v___x_3652_);
v___x_3657_ = lean_nat_sub(v___x_3656_, v_startInclusive_3648_);
v_a_3645_ = v___x_3657_;
v_b_3646_ = v___x_3655_;
goto _start;
}
else
{
lean_dec(v___x_3652_);
return v___x_3655_;
}
}
else
{
lean_dec(v_a_3645_);
return v_b_3646_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg___boxed(lean_object* v_s_3659_, lean_object* v_a_3660_, lean_object* v_b_3661_){
_start:
{
uint8_t v_b_boxed_3662_; uint8_t v_res_3663_; lean_object* v_r_3664_; 
v_b_boxed_3662_ = lean_unbox(v_b_3661_);
v_res_3663_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3659_, v_a_3660_, v_b_boxed_3662_);
lean_dec_ref(v_s_3659_);
v_r_3664_ = lean_box(v_res_3663_);
return v_r_3664_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(lean_object* v_s_3665_){
_start:
{
lean_object* v_searcher_3666_; uint8_t v___x_3667_; uint8_t v___x_3668_; 
v_searcher_3666_ = lean_unsigned_to_nat(0u);
v___x_3667_ = 0;
v___x_3668_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3665_, v_searcher_3666_, v___x_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1___boxed(lean_object* v_s_3669_){
_start:
{
uint8_t v_res_3670_; lean_object* v_r_3671_; 
v_res_3670_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v_s_3669_);
lean_dec_ref(v_s_3669_);
v_r_3671_ = lean_box(v_res_3670_);
return v_r_3671_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(lean_object* v_s_3672_, lean_object* v_pos_3673_){
_start:
{
lean_object* v_str_3674_; lean_object* v_startInclusive_3675_; lean_object* v_endExclusive_3676_; lean_object* v___x_3677_; lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v_decide_3688_; 
v_str_3674_ = lean_ctor_get(v_s_3672_, 0);
v_startInclusive_3675_ = lean_ctor_get(v_s_3672_, 1);
v_endExclusive_3676_ = lean_ctor_get(v_s_3672_, 2);
v___x_3677_ = lean_nat_add(v_startInclusive_3675_, v_pos_3673_);
v___x_3686_ = lean_unsigned_to_nat(0u);
v___x_3687_ = lean_nat_sub(v_endExclusive_3676_, v___x_3677_);
v_decide_3688_ = lean_nat_dec_eq(v___x_3686_, v___x_3687_);
lean_dec(v___x_3687_);
if (v_decide_3688_ == 0)
{
uint32_t v___x_3689_; uint32_t v___x_3711_; uint8_t v___x_3712_; 
v___x_3689_ = lean_string_utf8_get_fast(v_str_3674_, v___x_3677_);
v___x_3711_ = 65;
v___x_3712_ = lean_uint32_dec_le(v___x_3711_, v___x_3689_);
if (v___x_3712_ == 0)
{
goto v___jp_3706_;
}
else
{
uint32_t v___x_3713_; uint8_t v___x_3714_; 
v___x_3713_ = 90;
v___x_3714_ = lean_uint32_dec_le(v___x_3689_, v___x_3713_);
if (v___x_3714_ == 0)
{
goto v___jp_3706_;
}
else
{
goto v___jp_3678_;
}
}
v___jp_3690_:
{
uint32_t v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = 95;
v___x_3692_ = lean_uint32_dec_eq(v___x_3689_, v___x_3691_);
if (v___x_3692_ == 0)
{
uint32_t v___x_3693_; uint8_t v___x_3694_; 
v___x_3693_ = 39;
v___x_3694_ = lean_uint32_dec_eq(v___x_3689_, v___x_3693_);
if (v___x_3694_ == 0)
{
uint32_t v___x_3695_; uint8_t v___x_3696_; 
v___x_3695_ = 33;
v___x_3696_ = lean_uint32_dec_eq(v___x_3689_, v___x_3695_);
if (v___x_3696_ == 0)
{
uint32_t v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = 63;
v___x_3698_ = lean_uint32_dec_eq(v___x_3689_, v___x_3697_);
if (v___x_3698_ == 0)
{
uint8_t v___x_3699_; 
v___x_3699_ = l_Lean_isLetterLike(v___x_3689_);
if (v___x_3699_ == 0)
{
uint8_t v___x_3700_; 
v___x_3700_ = l_Lean_isSubScriptAlnum(v___x_3689_);
if (v___x_3700_ == 0)
{
lean_dec(v___x_3677_);
return v_pos_3673_;
}
else
{
goto v___jp_3678_;
}
}
else
{
goto v___jp_3678_;
}
}
else
{
goto v___jp_3678_;
}
}
else
{
goto v___jp_3678_;
}
}
else
{
goto v___jp_3678_;
}
}
else
{
goto v___jp_3678_;
}
}
v___jp_3701_:
{
uint32_t v___x_3702_; uint8_t v___x_3703_; 
v___x_3702_ = 48;
v___x_3703_ = lean_uint32_dec_le(v___x_3702_, v___x_3689_);
if (v___x_3703_ == 0)
{
goto v___jp_3690_;
}
else
{
uint32_t v___x_3704_; uint8_t v___x_3705_; 
v___x_3704_ = 57;
v___x_3705_ = lean_uint32_dec_le(v___x_3689_, v___x_3704_);
if (v___x_3705_ == 0)
{
goto v___jp_3690_;
}
else
{
goto v___jp_3678_;
}
}
}
v___jp_3706_:
{
uint32_t v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = 97;
v___x_3708_ = lean_uint32_dec_le(v___x_3707_, v___x_3689_);
if (v___x_3708_ == 0)
{
goto v___jp_3701_;
}
else
{
uint32_t v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = 122;
v___x_3710_ = lean_uint32_dec_le(v___x_3689_, v___x_3709_);
if (v___x_3710_ == 0)
{
goto v___jp_3701_;
}
else
{
goto v___jp_3678_;
}
}
}
}
else
{
lean_dec(v___x_3677_);
return v_pos_3673_;
}
v___jp_3678_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3679_ = lean_string_utf8_next_fast(v_str_3674_, v___x_3677_);
v___x_3680_ = lean_nat_sub(v___x_3679_, v___x_3677_);
lean_dec(v___x_3677_);
v___x_3681_ = lean_nat_add(v_pos_3673_, v___x_3680_);
lean_dec(v___x_3680_);
v___x_3682_ = lean_unsigned_to_nat(1u);
v___x_3683_ = lean_nat_add(v_pos_3673_, v___x_3682_);
v___x_3684_ = lean_nat_dec_le(v___x_3683_, v___x_3681_);
lean_dec(v___x_3683_);
if (v___x_3684_ == 0)
{
lean_dec(v___x_3681_);
return v_pos_3673_;
}
else
{
lean_dec(v_pos_3673_);
v_pos_3673_ = v___x_3681_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2___boxed(lean_object* v_s_3715_, lean_object* v_pos_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v_s_3715_, v_pos_3716_);
lean_dec_ref(v_s_3715_);
return v_res_3717_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__0(void){
_start:
{
uint32_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = l_Lean_idBeginEscape;
v___x_3719_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3720_ = lean_string_push(v___x_3719_, v___x_3718_);
return v___x_3720_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__1(void){
_start:
{
uint32_t v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = l_Lean_idEndEscape;
v___x_3722_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3723_ = lean_string_push(v___x_3722_, v___x_3721_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object* v_stx_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; uint8_t v___y_3731_; lean_object* v___x_3734_; lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3734_ = l_Lean_Syntax_getNumArgs(v_stx_3724_);
v___x_3735_ = lean_unsigned_to_nat(2u);
v___x_3736_ = lean_nat_dec_eq(v___x_3734_, v___x_3735_);
lean_dec(v___x_3734_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v_a_3726_);
return v___x_3738_;
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_unsigned_to_nat(0u);
v___x_3740_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3724_, v___x_3739_, v_a_3726_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v_a_3742_; lean_object* v___x_3743_; lean_object* v___y_3745_; lean_object* v___y_3780_; lean_object* v_startInclusive_3781_; lean_object* v_endExclusive_3782_; uint32_t v___y_3802_; uint32_t v___y_3807_; uint32_t v___y_3813_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
v_a_3742_ = lean_ctor_get(v___x_3740_, 1);
lean_inc(v_a_3742_);
lean_dec_ref_known(v___x_3740_, 2);
v___x_3743_ = l_Lean_Syntax_getAtomVal(v_a_3741_);
v___x_3829_ = lean_string_utf8_byte_size(v___x_3743_);
v___x_3830_ = lean_nat_dec_lt(v___x_3739_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3831_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3832_ = lean_string_append(v___x_3831_, v___x_3743_);
v___x_3833_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3834_ = lean_string_append(v___x_3832_, v___x_3833_);
v___x_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
v___y_3745_ = v___x_3835_;
goto v___jp_3744_;
}
else
{
uint8_t v_c_3836_; uint8_t v___x_3845_; uint8_t v___x_3846_; 
v_c_3836_ = lean_string_get_byte_fast(v___x_3743_, v___x_3739_);
v___x_3845_ = 97;
v___x_3846_ = lean_uint8_dec_le(v___x_3845_, v_c_3836_);
if (v___x_3846_ == 0)
{
goto v___jp_3840_;
}
else
{
uint8_t v___x_3847_; uint8_t v___x_3848_; 
v___x_3847_ = 122;
v___x_3848_ = lean_uint8_dec_le(v_c_3836_, v___x_3847_);
if (v___x_3848_ == 0)
{
goto v___jp_3840_;
}
else
{
goto v___jp_3825_;
}
}
v___jp_3837_:
{
uint8_t v___x_3838_; uint8_t v___x_3839_; 
v___x_3838_ = 95;
v___x_3839_ = lean_uint8_dec_eq(v_c_3836_, v___x_3838_);
if (v___x_3839_ == 0)
{
goto v___jp_3818_;
}
else
{
goto v___jp_3825_;
}
}
v___jp_3840_:
{
uint8_t v___x_3841_; uint8_t v___x_3842_; 
v___x_3841_ = 65;
v___x_3842_ = lean_uint8_dec_le(v___x_3841_, v_c_3836_);
if (v___x_3842_ == 0)
{
goto v___jp_3837_;
}
else
{
uint8_t v___x_3843_; uint8_t v___x_3844_; 
v___x_3843_ = 90;
v___x_3844_ = lean_uint8_dec_le(v_c_3836_, v___x_3843_);
if (v___x_3844_ == 0)
{
goto v___jp_3837_;
}
else
{
goto v___jp_3825_;
}
}
}
}
v___jp_3744_:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Fmt_fmt(v_a_3741_, v_a_3725_, v_a_3742_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v_a_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
v_a_3748_ = lean_ctor_get(v___x_3746_, 1);
lean_inc(v_a_3748_);
lean_dec_ref_known(v___x_3746_, 2);
v___x_3749_ = lean_unsigned_to_nat(1u);
v___x_3750_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3724_, v___x_3749_, v_a_3748_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v_a_3752_; lean_object* v___x_3753_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
v_a_3752_ = lean_ctor_get(v___x_3750_, 1);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3750_, 2);
v___x_3753_ = l_Lean_Fmt_fmt(v_a_3751_, v_a_3725_, v_a_3752_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v_a_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
v_a_3755_ = lean_ctor_get(v___x_3753_, 1);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3753_, 2);
v___x_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3743_);
v___x_3757_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3745_, v___x_3756_);
lean_dec_ref_known(v___x_3756_, 1);
lean_dec(v___y_3745_);
if (v___x_3757_ == 0)
{
uint8_t v___x_3758_; 
v___x_3758_ = 1;
v___y_3728_ = v_a_3754_;
v___y_3729_ = v_a_3755_;
v___y_3730_ = v_a_3747_;
v___y_3731_ = v___x_3758_;
goto v___jp_3727_;
}
else
{
uint8_t v___x_3759_; 
v___x_3759_ = 2;
v___y_3728_ = v_a_3754_;
v___y_3729_ = v_a_3755_;
v___y_3730_ = v_a_3747_;
v___y_3731_ = v___x_3759_;
goto v___jp_3727_;
}
}
else
{
lean_dec(v_a_3747_);
lean_dec(v___y_3745_);
lean_dec_ref(v___x_3743_);
return v___x_3753_;
}
}
else
{
lean_object* v_a_3760_; lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3747_);
lean_dec(v___y_3745_);
lean_dec_ref(v___x_3743_);
v_a_3760_ = lean_ctor_get(v___x_3750_, 0);
v_a_3761_ = lean_ctor_get(v___x_3750_, 1);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3750_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_inc(v_a_3760_);
lean_dec(v___x_3750_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3760_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_dec(v___y_3745_);
lean_dec_ref(v___x_3743_);
return v___x_3746_;
}
}
v___jp_3769_:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3770_ = lean_string_utf8_byte_size(v___x_3743_);
lean_inc_ref(v___x_3743_);
v___x_3771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3743_);
lean_ctor_set(v___x_3771_, 1, v___x_3739_);
lean_ctor_set(v___x_3771_, 2, v___x_3770_);
v___x_3772_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3771_);
lean_dec_ref_known(v___x_3771_, 3);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3773_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3774_ = lean_string_append(v___x_3773_, v___x_3743_);
v___x_3775_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3776_ = lean_string_append(v___x_3774_, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
v___y_3745_ = v___x_3777_;
goto v___jp_3744_;
}
else
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_box(0);
v___y_3745_ = v___x_3778_;
goto v___jp_3744_;
}
}
v___jp_3779_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v_decide_3785_; 
v___x_3783_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3780_, v___x_3739_);
lean_dec_ref(v___y_3780_);
v___x_3784_ = lean_nat_sub(v_endExclusive_3782_, v_startInclusive_3781_);
lean_dec(v_startInclusive_3781_);
lean_dec(v_endExclusive_3782_);
v_decide_3785_ = lean_nat_dec_eq(v___x_3783_, v___x_3784_);
lean_dec(v___x_3784_);
lean_dec(v___x_3783_);
if (v_decide_3785_ == 0)
{
goto v___jp_3769_;
}
else
{
lean_object* v___x_3786_; 
lean_inc_ref(v___x_3743_);
v___x_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3743_);
v___y_3745_ = v___x_3786_;
goto v___jp_3744_;
}
}
v___jp_3787_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v_startInclusive_3790_; lean_object* v_endExclusive_3791_; 
v___x_3788_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3789_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3788_);
v_startInclusive_3790_ = lean_ctor_get(v___x_3789_, 1);
lean_inc(v_startInclusive_3790_);
v_endExclusive_3791_ = lean_ctor_get(v___x_3789_, 2);
lean_inc(v_endExclusive_3791_);
v___y_3780_ = v___x_3789_;
v_startInclusive_3781_ = v_startInclusive_3790_;
v_endExclusive_3782_ = v_endExclusive_3791_;
goto v___jp_3779_;
}
v___jp_3792_:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; 
v___x_3793_ = lean_string_utf8_byte_size(v___x_3743_);
lean_inc_ref(v___x_3743_);
v___x_3794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3743_);
lean_ctor_set(v___x_3794_, 1, v___x_3739_);
lean_ctor_set(v___x_3794_, 2, v___x_3793_);
v___x_3795_ = lean_unsigned_to_nat(1u);
v___x_3796_ = l_Substring_Raw_nextn(v___x_3794_, v___x_3795_, v___x_3739_);
lean_dec_ref_known(v___x_3794_, 3);
v___x_3797_ = lean_string_is_valid_pos(v___x_3743_, v___x_3796_);
if (v___x_3797_ == 0)
{
lean_dec(v___x_3796_);
goto v___jp_3787_;
}
else
{
uint8_t v___x_3798_; 
v___x_3798_ = lean_string_is_valid_pos(v___x_3743_, v___x_3793_);
if (v___x_3798_ == 0)
{
lean_dec(v___x_3796_);
goto v___jp_3787_;
}
else
{
uint8_t v___x_3799_; 
v___x_3799_ = lean_nat_dec_le(v___x_3796_, v___x_3793_);
if (v___x_3799_ == 0)
{
lean_dec(v___x_3796_);
goto v___jp_3787_;
}
else
{
lean_object* v___x_3800_; 
lean_inc(v___x_3796_);
lean_inc_ref(v___x_3743_);
v___x_3800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3743_);
lean_ctor_set(v___x_3800_, 1, v___x_3796_);
lean_ctor_set(v___x_3800_, 2, v___x_3793_);
v___y_3780_ = v___x_3800_;
v_startInclusive_3781_ = v___x_3796_;
v_endExclusive_3782_ = v___x_3793_;
goto v___jp_3779_;
}
}
}
}
v___jp_3801_:
{
uint32_t v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = 95;
v___x_3804_ = lean_uint32_dec_eq(v___y_3802_, v___x_3803_);
if (v___x_3804_ == 0)
{
uint8_t v___x_3805_; 
v___x_3805_ = l_Lean_isLetterLike(v___y_3802_);
if (v___x_3805_ == 0)
{
goto v___jp_3769_;
}
else
{
goto v___jp_3792_;
}
}
else
{
goto v___jp_3792_;
}
}
v___jp_3806_:
{
uint32_t v___x_3808_; uint8_t v___x_3809_; 
v___x_3808_ = 97;
v___x_3809_ = lean_uint32_dec_le(v___x_3808_, v___y_3807_);
if (v___x_3809_ == 0)
{
v___y_3802_ = v___y_3807_;
goto v___jp_3801_;
}
else
{
uint32_t v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = 122;
v___x_3811_ = lean_uint32_dec_le(v___y_3807_, v___x_3810_);
if (v___x_3811_ == 0)
{
v___y_3802_ = v___y_3807_;
goto v___jp_3801_;
}
else
{
goto v___jp_3792_;
}
}
}
v___jp_3812_:
{
uint32_t v___x_3814_; uint8_t v___x_3815_; 
v___x_3814_ = 65;
v___x_3815_ = lean_uint32_dec_le(v___x_3814_, v___y_3813_);
if (v___x_3815_ == 0)
{
v___y_3807_ = v___y_3813_;
goto v___jp_3806_;
}
else
{
uint32_t v___x_3816_; uint8_t v___x_3817_; 
v___x_3816_ = 90;
v___x_3817_ = lean_uint32_dec_le(v___y_3813_, v___x_3816_);
if (v___x_3817_ == 0)
{
v___y_3807_ = v___y_3813_;
goto v___jp_3806_;
}
else
{
goto v___jp_3792_;
}
}
}
v___jp_3818_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = lean_string_utf8_byte_size(v___x_3743_);
lean_inc_ref(v___x_3743_);
v___x_3820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3743_);
lean_ctor_set(v___x_3820_, 1, v___x_3739_);
lean_ctor_set(v___x_3820_, 2, v___x_3819_);
v___x_3821_ = l_String_Slice_Pos_get_x3f(v___x_3820_, v___x_3739_);
lean_dec_ref_known(v___x_3820_, 3);
if (lean_obj_tag(v___x_3821_) == 0)
{
uint32_t v___x_3822_; 
v___x_3822_ = 65;
v___y_3813_ = v___x_3822_;
goto v___jp_3812_;
}
else
{
lean_object* v_val_3823_; uint32_t v___x_3824_; 
v_val_3823_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_val_3823_);
lean_dec_ref_known(v___x_3821_, 1);
v___x_3824_ = lean_unbox_uint32(v_val_3823_);
lean_dec(v_val_3823_);
v___y_3813_ = v___x_3824_;
goto v___jp_3812_;
}
}
v___jp_3825_:
{
lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = lean_unsigned_to_nat(1u);
v___x_3827_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3743_, v___x_3826_);
if (v___x_3827_ == 0)
{
goto v___jp_3818_;
}
else
{
lean_object* v___x_3828_; 
lean_inc_ref(v___x_3743_);
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3743_);
v___y_3745_ = v___x_3828_;
goto v___jp_3744_;
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
v_a_3849_ = lean_ctor_get(v___x_3740_, 0);
v_a_3850_ = lean_ctor_get(v___x_3740_, 1);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3740_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_inc(v_a_3849_);
lean_dec(v___x_3740_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3849_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
v___jp_3727_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_3730_, v___y_3728_, v___y_3731_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v___y_3729_);
return v___x_3733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object* v_stx_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_Fmt_fmtPrefixOperator(v_stx_3858_, v_a_3859_, v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_stx_3858_);
return v_res_3861_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(lean_object* v_s_3862_, lean_object* v_inst_3863_, lean_object* v_R_3864_, lean_object* v_a_3865_, uint8_t v_b_3866_, lean_object* v_c_3867_){
_start:
{
uint8_t v___x_3868_; 
v___x_3868_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3862_, v_a_3865_, v_b_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___boxed(lean_object* v_s_3869_, lean_object* v_inst_3870_, lean_object* v_R_3871_, lean_object* v_a_3872_, lean_object* v_b_3873_, lean_object* v_c_3874_){
_start:
{
uint8_t v_b_boxed_3875_; uint8_t v_res_3876_; lean_object* v_r_3877_; 
v_b_boxed_3875_ = lean_unbox(v_b_3873_);
v_res_3876_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(v_s_3869_, v_inst_3870_, v_R_3871_, v_a_3872_, v_b_boxed_3875_, v_c_3874_);
lean_dec_ref(v_s_3869_);
v_r_3877_ = lean_box(v_res_3876_);
return v_r_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object* v_stx_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3881_ = l_Lean_Syntax_getNumArgs(v_stx_3878_);
v___x_3882_ = lean_unsigned_to_nat(2u);
v___x_3883_ = lean_nat_dec_eq(v___x_3881_, v___x_3882_);
lean_dec(v___x_3881_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
lean_ctor_set(v___x_3885_, 1, v_a_3880_);
return v___x_3885_;
}
else
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_unsigned_to_nat(0u);
v___x_3887_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3878_, v___x_3886_, v_a_3880_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v_a_3889_; lean_object* v___x_3890_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
v_a_3889_ = lean_ctor_get(v___x_3887_, 1);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3887_, 2);
v___x_3890_ = l_Lean_Fmt_fmt(v_a_3888_, v_a_3879_, v_a_3889_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_4005_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_a_3892_ = lean_ctor_get(v___x_3890_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3894_ = v___x_3890_;
v_isShared_3895_ = v_isSharedCheck_4005_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_4005_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___y_3897_; lean_object* v___y_3898_; uint8_t v___y_3899_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_unsigned_to_nat(1u);
v___x_3905_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3878_, v___x_3904_, v_a_3892_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v_a_3907_; lean_object* v___x_3908_; lean_object* v___y_3910_; lean_object* v___y_3929_; lean_object* v_startInclusive_3930_; lean_object* v_endExclusive_3931_; uint32_t v___y_3950_; uint32_t v___y_3955_; uint32_t v___y_3961_; lean_object* v___x_3976_; uint8_t v___x_3977_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
v_a_3907_ = lean_ctor_get(v___x_3905_, 1);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3905_, 2);
v___x_3908_ = l_Lean_Syntax_getAtomVal(v_a_3906_);
v___x_3976_ = lean_string_utf8_byte_size(v___x_3908_);
v___x_3977_ = lean_nat_dec_lt(v___x_3886_, v___x_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3978_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3979_ = lean_string_append(v___x_3978_, v___x_3908_);
v___x_3980_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3981_ = lean_string_append(v___x_3979_, v___x_3980_);
v___x_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3981_);
v___y_3910_ = v___x_3982_;
goto v___jp_3909_;
}
else
{
uint8_t v_c_3983_; uint8_t v___x_3992_; uint8_t v___x_3993_; 
v_c_3983_ = lean_string_get_byte_fast(v___x_3908_, v___x_3886_);
v___x_3992_ = 97;
v___x_3993_ = lean_uint8_dec_le(v___x_3992_, v_c_3983_);
if (v___x_3993_ == 0)
{
goto v___jp_3987_;
}
else
{
uint8_t v___x_3994_; uint8_t v___x_3995_; 
v___x_3994_ = 122;
v___x_3995_ = lean_uint8_dec_le(v_c_3983_, v___x_3994_);
if (v___x_3995_ == 0)
{
goto v___jp_3987_;
}
else
{
goto v___jp_3973_;
}
}
v___jp_3984_:
{
uint8_t v___x_3985_; uint8_t v___x_3986_; 
v___x_3985_ = 95;
v___x_3986_ = lean_uint8_dec_eq(v_c_3983_, v___x_3985_);
if (v___x_3986_ == 0)
{
goto v___jp_3966_;
}
else
{
goto v___jp_3973_;
}
}
v___jp_3987_:
{
uint8_t v___x_3988_; uint8_t v___x_3989_; 
v___x_3988_ = 65;
v___x_3989_ = lean_uint8_dec_le(v___x_3988_, v_c_3983_);
if (v___x_3989_ == 0)
{
goto v___jp_3984_;
}
else
{
uint8_t v___x_3990_; uint8_t v___x_3991_; 
v___x_3990_ = 90;
v___x_3991_ = lean_uint8_dec_le(v_c_3983_, v___x_3990_);
if (v___x_3991_ == 0)
{
goto v___jp_3984_;
}
else
{
goto v___jp_3973_;
}
}
}
}
v___jp_3909_:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_Fmt_fmt(v_a_3906_, v_a_3879_, v_a_3907_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v_a_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
v_a_3913_ = lean_ctor_get(v___x_3911_, 1);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3911_, 2);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3908_);
v___x_3915_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3910_, v___x_3914_);
lean_dec_ref_known(v___x_3914_, 1);
lean_dec(v___y_3910_);
if (v___x_3915_ == 0)
{
uint8_t v___x_3916_; 
v___x_3916_ = 0;
v___y_3897_ = v_a_3913_;
v___y_3898_ = v_a_3912_;
v___y_3899_ = v___x_3916_;
goto v___jp_3896_;
}
else
{
uint8_t v___x_3917_; 
v___x_3917_ = 1;
v___y_3897_ = v_a_3913_;
v___y_3898_ = v_a_3912_;
v___y_3899_ = v___x_3917_;
goto v___jp_3896_;
}
}
else
{
lean_dec(v___y_3910_);
lean_dec_ref(v___x_3908_);
lean_del_object(v___x_3894_);
lean_dec(v_a_3891_);
return v___x_3911_;
}
}
v___jp_3918_:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3919_ = lean_string_utf8_byte_size(v___x_3908_);
lean_inc_ref(v___x_3908_);
v___x_3920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3908_);
lean_ctor_set(v___x_3920_, 1, v___x_3886_);
lean_ctor_set(v___x_3920_, 2, v___x_3919_);
v___x_3921_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3920_);
lean_dec_ref_known(v___x_3920_, 3);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3922_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3923_ = lean_string_append(v___x_3922_, v___x_3908_);
v___x_3924_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3925_ = lean_string_append(v___x_3923_, v___x_3924_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
v___y_3910_ = v___x_3926_;
goto v___jp_3909_;
}
else
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_box(0);
v___y_3910_ = v___x_3927_;
goto v___jp_3909_;
}
}
v___jp_3928_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v_decide_3934_; 
v___x_3932_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3929_, v___x_3886_);
lean_dec_ref(v___y_3929_);
v___x_3933_ = lean_nat_sub(v_endExclusive_3931_, v_startInclusive_3930_);
lean_dec(v_startInclusive_3930_);
lean_dec(v_endExclusive_3931_);
v_decide_3934_ = lean_nat_dec_eq(v___x_3932_, v___x_3933_);
lean_dec(v___x_3933_);
lean_dec(v___x_3932_);
if (v_decide_3934_ == 0)
{
goto v___jp_3918_;
}
else
{
lean_object* v___x_3935_; 
lean_inc_ref(v___x_3908_);
v___x_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3908_);
v___y_3910_ = v___x_3935_;
goto v___jp_3909_;
}
}
v___jp_3936_:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v_startInclusive_3939_; lean_object* v_endExclusive_3940_; 
v___x_3937_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3938_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3937_);
v_startInclusive_3939_ = lean_ctor_get(v___x_3938_, 1);
lean_inc(v_startInclusive_3939_);
v_endExclusive_3940_ = lean_ctor_get(v___x_3938_, 2);
lean_inc(v_endExclusive_3940_);
v___y_3929_ = v___x_3938_;
v_startInclusive_3930_ = v_startInclusive_3939_;
v_endExclusive_3931_ = v_endExclusive_3940_;
goto v___jp_3928_;
}
v___jp_3941_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3942_ = lean_string_utf8_byte_size(v___x_3908_);
lean_inc_ref(v___x_3908_);
v___x_3943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3908_);
lean_ctor_set(v___x_3943_, 1, v___x_3886_);
lean_ctor_set(v___x_3943_, 2, v___x_3942_);
v___x_3944_ = l_Substring_Raw_nextn(v___x_3943_, v___x_3904_, v___x_3886_);
lean_dec_ref_known(v___x_3943_, 3);
v___x_3945_ = lean_string_is_valid_pos(v___x_3908_, v___x_3944_);
if (v___x_3945_ == 0)
{
lean_dec(v___x_3944_);
goto v___jp_3936_;
}
else
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_string_is_valid_pos(v___x_3908_, v___x_3942_);
if (v___x_3946_ == 0)
{
lean_dec(v___x_3944_);
goto v___jp_3936_;
}
else
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_nat_dec_le(v___x_3944_, v___x_3942_);
if (v___x_3947_ == 0)
{
lean_dec(v___x_3944_);
goto v___jp_3936_;
}
else
{
lean_object* v___x_3948_; 
lean_inc(v___x_3944_);
lean_inc_ref(v___x_3908_);
v___x_3948_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3948_, 0, v___x_3908_);
lean_ctor_set(v___x_3948_, 1, v___x_3944_);
lean_ctor_set(v___x_3948_, 2, v___x_3942_);
v___y_3929_ = v___x_3948_;
v_startInclusive_3930_ = v___x_3944_;
v_endExclusive_3931_ = v___x_3942_;
goto v___jp_3928_;
}
}
}
}
v___jp_3949_:
{
uint32_t v___x_3951_; uint8_t v___x_3952_; 
v___x_3951_ = 95;
v___x_3952_ = lean_uint32_dec_eq(v___y_3950_, v___x_3951_);
if (v___x_3952_ == 0)
{
uint8_t v___x_3953_; 
v___x_3953_ = l_Lean_isLetterLike(v___y_3950_);
if (v___x_3953_ == 0)
{
goto v___jp_3918_;
}
else
{
goto v___jp_3941_;
}
}
else
{
goto v___jp_3941_;
}
}
v___jp_3954_:
{
uint32_t v___x_3956_; uint8_t v___x_3957_; 
v___x_3956_ = 97;
v___x_3957_ = lean_uint32_dec_le(v___x_3956_, v___y_3955_);
if (v___x_3957_ == 0)
{
v___y_3950_ = v___y_3955_;
goto v___jp_3949_;
}
else
{
uint32_t v___x_3958_; uint8_t v___x_3959_; 
v___x_3958_ = 122;
v___x_3959_ = lean_uint32_dec_le(v___y_3955_, v___x_3958_);
if (v___x_3959_ == 0)
{
v___y_3950_ = v___y_3955_;
goto v___jp_3949_;
}
else
{
goto v___jp_3941_;
}
}
}
v___jp_3960_:
{
uint32_t v___x_3962_; uint8_t v___x_3963_; 
v___x_3962_ = 65;
v___x_3963_ = lean_uint32_dec_le(v___x_3962_, v___y_3961_);
if (v___x_3963_ == 0)
{
v___y_3955_ = v___y_3961_;
goto v___jp_3954_;
}
else
{
uint32_t v___x_3964_; uint8_t v___x_3965_; 
v___x_3964_ = 90;
v___x_3965_ = lean_uint32_dec_le(v___y_3961_, v___x_3964_);
if (v___x_3965_ == 0)
{
v___y_3955_ = v___y_3961_;
goto v___jp_3954_;
}
else
{
goto v___jp_3941_;
}
}
}
v___jp_3966_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = lean_string_utf8_byte_size(v___x_3908_);
lean_inc_ref(v___x_3908_);
v___x_3968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3908_);
lean_ctor_set(v___x_3968_, 1, v___x_3886_);
lean_ctor_set(v___x_3968_, 2, v___x_3967_);
v___x_3969_ = l_String_Slice_Pos_get_x3f(v___x_3968_, v___x_3886_);
lean_dec_ref_known(v___x_3968_, 3);
if (lean_obj_tag(v___x_3969_) == 0)
{
uint32_t v___x_3970_; 
v___x_3970_ = 65;
v___y_3961_ = v___x_3970_;
goto v___jp_3960_;
}
else
{
lean_object* v_val_3971_; uint32_t v___x_3972_; 
v_val_3971_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_val_3971_);
lean_dec_ref_known(v___x_3969_, 1);
v___x_3972_ = lean_unbox_uint32(v_val_3971_);
lean_dec(v_val_3971_);
v___y_3961_ = v___x_3972_;
goto v___jp_3960_;
}
}
v___jp_3973_:
{
uint8_t v___x_3974_; 
v___x_3974_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3908_, v___x_3904_);
if (v___x_3974_ == 0)
{
goto v___jp_3966_;
}
else
{
lean_object* v___x_3975_; 
lean_inc_ref(v___x_3908_);
v___x_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3908_);
v___y_3910_ = v___x_3975_;
goto v___jp_3909_;
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_del_object(v___x_3894_);
lean_dec(v_a_3891_);
v_a_3996_ = lean_ctor_get(v___x_3905_, 0);
v_a_3997_ = lean_ctor_get(v___x_3905_, 1);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3905_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_inc(v_a_3996_);
lean_dec(v___x_3905_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3996_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
v___jp_3896_:
{
lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3900_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_3891_, v___y_3898_, v___y_3899_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 1, v___y_3897_);
lean_ctor_set(v___x_3894_, 0, v___x_3900_);
v___x_3902_ = v___x_3894_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v___y_3897_);
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
return v___x_3890_;
}
}
else
{
lean_object* v_a_4006_; lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
v_a_4006_ = lean_ctor_get(v___x_3887_, 0);
v_a_4007_ = lean_ctor_get(v___x_3887_, 1);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3887_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_inc(v_a_4006_);
lean_dec(v___x_3887_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4006_);
lean_ctor_set(v_reuseFailAlloc_4013_, 1, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object* v_stx_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Fmt_fmtPostfixOperator(v_stx_4015_, v_a_4016_, v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_stx_4015_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t v_sz_4019_, size_t v_i_4020_, lean_object* v_bs_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
uint8_t v___x_4024_; 
v___x_4024_ = lean_usize_dec_lt(v_i_4020_, v_sz_4019_);
if (v___x_4024_ == 0)
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v_bs_4021_);
lean_ctor_set(v___x_4025_, 1, v___y_4023_);
return v___x_4025_;
}
else
{
lean_object* v_v_4026_; lean_object* v_elseTk_4027_; lean_object* v_ifTk_4028_; lean_object* v_cond_4029_; lean_object* v_thenTk_4030_; lean_object* v_body_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4092_; 
v_v_4026_ = lean_array_uget(v_bs_4021_, v_i_4020_);
v_elseTk_4027_ = lean_ctor_get(v_v_4026_, 0);
v_ifTk_4028_ = lean_ctor_get(v_v_4026_, 1);
v_cond_4029_ = lean_ctor_get(v_v_4026_, 2);
v_thenTk_4030_ = lean_ctor_get(v_v_4026_, 3);
v_body_4031_ = lean_ctor_get(v_v_4026_, 4);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_v_4026_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4033_ = v_v_4026_;
v_isShared_4034_ = v_isSharedCheck_4092_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_body_4031_);
lean_inc(v_thenTk_4030_);
lean_inc(v_cond_4029_);
lean_inc(v_ifTk_4028_);
lean_inc(v_elseTk_4027_);
lean_dec(v_v_4026_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4092_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4035_; 
v___x_4035_ = l_Lean_Fmt_fmt(v_elseTk_4027_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_a_4037_; lean_object* v___x_4038_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
v_a_4037_ = lean_ctor_get(v___x_4035_, 1);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4035_, 2);
v___x_4038_ = l_Lean_Fmt_fmt(v_ifTk_4028_, v___y_4022_, v_a_4037_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v_a_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
v_a_4040_ = lean_ctor_get(v___x_4038_, 1);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4038_, 2);
v___x_4041_ = l_Lean_Fmt_fmt(v_thenTk_4030_, v___y_4022_, v_a_4040_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v_a_4043_; lean_object* v___x_4044_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
v_a_4043_ = lean_ctor_get(v___x_4041_, 1);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4041_, 2);
v___x_4044_ = l_Lean_Fmt_fmt(v_body_4031_, v___y_4022_, v_a_4043_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v_a_4046_; lean_object* v___x_4047_; lean_object* v_bs_x27_4048_; lean_object* v___x_4050_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
lean_inc(v_a_4045_);
v_a_4046_ = lean_ctor_get(v___x_4044_, 1);
lean_inc(v_a_4046_);
lean_dec_ref_known(v___x_4044_, 2);
v___x_4047_ = lean_unsigned_to_nat(0u);
v_bs_x27_4048_ = lean_array_uset(v_bs_4021_, v_i_4020_, v___x_4047_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 4, v_a_4045_);
lean_ctor_set(v___x_4033_, 3, v_a_4042_);
lean_ctor_set(v___x_4033_, 1, v_a_4039_);
lean_ctor_set(v___x_4033_, 0, v_a_4036_);
v___x_4050_ = v___x_4033_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4036_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v_a_4039_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v_cond_4029_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v_a_4042_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
size_t v___x_4051_; size_t v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_add(v_i_4020_, v___x_4051_);
v___x_4053_ = lean_array_uset(v_bs_x27_4048_, v_i_4020_, v___x_4050_);
v_i_4020_ = v___x_4052_;
v_bs_4021_ = v___x_4053_;
v___y_4023_ = v_a_4046_;
goto _start;
}
}
else
{
lean_object* v_a_4056_; lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec(v_a_4042_);
lean_dec(v_a_4039_);
lean_dec(v_a_4036_);
lean_del_object(v___x_4033_);
lean_dec_ref(v_cond_4029_);
lean_dec_ref(v_bs_4021_);
v_a_4056_ = lean_ctor_get(v___x_4044_, 0);
v_a_4057_ = lean_ctor_get(v___x_4044_, 1);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4044_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_inc(v_a_4056_);
lean_dec(v___x_4044_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4056_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
lean_dec(v_a_4039_);
lean_dec(v_a_4036_);
lean_del_object(v___x_4033_);
lean_dec(v_body_4031_);
lean_dec_ref(v_cond_4029_);
lean_dec_ref(v_bs_4021_);
v_a_4065_ = lean_ctor_get(v___x_4041_, 0);
v_a_4066_ = lean_ctor_get(v___x_4041_, 1);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4041_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_inc(v_a_4065_);
lean_dec(v___x_4041_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4065_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec(v_a_4036_);
lean_del_object(v___x_4033_);
lean_dec(v_body_4031_);
lean_dec(v_thenTk_4030_);
lean_dec_ref(v_cond_4029_);
lean_dec_ref(v_bs_4021_);
v_a_4074_ = lean_ctor_get(v___x_4038_, 0);
v_a_4075_ = lean_ctor_get(v___x_4038_, 1);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4038_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_inc(v_a_4074_);
lean_dec(v___x_4038_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4074_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_del_object(v___x_4033_);
lean_dec(v_body_4031_);
lean_dec(v_thenTk_4030_);
lean_dec_ref(v_cond_4029_);
lean_dec(v_ifTk_4028_);
lean_dec_ref(v_bs_4021_);
v_a_4083_ = lean_ctor_get(v___x_4035_, 0);
v_a_4084_ = lean_ctor_get(v___x_4035_, 1);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4035_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_inc(v_a_4083_);
lean_dec(v___x_4035_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4083_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object* v_sz_4093_, lean_object* v_i_4094_, lean_object* v_bs_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
size_t v_sz_boxed_4098_; size_t v_i_boxed_4099_; lean_object* v_res_4100_; 
v_sz_boxed_4098_ = lean_unbox_usize(v_sz_4093_);
lean_dec(v_sz_4093_);
v_i_boxed_4099_ = lean_unbox_usize(v_i_4094_);
lean_dec(v_i_4094_);
v_res_4100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_boxed_4098_, v_i_boxed_4099_, v_bs_4095_, v___y_4096_, v___y_4097_);
lean_dec_ref(v___y_4096_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object* v_a_4101_, lean_object* v_x_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4105_, 0, v_a_4101_);
v___x_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
lean_ctor_set(v___x_4106_, 1, v___y_4104_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object* v_a_4107_, lean_object* v_x_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4107_, v_x_4108_, v___y_4109_, v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec_ref(v_x_4108_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object* v___x_4112_, lean_object* v_val_4113_, lean_object* v_elseIfs_4114_, lean_object* v_ifTk_4115_, lean_object* v_cond_4116_, lean_object* v_thenTk_4117_, lean_object* v_thenBody_4118_, lean_object* v_a_4119_, lean_object* v_____r_4120_, lean_object* v_elseBody_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_inc(v_elseBody_4121_);
v___x_4124_ = l_Lean_Syntax_getKind(v_elseBody_4121_);
v___x_4125_ = l_Lean_Fmt_getConditionalFormatter_x3f(v___x_4112_, v___x_4124_);
lean_dec(v___x_4124_);
if (lean_obj_tag(v___x_4125_) == 1)
{
lean_object* v_val_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4186_; 
v_val_4126_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4186_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_val_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4186_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4130_; 
lean_inc_ref(v___y_4122_);
v___x_4130_ = lean_apply_3(v_val_4126_, v_elseBody_4121_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
if (lean_obj_tag(v_a_4131_) == 1)
{
lean_object* v_val_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4164_; 
lean_del_object(v___x_4128_);
lean_dec_ref(v_a_4119_);
v_val_4132_ = lean_ctor_get(v_a_4131_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_a_4131_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4134_ = v_a_4131_;
v_isShared_4135_ = v_isSharedCheck_4164_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_val_4132_);
lean_dec(v_a_4131_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4164_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4162_; 
v_a_4136_ = lean_ctor_get(v___x_4130_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4162_ == 0)
{
lean_object* v_unused_4163_; 
v_unused_4163_ = lean_ctor_get(v___x_4130_, 0);
lean_dec(v_unused_4163_);
v___x_4138_ = v___x_4130_;
v_isShared_4139_ = v_isSharedCheck_4162_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4130_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4162_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v_ifTk_4140_; lean_object* v_cond_4141_; lean_object* v_thenTk_4142_; lean_object* v_thenBody_4143_; lean_object* v_elseTk_x3f_4144_; lean_object* v_elseBody_x3f_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4160_; 
v_ifTk_4140_ = lean_ctor_get(v_val_4132_, 0);
v_cond_4141_ = lean_ctor_get(v_val_4132_, 1);
v_thenTk_4142_ = lean_ctor_get(v_val_4132_, 2);
v_thenBody_4143_ = lean_ctor_get(v_val_4132_, 3);
v_elseTk_x3f_4144_ = lean_ctor_get(v_val_4132_, 5);
v_elseBody_x3f_4145_ = lean_ctor_get(v_val_4132_, 6);
v_isSharedCheck_4160_ = !lean_is_exclusive(v_val_4132_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; 
v_unused_4161_ = lean_ctor_get(v_val_4132_, 4);
lean_dec(v_unused_4161_);
v___x_4147_ = v_val_4132_;
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_elseBody_x3f_4145_);
lean_inc(v_elseTk_x3f_4144_);
lean_inc(v_thenBody_4143_);
lean_inc(v_thenTk_4142_);
lean_inc(v_cond_4141_);
lean_inc(v_ifTk_4140_);
lean_dec(v_val_4132_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4160_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4149_, 0, v_val_4113_);
lean_ctor_set(v___x_4149_, 1, v_ifTk_4140_);
lean_ctor_set(v___x_4149_, 2, v_cond_4141_);
lean_ctor_set(v___x_4149_, 3, v_thenTk_4142_);
lean_ctor_set(v___x_4149_, 4, v_thenBody_4143_);
v___x_4150_ = lean_array_push(v_elseIfs_4114_, v___x_4149_);
if (v_isShared_4148_ == 0)
{
lean_ctor_set(v___x_4147_, 4, v___x_4150_);
lean_ctor_set(v___x_4147_, 3, v_thenBody_4118_);
lean_ctor_set(v___x_4147_, 2, v_thenTk_4117_);
lean_ctor_set(v___x_4147_, 1, v_cond_4116_);
lean_ctor_set(v___x_4147_, 0, v_ifTk_4115_);
v___x_4152_ = v___x_4147_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_ifTk_4115_);
lean_ctor_set(v_reuseFailAlloc_4159_, 1, v_cond_4116_);
lean_ctor_set(v_reuseFailAlloc_4159_, 2, v_thenTk_4117_);
lean_ctor_set(v_reuseFailAlloc_4159_, 3, v_thenBody_4118_);
lean_ctor_set(v_reuseFailAlloc_4159_, 4, v___x_4150_);
lean_ctor_set(v_reuseFailAlloc_4159_, 5, v_elseTk_x3f_4144_);
lean_ctor_set(v_reuseFailAlloc_4159_, 6, v_elseBody_x3f_4145_);
v___x_4152_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
lean_object* v___x_4154_; 
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 0, v___x_4152_);
v___x_4154_ = v___x_4134_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4152_);
v___x_4154_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4156_; 
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 0, v___x_4154_);
v___x_4156_ = v___x_4138_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4157_, 1, v_a_4136_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_a_4131_);
lean_dec(v_thenBody_4118_);
lean_dec(v_thenTk_4117_);
lean_dec_ref(v_cond_4116_);
lean_dec(v_ifTk_4115_);
lean_dec_ref(v_elseIfs_4114_);
lean_dec(v_val_4113_);
v_a_4165_ = lean_ctor_get(v___x_4130_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; 
v_unused_4176_ = lean_ctor_get(v___x_4130_, 0);
lean_dec(v_unused_4176_);
v___x_4167_ = v___x_4130_;
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4130_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4175_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 0);
lean_ctor_set(v___x_4128_, 0, v_a_4119_);
v___x_4170_ = v___x_4128_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4119_);
v___x_4170_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4172_; 
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4170_);
v___x_4172_ = v___x_4167_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_a_4165_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_del_object(v___x_4128_);
lean_dec_ref(v_a_4119_);
lean_dec(v_thenBody_4118_);
lean_dec(v_thenTk_4117_);
lean_dec_ref(v_cond_4116_);
lean_dec(v_ifTk_4115_);
lean_dec_ref(v_elseIfs_4114_);
lean_dec(v_val_4113_);
v_a_4177_ = lean_ctor_get(v___x_4130_, 0);
v_a_4178_ = lean_ctor_get(v___x_4130_, 1);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4130_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_inc(v_a_4177_);
lean_dec(v___x_4130_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4177_);
lean_ctor_set(v_reuseFailAlloc_4184_, 1, v_a_4178_);
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
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
lean_dec(v___x_4125_);
lean_dec(v_elseBody_4121_);
lean_dec(v_thenBody_4118_);
lean_dec(v_thenTk_4117_);
lean_dec_ref(v_cond_4116_);
lean_dec(v_ifTk_4115_);
lean_dec_ref(v_elseIfs_4114_);
lean_dec(v_val_4113_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_a_4119_);
v___x_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
lean_ctor_set(v___x_4188_, 1, v___y_4123_);
return v___x_4188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object* v___x_4189_, lean_object* v_val_4190_, lean_object* v_elseIfs_4191_, lean_object* v_ifTk_4192_, lean_object* v_cond_4193_, lean_object* v_thenTk_4194_, lean_object* v_thenBody_4195_, lean_object* v_a_4196_, lean_object* v_____r_4197_, lean_object* v_elseBody_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4189_, v_val_4190_, v_elseIfs_4191_, v_ifTk_4192_, v_cond_4193_, v_thenTk_4194_, v_thenBody_4195_, v_a_4196_, v_____r_4197_, v_elseBody_4198_, v___y_4199_, v___y_4200_);
lean_dec_ref(v___y_4199_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object* v___x_4216_, lean_object* v_a_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___y_4221_; lean_object* v_elseTk_x3f_4245_; 
v_elseTk_x3f_4245_ = lean_ctor_get(v_a_4217_, 5);
if (lean_obj_tag(v_elseTk_x3f_4245_) == 1)
{
lean_object* v_elseBody_x3f_4246_; 
v_elseBody_x3f_4246_ = lean_ctor_get(v_a_4217_, 6);
if (lean_obj_tag(v_elseBody_x3f_4246_) == 1)
{
lean_object* v_ifTk_4247_; lean_object* v_cond_4248_; lean_object* v_thenTk_4249_; lean_object* v_thenBody_4250_; lean_object* v_elseIfs_4251_; lean_object* v_val_4252_; lean_object* v_val_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v_ifTk_4247_ = lean_ctor_get(v_a_4217_, 0);
lean_inc(v_ifTk_4247_);
v_cond_4248_ = lean_ctor_get(v_a_4217_, 1);
lean_inc_ref(v_cond_4248_);
v_thenTk_4249_ = lean_ctor_get(v_a_4217_, 2);
lean_inc(v_thenTk_4249_);
v_thenBody_4250_ = lean_ctor_get(v_a_4217_, 3);
lean_inc(v_thenBody_4250_);
v_elseIfs_4251_ = lean_ctor_get(v_a_4217_, 4);
lean_inc_ref(v_elseIfs_4251_);
v_val_4252_ = lean_ctor_get(v_elseTk_x3f_4245_, 0);
lean_inc(v_val_4252_);
v_val_4253_ = lean_ctor_get(v_elseBody_x3f_4246_, 0);
v___x_4254_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3));
lean_inc(v_val_4253_);
v___x_4255_ = l_Lean_Syntax_isOfKind(v_val_4253_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_inc(v_val_4253_);
v___x_4256_ = lean_box(0);
lean_inc_ref(v___x_4216_);
v___x_4257_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4216_, v_val_4252_, v_elseIfs_4251_, v_ifTk_4247_, v_cond_4248_, v_thenTk_4249_, v_thenBody_4250_, v_a_4217_, v___x_4256_, v_val_4253_, v___y_4218_, v___y_4219_);
v___y_4221_ = v___x_4257_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = l_Lean_Syntax_getArg(v_val_4253_, v___x_4258_);
v___x_4260_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5));
lean_inc(v___x_4259_);
v___x_4261_ = l_Lean_Syntax_isOfKind(v___x_4259_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_inc(v_val_4253_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
lean_inc_ref(v___x_4216_);
v___x_4263_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4216_, v_val_4252_, v_elseIfs_4251_, v_ifTk_4247_, v_cond_4248_, v_thenTk_4249_, v_thenBody_4250_, v_a_4217_, v___x_4262_, v_val_4253_, v___y_4218_, v___y_4219_);
v___y_4221_ = v___x_4263_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; uint8_t v___x_4266_; 
v___x_4264_ = l_Lean_Syntax_getArg(v___x_4259_, v___x_4258_);
lean_dec(v___x_4259_);
v___x_4265_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4264_);
v___x_4266_ = l_Lean_Syntax_matchesNull(v___x_4264_, v___x_4265_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4267_; lean_object* v___x_4268_; 
lean_inc(v_val_4253_);
lean_dec(v___x_4264_);
v___x_4267_ = lean_box(0);
lean_inc_ref(v___x_4216_);
v___x_4268_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4216_, v_val_4252_, v_elseIfs_4251_, v_ifTk_4247_, v_cond_4248_, v_thenTk_4249_, v_thenBody_4250_, v_a_4217_, v___x_4267_, v_val_4253_, v___y_4218_, v___y_4219_);
v___y_4221_ = v___x_4268_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4269_ = l_Lean_Syntax_getArg(v___x_4264_, v___x_4258_);
lean_dec(v___x_4264_);
v___x_4270_ = lean_box(0);
lean_inc_ref(v___x_4216_);
v___x_4271_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4216_, v_val_4252_, v_elseIfs_4251_, v_ifTk_4247_, v_cond_4248_, v_thenTk_4249_, v_thenBody_4250_, v_a_4217_, v___x_4270_, v___x_4269_, v___y_4218_, v___y_4219_);
v___y_4221_ = v___x_4271_;
goto v___jp_4220_;
}
}
}
}
else
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_inc(v_elseBody_x3f_4246_);
lean_inc_ref(v_elseTk_x3f_4245_);
v___x_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4272_, 0, v_elseTk_x3f_4245_);
lean_ctor_set(v___x_4272_, 1, v_elseBody_x3f_4246_);
v___x_4273_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4217_, v___x_4272_, v___y_4218_, v___y_4219_);
lean_dec_ref_known(v___x_4272_, 2);
v___y_4221_ = v___x_4273_;
goto v___jp_4220_;
}
}
else
{
lean_object* v_elseBody_x3f_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v_elseBody_x3f_4274_ = lean_ctor_get(v_a_4217_, 6);
lean_inc(v_elseBody_x3f_4274_);
lean_inc(v_elseTk_x3f_4245_);
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v_elseTk_x3f_4245_);
lean_ctor_set(v___x_4275_, 1, v_elseBody_x3f_4274_);
v___x_4276_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4217_, v___x_4275_, v___y_4218_, v___y_4219_);
lean_dec_ref_known(v___x_4275_, 2);
v___y_4221_ = v___x_4276_;
goto v___jp_4220_;
}
v___jp_4220_:
{
if (lean_obj_tag(v___y_4221_) == 0)
{
lean_object* v_a_4222_; 
v_a_4222_ = lean_ctor_get(v___y_4221_, 0);
lean_inc(v_a_4222_);
if (lean_obj_tag(v_a_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4231_; 
lean_dec_ref(v___x_4216_);
v_a_4223_ = lean_ctor_get(v___y_4221_, 1);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___y_4221_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v___y_4221_, 0);
lean_dec(v_unused_4232_);
v___x_4225_ = v___y_4221_;
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___y_4221_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4231_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v_a_4227_; lean_object* v___x_4229_; 
v_a_4227_ = lean_ctor_get(v_a_4222_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v_a_4222_, 1);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v_a_4227_);
v___x_4229_ = v___x_4225_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4227_);
lean_ctor_set(v_reuseFailAlloc_4230_, 1, v_a_4223_);
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
lean_object* v_a_4233_; lean_object* v_a_4234_; 
v_a_4233_ = lean_ctor_get(v___y_4221_, 1);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___y_4221_, 2);
v_a_4234_ = lean_ctor_get(v_a_4222_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v_a_4222_, 1);
v_a_4217_ = v_a_4234_;
v___y_4219_ = v_a_4233_;
goto _start;
}
}
else
{
lean_object* v_a_4236_; lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v___x_4216_);
v_a_4236_ = lean_ctor_get(v___y_4221_, 0);
v_a_4237_ = lean_ctor_get(v___y_4221_, 1);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___y_4221_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___y_4221_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_inc(v_a_4236_);
lean_dec(v___y_4221_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4236_);
lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object* v___x_4277_, lean_object* v_a_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4277_, v_a_4278_, v___y_4279_, v___y_4280_);
lean_dec_ref(v___y_4279_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object* v_initialFmt_4282_, lean_object* v_stx_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v___y_4287_; uint8_t v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4299_; uint8_t v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v_env_4313_; lean_object* v___x_4314_; 
v_env_4313_ = lean_ctor_get(v_a_4284_, 0);
lean_inc_ref(v_a_4284_);
lean_inc(v_stx_4283_);
v___x_4314_ = lean_apply_3(v_initialFmt_4282_, v_stx_4283_, v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
if (lean_obj_tag(v_a_4315_) == 1)
{
lean_object* v_a_4316_; lean_object* v_val_4317_; lean_object* v___x_4318_; 
v_a_4316_ = lean_ctor_get(v___x_4314_, 1);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4314_, 2);
v_val_4317_ = lean_ctor_get(v_a_4315_, 0);
lean_inc(v_val_4317_);
lean_dec_ref_known(v_a_4315_, 1);
v___x_4318_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_4283_, v_a_4284_, v_a_4316_);
lean_dec(v_stx_4283_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v_a_4320_; uint8_t v___y_4322_; uint8_t v___x_4372_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
v_a_4320_ = lean_ctor_get(v___x_4318_, 1);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4318_, 2);
v___x_4372_ = lean_unbox(v_a_4319_);
lean_dec(v_a_4319_);
if (v___x_4372_ == 0)
{
uint8_t v___x_4373_; 
v___x_4373_ = 1;
v___y_4322_ = v___x_4373_;
goto v___jp_4321_;
}
else
{
uint8_t v___x_4374_; 
v___x_4374_ = 0;
v___y_4322_ = v___x_4374_;
goto v___jp_4321_;
}
v___jp_4321_:
{
lean_object* v___x_4323_; 
lean_inc_ref(v_env_4313_);
v___x_4323_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v_env_4313_, v_val_4317_, v_a_4284_, v_a_4320_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v_a_4325_; lean_object* v_ifTk_4326_; lean_object* v_cond_4327_; lean_object* v_thenTk_4328_; lean_object* v_thenBody_4329_; lean_object* v_elseIfs_4330_; lean_object* v_elseTk_x3f_4331_; lean_object* v_elseBody_x3f_4332_; lean_object* v___x_4333_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
v_a_4325_ = lean_ctor_get(v___x_4323_, 1);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4323_, 2);
v_ifTk_4326_ = lean_ctor_get(v_a_4324_, 0);
lean_inc(v_ifTk_4326_);
v_cond_4327_ = lean_ctor_get(v_a_4324_, 1);
lean_inc_ref(v_cond_4327_);
v_thenTk_4328_ = lean_ctor_get(v_a_4324_, 2);
lean_inc(v_thenTk_4328_);
v_thenBody_4329_ = lean_ctor_get(v_a_4324_, 3);
lean_inc(v_thenBody_4329_);
v_elseIfs_4330_ = lean_ctor_get(v_a_4324_, 4);
lean_inc_ref(v_elseIfs_4330_);
v_elseTk_x3f_4331_ = lean_ctor_get(v_a_4324_, 5);
lean_inc(v_elseTk_x3f_4331_);
v_elseBody_x3f_4332_ = lean_ctor_get(v_a_4324_, 6);
lean_inc(v_elseBody_x3f_4332_);
lean_dec(v_a_4324_);
v___x_4333_ = l_Lean_Fmt_fmt(v_ifTk_4326_, v_a_4284_, v_a_4325_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v_a_4335_; lean_object* v___x_4336_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
v_a_4335_ = lean_ctor_get(v___x_4333_, 1);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4333_, 2);
v___x_4336_ = l_Lean_Fmt_fmt(v_thenTk_4328_, v_a_4284_, v_a_4335_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; lean_object* v_a_4338_; lean_object* v___x_4339_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
v_a_4338_ = lean_ctor_get(v___x_4336_, 1);
lean_inc(v_a_4338_);
lean_dec_ref_known(v___x_4336_, 2);
v___x_4339_ = l_Lean_Fmt_fmt(v_thenBody_4329_, v_a_4284_, v_a_4338_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v_a_4341_; size_t v_sz_4342_; size_t v___x_4343_; lean_object* v___x_4344_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
v_a_4341_ = lean_ctor_get(v___x_4339_, 1);
lean_inc(v_a_4341_);
lean_dec_ref_known(v___x_4339_, 2);
v_sz_4342_ = lean_array_size(v_elseIfs_4330_);
v___x_4343_ = ((size_t)0ULL);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_4342_, v___x_4343_, v_elseIfs_4330_, v_a_4284_, v_a_4341_);
if (lean_obj_tag(v___x_4344_) == 0)
{
if (lean_obj_tag(v_elseTk_x3f_4331_) == 0)
{
lean_object* v_a_4345_; lean_object* v_a_4346_; lean_object* v___x_4347_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
v_a_4346_ = lean_ctor_get(v___x_4344_, 1);
lean_inc(v_a_4346_);
lean_dec_ref_known(v___x_4344_, 2);
v___x_4347_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4299_ = v_a_4337_;
v___y_4300_ = v___y_4322_;
v___y_4301_ = v_a_4334_;
v___y_4302_ = v_elseBody_x3f_4332_;
v___y_4303_ = v_a_4346_;
v___y_4304_ = v_a_4345_;
v___y_4305_ = v_cond_4327_;
v___y_4306_ = v_a_4340_;
v___y_4307_ = v___x_4347_;
goto v___jp_4298_;
}
else
{
lean_object* v_a_4348_; lean_object* v_a_4349_; lean_object* v_val_4350_; lean_object* v___x_4351_; 
v_a_4348_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4348_);
v_a_4349_ = lean_ctor_get(v___x_4344_, 1);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4344_, 2);
v_val_4350_ = lean_ctor_get(v_elseTk_x3f_4331_, 0);
lean_inc(v_val_4350_);
lean_dec_ref_known(v_elseTk_x3f_4331_, 1);
v___x_4351_ = l_Lean_Fmt_fmt(v_val_4350_, v_a_4284_, v_a_4349_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v_a_4353_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
v_a_4353_ = lean_ctor_get(v___x_4351_, 1);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4351_, 2);
v___y_4299_ = v_a_4337_;
v___y_4300_ = v___y_4322_;
v___y_4301_ = v_a_4334_;
v___y_4302_ = v_elseBody_x3f_4332_;
v___y_4303_ = v_a_4353_;
v___y_4304_ = v_a_4348_;
v___y_4305_ = v_cond_4327_;
v___y_4306_ = v_a_4340_;
v___y_4307_ = v_a_4352_;
goto v___jp_4298_;
}
else
{
lean_dec(v_a_4348_);
lean_dec(v_a_4340_);
lean_dec(v_a_4337_);
lean_dec(v_a_4334_);
lean_dec(v_elseBody_x3f_4332_);
lean_dec_ref(v_cond_4327_);
return v___x_4351_;
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec(v_a_4340_);
lean_dec(v_a_4337_);
lean_dec(v_a_4334_);
lean_dec(v_elseBody_x3f_4332_);
lean_dec(v_elseTk_x3f_4331_);
lean_dec_ref(v_cond_4327_);
v_a_4354_ = lean_ctor_get(v___x_4344_, 0);
v_a_4355_ = lean_ctor_get(v___x_4344_, 1);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4344_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_inc(v_a_4354_);
lean_dec(v___x_4344_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4354_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
lean_dec(v_a_4337_);
lean_dec(v_a_4334_);
lean_dec(v_elseBody_x3f_4332_);
lean_dec(v_elseTk_x3f_4331_);
lean_dec_ref(v_elseIfs_4330_);
lean_dec_ref(v_cond_4327_);
return v___x_4339_;
}
}
else
{
lean_dec(v_a_4334_);
lean_dec(v_elseBody_x3f_4332_);
lean_dec(v_elseTk_x3f_4331_);
lean_dec_ref(v_elseIfs_4330_);
lean_dec(v_thenBody_4329_);
lean_dec_ref(v_cond_4327_);
return v___x_4336_;
}
}
else
{
lean_dec(v_elseBody_x3f_4332_);
lean_dec(v_elseTk_x3f_4331_);
lean_dec_ref(v_elseIfs_4330_);
lean_dec(v_thenBody_4329_);
lean_dec(v_thenTk_4328_);
lean_dec_ref(v_cond_4327_);
return v___x_4333_;
}
}
else
{
lean_object* v_a_4363_; lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
v_a_4363_ = lean_ctor_get(v___x_4323_, 0);
v_a_4364_ = lean_ctor_get(v___x_4323_, 1);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4323_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_inc(v_a_4363_);
lean_dec(v___x_4323_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4363_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
else
{
lean_object* v_a_4375_; lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_val_4317_);
v_a_4375_ = lean_ctor_get(v___x_4318_, 0);
v_a_4376_ = lean_ctor_get(v___x_4318_, 1);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4318_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_inc(v_a_4375_);
lean_dec(v___x_4318_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4375_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
else
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4392_; 
lean_dec(v_a_4315_);
lean_dec(v_stx_4283_);
v_a_4384_ = lean_ctor_get(v___x_4314_, 1);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4392_ == 0)
{
lean_object* v_unused_4393_; 
v_unused_4393_ = lean_ctor_get(v___x_4314_, 0);
lean_dec(v_unused_4393_);
v___x_4386_ = v___x_4314_;
v_isShared_4387_ = v_isSharedCheck_4392_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4314_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4392_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4388_; lean_object* v___x_4390_; 
v___x_4388_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4387_ == 0)
{
lean_ctor_set_tag(v___x_4386_, 1);
lean_ctor_set(v___x_4386_, 0, v___x_4388_);
v___x_4390_ = v___x_4386_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_a_4384_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
else
{
lean_object* v_a_4394_; lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4402_; 
lean_dec(v_stx_4283_);
v_a_4394_ = lean_ctor_get(v___x_4314_, 0);
v_a_4395_ = lean_ctor_get(v___x_4314_, 1);
v_isSharedCheck_4402_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4402_ == 0)
{
v___x_4397_ = v___x_4314_;
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_inc(v_a_4394_);
lean_dec(v___x_4314_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4402_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4400_; 
if (v_isShared_4398_ == 0)
{
v___x_4400_ = v___x_4397_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4401_; 
v_reuseFailAlloc_4401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4401_, 0, v_a_4394_);
lean_ctor_set(v_reuseFailAlloc_4401_, 1, v_a_4395_);
v___x_4400_ = v_reuseFailAlloc_4401_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
return v___x_4400_;
}
}
}
v___jp_4286_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = l_Lean_Fmt_Layouts_conditional(v___y_4290_, v___y_4293_, v___y_4287_, v___y_4294_, v___y_4292_, v___y_4289_, v___y_4295_, v___y_4288_);
lean_dec_ref(v___y_4292_);
v___x_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4296_);
lean_ctor_set(v___x_4297_, 1, v___y_4291_);
return v___x_4297_;
}
v___jp_4298_:
{
if (lean_obj_tag(v___y_4302_) == 0)
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4287_ = v___y_4299_;
v___y_4288_ = v___y_4300_;
v___y_4289_ = v___y_4307_;
v___y_4290_ = v___y_4301_;
v___y_4291_ = v___y_4303_;
v___y_4292_ = v___y_4304_;
v___y_4293_ = v___y_4305_;
v___y_4294_ = v___y_4306_;
v___y_4295_ = v___x_4308_;
goto v___jp_4286_;
}
else
{
lean_object* v_val_4309_; lean_object* v___x_4310_; 
v_val_4309_ = lean_ctor_get(v___y_4302_, 0);
lean_inc(v_val_4309_);
lean_dec_ref_known(v___y_4302_, 1);
v___x_4310_ = l_Lean_Fmt_fmt(v_val_4309_, v_a_4284_, v___y_4303_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v_a_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
v_a_4312_ = lean_ctor_get(v___x_4310_, 1);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4310_, 2);
v___y_4287_ = v___y_4299_;
v___y_4288_ = v___y_4300_;
v___y_4289_ = v___y_4307_;
v___y_4290_ = v___y_4301_;
v___y_4291_ = v_a_4312_;
v___y_4292_ = v___y_4304_;
v___y_4293_ = v___y_4305_;
v___y_4294_ = v___y_4306_;
v___y_4295_ = v_a_4311_;
goto v___jp_4286_;
}
else
{
lean_dec_ref(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v___y_4301_);
lean_dec_ref(v___y_4299_);
return v___x_4310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object* v_initialFmt_4403_, lean_object* v_stx_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_Fmt_fmtConditional(v_initialFmt_4403_, v_stx_4404_, v_a_4405_, v_a_4406_);
lean_dec_ref(v_a_4405_);
return v_res_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object* v___x_4408_, lean_object* v_inst_4409_, lean_object* v_a_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v___x_4413_; 
v___x_4413_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4408_, v_a_4410_, v___y_4411_, v___y_4412_);
return v___x_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object* v___x_4414_, lean_object* v_inst_4415_, lean_object* v_a_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(v___x_4414_, v_inst_4415_, v_a_4416_, v___y_4417_, v___y_4418_);
lean_dec_ref(v___y_4417_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t v_sz_4420_, size_t v_i_4421_, lean_object* v_bs_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
uint8_t v___x_4425_; 
v___x_4425_ = lean_usize_dec_lt(v_i_4421_, v_sz_4420_);
if (v___x_4425_ == 0)
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4426_, 0, v_bs_4422_);
lean_ctor_set(v___x_4426_, 1, v___y_4424_);
return v___x_4426_;
}
else
{
lean_object* v_v_4427_; size_t v_sz_4428_; size_t v___x_4429_; lean_object* v___x_4430_; 
v_v_4427_ = lean_array_uget_borrowed(v_bs_4422_, v_i_4421_);
v_sz_4428_ = lean_array_size(v_v_4427_);
v___x_4429_ = ((size_t)0ULL);
lean_inc(v_v_4427_);
v___x_4430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_4428_, v___x_4429_, v_v_4427_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v_a_4432_; lean_object* v___x_4433_; lean_object* v_bs_x27_4434_; size_t v___x_4435_; size_t v___x_4436_; lean_object* v___x_4437_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4431_);
v_a_4432_ = lean_ctor_get(v___x_4430_, 1);
lean_inc(v_a_4432_);
lean_dec_ref_known(v___x_4430_, 2);
v___x_4433_ = lean_unsigned_to_nat(0u);
v_bs_x27_4434_ = lean_array_uset(v_bs_4422_, v_i_4421_, v___x_4433_);
v___x_4435_ = ((size_t)1ULL);
v___x_4436_ = lean_usize_add(v_i_4421_, v___x_4435_);
v___x_4437_ = lean_array_uset(v_bs_x27_4434_, v_i_4421_, v_a_4431_);
v_i_4421_ = v___x_4436_;
v_bs_4422_ = v___x_4437_;
v___y_4424_ = v_a_4432_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4422_);
return v___x_4430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object* v_sz_4439_, lean_object* v_i_4440_, lean_object* v_bs_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
size_t v_sz_boxed_4444_; size_t v_i_boxed_4445_; lean_object* v_res_4446_; 
v_sz_boxed_4444_ = lean_unbox_usize(v_sz_4439_);
lean_dec(v_sz_4439_);
v_i_boxed_4445_ = lean_unbox_usize(v_i_4440_);
lean_dec(v_i_4440_);
v_res_4446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_boxed_4444_, v_i_boxed_4445_, v_bs_4441_, v___y_4442_, v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(size_t v_sz_4447_, size_t v_i_4448_, lean_object* v_bs_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
uint8_t v___x_4452_; 
v___x_4452_ = lean_usize_dec_lt(v_i_4448_, v_sz_4447_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; 
v___x_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4453_, 0, v_bs_4449_);
lean_ctor_set(v___x_4453_, 1, v___y_4451_);
return v___x_4453_;
}
else
{
lean_object* v_v_4454_; size_t v_sz_4455_; size_t v___x_4456_; lean_object* v___x_4457_; 
v_v_4454_ = lean_array_uget_borrowed(v_bs_4449_, v_i_4448_);
v_sz_4455_ = lean_array_size(v_v_4454_);
v___x_4456_ = ((size_t)0ULL);
lean_inc(v_v_4454_);
v___x_4457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_4455_, v___x_4456_, v_v_4454_, v___y_4450_, v___y_4451_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v_a_4459_; lean_object* v___x_4460_; lean_object* v_bs_x27_4461_; size_t v___x_4462_; size_t v___x_4463_; lean_object* v___x_4464_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4458_);
v_a_4459_ = lean_ctor_get(v___x_4457_, 1);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4457_, 2);
v___x_4460_ = lean_unsigned_to_nat(0u);
v_bs_x27_4461_ = lean_array_uset(v_bs_4449_, v_i_4448_, v___x_4460_);
v___x_4462_ = ((size_t)1ULL);
v___x_4463_ = lean_usize_add(v_i_4448_, v___x_4462_);
v___x_4464_ = lean_array_uset(v_bs_x27_4461_, v_i_4448_, v_a_4458_);
v_i_4448_ = v___x_4463_;
v_bs_4449_ = v___x_4464_;
v___y_4451_ = v_a_4459_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4449_);
return v___x_4457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1___boxed(lean_object* v_sz_4466_, lean_object* v_i_4467_, lean_object* v_bs_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
size_t v_sz_boxed_4471_; size_t v_i_boxed_4472_; lean_object* v_res_4473_; 
v_sz_boxed_4471_ = lean_unbox_usize(v_sz_4466_);
lean_dec(v_sz_4466_);
v_i_boxed_4472_ = lean_unbox_usize(v_i_4467_);
lean_dec(v_i_4467_);
v_res_4473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_boxed_4471_, v_i_boxed_4472_, v_bs_4468_, v___y_4469_, v___y_4470_);
lean_dec_ref(v___y_4469_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object* v_bgs_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
size_t v_sz_4477_; size_t v___x_4478_; lean_object* v___x_4479_; 
v_sz_4477_ = lean_array_size(v_bgs_4474_);
v___x_4478_ = ((size_t)0ULL);
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_4477_, v___x_4478_, v_bgs_4474_, v_a_4475_, v_a_4476_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object* v_bgs_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lean_Fmt_fmtBinderGroups(v_bgs_4480_, v_a_4481_, v_a_4482_);
lean_dec_ref(v_a_4481_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object* v_lhs_4484_, lean_object* v_rhs_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v___x_4488_; 
v___x_4488_ = l_Lean_Fmt_fmt(v_lhs_4484_, v_a_4486_, v_a_4487_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v_a_4490_; lean_object* v___x_4491_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
v_a_4490_ = lean_ctor_get(v___x_4488_, 1);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4488_, 2);
v___x_4491_ = l_Lean_Fmt_fmt(v_rhs_4485_, v_a_4486_, v_a_4490_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4507_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
v_a_4493_ = lean_ctor_get(v___x_4491_, 1);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4495_ = v___x_4491_;
v_isShared_4496_ = v_isSharedCheck_4507_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_inc(v_a_4492_);
lean_dec(v___x_4491_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4507_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; uint8_t v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4505_; 
v___x_4497_ = lean_unsigned_to_nat(2u);
v___x_4498_ = lean_mk_empty_array_with_capacity(v___x_4497_);
v___x_4499_ = lean_array_push(v___x_4498_, v_a_4489_);
v___x_4500_ = lean_array_push(v___x_4499_, v_a_4492_);
v___x_4501_ = 1;
v___x_4502_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4500_, v___x_4501_);
lean_dec_ref(v___x_4500_);
v___x_4503_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4502_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4503_);
v___x_4505_ = v___x_4495_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4503_);
lean_ctor_set(v_reuseFailAlloc_4506_, 1, v_a_4493_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
else
{
lean_dec(v_a_4489_);
return v___x_4491_;
}
}
else
{
lean_dec(v_rhs_4485_);
return v___x_4488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object* v_lhs_4508_, lean_object* v_rhs_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4508_, v_rhs_4509_, v_a_4510_, v_a_4511_);
lean_dec_ref(v_a_4510_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object* v_head_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_quantifier_4516_; lean_object* v_binders_4517_; lean_object* v_typeAscriptionTk_x3f_4518_; lean_object* v_type_x3f_4519_; lean_object* v_commaTk_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4633_; 
v_quantifier_4516_ = lean_ctor_get(v_head_4513_, 0);
v_binders_4517_ = lean_ctor_get(v_head_4513_, 1);
v_typeAscriptionTk_x3f_4518_ = lean_ctor_get(v_head_4513_, 2);
v_type_x3f_4519_ = lean_ctor_get(v_head_4513_, 3);
v_commaTk_4520_ = lean_ctor_get(v_head_4513_, 4);
v_isSharedCheck_4633_ = !lean_is_exclusive(v_head_4513_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4522_ = v_head_4513_;
v_isShared_4523_ = v_isSharedCheck_4633_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_commaTk_4520_);
lean_inc(v_type_x3f_4519_);
lean_inc(v_typeAscriptionTk_x3f_4518_);
lean_inc(v_binders_4517_);
lean_inc(v_quantifier_4516_);
lean_dec(v_head_4513_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4633_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_Fmt_fmt(v_quantifier_4516_, v_a_4514_, v_a_4515_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v_a_4526_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v_binderGroups_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
v_a_4526_ = lean_ctor_get(v___x_4524_, 1);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4524_, 2);
if (lean_obj_tag(v_binders_4517_) == 0)
{
lean_object* v_group_4592_; lean_object* v___x_4593_; 
v_group_4592_ = lean_ctor_get(v_binders_4517_, 0);
lean_inc_ref(v_group_4592_);
lean_dec_ref_known(v_binders_4517_, 1);
v___x_4593_ = l_Lean_Fmt_fmtBinderGroups(v_group_4592_, v_a_4514_, v_a_4526_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v_a_4595_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
v_a_4595_ = lean_ctor_get(v___x_4593_, 1);
lean_inc(v_a_4595_);
lean_dec_ref_known(v___x_4593_, 2);
v_binderGroups_4575_ = v_a_4594_;
v___y_4576_ = v_a_4514_;
v___y_4577_ = v_a_4595_;
goto v___jp_4574_;
}
else
{
lean_object* v_a_4596_; lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
lean_dec(v_a_4525_);
lean_del_object(v___x_4522_);
lean_dec(v_commaTk_4520_);
lean_dec(v_type_x3f_4519_);
lean_dec(v_typeAscriptionTk_x3f_4518_);
v_a_4596_ = lean_ctor_get(v___x_4593_, 0);
v_a_4597_ = lean_ctor_get(v___x_4593_, 1);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4593_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_inc(v_a_4596_);
lean_dec(v___x_4593_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4596_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
}
else
{
lean_object* v_lhs_4605_; lean_object* v_rhs_4606_; lean_object* v___x_4607_; 
v_lhs_4605_ = lean_ctor_get(v_binders_4517_, 0);
lean_inc(v_lhs_4605_);
v_rhs_4606_ = lean_ctor_get(v_binders_4517_, 1);
lean_inc(v_rhs_4606_);
lean_dec_ref_known(v_binders_4517_, 2);
v___x_4607_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4605_, v_rhs_4606_, v_a_4514_, v_a_4526_);
if (lean_obj_tag(v___x_4607_) == 0)
{
lean_object* v_a_4608_; lean_object* v_a_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; 
v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc(v_a_4608_);
v_a_4609_ = lean_ctor_get(v___x_4607_, 1);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4607_, 2);
v___x_4610_ = lean_unsigned_to_nat(1u);
v___x_4611_ = lean_mk_empty_array_with_capacity(v___x_4610_);
lean_inc_ref_n(v___x_4611_, 2);
v___x_4612_ = lean_array_push(v___x_4611_, v_a_4608_);
v___x_4613_ = lean_array_push(v___x_4611_, v___x_4612_);
v___x_4614_ = lean_array_push(v___x_4611_, v___x_4613_);
v_binderGroups_4575_ = v___x_4614_;
v___y_4576_ = v_a_4514_;
v___y_4577_ = v_a_4609_;
goto v___jp_4574_;
}
else
{
lean_object* v_a_4615_; lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4623_; 
lean_dec(v_a_4525_);
lean_del_object(v___x_4522_);
lean_dec(v_commaTk_4520_);
lean_dec(v_type_x3f_4519_);
lean_dec(v_typeAscriptionTk_x3f_4518_);
v_a_4615_ = lean_ctor_get(v___x_4607_, 0);
v_a_4616_ = lean_ctor_get(v___x_4607_, 1);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4618_ = v___x_4607_;
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_inc(v_a_4615_);
lean_dec(v___x_4607_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4623_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4621_; 
if (v_isShared_4619_ == 0)
{
v___x_4621_ = v___x_4618_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4615_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_a_4616_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
v___jp_4527_:
{
lean_object* v___x_4533_; 
v___x_4533_ = l_Lean_Fmt_fmt(v_commaTk_4520_, v___y_4530_, v___y_4528_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v_a_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4545_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
v_a_4535_ = lean_ctor_get(v___x_4533_, 1);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4537_ = v___x_4533_;
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_a_4535_);
lean_inc(v_a_4534_);
lean_dec(v___x_4533_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 4, v_a_4534_);
lean_ctor_set(v___x_4522_, 3, v___y_4532_);
lean_ctor_set(v___x_4522_, 2, v___y_4531_);
lean_ctor_set(v___x_4522_, 1, v___y_4529_);
lean_ctor_set(v___x_4522_, 0, v_a_4525_);
v___x_4540_ = v___x_4522_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4525_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v___y_4529_);
lean_ctor_set(v_reuseFailAlloc_4544_, 2, v___y_4531_);
lean_ctor_set(v_reuseFailAlloc_4544_, 3, v___y_4532_);
lean_ctor_set(v_reuseFailAlloc_4544_, 4, v_a_4534_);
v___x_4540_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4542_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v___x_4540_);
v___x_4542_ = v___x_4537_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4540_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v_a_4535_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec_ref(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v___y_4529_);
lean_dec(v_a_4525_);
lean_del_object(v___x_4522_);
v_a_4546_ = lean_ctor_get(v___x_4533_, 0);
v_a_4547_ = lean_ctor_get(v___x_4533_, 1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4533_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_inc(v_a_4546_);
lean_dec(v___x_4533_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4546_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
v___jp_4555_:
{
if (lean_obj_tag(v_type_x3f_4519_) == 0)
{
lean_object* v___x_4560_; 
v___x_4560_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4528_ = v___y_4557_;
v___y_4529_ = v___y_4556_;
v___y_4530_ = v___y_4558_;
v___y_4531_ = v___y_4559_;
v___y_4532_ = v___x_4560_;
goto v___jp_4527_;
}
else
{
lean_object* v_val_4561_; lean_object* v___x_4562_; 
v_val_4561_ = lean_ctor_get(v_type_x3f_4519_, 0);
lean_inc(v_val_4561_);
lean_dec_ref_known(v_type_x3f_4519_, 1);
v___x_4562_ = l_Lean_Fmt_fmt(v_val_4561_, v___y_4558_, v___y_4557_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; lean_object* v_a_4564_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
v_a_4564_ = lean_ctor_get(v___x_4562_, 1);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4562_, 2);
v___y_4528_ = v_a_4564_;
v___y_4529_ = v___y_4556_;
v___y_4530_ = v___y_4558_;
v___y_4531_ = v___y_4559_;
v___y_4532_ = v_a_4563_;
goto v___jp_4527_;
}
else
{
lean_object* v_a_4565_; lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec_ref(v___y_4559_);
lean_dec_ref(v___y_4556_);
lean_dec(v_a_4525_);
lean_del_object(v___x_4522_);
lean_dec(v_commaTk_4520_);
v_a_4565_ = lean_ctor_get(v___x_4562_, 0);
v_a_4566_ = lean_ctor_get(v___x_4562_, 1);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4562_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_inc(v_a_4565_);
lean_dec(v___x_4562_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4565_);
lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_a_4566_);
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
}
v___jp_4574_:
{
if (lean_obj_tag(v_typeAscriptionTk_x3f_4518_) == 0)
{
lean_object* v___x_4578_; 
v___x_4578_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4556_ = v_binderGroups_4575_;
v___y_4557_ = v___y_4577_;
v___y_4558_ = v___y_4576_;
v___y_4559_ = v___x_4578_;
goto v___jp_4555_;
}
else
{
lean_object* v_val_4579_; lean_object* v___x_4580_; 
v_val_4579_ = lean_ctor_get(v_typeAscriptionTk_x3f_4518_, 0);
lean_inc(v_val_4579_);
lean_dec_ref_known(v_typeAscriptionTk_x3f_4518_, 1);
v___x_4580_ = l_Lean_Fmt_fmt(v_val_4579_, v___y_4576_, v___y_4577_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v_a_4582_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
v_a_4582_ = lean_ctor_get(v___x_4580_, 1);
lean_inc(v_a_4582_);
lean_dec_ref_known(v___x_4580_, 2);
v___y_4556_ = v_binderGroups_4575_;
v___y_4557_ = v_a_4582_;
v___y_4558_ = v___y_4576_;
v___y_4559_ = v_a_4581_;
goto v___jp_4555_;
}
else
{
lean_object* v_a_4583_; lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_dec_ref(v_binderGroups_4575_);
lean_dec(v_a_4525_);
lean_del_object(v___x_4522_);
lean_dec(v_commaTk_4520_);
lean_dec(v_type_x3f_4519_);
v_a_4583_ = lean_ctor_get(v___x_4580_, 0);
v_a_4584_ = lean_ctor_get(v___x_4580_, 1);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4580_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_inc(v_a_4583_);
lean_dec(v___x_4580_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
lean_object* v___x_4589_; 
if (v_isShared_4587_ == 0)
{
v___x_4589_ = v___x_4586_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4583_);
lean_ctor_set(v_reuseFailAlloc_4590_, 1, v_a_4584_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_del_object(v___x_4522_);
lean_dec(v_commaTk_4520_);
lean_dec(v_type_x3f_4519_);
lean_dec(v_typeAscriptionTk_x3f_4518_);
lean_dec_ref(v_binders_4517_);
v_a_4624_ = lean_ctor_get(v___x_4524_, 0);
v_a_4625_ = lean_ctor_get(v___x_4524_, 1);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4524_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_inc(v_a_4624_);
lean_dec(v___x_4524_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4624_);
lean_ctor_set(v_reuseFailAlloc_4631_, 1, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object* v_head_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_Lean_Fmt_fmtQuantifierHead(v_head_4634_, v_a_4635_, v_a_4636_);
lean_dec_ref(v_a_4635_);
return v_res_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t v_sz_4638_, size_t v_i_4639_, lean_object* v_bs_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
uint8_t v___x_4643_; 
v___x_4643_ = lean_usize_dec_lt(v_i_4639_, v_sz_4638_);
if (v___x_4643_ == 0)
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v_bs_4640_);
lean_ctor_set(v___x_4644_, 1, v___y_4642_);
return v___x_4644_;
}
else
{
lean_object* v_v_4645_; lean_object* v___x_4646_; 
v_v_4645_ = lean_array_uget_borrowed(v_bs_4640_, v_i_4639_);
lean_inc(v_v_4645_);
v___x_4646_ = l_Lean_Fmt_fmtQuantifierHead(v_v_4645_, v___y_4641_, v___y_4642_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v_a_4648_; lean_object* v___x_4649_; lean_object* v_bs_x27_4650_; size_t v___x_4651_; size_t v___x_4652_; lean_object* v___x_4653_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc(v_a_4647_);
v_a_4648_ = lean_ctor_get(v___x_4646_, 1);
lean_inc(v_a_4648_);
lean_dec_ref_known(v___x_4646_, 2);
v___x_4649_ = lean_unsigned_to_nat(0u);
v_bs_x27_4650_ = lean_array_uset(v_bs_4640_, v_i_4639_, v___x_4649_);
v___x_4651_ = ((size_t)1ULL);
v___x_4652_ = lean_usize_add(v_i_4639_, v___x_4651_);
v___x_4653_ = lean_array_uset(v_bs_x27_4650_, v_i_4639_, v_a_4647_);
v_i_4639_ = v___x_4652_;
v_bs_4640_ = v___x_4653_;
v___y_4642_ = v_a_4648_;
goto _start;
}
else
{
lean_object* v_a_4655_; lean_object* v_a_4656_; lean_object* v___x_4658_; uint8_t v_isShared_4659_; uint8_t v_isSharedCheck_4663_; 
lean_dec_ref(v_bs_4640_);
v_a_4655_ = lean_ctor_get(v___x_4646_, 0);
v_a_4656_ = lean_ctor_get(v___x_4646_, 1);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4658_ = v___x_4646_;
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
else
{
lean_inc(v_a_4656_);
lean_inc(v_a_4655_);
lean_dec(v___x_4646_);
v___x_4658_ = lean_box(0);
v_isShared_4659_ = v_isSharedCheck_4663_;
goto v_resetjp_4657_;
}
v_resetjp_4657_:
{
lean_object* v___x_4661_; 
if (v_isShared_4659_ == 0)
{
v___x_4661_ = v___x_4658_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_a_4655_);
lean_ctor_set(v_reuseFailAlloc_4662_, 1, v_a_4656_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object* v_sz_4664_, lean_object* v_i_4665_, lean_object* v_bs_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
size_t v_sz_boxed_4669_; size_t v_i_boxed_4670_; lean_object* v_res_4671_; 
v_sz_boxed_4669_ = lean_unbox_usize(v_sz_4664_);
lean_dec(v_sz_4664_);
v_i_boxed_4670_ = lean_unbox_usize(v_i_4665_);
lean_dec(v_i_4665_);
v_res_4671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_boxed_4669_, v_i_boxed_4670_, v_bs_4666_, v___y_4667_, v___y_4668_);
lean_dec_ref(v___y_4667_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object* v_deconstructQuantifier_x3f_4672_, lean_object* v_stx_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
lean_object* v_env_4676_; lean_object* v___x_4677_; lean_object* v_quantifiers_4678_; lean_object* v_body_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4715_; 
v_env_4676_ = lean_ctor_get(v_a_4674_, 0);
lean_inc_ref(v_env_4676_);
v___x_4677_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(v_env_4676_, v_deconstructQuantifier_x3f_4672_, v_stx_4673_);
v_quantifiers_4678_ = lean_ctor_get(v___x_4677_, 0);
v_body_4679_ = lean_ctor_get(v___x_4677_, 1);
v_isSharedCheck_4715_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4681_ = v___x_4677_;
v_isShared_4682_ = v_isSharedCheck_4715_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_body_4679_);
lean_inc(v_quantifiers_4678_);
lean_dec(v___x_4677_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4715_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v___x_4683_ = lean_array_get_size(v_quantifiers_4678_);
v___x_4684_ = lean_unsigned_to_nat(0u);
v___x_4685_ = lean_nat_dec_eq(v___x_4683_, v___x_4684_);
if (v___x_4685_ == 0)
{
size_t v_sz_4686_; size_t v___x_4687_; lean_object* v___x_4688_; 
lean_del_object(v___x_4681_);
v_sz_4686_ = lean_array_size(v_quantifiers_4678_);
v___x_4687_ = ((size_t)0ULL);
v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_4686_, v___x_4687_, v_quantifiers_4678_, v_a_4674_, v_a_4675_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v_a_4690_; lean_object* v___x_4691_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
v_a_4690_ = lean_ctor_get(v___x_4688_, 1);
lean_inc(v_a_4690_);
lean_dec_ref_known(v___x_4688_, 2);
v___x_4691_ = l_Lean_Fmt_fmt(v_body_4679_, v_a_4674_, v_a_4690_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4701_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
v_a_4693_ = lean_ctor_get(v___x_4691_, 1);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4695_ = v___x_4691_;
v_isShared_4696_ = v_isSharedCheck_4701_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_inc(v_a_4692_);
lean_dec(v___x_4691_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4701_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4697_; lean_object* v___x_4699_; 
v___x_4697_ = l_Lean_Fmt_Layouts_quantified(v_a_4689_, v_a_4692_);
if (v_isShared_4696_ == 0)
{
lean_ctor_set(v___x_4695_, 0, v___x_4697_);
v___x_4699_ = v___x_4695_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4700_, 1, v_a_4693_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
else
{
lean_dec(v_a_4689_);
return v___x_4691_;
}
}
else
{
lean_object* v_a_4702_; lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v_body_4679_);
v_a_4702_ = lean_ctor_get(v___x_4688_, 0);
v_a_4703_ = lean_ctor_get(v___x_4688_, 1);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4688_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_inc(v_a_4702_);
lean_dec(v___x_4688_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4702_);
lean_ctor_set(v_reuseFailAlloc_4709_, 1, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
else
{
lean_object* v___x_4711_; lean_object* v___x_4713_; 
lean_dec(v_body_4679_);
lean_dec_ref(v_quantifiers_4678_);
v___x_4711_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4682_ == 0)
{
lean_ctor_set_tag(v___x_4681_, 1);
lean_ctor_set(v___x_4681_, 1, v_a_4675_);
lean_ctor_set(v___x_4681_, 0, v___x_4711_);
v___x_4713_ = v___x_4681_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v_a_4675_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object* v_deconstructQuantifier_x3f_4716_, lean_object* v_stx_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l_Lean_Fmt_fmtQuantifier(v_deconstructQuantifier_x3f_4716_, v_stx_4717_, v_a_4718_, v_a_4719_);
lean_dec_ref(v_a_4718_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_){
_start:
{
uint8_t v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = 0;
v___x_4725_ = l_Lean_Fmt_fmtRaw(v___x_4724_, v_a_4721_, v_a_4722_, v_a_4723_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Lean_Fmt_fmtAtomic(v_a_4726_, v_a_4727_, v_a_4728_);
lean_dec_ref(v_a_4727_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f(lean_object* v_ctx_4730_, lean_object* v_choiceStx_4731_){
_start:
{
uint8_t v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = 0;
v___x_4733_ = l_Lean_Syntax_getRange_x3f(v_choiceStx_4731_, v___x_4732_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v___x_4734_; 
lean_dec_ref(v_ctx_4730_);
v___x_4734_ = lean_box(0);
return v___x_4734_;
}
else
{
lean_object* v_val_4735_; lean_object* v_resolveChoiceNode_4736_; lean_object* v___x_4737_; 
v_val_4735_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_val_4735_);
lean_dec_ref_known(v___x_4733_, 1);
v_resolveChoiceNode_4736_ = lean_ctor_get(v_ctx_4730_, 2);
lean_inc_ref(v_resolveChoiceNode_4736_);
lean_dec_ref(v_ctx_4730_);
v___x_4737_ = lean_apply_1(v_resolveChoiceNode_4736_, v_val_4735_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v___x_4738_; 
v___x_4738_ = lean_box(0);
return v___x_4738_;
}
else
{
lean_object* v_val_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4757_; 
v_val_4739_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4741_ = v___x_4737_;
v_isShared_4742_ = v_isSharedCheck_4757_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_val_4739_);
lean_dec(v___x_4737_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4757_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v_stx_4743_; lean_object* v_chosenAltIdx_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; uint8_t v___x_4747_; 
v_stx_4743_ = lean_ctor_get(v_val_4739_, 0);
lean_inc(v_stx_4743_);
v_chosenAltIdx_4744_ = lean_ctor_get(v_val_4739_, 1);
lean_inc(v_chosenAltIdx_4744_);
lean_dec(v_val_4739_);
v___x_4745_ = l_Lean_Syntax_getNumArgs(v_stx_4743_);
lean_dec(v_stx_4743_);
v___x_4746_ = l_Lean_Syntax_getNumArgs(v_choiceStx_4731_);
v___x_4747_ = lean_nat_dec_eq(v___x_4745_, v___x_4746_);
lean_dec(v___x_4746_);
lean_dec(v___x_4745_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; 
lean_dec(v_chosenAltIdx_4744_);
lean_del_object(v___x_4741_);
v___x_4748_ = lean_box(0);
return v___x_4748_;
}
else
{
lean_object* v___x_4749_; lean_object* v___x_4750_; uint8_t v___x_4751_; 
v___x_4749_ = l_Lean_Syntax_getArgs(v_choiceStx_4731_);
v___x_4750_ = lean_array_get_size(v___x_4749_);
v___x_4751_ = lean_nat_dec_lt(v_chosenAltIdx_4744_, v___x_4750_);
if (v___x_4751_ == 0)
{
lean_object* v___x_4752_; 
lean_dec_ref(v___x_4749_);
lean_dec(v_chosenAltIdx_4744_);
lean_del_object(v___x_4741_);
v___x_4752_ = lean_box(0);
return v___x_4752_;
}
else
{
lean_object* v___x_4753_; lean_object* v___x_4755_; 
v___x_4753_ = lean_array_fget(v___x_4749_, v_chosenAltIdx_4744_);
lean_dec(v_chosenAltIdx_4744_);
lean_dec_ref(v___x_4749_);
if (v_isShared_4742_ == 0)
{
lean_ctor_set(v___x_4741_, 0, v___x_4753_);
v___x_4755_ = v___x_4741_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4753_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f___boxed(lean_object* v_ctx_4758_, lean_object* v_choiceStx_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f(v_ctx_4758_, v_choiceStx_4759_);
lean_dec(v_choiceStx_4759_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_resolveChoiceNodes(lean_object* v_ctx_4761_, lean_object* v_x_4762_){
_start:
{
if (lean_obj_tag(v_x_4762_) == 1)
{
lean_object* v_info_4763_; lean_object* v_kind_4764_; lean_object* v_args_4765_; lean_object* v___x_4766_; uint8_t v___x_4767_; 
v_info_4763_ = lean_ctor_get(v_x_4762_, 0);
lean_inc(v_info_4763_);
v_kind_4764_ = lean_ctor_get(v_x_4762_, 1);
lean_inc(v_kind_4764_);
v_args_4765_ = lean_ctor_get(v_x_4762_, 2);
lean_inc_ref(v_args_4765_);
v___x_4766_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_4767_ = lean_name_eq(v_kind_4764_, v___x_4766_);
if (v___x_4767_ == 0)
{
lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4777_; 
v_isSharedCheck_4777_ = !lean_is_exclusive(v_x_4762_);
if (v_isSharedCheck_4777_ == 0)
{
lean_object* v_unused_4778_; lean_object* v_unused_4779_; lean_object* v_unused_4780_; 
v_unused_4778_ = lean_ctor_get(v_x_4762_, 2);
lean_dec(v_unused_4778_);
v_unused_4779_ = lean_ctor_get(v_x_4762_, 1);
lean_dec(v_unused_4779_);
v_unused_4780_ = lean_ctor_get(v_x_4762_, 0);
lean_dec(v_unused_4780_);
v___x_4769_ = v_x_4762_;
v_isShared_4770_ = v_isSharedCheck_4777_;
goto v_resetjp_4768_;
}
else
{
lean_dec(v_x_4762_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4777_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
size_t v_sz_4771_; size_t v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4775_; 
v_sz_4771_ = lean_array_size(v_args_4765_);
v___x_4772_ = ((size_t)0ULL);
v___x_4773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(v_ctx_4761_, v_sz_4771_, v___x_4772_, v_args_4765_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 2, v___x_4773_);
v___x_4775_ = v___x_4769_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_info_4763_);
lean_ctor_set(v_reuseFailAlloc_4776_, 1, v_kind_4764_);
lean_ctor_set(v_reuseFailAlloc_4776_, 2, v___x_4773_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
else
{
lean_object* v___x_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4793_; 
lean_inc_ref(v_ctx_4761_);
v___x_4781_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f(v_ctx_4761_, v_x_4762_);
v_isSharedCheck_4793_ = !lean_is_exclusive(v_x_4762_);
if (v_isSharedCheck_4793_ == 0)
{
lean_object* v_unused_4794_; lean_object* v_unused_4795_; lean_object* v_unused_4796_; 
v_unused_4794_ = lean_ctor_get(v_x_4762_, 2);
lean_dec(v_unused_4794_);
v_unused_4795_ = lean_ctor_get(v_x_4762_, 1);
lean_dec(v_unused_4795_);
v_unused_4796_ = lean_ctor_get(v_x_4762_, 0);
lean_dec(v_unused_4796_);
v___x_4783_ = v_x_4762_;
v_isShared_4784_ = v_isSharedCheck_4793_;
goto v_resetjp_4782_;
}
else
{
lean_dec(v_x_4762_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4793_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
if (lean_obj_tag(v___x_4781_) == 0)
{
size_t v_sz_4785_; size_t v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4789_; 
v_sz_4785_ = lean_array_size(v_args_4765_);
v___x_4786_ = ((size_t)0ULL);
v___x_4787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(v_ctx_4761_, v_sz_4785_, v___x_4786_, v_args_4765_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 2, v___x_4787_);
v___x_4789_ = v___x_4783_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_info_4763_);
lean_ctor_set(v_reuseFailAlloc_4790_, 1, v_kind_4764_);
lean_ctor_set(v_reuseFailAlloc_4790_, 2, v___x_4787_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
else
{
lean_object* v_val_4791_; 
lean_del_object(v___x_4783_);
lean_dec_ref(v_args_4765_);
lean_dec(v_kind_4764_);
lean_dec(v_info_4763_);
v_val_4791_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_val_4791_);
lean_dec_ref_known(v___x_4781_, 1);
v_x_4762_ = v_val_4791_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v_ctx_4761_);
return v_x_4762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(lean_object* v_ctx_4797_, size_t v_sz_4798_, size_t v_i_4799_, lean_object* v_bs_4800_){
_start:
{
uint8_t v___x_4801_; 
v___x_4801_ = lean_usize_dec_lt(v_i_4799_, v_sz_4798_);
if (v___x_4801_ == 0)
{
lean_dec_ref(v_ctx_4797_);
return v_bs_4800_;
}
else
{
lean_object* v_v_4802_; lean_object* v___x_4803_; lean_object* v_bs_x27_4804_; lean_object* v___x_4805_; size_t v___x_4806_; size_t v___x_4807_; lean_object* v___x_4808_; 
v_v_4802_ = lean_array_uget(v_bs_4800_, v_i_4799_);
v___x_4803_ = lean_unsigned_to_nat(0u);
v_bs_x27_4804_ = lean_array_uset(v_bs_4800_, v_i_4799_, v___x_4803_);
lean_inc_ref(v_ctx_4797_);
v___x_4805_ = l_Lean_Fmt_resolveChoiceNodes(v_ctx_4797_, v_v_4802_);
v___x_4806_ = ((size_t)1ULL);
v___x_4807_ = lean_usize_add(v_i_4799_, v___x_4806_);
v___x_4808_ = lean_array_uset(v_bs_x27_4804_, v_i_4799_, v___x_4805_);
v_i_4799_ = v___x_4807_;
v_bs_4800_ = v___x_4808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0___boxed(lean_object* v_ctx_4810_, lean_object* v_sz_4811_, lean_object* v_i_4812_, lean_object* v_bs_4813_){
_start:
{
size_t v_sz_boxed_4814_; size_t v_i_boxed_4815_; lean_object* v_res_4816_; 
v_sz_boxed_4814_ = lean_unbox_usize(v_sz_4811_);
lean_dec(v_sz_4811_);
v_i_boxed_4815_ = lean_unbox_usize(v_i_4812_);
lean_dec(v_i_4812_);
v_res_4816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(v_ctx_4810_, v_sz_boxed_4814_, v_i_boxed_4815_, v_bs_4813_);
return v_res_4816_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4823_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed), 3, 0);
v___x_4824_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2));
v___x_4825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4825_, 0, v___x_4824_);
lean_ctor_set(v___x_4825_, 1, v___x_4823_);
return v___x_4825_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4(void){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3);
v___x_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4826_);
return v___x_4827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object* v_kind_4828_){
_start:
{
lean_object* v___x_4829_; uint8_t v___x_4830_; 
v___x_4829_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_4830_ = lean_name_eq(v_kind_4828_, v___x_4829_);
if (v___x_4830_ == 0)
{
lean_object* v___x_4831_; 
v___x_4831_ = lean_box(0);
return v___x_4831_;
}
else
{
lean_object* v___x_4832_; 
v___x_4832_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4);
return v___x_4832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object* v_kind_4833_){
_start:
{
lean_object* v_res_4834_; 
v_res_4834_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4833_);
lean_dec(v_kind_4833_);
return v_res_4834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object* v_x_4835_, lean_object* v_x_4836_, lean_object* v_kind_4837_){
_start:
{
lean_object* v___x_4838_; 
v___x_4838_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object* v_x_4839_, lean_object* v_x_4840_, lean_object* v_kind_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(v_x_4839_, v_x_4840_, v_kind_4841_);
lean_dec(v_kind_4841_);
lean_dec_ref(v_x_4840_);
lean_dec_ref(v_x_4839_);
return v_res_4842_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object* v_x_4848_){
_start:
{
if (lean_obj_tag(v_x_4848_) == 1)
{
lean_object* v_pre_4849_; lean_object* v_str_4850_; lean_object* v___x_4851_; uint8_t v___x_4852_; 
v_pre_4849_ = lean_ctor_get(v_x_4848_, 0);
v_str_4850_ = lean_ctor_get(v_x_4848_, 1);
v___x_4851_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0));
v___x_4852_ = lean_string_dec_eq(v_str_4850_, v___x_4851_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4853_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1));
v___x_4854_ = lean_string_dec_eq(v_str_4850_, v___x_4853_);
if (v___x_4854_ == 0)
{
lean_object* v___x_4855_; uint8_t v___x_4856_; 
v___x_4855_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2));
v___x_4856_ = lean_string_dec_eq(v_str_4850_, v___x_4855_);
if (v___x_4856_ == 0)
{
lean_object* v___x_4857_; uint8_t v___x_4858_; 
v___x_4857_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3));
v___x_4858_ = lean_string_dec_eq(v_str_4850_, v___x_4857_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4859_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4));
v___x_4860_ = lean_string_dec_eq(v_str_4850_, v___x_4859_);
if (v___x_4860_ == 0)
{
return v___x_4860_;
}
else
{
if (lean_obj_tag(v_pre_4849_) == 0)
{
return v___x_4860_;
}
else
{
return v___x_4858_;
}
}
}
else
{
return v___x_4858_;
}
}
else
{
return v___x_4856_;
}
}
else
{
return v___x_4854_;
}
}
else
{
return v___x_4852_;
}
}
else
{
uint8_t v___x_4861_; 
v___x_4861_ = 0;
return v___x_4861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object* v_x_4862_){
_start:
{
uint8_t v_res_4863_; lean_object* v_r_4864_; 
v_res_4863_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_x_4862_);
lean_dec(v_x_4862_);
v_r_4864_ = lean_box(v_res_4863_);
return v_r_4864_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2(void){
_start:
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4870_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAtomic___boxed), 3, 0);
v___x_4871_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1));
v___x_4872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
lean_ctor_set(v___x_4872_, 1, v___x_4870_);
return v___x_4872_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2);
v___x_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
return v___x_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object* v_kind_4875_){
_start:
{
uint8_t v___x_4876_; 
v___x_4876_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_kind_4875_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; 
v___x_4877_ = lean_box(0);
return v___x_4877_;
}
else
{
lean_object* v___x_4878_; 
v___x_4878_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object* v_kind_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4879_);
lean_dec(v_kind_4879_);
return v_res_4880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object* v_x_4881_, lean_object* v_x_4882_, lean_object* v_kind_4883_){
_start:
{
lean_object* v___x_4884_; 
v___x_4884_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4883_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object* v_x_4885_, lean_object* v_x_4886_, lean_object* v_kind_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(v_x_4885_, v_x_4886_, v_kind_4887_);
lean_dec(v_kind_4887_);
lean_dec_ref(v_x_4886_);
lean_dec_ref(v_x_4885_);
return v_res_4888_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4(void){
_start:
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4899_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostfixOperator___boxed), 3, 0);
v___x_4900_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3));
v___x_4901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4900_);
lean_ctor_set(v___x_4901_, 1, v___x_4899_);
return v___x_4901_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5(void){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4902_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4);
v___x_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4902_);
return v___x_4903_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8(void){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
v___x_4909_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrefixOperator___boxed), 3, 0);
v___x_4910_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7));
v___x_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
lean_ctor_set(v___x_4911_, 1, v___x_4909_);
return v___x_4911_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9(void){
_start:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; 
v___x_4912_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8);
v___x_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4912_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object* v_env_4914_, lean_object* v_opts_4915_, lean_object* v_kind_4916_){
_start:
{
lean_object* v___x_4917_; 
lean_inc(v_kind_4916_);
lean_inc_ref(v_env_4914_);
v___x_4917_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_4914_, v_opts_4915_, v_kind_4916_);
if (lean_obj_tag(v___x_4917_) == 1)
{
lean_object* v_val_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4928_; 
lean_dec(v_kind_4916_);
lean_dec_ref(v_env_4914_);
v_val_4918_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4920_ = v___x_4917_;
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_val_4918_);
lean_dec(v___x_4917_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4926_; 
v___x_4922_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1));
v___x_4923_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInfixOperator___boxed), 4, 1);
lean_closure_set(v___x_4923_, 0, v_val_4918_);
v___x_4924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4922_);
lean_ctor_set(v___x_4924_, 1, v___x_4923_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 0, v___x_4924_);
v___x_4926_ = v___x_4920_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v___x_4924_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
else
{
uint8_t v___x_4929_; 
lean_dec(v___x_4917_);
lean_inc(v_kind_4916_);
lean_inc_ref(v_env_4914_);
v___x_4929_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_4914_, v_opts_4915_, v_kind_4916_);
if (v___x_4929_ == 0)
{
uint8_t v___x_4930_; 
v___x_4930_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_4914_, v_opts_4915_, v_kind_4916_);
if (v___x_4930_ == 0)
{
lean_object* v___x_4931_; 
v___x_4931_ = lean_box(0);
return v___x_4931_;
}
else
{
lean_object* v___x_4932_; 
v___x_4932_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5);
return v___x_4932_;
}
}
else
{
lean_object* v___x_4933_; 
lean_dec(v_kind_4916_);
lean_dec_ref(v_env_4914_);
v___x_4933_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9);
return v___x_4933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object* v_env_4934_, lean_object* v_opts_4935_, lean_object* v_kind_4936_){
_start:
{
lean_object* v_res_4937_; 
v_res_4937_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(v_env_4934_, v_opts_4935_, v_kind_4936_);
lean_dec_ref(v_opts_4935_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object* v_env_4938_, lean_object* v_opts_4939_, lean_object* v_kind_4940_){
_start:
{
uint8_t v___x_4941_; 
v___x_4941_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_4938_, v_opts_4939_, v_kind_4940_);
if (v___x_4941_ == 0)
{
lean_object* v___x_4942_; 
v___x_4942_ = lean_box(0);
return v___x_4942_;
}
else
{
lean_object* v___x_4943_; 
v___x_4943_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object* v_env_4944_, lean_object* v_opts_4945_, lean_object* v_kind_4946_){
_start:
{
lean_object* v_res_4947_; 
v_res_4947_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(v_env_4944_, v_opts_4945_, v_kind_4946_);
lean_dec_ref(v_opts_4945_);
return v_res_4947_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(lean_object* v_x_4948_, lean_object* v_x_4949_){
_start:
{
if (lean_obj_tag(v_x_4948_) == 0)
{
if (lean_obj_tag(v_x_4949_) == 0)
{
uint8_t v___x_4950_; 
v___x_4950_ = 1;
return v___x_4950_;
}
else
{
uint8_t v___x_4951_; 
v___x_4951_ = 0;
return v___x_4951_;
}
}
else
{
if (lean_obj_tag(v_x_4949_) == 0)
{
uint8_t v___x_4952_; 
v___x_4952_ = 0;
return v___x_4952_;
}
else
{
lean_object* v_val_4953_; lean_object* v_val_4954_; uint8_t v___x_4955_; 
v_val_4953_ = lean_ctor_get(v_x_4948_, 0);
v_val_4954_ = lean_ctor_get(v_x_4949_, 0);
v___x_4955_ = lean_nat_dec_eq(v_val_4953_, v_val_4954_);
return v___x_4955_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0___boxed(lean_object* v_x_4956_, lean_object* v_x_4957_){
_start:
{
uint8_t v_res_4958_; lean_object* v_r_4959_; 
v_res_4958_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v_x_4956_, v_x_4957_);
lean_dec(v_x_4957_);
lean_dec(v_x_4956_);
v_r_4959_ = lean_box(v_res_4958_);
return v_r_4959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(lean_object* v_lineInfos_4960_, lean_object* v___f_4961_, lean_object* v___f_4962_, lean_object* v_pos_4963_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_4960_, v_pos_4963_, v___f_4961_, v___f_4962_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v___x_4965_; 
v___x_4965_ = lean_box(0);
return v___x_4965_;
}
else
{
lean_object* v_val_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4974_; 
v_val_4966_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4968_ = v___x_4964_;
v_isShared_4969_ = v_isSharedCheck_4974_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_val_4966_);
lean_dec(v___x_4964_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4974_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v_fst_4970_; lean_object* v___x_4972_; 
v_fst_4970_ = lean_ctor_get(v_val_4966_, 0);
lean_inc(v_fst_4970_);
lean_dec(v_val_4966_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v_fst_4970_);
v___x_4972_ = v___x_4968_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_fst_4970_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2___boxed(lean_object* v_lineInfos_4975_, lean_object* v___f_4976_, lean_object* v___f_4977_, lean_object* v_pos_4978_){
_start:
{
lean_object* v_res_4979_; 
v_res_4979_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4975_, v___f_4976_, v___f_4977_, v_pos_4978_);
lean_dec_ref(v_lineInfos_4975_);
return v_res_4979_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(lean_object* v_lineInfos_4980_, lean_object* v_a_4981_, lean_object* v_b_4982_){
_start:
{
lean_object* v___f_4983_; lean_object* v___f_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; uint8_t v___x_4987_; 
v___f_4983_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_4984_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_4985_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4980_, v___f_4983_, v___f_4984_, v_a_4981_);
v___x_4986_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4980_, v___f_4983_, v___f_4984_, v_b_4982_);
v___x_4987_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v___x_4985_, v___x_4986_);
lean_dec(v___x_4986_);
lean_dec(v___x_4985_);
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___boxed(lean_object* v_lineInfos_4988_, lean_object* v_a_4989_, lean_object* v_b_4990_){
_start:
{
uint8_t v_res_4991_; lean_object* v_r_4992_; 
v_res_4991_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4988_, v_a_4989_, v_b_4990_);
lean_dec_ref(v_lineInfos_4988_);
v_r_4992_ = lean_box(v_res_4991_);
return v_r_4992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(lean_object* v_val_4993_, uint8_t v_opOnLhsLine_4994_, lean_object* v_val_4995_, uint8_t v_opOnRhsLine_4996_, lean_object* v___x_4997_, lean_object* v___x_4998_, lean_object* v_as_4999_, size_t v_sz_5000_, size_t v_i_5001_, lean_object* v_b_5002_){
_start:
{
lean_object* v_a_5004_; uint8_t v___x_5008_; 
v___x_5008_ = lean_usize_dec_lt(v_i_5001_, v_sz_5000_);
if (v___x_5008_ == 0)
{
lean_dec_ref(v_val_4995_);
lean_dec_ref(v_val_4993_);
return v_b_5002_;
}
else
{
lean_object* v_a_5009_; uint8_t v_kind_5010_; uint8_t v_placement_5011_; lean_object* v_originalTokenRange_5012_; lean_object* v_originalWhitespaceRange_5013_; uint8_t v_originalWhitespaceKind_5014_; lean_object* v_content_5015_; uint8_t v_emptyLineBefore_5016_; uint8_t v___y_5023_; 
v_a_5009_ = lean_array_uget_borrowed(v_as_4999_, v_i_5001_);
v_kind_5010_ = lean_ctor_get_uint8(v_a_5009_, sizeof(void*)*3);
v_placement_5011_ = lean_ctor_get_uint8(v_a_5009_, sizeof(void*)*3 + 1);
v_originalTokenRange_5012_ = lean_ctor_get(v_a_5009_, 0);
v_originalWhitespaceRange_5013_ = lean_ctor_get(v_a_5009_, 1);
v_originalWhitespaceKind_5014_ = lean_ctor_get_uint8(v_a_5009_, sizeof(void*)*3 + 2);
v_content_5015_ = lean_ctor_get(v_a_5009_, 2);
v_emptyLineBefore_5016_ = lean_ctor_get_uint8(v_a_5009_, sizeof(void*)*3 + 3);
if (v_placement_5011_ == 0)
{
lean_object* v___x_5026_; uint8_t v___x_5027_; 
v___x_5026_ = lean_unsigned_to_nat(3u);
v___x_5027_ = lean_nat_dec_eq(v___x_4997_, v___x_5026_);
v___y_5023_ = v___x_5027_;
goto v___jp_5022_;
}
else
{
lean_object* v___x_5028_; uint8_t v___x_5029_; 
v___x_5028_ = lean_unsigned_to_nat(0u);
v___x_5029_ = lean_nat_dec_eq(v___x_4998_, v___x_5028_);
v___y_5023_ = v___x_5029_;
goto v___jp_5022_;
}
v___jp_5017_:
{
uint8_t v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5018_ = 1;
lean_inc_ref(v_content_5015_);
lean_inc_ref(v_originalWhitespaceRange_5013_);
lean_inc_ref(v_originalTokenRange_5012_);
v___x_5019_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5019_, 0, v_originalTokenRange_5012_);
lean_ctor_set(v___x_5019_, 1, v_originalWhitespaceRange_5013_);
lean_ctor_set(v___x_5019_, 2, v_content_5015_);
lean_ctor_set_uint8(v___x_5019_, sizeof(void*)*3, v_kind_5010_);
lean_ctor_set_uint8(v___x_5019_, sizeof(void*)*3 + 1, v___x_5018_);
lean_ctor_set_uint8(v___x_5019_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_5014_);
lean_ctor_set_uint8(v___x_5019_, sizeof(void*)*3 + 3, v_emptyLineBefore_5016_);
lean_inc_ref(v_val_4993_);
v___x_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
lean_ctor_set(v___x_5020_, 1, v_val_4993_);
v___x_5021_ = lean_array_push(v_b_5002_, v___x_5020_);
v_a_5004_ = v___x_5021_;
goto v___jp_5003_;
}
v___jp_5022_:
{
if (v___y_5023_ == 0)
{
goto v___jp_5017_;
}
else
{
if (v_opOnRhsLine_4996_ == 0)
{
if (v_opOnLhsLine_4994_ == 0)
{
goto v___jp_5017_;
}
else
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
lean_inc_ref(v_val_4995_);
lean_inc(v_a_5009_);
v___x_5024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5024_, 0, v_a_5009_);
lean_ctor_set(v___x_5024_, 1, v_val_4995_);
v___x_5025_ = lean_array_push(v_b_5002_, v___x_5024_);
v_a_5004_ = v___x_5025_;
goto v___jp_5003_;
}
}
else
{
v_a_5004_ = v_b_5002_;
goto v___jp_5003_;
}
}
}
}
v___jp_5003_:
{
size_t v___x_5005_; size_t v___x_5006_; 
v___x_5005_ = ((size_t)1ULL);
v___x_5006_ = lean_usize_add(v_i_5001_, v___x_5005_);
v_i_5001_ = v___x_5006_;
v_b_5002_ = v_a_5004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0___boxed(lean_object* v_val_5030_, lean_object* v_opOnLhsLine_5031_, lean_object* v_val_5032_, lean_object* v_opOnRhsLine_5033_, lean_object* v___x_5034_, lean_object* v___x_5035_, lean_object* v_as_5036_, lean_object* v_sz_5037_, lean_object* v_i_5038_, lean_object* v_b_5039_){
_start:
{
uint8_t v_opOnLhsLine_boxed_5040_; uint8_t v_opOnRhsLine_boxed_5041_; size_t v_sz_boxed_5042_; size_t v_i_boxed_5043_; lean_object* v_res_5044_; 
v_opOnLhsLine_boxed_5040_ = lean_unbox(v_opOnLhsLine_5031_);
v_opOnRhsLine_boxed_5041_ = lean_unbox(v_opOnRhsLine_5033_);
v_sz_boxed_5042_ = lean_unbox_usize(v_sz_5037_);
lean_dec(v_sz_5037_);
v_i_boxed_5043_ = lean_unbox_usize(v_i_5038_);
lean_dec(v_i_5038_);
v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_5030_, v_opOnLhsLine_boxed_5040_, v_val_5032_, v_opOnRhsLine_boxed_5041_, v___x_5034_, v___x_5035_, v_as_5036_, v_sz_boxed_5042_, v_i_boxed_5043_, v_b_5039_);
lean_dec_ref(v_as_5036_);
lean_dec(v___x_5035_);
lean_dec(v___x_5034_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector(lean_object* v_ctx_5047_, lean_object* v_stx_5048_){
_start:
{
lean_object* v___x_5051_; lean_object* v___x_5052_; uint8_t v___x_5053_; 
v___x_5051_ = l_Lean_Syntax_getNumArgs(v_stx_5048_);
v___x_5052_ = lean_unsigned_to_nat(3u);
v___x_5053_ = lean_nat_dec_eq(v___x_5051_, v___x_5052_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; 
lean_dec(v___x_5051_);
lean_dec(v_stx_5048_);
lean_dec_ref(v_ctx_5047_);
v___x_5054_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5054_;
}
else
{
lean_object* v___x_5055_; lean_object* v___x_5056_; uint8_t v___x_5057_; 
v___x_5055_ = lean_unsigned_to_nat(1u);
v___x_5056_ = l_Lean_Syntax_getArg(v_stx_5048_, v___x_5055_);
v___x_5057_ = l_Lean_Syntax_isAtom(v___x_5056_);
if (v___x_5057_ == 0)
{
lean_object* v___x_5058_; 
lean_dec(v___x_5056_);
lean_dec(v___x_5051_);
lean_dec(v_stx_5048_);
lean_dec_ref(v_ctx_5047_);
v___x_5058_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5058_;
}
else
{
lean_object* v_env_5059_; lean_object* v_opts_5060_; lean_object* v_lineInfos_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
v_env_5059_ = lean_ctor_get(v_ctx_5047_, 0);
v_opts_5060_ = lean_ctor_get(v_ctx_5047_, 1);
v_lineInfos_5061_ = lean_ctor_get(v_ctx_5047_, 2);
lean_inc_ref(v_lineInfos_5061_);
v___x_5062_ = lean_unsigned_to_nat(0u);
v___x_5063_ = l_Lean_Syntax_getArg(v_stx_5048_, v___x_5062_);
v___x_5064_ = lean_unsigned_to_nat(2u);
v___x_5065_ = l_Lean_Syntax_getArg(v_stx_5048_, v___x_5064_);
v___x_5066_ = l_Lean_Syntax_getKind(v_stx_5048_);
lean_inc_ref(v_env_5059_);
v___x_5067_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_5059_, v_opts_5060_, v___x_5066_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v___x_5068_; 
lean_dec(v___x_5065_);
lean_dec(v___x_5063_);
lean_dec_ref(v_lineInfos_5061_);
lean_dec(v___x_5056_);
lean_dec(v___x_5051_);
lean_dec_ref(v_ctx_5047_);
v___x_5068_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5068_;
}
else
{
lean_object* v_comments_5069_; lean_object* v___x_5070_; uint8_t v___x_5071_; 
lean_dec_ref_known(v___x_5067_, 1);
v_comments_5069_ = l_Lean_Fmt_CommentCollector_Context_trailingComments(v_ctx_5047_, v___x_5056_);
lean_dec_ref(v_ctx_5047_);
v___x_5070_ = lean_array_get_size(v_comments_5069_);
v___x_5071_ = lean_nat_dec_eq(v___x_5070_, v___x_5062_);
if (v___x_5071_ == 0)
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = l_Lean_Syntax_getTailInfo(v___x_5063_);
lean_dec(v___x_5063_);
v___x_5073_ = l_Lean_SourceInfo_getRange_x3f(v___x_5071_, v___x_5072_);
lean_dec(v___x_5072_);
if (lean_obj_tag(v___x_5073_) == 1)
{
lean_object* v_val_5074_; lean_object* v___x_5075_; 
v_val_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_val_5074_);
lean_dec_ref_known(v___x_5073_, 1);
v___x_5075_ = l_Lean_Syntax_getRange_x3f(v___x_5056_, v___x_5071_);
lean_dec(v___x_5056_);
if (lean_obj_tag(v___x_5075_) == 1)
{
lean_object* v_val_5076_; lean_object* v___x_5077_; 
v_val_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_val_5076_);
lean_dec_ref_known(v___x_5075_, 1);
v___x_5077_ = l_Lean_Syntax_getPos_x3f(v___x_5065_, v___x_5071_);
lean_dec(v___x_5065_);
if (lean_obj_tag(v___x_5077_) == 1)
{
lean_object* v_val_5078_; lean_object* v_stop_5079_; lean_object* v_start_5080_; lean_object* v_stop_5081_; uint8_t v_opOnLhsLine_5082_; uint8_t v_opOnRhsLine_5083_; lean_object* v_r_5084_; size_t v_sz_5085_; size_t v___x_5086_; lean_object* v___x_5087_; 
v_val_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_val_5078_);
lean_dec_ref_known(v___x_5077_, 1);
v_stop_5079_ = lean_ctor_get(v_val_5074_, 1);
v_start_5080_ = lean_ctor_get(v_val_5076_, 0);
v_stop_5081_ = lean_ctor_get(v_val_5076_, 1);
lean_inc(v_start_5080_);
lean_inc(v_stop_5079_);
v_opOnLhsLine_5082_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_5061_, v_stop_5079_, v_start_5080_);
lean_inc(v_stop_5081_);
v_opOnRhsLine_5083_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_5061_, v_stop_5081_, v_val_5078_);
lean_dec_ref(v_lineInfos_5061_);
v_r_5084_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
v_sz_5085_ = lean_array_size(v_comments_5069_);
v___x_5086_ = ((size_t)0ULL);
v___x_5087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_5076_, v_opOnLhsLine_5082_, v_val_5074_, v_opOnRhsLine_5083_, v___x_5051_, v___x_5070_, v_comments_5069_, v_sz_5085_, v___x_5086_, v_r_5084_);
lean_dec_ref(v_comments_5069_);
lean_dec(v___x_5051_);
return v___x_5087_;
}
else
{
lean_dec(v___x_5077_);
lean_dec(v_val_5076_);
lean_dec(v_val_5074_);
lean_dec_ref(v_comments_5069_);
lean_dec_ref(v_lineInfos_5061_);
lean_dec(v___x_5051_);
goto v___jp_5049_;
}
}
else
{
lean_dec(v___x_5075_);
lean_dec(v_val_5074_);
lean_dec_ref(v_comments_5069_);
lean_dec(v___x_5065_);
lean_dec_ref(v_lineInfos_5061_);
lean_dec(v___x_5051_);
goto v___jp_5049_;
}
}
else
{
lean_dec(v___x_5073_);
lean_dec_ref(v_comments_5069_);
lean_dec(v___x_5065_);
lean_dec_ref(v_lineInfos_5061_);
lean_dec(v___x_5056_);
lean_dec(v___x_5051_);
goto v___jp_5049_;
}
}
else
{
lean_object* v___x_5088_; 
lean_dec_ref(v_comments_5069_);
lean_dec(v___x_5065_);
lean_dec(v___x_5063_);
lean_dec_ref(v_lineInfos_5061_);
lean_dec(v___x_5056_);
lean_dec(v___x_5051_);
v___x_5088_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5088_;
}
}
}
}
v___jp_5049_:
{
lean_object* v___x_5050_; 
v___x_5050_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_){
_start:
{
lean_object* v___x_5093_; 
lean_inc_ref(v___y_5091_);
v___x_5093_ = lean_apply_3(v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec_ref(v___y_5096_);
return v_res_5098_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___f_5101_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5102_ = l_Lean_Fmt_fmtAttribute;
v___x_5103_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5103_, 0, lean_box(0));
lean_closure_set(v___x_5103_, 1, v___x_5102_);
lean_closure_set(v___x_5103_, 2, v___f_5101_);
return v___x_5103_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___f_5104_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5105_ = l_Lean_Fmt_infixFmtAttribute;
v___x_5106_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5106_, 0, lean_box(0));
lean_closure_set(v___x_5106_, 1, v___x_5105_);
lean_closure_set(v___x_5106_, 2, v___f_5104_);
return v___x_5106_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5108_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5109_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_5110_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5110_, 0, lean_box(0));
lean_closure_set(v___x_5110_, 1, v___x_5109_);
lean_closure_set(v___x_5110_, 2, v___x_5108_);
return v___x_5110_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5112_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5113_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_5114_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5114_, 0, lean_box(0));
lean_closure_set(v___x_5114_, 1, v___x_5113_);
lean_closure_set(v___x_5114_, 2, v___x_5112_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
v___x_5116_ = lean_unsigned_to_nat(1100u);
v___x_5117_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed), 3, 0);
v___x_5118_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5116_, v___x_5117_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
lean_dec_ref_known(v___x_5118_, 1);
v___x_5119_ = lean_unsigned_to_nat(1000u);
v___x_5120_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5121_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5119_, v___x_5120_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
lean_dec_ref_known(v___x_5121_, 1);
v___x_5122_ = lean_unsigned_to_nat(900u);
v___x_5123_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed), 3, 0);
v___x_5124_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5122_, v___x_5123_);
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
lean_dec_ref_known(v___x_5124_, 1);
v___x_5125_ = lean_unsigned_to_nat(800u);
v___x_5126_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5127_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5125_, v___x_5126_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v___x_5128_; lean_object* v___x_5129_; 
lean_dec_ref_known(v___x_5127_, 1);
v___x_5128_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5129_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5125_, v___x_5128_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v___x_5130_; lean_object* v___x_5131_; 
lean_dec_ref_known(v___x_5129_, 1);
v___x_5130_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5131_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5125_, v___x_5130_);
if (lean_obj_tag(v___x_5131_) == 0)
{
lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
lean_dec_ref_known(v___x_5131_, 1);
v___x_5132_ = lean_unsigned_to_nat(600u);
v___x_5133_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed), 3, 0);
v___x_5134_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5132_, v___x_5133_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
lean_dec_ref_known(v___x_5134_, 1);
v___x_5135_ = lean_unsigned_to_nat(400u);
v___x_5136_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed), 3, 0);
v___x_5137_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5135_, v___x_5136_);
return v___x_5137_;
}
else
{
return v___x_5134_;
}
}
else
{
return v___x_5131_;
}
}
else
{
return v___x_5129_;
}
}
else
{
return v___x_5127_;
}
}
else
{
return v___x_5124_;
}
}
else
{
return v___x_5121_;
}
}
else
{
return v___x_5118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_();
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5141_ = lean_unsigned_to_nat(500u);
v___x_5142_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector), 2, 0);
v___x_5143_ = l_Lean_Fmt_addBuiltinCommentCollector(v___x_5141_, v___x_5142_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2____boxed(lean_object* v_a_5144_){
_start:
{
lean_object* v_res_5145_; 
v_res_5145_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_();
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object* v_stx_x3f_5146_, lean_object* v_a_5147_, lean_object* v_a_5148_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5146_) == 1)
{
lean_object* v_val_5149_; lean_object* v___x_5150_; 
v_val_5149_ = lean_ctor_get(v_stx_x3f_5146_, 0);
lean_inc(v_val_5149_);
lean_dec_ref_known(v_stx_x3f_5146_, 1);
v___x_5150_ = l_Lean_Fmt_fmt(v_val_5149_, v_a_5147_, v_a_5148_);
return v___x_5150_;
}
else
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
lean_dec(v_stx_x3f_5146_);
v___x_5151_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5152_, 0, v___x_5151_);
lean_ctor_set(v___x_5152_, 1, v_a_5148_);
return v___x_5152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object* v_stx_x3f_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l_Lean_Fmt_fmt_x3f(v_stx_x3f_5153_, v_a_5154_, v_a_5155_);
lean_dec_ref(v_a_5154_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object* v_f_5157_, lean_object* v_formatterName_5158_, lean_object* v_stx_x3f_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5159_) == 1)
{
lean_object* v_val_5162_; lean_object* v___x_5163_; 
v_val_5162_ = lean_ctor_get(v_stx_x3f_5159_, 0);
lean_inc(v_val_5162_);
lean_dec_ref_known(v_stx_x3f_5159_, 1);
v___x_5163_ = l_Lean_Fmt_fmtWith(v_f_5157_, v_formatterName_5158_, v_val_5162_, v_a_5160_, v_a_5161_);
return v___x_5163_;
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5165_; 
lean_dec(v_stx_x3f_5159_);
lean_dec(v_formatterName_5158_);
lean_dec_ref(v_f_5157_);
v___x_5164_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5165_, 0, v___x_5164_);
lean_ctor_set(v___x_5165_, 1, v_a_5161_);
return v___x_5165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object* v_f_5166_, lean_object* v_formatterName_5167_, lean_object* v_stx_x3f_5168_, lean_object* v_a_5169_, lean_object* v_a_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l_Lean_Fmt_fmtWith_x3f(v_f_5166_, v_formatterName_5167_, v_stx_x3f_5168_, v_a_5169_, v_a_5170_);
lean_dec_ref(v_a_5169_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object* v_array_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
size_t v_sz_5175_; size_t v___x_5176_; lean_object* v___x_5177_; 
v_sz_5175_ = lean_array_size(v_array_5172_);
v___x_5176_ = ((size_t)0ULL);
v___x_5177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5175_, v___x_5176_, v_array_5172_, v_a_5173_, v_a_5174_);
return v___x_5177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object* v_array_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_Fmt_fmtArray___redArg(v_array_5178_, v_a_5179_, v_a_5180_);
lean_dec_ref(v_a_5179_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object* v_ks_5182_, lean_object* v_array_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v___x_5186_; 
v___x_5186_ = l_Lean_Fmt_fmtArray___redArg(v_array_5183_, v_a_5184_, v_a_5185_);
return v___x_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object* v_ks_5187_, lean_object* v_array_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Lean_Fmt_fmtArray(v_ks_5187_, v_array_5188_, v_a_5189_, v_a_5190_);
lean_dec_ref(v_a_5189_);
lean_dec(v_ks_5187_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object* v_f_5192_, lean_object* v_formatterName_5193_, size_t v_sz_5194_, size_t v_i_5195_, lean_object* v_bs_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
uint8_t v___x_5199_; 
v___x_5199_ = lean_usize_dec_lt(v_i_5195_, v_sz_5194_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; 
lean_dec(v_formatterName_5193_);
lean_dec_ref(v_f_5192_);
v___x_5200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5200_, 0, v_bs_5196_);
lean_ctor_set(v___x_5200_, 1, v___y_5198_);
return v___x_5200_;
}
else
{
lean_object* v_v_5201_; lean_object* v___x_5202_; 
v_v_5201_ = lean_array_uget_borrowed(v_bs_5196_, v_i_5195_);
lean_inc(v_v_5201_);
lean_inc(v_formatterName_5193_);
lean_inc_ref(v_f_5192_);
v___x_5202_ = l_Lean_Fmt_fmtWith(v_f_5192_, v_formatterName_5193_, v_v_5201_, v___y_5197_, v___y_5198_);
if (lean_obj_tag(v___x_5202_) == 0)
{
lean_object* v_a_5203_; lean_object* v_a_5204_; lean_object* v___x_5205_; lean_object* v_bs_x27_5206_; size_t v___x_5207_; size_t v___x_5208_; lean_object* v___x_5209_; 
v_a_5203_ = lean_ctor_get(v___x_5202_, 0);
lean_inc(v_a_5203_);
v_a_5204_ = lean_ctor_get(v___x_5202_, 1);
lean_inc(v_a_5204_);
lean_dec_ref_known(v___x_5202_, 2);
v___x_5205_ = lean_unsigned_to_nat(0u);
v_bs_x27_5206_ = lean_array_uset(v_bs_5196_, v_i_5195_, v___x_5205_);
v___x_5207_ = ((size_t)1ULL);
v___x_5208_ = lean_usize_add(v_i_5195_, v___x_5207_);
v___x_5209_ = lean_array_uset(v_bs_x27_5206_, v_i_5195_, v_a_5203_);
v_i_5195_ = v___x_5208_;
v_bs_5196_ = v___x_5209_;
v___y_5198_ = v_a_5204_;
goto _start;
}
else
{
lean_object* v_a_5211_; lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
lean_dec_ref(v_bs_5196_);
lean_dec(v_formatterName_5193_);
lean_dec_ref(v_f_5192_);
v_a_5211_ = lean_ctor_get(v___x_5202_, 0);
v_a_5212_ = lean_ctor_get(v___x_5202_, 1);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5202_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5202_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_inc(v_a_5211_);
lean_dec(v___x_5202_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5211_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v_a_5212_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object* v_f_5220_, lean_object* v_formatterName_5221_, lean_object* v_sz_5222_, lean_object* v_i_5223_, lean_object* v_bs_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
size_t v_sz_boxed_5227_; size_t v_i_boxed_5228_; lean_object* v_res_5229_; 
v_sz_boxed_5227_ = lean_unbox_usize(v_sz_5222_);
lean_dec(v_sz_5222_);
v_i_boxed_5228_ = lean_unbox_usize(v_i_5223_);
lean_dec(v_i_5223_);
v_res_5229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5220_, v_formatterName_5221_, v_sz_boxed_5227_, v_i_boxed_5228_, v_bs_5224_, v___y_5225_, v___y_5226_);
lean_dec_ref(v___y_5225_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object* v_f_5230_, lean_object* v_formatterName_5231_, lean_object* v_array_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_){
_start:
{
size_t v_sz_5235_; size_t v___x_5236_; lean_object* v___x_5237_; 
v_sz_5235_ = lean_array_size(v_array_5232_);
v___x_5236_ = ((size_t)0ULL);
v___x_5237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5230_, v_formatterName_5231_, v_sz_5235_, v___x_5236_, v_array_5232_, v_a_5233_, v_a_5234_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object* v_f_5238_, lean_object* v_formatterName_5239_, lean_object* v_array_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5238_, v_formatterName_5239_, v_array_5240_, v_a_5241_, v_a_5242_);
lean_dec_ref(v_a_5241_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object* v_ks_5244_, lean_object* v_f_5245_, lean_object* v_formatterName_5246_, lean_object* v_array_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5245_, v_formatterName_5246_, v_array_5247_, v_a_5248_, v_a_5249_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object* v_ks_5251_, lean_object* v_f_5252_, lean_object* v_formatterName_5253_, lean_object* v_array_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_Lean_Fmt_fmtArrayWith(v_ks_5251_, v_f_5252_, v_formatterName_5253_, v_array_5254_, v_a_5255_, v_a_5256_);
lean_dec_ref(v_a_5255_);
lean_dec(v_ks_5251_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object* v_sepArray_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
size_t v_sz_5261_; size_t v___x_5262_; lean_object* v___x_5263_; 
v_sz_5261_ = lean_array_size(v_sepArray_5258_);
v___x_5262_ = ((size_t)0ULL);
v___x_5263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5261_, v___x_5262_, v_sepArray_5258_, v_a_5259_, v_a_5260_);
if (lean_obj_tag(v___x_5263_) == 0)
{
lean_object* v_a_5264_; lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5272_; 
v_a_5264_ = lean_ctor_get(v___x_5263_, 0);
v_a_5265_ = lean_ctor_get(v___x_5263_, 1);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5267_ = v___x_5263_;
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_inc(v_a_5264_);
lean_dec(v___x_5263_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5270_; 
if (v_isShared_5268_ == 0)
{
v___x_5270_ = v___x_5267_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_a_5264_);
lean_ctor_set(v_reuseFailAlloc_5271_, 1, v_a_5265_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
return v___x_5270_;
}
}
}
else
{
lean_object* v_a_5273_; lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
v_a_5273_ = lean_ctor_get(v___x_5263_, 0);
v_a_5274_ = lean_ctor_get(v___x_5263_, 1);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5263_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_inc(v_a_5273_);
lean_dec(v___x_5263_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5273_);
lean_ctor_set(v_reuseFailAlloc_5280_, 1, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object* v_sepArray_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v_res_5285_; 
v_res_5285_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5282_, v_a_5283_, v_a_5284_);
lean_dec_ref(v_a_5283_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object* v_sep_5286_, lean_object* v_sepArray_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_){
_start:
{
lean_object* v___x_5290_; 
v___x_5290_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5287_, v_a_5288_, v_a_5289_);
return v___x_5290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object* v_sep_5291_, lean_object* v_sepArray_5292_, lean_object* v_a_5293_, lean_object* v_a_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_Lean_Fmt_fmtSepArray(v_sep_5291_, v_sepArray_5292_, v_a_5293_, v_a_5294_);
lean_dec_ref(v_a_5293_);
lean_dec_ref(v_sep_5291_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object* v_f_5296_, lean_object* v_formatterName_5297_, size_t v_sz_5298_, size_t v_i_5299_, lean_object* v_bs_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
uint8_t v___x_5303_; 
v___x_5303_ = lean_usize_dec_lt(v_i_5299_, v_sz_5298_);
if (v___x_5303_ == 0)
{
lean_object* v___x_5304_; 
lean_dec(v_formatterName_5297_);
lean_dec_ref(v_f_5296_);
v___x_5304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5304_, 0, v_bs_5300_);
lean_ctor_set(v___x_5304_, 1, v___y_5302_);
return v___x_5304_;
}
else
{
lean_object* v_v_5305_; lean_object* v___x_5306_; lean_object* v_bs_x27_5307_; lean_object* v___y_5309_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; uint8_t v___x_5328_; 
v_v_5305_ = lean_array_uget(v_bs_5300_, v_i_5299_);
v___x_5306_ = lean_unsigned_to_nat(0u);
v_bs_x27_5307_ = lean_array_uset(v_bs_5300_, v_i_5299_, v___x_5306_);
v___x_5325_ = lean_usize_to_nat(v_i_5299_);
v___x_5326_ = lean_unsigned_to_nat(2u);
v___x_5327_ = lean_nat_mod(v___x_5325_, v___x_5326_);
lean_dec(v___x_5325_);
v___x_5328_ = lean_nat_dec_eq(v___x_5327_, v___x_5306_);
lean_dec(v___x_5327_);
if (v___x_5328_ == 0)
{
lean_object* v___x_5329_; 
v___x_5329_ = l_Lean_Fmt_fmt(v_v_5305_, v___y_5301_, v___y_5302_);
v___y_5309_ = v___x_5329_;
goto v___jp_5308_;
}
else
{
lean_object* v___x_5330_; 
lean_inc(v_formatterName_5297_);
lean_inc_ref(v_f_5296_);
v___x_5330_ = l_Lean_Fmt_fmtWith(v_f_5296_, v_formatterName_5297_, v_v_5305_, v___y_5301_, v___y_5302_);
v___y_5309_ = v___x_5330_;
goto v___jp_5308_;
}
v___jp_5308_:
{
if (lean_obj_tag(v___y_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v_a_5311_; size_t v___x_5312_; size_t v___x_5313_; lean_object* v___x_5314_; 
v_a_5310_ = lean_ctor_get(v___y_5309_, 0);
lean_inc(v_a_5310_);
v_a_5311_ = lean_ctor_get(v___y_5309_, 1);
lean_inc(v_a_5311_);
lean_dec_ref_known(v___y_5309_, 2);
v___x_5312_ = ((size_t)1ULL);
v___x_5313_ = lean_usize_add(v_i_5299_, v___x_5312_);
v___x_5314_ = lean_array_uset(v_bs_x27_5307_, v_i_5299_, v_a_5310_);
v_i_5299_ = v___x_5313_;
v_bs_5300_ = v___x_5314_;
v___y_5302_ = v_a_5311_;
goto _start;
}
else
{
lean_object* v_a_5316_; lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5324_; 
lean_dec_ref(v_bs_x27_5307_);
lean_dec(v_formatterName_5297_);
lean_dec_ref(v_f_5296_);
v_a_5316_ = lean_ctor_get(v___y_5309_, 0);
v_a_5317_ = lean_ctor_get(v___y_5309_, 1);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___y_5309_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5319_ = v___y_5309_;
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_inc(v_a_5316_);
lean_dec(v___y_5309_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5322_; 
if (v_isShared_5320_ == 0)
{
v___x_5322_ = v___x_5319_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_a_5316_);
lean_ctor_set(v_reuseFailAlloc_5323_, 1, v_a_5317_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
return v___x_5322_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object* v_f_5331_, lean_object* v_formatterName_5332_, lean_object* v_sz_5333_, lean_object* v_i_5334_, lean_object* v_bs_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
size_t v_sz_boxed_5338_; size_t v_i_boxed_5339_; lean_object* v_res_5340_; 
v_sz_boxed_5338_ = lean_unbox_usize(v_sz_5333_);
lean_dec(v_sz_5333_);
v_i_boxed_5339_ = lean_unbox_usize(v_i_5334_);
lean_dec(v_i_5334_);
v_res_5340_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5331_, v_formatterName_5332_, v_sz_boxed_5338_, v_i_boxed_5339_, v_bs_5335_, v___y_5336_, v___y_5337_);
lean_dec_ref(v___y_5336_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object* v_f_5341_, lean_object* v_formatterName_5342_, lean_object* v_sepArray_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_){
_start:
{
size_t v_sz_5346_; size_t v___x_5347_; lean_object* v___x_5348_; 
v_sz_5346_ = lean_array_size(v_sepArray_5343_);
v___x_5347_ = ((size_t)0ULL);
v___x_5348_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5341_, v_formatterName_5342_, v_sz_5346_, v___x_5347_, v_sepArray_5343_, v_a_5344_, v_a_5345_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v_a_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5357_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
v_a_5350_ = lean_ctor_get(v___x_5348_, 1);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5352_ = v___x_5348_;
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_a_5350_);
lean_inc(v_a_5349_);
lean_dec(v___x_5348_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5357_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5355_; 
if (v_isShared_5353_ == 0)
{
v___x_5355_ = v___x_5352_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5349_);
lean_ctor_set(v_reuseFailAlloc_5356_, 1, v_a_5350_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5366_; 
v_a_5358_ = lean_ctor_get(v___x_5348_, 0);
v_a_5359_ = lean_ctor_get(v___x_5348_, 1);
v_isSharedCheck_5366_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5366_ == 0)
{
v___x_5361_ = v___x_5348_;
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_inc(v_a_5358_);
lean_dec(v___x_5348_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5366_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5364_; 
if (v_isShared_5362_ == 0)
{
v___x_5364_ = v___x_5361_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5365_; 
v_reuseFailAlloc_5365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_a_5358_);
lean_ctor_set(v_reuseFailAlloc_5365_, 1, v_a_5359_);
v___x_5364_ = v_reuseFailAlloc_5365_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
return v___x_5364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object* v_f_5367_, lean_object* v_formatterName_5368_, lean_object* v_sepArray_5369_, lean_object* v_a_5370_, lean_object* v_a_5371_){
_start:
{
lean_object* v_res_5372_; 
v_res_5372_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5367_, v_formatterName_5368_, v_sepArray_5369_, v_a_5370_, v_a_5371_);
lean_dec_ref(v_a_5370_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object* v_sep_5373_, lean_object* v_f_5374_, lean_object* v_formatterName_5375_, lean_object* v_sepArray_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_){
_start:
{
lean_object* v___x_5379_; 
v___x_5379_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5374_, v_formatterName_5375_, v_sepArray_5376_, v_a_5377_, v_a_5378_);
return v___x_5379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object* v_sep_5380_, lean_object* v_f_5381_, lean_object* v_formatterName_5382_, lean_object* v_sepArray_5383_, lean_object* v_a_5384_, lean_object* v_a_5385_){
_start:
{
lean_object* v_res_5386_; 
v_res_5386_ = l_Lean_Fmt_fmtSepArrayWith(v_sep_5380_, v_f_5381_, v_formatterName_5382_, v_sepArray_5383_, v_a_5384_, v_a_5385_);
lean_dec_ref(v_a_5384_);
lean_dec_ref(v_sep_5380_);
return v_res_5386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object* v_f_5387_, lean_object* v_formatterName_5388_, lean_object* v_as_5389_, size_t v_sz_5390_, size_t v_i_5391_, lean_object* v_bs_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_){
_start:
{
lean_object* v___x_5395_; 
v___x_5395_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5387_, v_formatterName_5388_, v_sz_5390_, v_i_5391_, v_bs_5392_, v___y_5393_, v___y_5394_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object* v_f_5396_, lean_object* v_formatterName_5397_, lean_object* v_as_5398_, lean_object* v_sz_5399_, lean_object* v_i_5400_, lean_object* v_bs_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_){
_start:
{
size_t v_sz_boxed_5404_; size_t v_i_boxed_5405_; lean_object* v_res_5406_; 
v_sz_boxed_5404_ = lean_unbox_usize(v_sz_5399_);
lean_dec(v_sz_5399_);
v_i_boxed_5405_ = lean_unbox_usize(v_i_5400_);
lean_dec(v_i_5400_);
v_res_5406_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(v_f_5396_, v_formatterName_5397_, v_as_5398_, v_sz_boxed_5404_, v_i_boxed_5405_, v_bs_5401_, v___y_5402_, v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec_ref(v_as_5398_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object* v_sepArray_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_){
_start:
{
size_t v_sz_5410_; size_t v___x_5411_; lean_object* v___x_5412_; 
v_sz_5410_ = lean_array_size(v_sepArray_5407_);
v___x_5411_ = ((size_t)0ULL);
v___x_5412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5410_, v___x_5411_, v_sepArray_5407_, v_a_5408_, v_a_5409_);
if (lean_obj_tag(v___x_5412_) == 0)
{
lean_object* v_a_5413_; lean_object* v_a_5414_; lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5421_; 
v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
v_a_5414_ = lean_ctor_get(v___x_5412_, 1);
v_isSharedCheck_5421_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5421_ == 0)
{
v___x_5416_ = v___x_5412_;
v_isShared_5417_ = v_isSharedCheck_5421_;
goto v_resetjp_5415_;
}
else
{
lean_inc(v_a_5414_);
lean_inc(v_a_5413_);
lean_dec(v___x_5412_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5421_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
lean_object* v___x_5419_; 
if (v_isShared_5417_ == 0)
{
v___x_5419_ = v___x_5416_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_a_5413_);
lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_a_5414_);
v___x_5419_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
return v___x_5419_;
}
}
}
else
{
lean_object* v_a_5422_; lean_object* v_a_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5430_; 
v_a_5422_ = lean_ctor_get(v___x_5412_, 0);
v_a_5423_ = lean_ctor_get(v___x_5412_, 1);
v_isSharedCheck_5430_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5430_ == 0)
{
v___x_5425_ = v___x_5412_;
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_a_5423_);
lean_inc(v_a_5422_);
lean_dec(v___x_5412_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5430_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v___x_5428_; 
if (v_isShared_5426_ == 0)
{
v___x_5428_ = v___x_5425_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5422_);
lean_ctor_set(v_reuseFailAlloc_5429_, 1, v_a_5423_);
v___x_5428_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
return v___x_5428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object* v_sepArray_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5431_, v_a_5432_, v_a_5433_);
lean_dec_ref(v_a_5432_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object* v_ks_5435_, lean_object* v_sep_5436_, lean_object* v_sepArray_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v___x_5440_; 
v___x_5440_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5437_, v_a_5438_, v_a_5439_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object* v_ks_5441_, lean_object* v_sep_5442_, lean_object* v_sepArray_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
lean_object* v_res_5446_; 
v_res_5446_ = l_Lean_Fmt_fmtTSepArray(v_ks_5441_, v_sep_5442_, v_sepArray_5443_, v_a_5444_, v_a_5445_);
lean_dec_ref(v_a_5444_);
lean_dec_ref(v_sep_5442_);
lean_dec(v_ks_5441_);
return v_res_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object* v_f_5447_, lean_object* v_formatterName_5448_, lean_object* v_sepArray_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_){
_start:
{
size_t v_sz_5452_; size_t v___x_5453_; lean_object* v___x_5454_; 
v_sz_5452_ = lean_array_size(v_sepArray_5449_);
v___x_5453_ = ((size_t)0ULL);
v___x_5454_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5447_, v_formatterName_5448_, v_sz_5452_, v___x_5453_, v_sepArray_5449_, v_a_5450_, v_a_5451_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5463_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
v_a_5456_ = lean_ctor_get(v___x_5454_, 1);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5458_ = v___x_5454_;
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_inc(v_a_5455_);
lean_dec(v___x_5454_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5463_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5461_; 
if (v_isShared_5459_ == 0)
{
v___x_5461_ = v___x_5458_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_a_5455_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_a_5456_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
}
else
{
lean_object* v_a_5464_; lean_object* v_a_5465_; lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5472_; 
v_a_5464_ = lean_ctor_get(v___x_5454_, 0);
v_a_5465_ = lean_ctor_get(v___x_5454_, 1);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5472_ == 0)
{
v___x_5467_ = v___x_5454_;
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
else
{
lean_inc(v_a_5465_);
lean_inc(v_a_5464_);
lean_dec(v___x_5454_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5472_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v___x_5470_; 
if (v_isShared_5468_ == 0)
{
v___x_5470_ = v___x_5467_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_a_5464_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v_a_5465_);
v___x_5470_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
return v___x_5470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object* v_f_5473_, lean_object* v_formatterName_5474_, lean_object* v_sepArray_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_){
_start:
{
lean_object* v_res_5478_; 
v_res_5478_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5473_, v_formatterName_5474_, v_sepArray_5475_, v_a_5476_, v_a_5477_);
lean_dec_ref(v_a_5476_);
return v_res_5478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object* v_ks_5479_, lean_object* v_sep_5480_, lean_object* v_f_5481_, lean_object* v_formatterName_5482_, lean_object* v_sepArray_5483_, lean_object* v_a_5484_, lean_object* v_a_5485_){
_start:
{
lean_object* v___x_5486_; 
v___x_5486_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5481_, v_formatterName_5482_, v_sepArray_5483_, v_a_5484_, v_a_5485_);
return v___x_5486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object* v_ks_5487_, lean_object* v_sep_5488_, lean_object* v_f_5489_, lean_object* v_formatterName_5490_, lean_object* v_sepArray_5491_, lean_object* v_a_5492_, lean_object* v_a_5493_){
_start:
{
lean_object* v_res_5494_; 
v_res_5494_ = l_Lean_Fmt_fmtTSepArrayWith(v_ks_5487_, v_sep_5488_, v_f_5489_, v_formatterName_5490_, v_sepArray_5491_, v_a_5492_, v_a_5493_);
lean_dec_ref(v_a_5492_);
lean_dec_ref(v_sep_5488_);
lean_dec(v_ks_5487_);
return v_res_5494_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(uint8_t v___x_5495_, lean_object* v___x_5496_, lean_object* v___x_5497_, lean_object* v___x_5498_, lean_object* v_a_5499_, lean_object* v_b_5500_){
_start:
{
lean_object* v___x_5501_; uint8_t v_decide_5502_; 
v___x_5501_ = lean_nat_sub(v___x_5496_, v___x_5497_);
v_decide_5502_ = lean_nat_dec_eq(v_a_5499_, v___x_5501_);
lean_dec(v___x_5501_);
if (v_decide_5502_ == 0)
{
uint32_t v___x_5503_; lean_object* v___x_5504_; uint32_t v___x_5505_; uint8_t v___x_5506_; 
v___x_5503_ = 10;
v___x_5504_ = lean_nat_add(v___x_5497_, v_a_5499_);
v___x_5505_ = lean_string_utf8_get_fast(v___x_5498_, v___x_5504_);
v___x_5506_ = lean_uint32_dec_eq(v___x_5505_, v___x_5503_);
if (v___x_5506_ == 0)
{
lean_object* v___x_5507_; lean_object* v___x_5508_; 
lean_dec(v_a_5499_);
v___x_5507_ = lean_string_utf8_next_fast(v___x_5498_, v___x_5504_);
lean_dec(v___x_5504_);
v___x_5508_ = lean_nat_sub(v___x_5507_, v___x_5497_);
v_a_5499_ = v___x_5508_;
goto _start;
}
else
{
lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; 
v___x_5510_ = lean_string_utf8_next_fast(v___x_5498_, v___x_5504_);
v___x_5511_ = lean_nat_sub(v___x_5510_, v___x_5504_);
lean_dec(v___x_5504_);
v___x_5512_ = lean_nat_add(v_a_5499_, v___x_5511_);
lean_dec(v___x_5511_);
lean_dec(v_a_5499_);
if (v___x_5495_ == 0)
{
v_a_5499_ = v___x_5512_;
goto _start;
}
else
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = lean_unsigned_to_nat(1u);
v___x_5515_ = lean_nat_add(v_b_5500_, v___x_5514_);
lean_dec(v_b_5500_);
v_a_5499_ = v___x_5512_;
v_b_5500_ = v___x_5515_;
goto _start;
}
}
}
else
{
lean_dec(v_a_5499_);
return v_b_5500_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___x_5517_, lean_object* v___x_5518_, lean_object* v___x_5519_, lean_object* v___x_5520_, lean_object* v_a_5521_, lean_object* v_b_5522_){
_start:
{
uint8_t v___x_2013__boxed_5523_; lean_object* v_res_5524_; 
v___x_2013__boxed_5523_ = lean_unbox(v___x_5517_);
v_res_5524_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_2013__boxed_5523_, v___x_5518_, v___x_5519_, v___x_5520_, v_a_5521_, v_b_5522_);
lean_dec_ref(v___x_5520_);
lean_dec(v___x_5519_);
lean_dec(v___x_5518_);
return v_res_5524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5527_, lean_object* v_minNewlines_5528_, lean_object* v_leadingTk_5529_, lean_object* v_leading_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_){
_start:
{
lean_object* v___y_5540_; lean_object* v___y_5551_; lean_object* v_str_5553_; lean_object* v_startPos_5554_; lean_object* v_stopPos_5555_; uint8_t v___x_5556_; 
v_str_5553_ = lean_ctor_get(v_leading_5530_, 0);
v_startPos_5554_ = lean_ctor_get(v_leading_5530_, 1);
v_stopPos_5555_ = lean_ctor_get(v_leading_5530_, 2);
v___x_5556_ = lean_string_is_valid_pos(v_str_5553_, v_startPos_5554_);
if (v___x_5556_ == 0)
{
lean_dec(v_minNewlines_5528_);
lean_dec(v_maxNewlines_5527_);
goto v___jp_5533_;
}
else
{
uint8_t v___x_5557_; 
v___x_5557_ = lean_string_is_valid_pos(v_str_5553_, v_stopPos_5555_);
if (v___x_5557_ == 0)
{
lean_dec(v_minNewlines_5528_);
lean_dec(v_maxNewlines_5527_);
goto v___jp_5533_;
}
else
{
uint8_t v___x_5558_; 
v___x_5558_ = lean_nat_dec_le(v_startPos_5554_, v_stopPos_5555_);
if (v___x_5558_ == 0)
{
lean_dec(v_minNewlines_5528_);
lean_dec(v_maxNewlines_5527_);
goto v___jp_5533_;
}
else
{
lean_object* v_searcher_5559_; lean_object* v_numNewlines_5560_; uint8_t v___x_5561_; 
lean_dec(v_leadingTk_5529_);
v_searcher_5559_ = lean_unsigned_to_nat(0u);
v_numNewlines_5560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5558_, v_stopPos_5555_, v_startPos_5554_, v_str_5553_, v_searcher_5559_, v_searcher_5559_);
v___x_5561_ = lean_nat_dec_le(v_numNewlines_5560_, v_minNewlines_5528_);
if (v___x_5561_ == 0)
{
lean_dec(v_minNewlines_5528_);
v___y_5551_ = v_numNewlines_5560_;
goto v___jp_5550_;
}
else
{
lean_dec(v_numNewlines_5560_);
v___y_5551_ = v_minNewlines_5528_;
goto v___jp_5550_;
}
}
}
}
v___jp_5533_:
{
lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; 
v___x_5534_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5535_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5536_, 0, v_leadingTk_5529_);
lean_ctor_set(v___x_5536_, 1, v___x_5534_);
lean_ctor_set(v___x_5536_, 2, v___x_5535_);
v___x_5537_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5536_);
v___x_5538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5537_);
lean_ctor_set(v___x_5538_, 1, v___y_5532_);
return v___x_5538_;
}
v___jp_5539_:
{
lean_object* v___x_5541_; lean_object* v_nls_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5541_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5542_ = lean_mk_array(v___y_5540_, v___x_5541_);
v___x_5543_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5542_);
v___x_5544_ = lean_box(0);
v___x_5545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5543_);
lean_ctor_set(v___x_5545_, 1, v___x_5544_);
v___x_5546_ = lean_unsigned_to_nat(1u);
v___x_5547_ = lean_mk_empty_array_with_capacity(v___x_5546_);
v___x_5548_ = lean_array_push(v___x_5547_, v___x_5545_);
v___x_5549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
lean_ctor_set(v___x_5549_, 1, v___y_5532_);
return v___x_5549_;
}
v___jp_5550_:
{
uint8_t v___x_5552_; 
v___x_5552_ = lean_nat_dec_le(v___y_5551_, v_maxNewlines_5527_);
if (v___x_5552_ == 0)
{
lean_dec(v___y_5551_);
v___y_5540_ = v_maxNewlines_5527_;
goto v___jp_5539_;
}
else
{
lean_dec(v_maxNewlines_5527_);
v___y_5540_ = v___y_5551_;
goto v___jp_5539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5562_, lean_object* v_minNewlines_5563_, lean_object* v_leadingTk_5564_, lean_object* v_leading_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_){
_start:
{
lean_object* v_res_5568_; 
v_res_5568_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(v_maxNewlines_5562_, v_minNewlines_5563_, v_leadingTk_5564_, v_leading_5565_, v___y_5566_, v___y_5567_);
lean_dec_ref(v___y_5566_);
lean_dec_ref(v_leading_5565_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object* v_stx_5569_, lean_object* v_minNewlines_5570_, lean_object* v_maxNewlines_5571_, lean_object* v_a_5572_, lean_object* v_a_5573_){
_start:
{
lean_object* v___f_5574_; lean_object* v___x_5575_; 
v___f_5574_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5574_, 0, v_maxNewlines_5571_);
lean_closure_set(v___f_5574_, 1, v_minNewlines_5570_);
v___x_5575_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_5569_, v___f_5574_, v_a_5572_, v_a_5573_);
return v___x_5575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object* v_stx_5576_, lean_object* v_minNewlines_5577_, lean_object* v_maxNewlines_5578_, lean_object* v_a_5579_, lean_object* v_a_5580_){
_start:
{
lean_object* v_res_5581_; 
v_res_5581_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines(v_stx_5576_, v_minNewlines_5577_, v_maxNewlines_5578_, v_a_5579_, v_a_5580_);
lean_dec_ref(v_a_5579_);
return v_res_5581_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(uint8_t v___x_5582_, lean_object* v___x_5583_, lean_object* v___x_5584_, lean_object* v___x_5585_, lean_object* v___x_5586_, lean_object* v_inst_5587_, lean_object* v_R_5588_, lean_object* v_a_5589_, lean_object* v_b_5590_, lean_object* v_c_5591_){
_start:
{
lean_object* v___x_5592_; 
v___x_5592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5582_, v___x_5583_, v___x_5584_, v___x_5586_, v_a_5589_, v_b_5590_);
return v___x_5592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object* v___x_5593_, lean_object* v___x_5594_, lean_object* v___x_5595_, lean_object* v___x_5596_, lean_object* v___x_5597_, lean_object* v_inst_5598_, lean_object* v_R_5599_, lean_object* v_a_5600_, lean_object* v_b_5601_, lean_object* v_c_5602_){
_start:
{
uint8_t v___x_2122__boxed_5603_; lean_object* v_res_5604_; 
v___x_2122__boxed_5603_ = lean_unbox(v___x_5593_);
v_res_5604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(v___x_2122__boxed_5603_, v___x_5594_, v___x_5595_, v___x_5596_, v___x_5597_, v_inst_5598_, v_R_5599_, v_a_5600_, v_b_5601_, v_c_5602_);
lean_dec_ref(v___x_5597_);
lean_dec_ref(v___x_5596_);
lean_dec(v___x_5595_);
lean_dec(v___x_5594_);
return v_res_5604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5605_, lean_object* v_minNewlines_5606_, lean_object* v_trailingTk_5607_, lean_object* v_trailing_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_){
_start:
{
lean_object* v___y_5618_; lean_object* v___y_5629_; lean_object* v_str_5631_; lean_object* v_startPos_5632_; lean_object* v_stopPos_5633_; uint8_t v___x_5634_; 
v_str_5631_ = lean_ctor_get(v_trailing_5608_, 0);
v_startPos_5632_ = lean_ctor_get(v_trailing_5608_, 1);
v_stopPos_5633_ = lean_ctor_get(v_trailing_5608_, 2);
v___x_5634_ = lean_string_is_valid_pos(v_str_5631_, v_startPos_5632_);
if (v___x_5634_ == 0)
{
lean_dec(v_minNewlines_5606_);
lean_dec(v_maxNewlines_5605_);
goto v___jp_5611_;
}
else
{
uint8_t v___x_5635_; 
v___x_5635_ = lean_string_is_valid_pos(v_str_5631_, v_stopPos_5633_);
if (v___x_5635_ == 0)
{
lean_dec(v_minNewlines_5606_);
lean_dec(v_maxNewlines_5605_);
goto v___jp_5611_;
}
else
{
uint8_t v___x_5636_; 
v___x_5636_ = lean_nat_dec_le(v_startPos_5632_, v_stopPos_5633_);
if (v___x_5636_ == 0)
{
lean_dec(v_minNewlines_5606_);
lean_dec(v_maxNewlines_5605_);
goto v___jp_5611_;
}
else
{
lean_object* v_searcher_5637_; lean_object* v_numNewlines_5638_; uint8_t v___x_5639_; 
lean_dec(v_trailingTk_5607_);
v_searcher_5637_ = lean_unsigned_to_nat(0u);
v_numNewlines_5638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5636_, v_stopPos_5633_, v_startPos_5632_, v_str_5631_, v_searcher_5637_, v_searcher_5637_);
v___x_5639_ = lean_nat_dec_le(v_numNewlines_5638_, v_minNewlines_5606_);
if (v___x_5639_ == 0)
{
lean_dec(v_minNewlines_5606_);
v___y_5629_ = v_numNewlines_5638_;
goto v___jp_5628_;
}
else
{
lean_dec(v_numNewlines_5638_);
v___y_5629_ = v_minNewlines_5606_;
goto v___jp_5628_;
}
}
}
}
v___jp_5611_:
{
lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; 
v___x_5612_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5613_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5614_, 0, v_trailingTk_5607_);
lean_ctor_set(v___x_5614_, 1, v___x_5612_);
lean_ctor_set(v___x_5614_, 2, v___x_5613_);
v___x_5615_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5615_, 0, v___x_5614_);
v___x_5616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
lean_ctor_set(v___x_5616_, 1, v___y_5610_);
return v___x_5616_;
}
v___jp_5617_:
{
lean_object* v___x_5619_; lean_object* v_nls_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v___x_5619_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5620_ = lean_mk_array(v___y_5618_, v___x_5619_);
v___x_5621_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5620_);
v___x_5622_ = lean_box(0);
v___x_5623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5621_);
lean_ctor_set(v___x_5623_, 1, v___x_5622_);
v___x_5624_ = lean_unsigned_to_nat(1u);
v___x_5625_ = lean_mk_empty_array_with_capacity(v___x_5624_);
v___x_5626_ = lean_array_push(v___x_5625_, v___x_5623_);
v___x_5627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___x_5626_);
lean_ctor_set(v___x_5627_, 1, v___y_5610_);
return v___x_5627_;
}
v___jp_5628_:
{
uint8_t v___x_5630_; 
v___x_5630_ = lean_nat_dec_le(v___y_5629_, v_maxNewlines_5605_);
if (v___x_5630_ == 0)
{
lean_dec(v___y_5629_);
v___y_5618_ = v_maxNewlines_5605_;
goto v___jp_5617_;
}
else
{
lean_dec(v_maxNewlines_5605_);
v___y_5618_ = v___y_5629_;
goto v___jp_5617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5640_, lean_object* v_minNewlines_5641_, lean_object* v_trailingTk_5642_, lean_object* v_trailing_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(v_maxNewlines_5640_, v_minNewlines_5641_, v_trailingTk_5642_, v_trailing_5643_, v___y_5644_, v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec_ref(v_trailing_5643_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object* v_stx_5647_, lean_object* v_minNewlines_5648_, lean_object* v_maxNewlines_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_){
_start:
{
lean_object* v___f_5652_; lean_object* v___x_5653_; 
v___f_5652_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5652_, 0, v_maxNewlines_5649_);
lean_closure_set(v___f_5652_, 1, v_minNewlines_5648_);
v___x_5653_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_5647_, v___f_5652_, v_a_5650_, v_a_5651_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object* v_stx_5654_, lean_object* v_minNewlines_5655_, lean_object* v_maxNewlines_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_){
_start:
{
lean_object* v_res_5659_; 
v_res_5659_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v_stx_5654_, v_minNewlines_5655_, v_maxNewlines_5656_, v_a_5657_, v_a_5658_);
lean_dec_ref(v_a_5657_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object* v_b_5660_, lean_object* v_a_5661_, lean_object* v_trailingDoc_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_){
_start:
{
lean_object* v___y_5666_; uint8_t v___x_5670_; 
v___x_5670_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_5661_);
if (v___x_5670_ == 0)
{
uint8_t v___x_5671_; 
v___x_5671_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_trailingDoc_5662_);
if (v___x_5671_ == 0)
{
lean_object* v_doc_5672_; lean_object* v_doc_5673_; uint8_t v___x_5674_; 
v_doc_5672_ = lean_ctor_get(v_a_5661_, 0);
lean_inc(v_doc_5672_);
lean_dec_ref(v_a_5661_);
v_doc_5673_ = lean_ctor_get(v_trailingDoc_5662_, 0);
lean_inc(v_doc_5673_);
lean_dec_ref(v_trailingDoc_5662_);
v___x_5674_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5672_);
if (v___x_5674_ == 0)
{
uint8_t v___x_5675_; 
v___x_5675_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5673_);
if (v___x_5675_ == 0)
{
lean_object* v___x_5676_; lean_object* v___x_5677_; 
v___x_5676_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_5672_, v_doc_5673_);
v___x_5677_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_5676_);
v___y_5666_ = v___x_5677_;
goto v___jp_5665_;
}
else
{
lean_object* v___x_5678_; 
lean_dec(v_doc_5673_);
v___x_5678_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5672_);
v___y_5666_ = v___x_5678_;
goto v___jp_5665_;
}
}
else
{
lean_object* v___x_5679_; 
lean_dec(v_doc_5672_);
v___x_5679_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5673_);
v___y_5666_ = v___x_5679_;
goto v___jp_5665_;
}
}
else
{
lean_dec_ref(v_trailingDoc_5662_);
v___y_5666_ = v_a_5661_;
goto v___jp_5665_;
}
}
else
{
lean_dec_ref(v_a_5661_);
v___y_5666_ = v_trailingDoc_5662_;
goto v___jp_5665_;
}
v___jp_5665_:
{
lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; 
v___x_5667_ = lean_array_push(v_b_5660_, v___y_5666_);
v___x_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
v___x_5669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5669_, 0, v___x_5668_);
lean_ctor_set(v___x_5669_, 1, v___y_5664_);
return v___x_5669_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object* v_b_5680_, lean_object* v_a_5681_, lean_object* v_trailingDoc_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5680_, v_a_5681_, v_trailingDoc_5682_, v___y_5683_, v___y_5684_);
lean_dec_ref(v___y_5683_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object* v_upperBound_5686_, lean_object* v_stxs_5687_, lean_object* v___x_5688_, lean_object* v_a_5689_, lean_object* v_b_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
uint8_t v___x_5693_; 
v___x_5693_ = lean_nat_dec_lt(v_a_5689_, v_upperBound_5686_);
if (v___x_5693_ == 0)
{
lean_object* v___x_5694_; 
lean_dec(v_a_5689_);
v___x_5694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5694_, 0, v_b_5690_);
lean_ctor_set(v___x_5694_, 1, v___y_5692_);
return v___x_5694_;
}
else
{
lean_object* v___x_5695_; lean_object* v___x_5696_; 
v___x_5695_ = lean_array_fget_borrowed(v_stxs_5687_, v_a_5689_);
lean_inc(v___x_5695_);
v___x_5696_ = l_Lean_Fmt_fmt(v___x_5695_, v___y_5691_, v___y_5692_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v_a_5698_; lean_object* v___x_5699_; lean_object* v___y_5701_; lean_object* v___x_5726_; uint8_t v___x_5727_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
lean_inc(v_a_5697_);
v_a_5698_ = lean_ctor_get(v___x_5696_, 1);
lean_inc(v_a_5698_);
lean_dec_ref_known(v___x_5696_, 2);
v___x_5699_ = lean_unsigned_to_nat(1u);
v___x_5726_ = lean_nat_sub(v___x_5688_, v___x_5699_);
v___x_5727_ = lean_nat_dec_lt(v_a_5689_, v___x_5726_);
lean_dec(v___x_5726_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; lean_object* v___x_5729_; 
v___x_5728_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5729_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5690_, v_a_5697_, v___x_5728_, v___y_5691_, v_a_5698_);
v___y_5701_ = v___x_5729_;
goto v___jp_5700_;
}
else
{
lean_object* v___x_5730_; lean_object* v___x_5731_; 
v___x_5730_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5695_);
v___x_5731_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v___x_5695_, v___x_5699_, v___x_5730_, v___y_5691_, v_a_5698_);
if (lean_obj_tag(v___x_5731_) == 0)
{
lean_object* v_a_5732_; lean_object* v_a_5733_; lean_object* v___x_5734_; 
v_a_5732_ = lean_ctor_get(v___x_5731_, 0);
lean_inc(v_a_5732_);
v_a_5733_ = lean_ctor_get(v___x_5731_, 1);
lean_inc(v_a_5733_);
lean_dec_ref_known(v___x_5731_, 2);
v___x_5734_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5690_, v_a_5697_, v_a_5732_, v___y_5691_, v_a_5733_);
v___y_5701_ = v___x_5734_;
goto v___jp_5700_;
}
else
{
lean_object* v_a_5735_; lean_object* v_a_5736_; lean_object* v___x_5738_; uint8_t v_isShared_5739_; uint8_t v_isSharedCheck_5743_; 
lean_dec(v_a_5697_);
lean_dec_ref(v_b_5690_);
lean_dec(v_a_5689_);
v_a_5735_ = lean_ctor_get(v___x_5731_, 0);
v_a_5736_ = lean_ctor_get(v___x_5731_, 1);
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5731_);
if (v_isSharedCheck_5743_ == 0)
{
v___x_5738_ = v___x_5731_;
v_isShared_5739_ = v_isSharedCheck_5743_;
goto v_resetjp_5737_;
}
else
{
lean_inc(v_a_5736_);
lean_inc(v_a_5735_);
lean_dec(v___x_5731_);
v___x_5738_ = lean_box(0);
v_isShared_5739_ = v_isSharedCheck_5743_;
goto v_resetjp_5737_;
}
v_resetjp_5737_:
{
lean_object* v___x_5741_; 
if (v_isShared_5739_ == 0)
{
v___x_5741_ = v___x_5738_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_a_5735_);
lean_ctor_set(v_reuseFailAlloc_5742_, 1, v_a_5736_);
v___x_5741_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
return v___x_5741_;
}
}
}
}
v___jp_5700_:
{
if (lean_obj_tag(v___y_5701_) == 0)
{
lean_object* v_a_5702_; 
v_a_5702_ = lean_ctor_get(v___y_5701_, 0);
lean_inc(v_a_5702_);
if (lean_obj_tag(v_a_5702_) == 0)
{
lean_object* v_a_5703_; lean_object* v___x_5705_; uint8_t v_isShared_5706_; uint8_t v_isSharedCheck_5711_; 
lean_dec(v_a_5689_);
v_a_5703_ = lean_ctor_get(v___y_5701_, 1);
v_isSharedCheck_5711_ = !lean_is_exclusive(v___y_5701_);
if (v_isSharedCheck_5711_ == 0)
{
lean_object* v_unused_5712_; 
v_unused_5712_ = lean_ctor_get(v___y_5701_, 0);
lean_dec(v_unused_5712_);
v___x_5705_ = v___y_5701_;
v_isShared_5706_ = v_isSharedCheck_5711_;
goto v_resetjp_5704_;
}
else
{
lean_inc(v_a_5703_);
lean_dec(v___y_5701_);
v___x_5705_ = lean_box(0);
v_isShared_5706_ = v_isSharedCheck_5711_;
goto v_resetjp_5704_;
}
v_resetjp_5704_:
{
lean_object* v_a_5707_; lean_object* v___x_5709_; 
v_a_5707_ = lean_ctor_get(v_a_5702_, 0);
lean_inc(v_a_5707_);
lean_dec_ref_known(v_a_5702_, 1);
if (v_isShared_5706_ == 0)
{
lean_ctor_set(v___x_5705_, 0, v_a_5707_);
v___x_5709_ = v___x_5705_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_a_5707_);
lean_ctor_set(v_reuseFailAlloc_5710_, 1, v_a_5703_);
v___x_5709_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
return v___x_5709_;
}
}
}
else
{
lean_object* v_a_5713_; lean_object* v_a_5714_; lean_object* v___x_5715_; 
v_a_5713_ = lean_ctor_get(v___y_5701_, 1);
lean_inc(v_a_5713_);
lean_dec_ref_known(v___y_5701_, 2);
v_a_5714_ = lean_ctor_get(v_a_5702_, 0);
lean_inc(v_a_5714_);
lean_dec_ref_known(v_a_5702_, 1);
v___x_5715_ = lean_nat_add(v_a_5689_, v___x_5699_);
lean_dec(v_a_5689_);
v_a_5689_ = v___x_5715_;
v_b_5690_ = v_a_5714_;
v___y_5692_ = v_a_5713_;
goto _start;
}
}
else
{
lean_object* v_a_5717_; lean_object* v_a_5718_; lean_object* v___x_5720_; uint8_t v_isShared_5721_; uint8_t v_isSharedCheck_5725_; 
lean_dec(v_a_5689_);
v_a_5717_ = lean_ctor_get(v___y_5701_, 0);
v_a_5718_ = lean_ctor_get(v___y_5701_, 1);
v_isSharedCheck_5725_ = !lean_is_exclusive(v___y_5701_);
if (v_isSharedCheck_5725_ == 0)
{
v___x_5720_ = v___y_5701_;
v_isShared_5721_ = v_isSharedCheck_5725_;
goto v_resetjp_5719_;
}
else
{
lean_inc(v_a_5718_);
lean_inc(v_a_5717_);
lean_dec(v___y_5701_);
v___x_5720_ = lean_box(0);
v_isShared_5721_ = v_isSharedCheck_5725_;
goto v_resetjp_5719_;
}
v_resetjp_5719_:
{
lean_object* v___x_5723_; 
if (v_isShared_5721_ == 0)
{
v___x_5723_ = v___x_5720_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_a_5717_);
lean_ctor_set(v_reuseFailAlloc_5724_, 1, v_a_5718_);
v___x_5723_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
return v___x_5723_;
}
}
}
}
}
else
{
lean_object* v_a_5744_; lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec_ref(v_b_5690_);
lean_dec(v_a_5689_);
v_a_5744_ = lean_ctor_get(v___x_5696_, 0);
v_a_5745_ = lean_ctor_get(v___x_5696_, 1);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5696_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_inc(v_a_5744_);
lean_dec(v___x_5696_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5748_ == 0)
{
v___x_5750_ = v___x_5747_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5744_);
lean_ctor_set(v_reuseFailAlloc_5751_, 1, v_a_5745_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object* v_upperBound_5753_, lean_object* v_stxs_5754_, lean_object* v___x_5755_, lean_object* v_a_5756_, lean_object* v_b_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_){
_start:
{
lean_object* v_res_5760_; 
v_res_5760_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5753_, v_stxs_5754_, v___x_5755_, v_a_5756_, v_b_5757_, v___y_5758_, v___y_5759_);
lean_dec_ref(v___y_5758_);
lean_dec(v___x_5755_);
lean_dec_ref(v_stxs_5754_);
lean_dec(v_upperBound_5753_);
return v_res_5760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object* v_stxs_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_){
_start:
{
lean_object* v___x_5766_; lean_object* v___x_5767_; uint8_t v___x_5768_; 
v___x_5766_ = lean_array_get_size(v_stxs_5763_);
v___x_5767_ = lean_unsigned_to_nat(1u);
v___x_5768_ = lean_nat_dec_eq(v___x_5766_, v___x_5767_);
if (v___x_5768_ == 0)
{
lean_object* v___x_5769_; lean_object* v_acc_5770_; lean_object* v___x_5771_; 
v___x_5769_ = lean_unsigned_to_nat(0u);
v_acc_5770_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_5771_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v___x_5766_, v_stxs_5763_, v___x_5766_, v___x_5769_, v_acc_5770_, v_a_5764_, v_a_5765_);
if (lean_obj_tag(v___x_5771_) == 0)
{
lean_object* v_a_5772_; lean_object* v_a_5773_; lean_object* v___x_5775_; uint8_t v_isShared_5776_; uint8_t v_isSharedCheck_5781_; 
v_a_5772_ = lean_ctor_get(v___x_5771_, 0);
v_a_5773_ = lean_ctor_get(v___x_5771_, 1);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___x_5771_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5775_ = v___x_5771_;
v_isShared_5776_ = v_isSharedCheck_5781_;
goto v_resetjp_5774_;
}
else
{
lean_inc(v_a_5773_);
lean_inc(v_a_5772_);
lean_dec(v___x_5771_);
v___x_5775_ = lean_box(0);
v_isShared_5776_ = v_isSharedCheck_5781_;
goto v_resetjp_5774_;
}
v_resetjp_5774_:
{
lean_object* v___x_5777_; lean_object* v___x_5779_; 
v___x_5777_ = l_Lean_Fmt_TaggedDoc_join(v_a_5772_);
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 0, v___x_5777_);
v___x_5779_ = v___x_5775_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5777_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v_a_5773_);
v___x_5779_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
return v___x_5779_;
}
}
}
else
{
lean_object* v_a_5782_; lean_object* v_a_5783_; lean_object* v___x_5785_; uint8_t v_isShared_5786_; uint8_t v_isSharedCheck_5790_; 
v_a_5782_ = lean_ctor_get(v___x_5771_, 0);
v_a_5783_ = lean_ctor_get(v___x_5771_, 1);
v_isSharedCheck_5790_ = !lean_is_exclusive(v___x_5771_);
if (v_isSharedCheck_5790_ == 0)
{
v___x_5785_ = v___x_5771_;
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
else
{
lean_inc(v_a_5783_);
lean_inc(v_a_5782_);
lean_dec(v___x_5771_);
v___x_5785_ = lean_box(0);
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
v_resetjp_5784_:
{
lean_object* v___x_5788_; 
if (v_isShared_5786_ == 0)
{
v___x_5788_ = v___x_5785_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_a_5782_);
lean_ctor_set(v_reuseFailAlloc_5789_, 1, v_a_5783_);
v___x_5788_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
return v___x_5788_;
}
}
}
}
else
{
lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; 
v___x_5791_ = lean_box(0);
v___x_5792_ = lean_unsigned_to_nat(0u);
v___x_5793_ = lean_array_get_borrowed(v___x_5791_, v_stxs_5763_, v___x_5792_);
lean_inc(v___x_5793_);
v___x_5794_ = l_Lean_Fmt_fmt(v___x_5793_, v_a_5764_, v_a_5765_);
return v___x_5794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object* v_stxs_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_){
_start:
{
lean_object* v_res_5798_; 
v_res_5798_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(v_stxs_5795_, v_a_5796_, v_a_5797_);
lean_dec_ref(v_a_5796_);
lean_dec_ref(v_stxs_5795_);
return v_res_5798_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object* v_upperBound_5799_, lean_object* v_stxs_5800_, lean_object* v___x_5801_, lean_object* v_inst_5802_, lean_object* v_R_5803_, lean_object* v_a_5804_, lean_object* v_b_5805_, lean_object* v_c_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v___x_5809_; 
v___x_5809_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5799_, v_stxs_5800_, v___x_5801_, v_a_5804_, v_b_5805_, v___y_5807_, v___y_5808_);
return v___x_5809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object* v_upperBound_5810_, lean_object* v_stxs_5811_, lean_object* v___x_5812_, lean_object* v_inst_5813_, lean_object* v_R_5814_, lean_object* v_a_5815_, lean_object* v_b_5816_, lean_object* v_c_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_){
_start:
{
lean_object* v_res_5820_; 
v_res_5820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(v_upperBound_5810_, v_stxs_5811_, v___x_5812_, v_inst_5813_, v_R_5814_, v_a_5815_, v_b_5816_, v_c_5817_, v___y_5818_, v___y_5819_);
lean_dec_ref(v___y_5818_);
lean_dec(v___x_5812_);
lean_dec_ref(v_stxs_5811_);
lean_dec(v_upperBound_5810_);
return v_res_5820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object* v_comments_5821_, lean_object* v_out_5822_, lean_object* v_a_5823_){
_start:
{
lean_object* v___x_5824_; uint8_t v___x_5825_; 
v___x_5824_ = lean_array_get_size(v_comments_5821_);
v___x_5825_ = lean_nat_dec_lt(v_a_5823_, v___x_5824_);
if (v___x_5825_ == 0)
{
return v_a_5823_;
}
else
{
lean_object* v___x_5826_; lean_object* v_originalWhitespaceRange_5827_; lean_object* v_stop_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; uint8_t v___x_5831_; 
v___x_5826_ = lean_array_fget_borrowed(v_comments_5821_, v_a_5823_);
v_originalWhitespaceRange_5827_ = lean_ctor_get(v___x_5826_, 1);
v_stop_5828_ = lean_ctor_get(v_originalWhitespaceRange_5827_, 1);
v___x_5829_ = lean_unsigned_to_nat(1u);
v___x_5830_ = lean_nat_add(v_out_5822_, v___x_5829_);
v___x_5831_ = lean_nat_dec_le(v___x_5830_, v_stop_5828_);
lean_dec(v___x_5830_);
if (v___x_5831_ == 0)
{
lean_object* v___x_5832_; 
v___x_5832_ = lean_nat_add(v_a_5823_, v___x_5829_);
lean_dec(v_a_5823_);
v_a_5823_ = v___x_5832_;
goto _start;
}
else
{
return v_a_5823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object* v_comments_5834_, lean_object* v_out_5835_, lean_object* v_a_5836_){
_start:
{
lean_object* v_res_5837_; 
v_res_5837_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5834_, v_out_5835_, v_a_5836_);
lean_dec(v_out_5835_);
lean_dec_ref(v_comments_5834_);
return v_res_5837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_5838_, lean_object* v_x_5839_){
_start:
{
if (lean_obj_tag(v_x_5839_) == 0)
{
return v_x_5838_;
}
else
{
lean_object* v_key_5840_; lean_object* v_value_5841_; lean_object* v_tail_5842_; lean_object* v___x_5844_; uint8_t v_isShared_5845_; uint8_t v_isSharedCheck_5865_; 
v_key_5840_ = lean_ctor_get(v_x_5839_, 0);
v_value_5841_ = lean_ctor_get(v_x_5839_, 1);
v_tail_5842_ = lean_ctor_get(v_x_5839_, 2);
v_isSharedCheck_5865_ = !lean_is_exclusive(v_x_5839_);
if (v_isSharedCheck_5865_ == 0)
{
v___x_5844_ = v_x_5839_;
v_isShared_5845_ = v_isSharedCheck_5865_;
goto v_resetjp_5843_;
}
else
{
lean_inc(v_tail_5842_);
lean_inc(v_value_5841_);
lean_inc(v_key_5840_);
lean_dec(v_x_5839_);
v___x_5844_ = lean_box(0);
v_isShared_5845_ = v_isSharedCheck_5865_;
goto v_resetjp_5843_;
}
v_resetjp_5843_:
{
lean_object* v___x_5846_; uint64_t v___x_5847_; uint64_t v___x_5848_; uint64_t v___x_5849_; uint64_t v_fold_5850_; uint64_t v___x_5851_; uint64_t v___x_5852_; uint64_t v___x_5853_; size_t v___x_5854_; size_t v___x_5855_; size_t v___x_5856_; size_t v___x_5857_; size_t v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5861_; 
v___x_5846_ = lean_array_get_size(v_x_5838_);
v___x_5847_ = lean_uint64_of_nat(v_key_5840_);
v___x_5848_ = 32ULL;
v___x_5849_ = lean_uint64_shift_right(v___x_5847_, v___x_5848_);
v_fold_5850_ = lean_uint64_xor(v___x_5847_, v___x_5849_);
v___x_5851_ = 16ULL;
v___x_5852_ = lean_uint64_shift_right(v_fold_5850_, v___x_5851_);
v___x_5853_ = lean_uint64_xor(v_fold_5850_, v___x_5852_);
v___x_5854_ = lean_uint64_to_usize(v___x_5853_);
v___x_5855_ = lean_usize_of_nat(v___x_5846_);
v___x_5856_ = ((size_t)1ULL);
v___x_5857_ = lean_usize_sub(v___x_5855_, v___x_5856_);
v___x_5858_ = lean_usize_land(v___x_5854_, v___x_5857_);
v___x_5859_ = lean_array_uget_borrowed(v_x_5838_, v___x_5858_);
lean_inc(v___x_5859_);
if (v_isShared_5845_ == 0)
{
lean_ctor_set(v___x_5844_, 2, v___x_5859_);
v___x_5861_ = v___x_5844_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_key_5840_);
lean_ctor_set(v_reuseFailAlloc_5864_, 1, v_value_5841_);
lean_ctor_set(v_reuseFailAlloc_5864_, 2, v___x_5859_);
v___x_5861_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
lean_object* v___x_5862_; 
v___x_5862_ = lean_array_uset(v_x_5838_, v___x_5858_, v___x_5861_);
v_x_5838_ = v___x_5862_;
v_x_5839_ = v_tail_5842_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object* v_i_5866_, lean_object* v_source_5867_, lean_object* v_target_5868_){
_start:
{
lean_object* v___x_5869_; uint8_t v___x_5870_; 
v___x_5869_ = lean_array_get_size(v_source_5867_);
v___x_5870_ = lean_nat_dec_lt(v_i_5866_, v___x_5869_);
if (v___x_5870_ == 0)
{
lean_dec_ref(v_source_5867_);
lean_dec(v_i_5866_);
return v_target_5868_;
}
else
{
lean_object* v_es_5871_; lean_object* v___x_5872_; lean_object* v_source_5873_; lean_object* v_target_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; 
v_es_5871_ = lean_array_fget(v_source_5867_, v_i_5866_);
v___x_5872_ = lean_box(0);
v_source_5873_ = lean_array_fset(v_source_5867_, v_i_5866_, v___x_5872_);
v_target_5874_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_target_5868_, v_es_5871_);
v___x_5875_ = lean_unsigned_to_nat(1u);
v___x_5876_ = lean_nat_add(v_i_5866_, v___x_5875_);
lean_dec(v_i_5866_);
v_i_5866_ = v___x_5876_;
v_source_5867_ = v_source_5873_;
v_target_5868_ = v_target_5874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object* v_data_5878_){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v_nbuckets_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5879_ = lean_array_get_size(v_data_5878_);
v___x_5880_ = lean_unsigned_to_nat(2u);
v_nbuckets_5881_ = lean_nat_mul(v___x_5879_, v___x_5880_);
v___x_5882_ = lean_unsigned_to_nat(0u);
v___x_5883_ = lean_box(0);
v___x_5884_ = lean_mk_array(v_nbuckets_5881_, v___x_5883_);
v___x_5885_ = lean_array_propagate_mark(v_data_5878_, v___x_5884_);
v___x_5886_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v___x_5882_, v_data_5878_, v___x_5885_);
return v___x_5886_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object* v_a_5887_, lean_object* v_x_5888_){
_start:
{
if (lean_obj_tag(v_x_5888_) == 0)
{
uint8_t v___x_5889_; 
v___x_5889_ = 0;
return v___x_5889_;
}
else
{
lean_object* v_key_5890_; lean_object* v_tail_5891_; uint8_t v___x_5892_; 
v_key_5890_ = lean_ctor_get(v_x_5888_, 0);
v_tail_5891_ = lean_ctor_get(v_x_5888_, 2);
v___x_5892_ = lean_nat_dec_eq(v_key_5890_, v_a_5887_);
if (v___x_5892_ == 0)
{
v_x_5888_ = v_tail_5891_;
goto _start;
}
else
{
return v___x_5892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object* v_a_5894_, lean_object* v_x_5895_){
_start:
{
uint8_t v_res_5896_; lean_object* v_r_5897_; 
v_res_5896_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5894_, v_x_5895_);
lean_dec(v_x_5895_);
lean_dec(v_a_5894_);
v_r_5897_ = lean_box(v_res_5896_);
return v_r_5897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object* v_x_5900_){
_start:
{
if (lean_obj_tag(v_x_5900_) == 0)
{
lean_object* v___x_5901_; 
v___x_5901_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0));
return v___x_5901_;
}
else
{
lean_object* v_val_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5911_; 
v_val_5902_ = lean_ctor_get(v_x_5900_, 0);
v_isSharedCheck_5911_ = !lean_is_exclusive(v_x_5900_);
if (v_isSharedCheck_5911_ == 0)
{
v___x_5904_ = v_x_5900_;
v_isShared_5905_ = v_isSharedCheck_5911_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_val_5902_);
lean_dec(v_x_5900_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5911_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5909_; 
v___x_5906_ = lean_unsigned_to_nat(1u);
v___x_5907_ = lean_nat_add(v_val_5902_, v___x_5906_);
lean_dec(v_val_5902_);
if (v_isShared_5905_ == 0)
{
lean_ctor_set(v___x_5904_, 0, v___x_5907_);
v___x_5909_ = v___x_5904_;
goto v_reusejp_5908_;
}
else
{
lean_object* v_reuseFailAlloc_5910_; 
v_reuseFailAlloc_5910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5910_, 0, v___x_5907_);
v___x_5909_ = v_reuseFailAlloc_5910_;
goto v_reusejp_5908_;
}
v_reusejp_5908_:
{
return v___x_5909_;
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; 
v___x_5912_ = lean_box(0);
v___x_5913_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5912_);
return v___x_5913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object* v_a_5914_, lean_object* v_x_5915_){
_start:
{
if (lean_obj_tag(v_x_5915_) == 0)
{
lean_object* v___x_5916_; lean_object* v_val_5917_; lean_object* v___x_5918_; 
v___x_5916_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0);
v_val_5917_ = lean_ctor_get(v___x_5916_, 0);
lean_inc(v_val_5917_);
v___x_5918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5918_, 0, v_a_5914_);
lean_ctor_set(v___x_5918_, 1, v_val_5917_);
lean_ctor_set(v___x_5918_, 2, v_x_5915_);
return v___x_5918_;
}
else
{
lean_object* v_key_5919_; lean_object* v_value_5920_; lean_object* v_tail_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5936_; 
v_key_5919_ = lean_ctor_get(v_x_5915_, 0);
v_value_5920_ = lean_ctor_get(v_x_5915_, 1);
v_tail_5921_ = lean_ctor_get(v_x_5915_, 2);
v_isSharedCheck_5936_ = !lean_is_exclusive(v_x_5915_);
if (v_isSharedCheck_5936_ == 0)
{
v___x_5923_ = v_x_5915_;
v_isShared_5924_ = v_isSharedCheck_5936_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_tail_5921_);
lean_inc(v_value_5920_);
lean_inc(v_key_5919_);
lean_dec(v_x_5915_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5936_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
uint8_t v___x_5925_; 
v___x_5925_ = lean_nat_dec_eq(v_key_5919_, v_a_5914_);
if (v___x_5925_ == 0)
{
lean_object* v_tail_5926_; lean_object* v___x_5928_; 
v_tail_5926_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5914_, v_tail_5921_);
if (v_isShared_5924_ == 0)
{
lean_ctor_set(v___x_5923_, 2, v_tail_5926_);
v___x_5928_ = v___x_5923_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v_key_5919_);
lean_ctor_set(v_reuseFailAlloc_5929_, 1, v_value_5920_);
lean_ctor_set(v_reuseFailAlloc_5929_, 2, v_tail_5926_);
v___x_5928_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
return v___x_5928_;
}
}
else
{
lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v_val_5932_; lean_object* v___x_5934_; 
lean_dec(v_key_5919_);
v___x_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5930_, 0, v_value_5920_);
v___x_5931_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5930_);
v_val_5932_ = lean_ctor_get(v___x_5931_, 0);
lean_inc(v_val_5932_);
lean_dec(v___x_5931_);
if (v_isShared_5924_ == 0)
{
lean_ctor_set(v___x_5923_, 1, v_val_5932_);
lean_ctor_set(v___x_5923_, 0, v_a_5914_);
v___x_5934_ = v___x_5923_;
goto v_reusejp_5933_;
}
else
{
lean_object* v_reuseFailAlloc_5935_; 
v_reuseFailAlloc_5935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_a_5914_);
lean_ctor_set(v_reuseFailAlloc_5935_, 1, v_val_5932_);
lean_ctor_set(v_reuseFailAlloc_5935_, 2, v_tail_5921_);
v___x_5934_ = v_reuseFailAlloc_5935_;
goto v_reusejp_5933_;
}
v_reusejp_5933_:
{
return v___x_5934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object* v_m_5937_, lean_object* v_a_5938_){
_start:
{
lean_object* v_size_5939_; lean_object* v_buckets_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5988_; 
v_size_5939_ = lean_ctor_get(v_m_5937_, 0);
v_buckets_5940_ = lean_ctor_get(v_m_5937_, 1);
v_isSharedCheck_5988_ = !lean_is_exclusive(v_m_5937_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5942_ = v_m_5937_;
v_isShared_5943_ = v_isSharedCheck_5988_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_buckets_5940_);
lean_inc(v_size_5939_);
lean_dec(v_m_5937_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5988_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5944_; uint64_t v___x_5945_; uint64_t v___x_5946_; uint64_t v___x_5947_; uint64_t v_fold_5948_; uint64_t v___x_5949_; uint64_t v___x_5950_; uint64_t v___x_5951_; size_t v___x_5952_; size_t v___x_5953_; size_t v___x_5954_; size_t v___x_5955_; size_t v___x_5956_; lean_object* v_bkt_5957_; uint8_t v___x_5958_; 
v___x_5944_ = lean_array_get_size(v_buckets_5940_);
v___x_5945_ = lean_uint64_of_nat(v_a_5938_);
v___x_5946_ = 32ULL;
v___x_5947_ = lean_uint64_shift_right(v___x_5945_, v___x_5946_);
v_fold_5948_ = lean_uint64_xor(v___x_5945_, v___x_5947_);
v___x_5949_ = 16ULL;
v___x_5950_ = lean_uint64_shift_right(v_fold_5948_, v___x_5949_);
v___x_5951_ = lean_uint64_xor(v_fold_5948_, v___x_5950_);
v___x_5952_ = lean_uint64_to_usize(v___x_5951_);
v___x_5953_ = lean_usize_of_nat(v___x_5944_);
v___x_5954_ = ((size_t)1ULL);
v___x_5955_ = lean_usize_sub(v___x_5953_, v___x_5954_);
v___x_5956_ = lean_usize_land(v___x_5952_, v___x_5955_);
v_bkt_5957_ = lean_array_uget_borrowed(v_buckets_5940_, v___x_5956_);
v___x_5958_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5938_, v_bkt_5957_);
if (v___x_5958_ == 0)
{
lean_object* v___x_5959_; lean_object* v_size_x27_5960_; lean_object* v___x_5961_; lean_object* v_buckets_x27_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; uint8_t v___x_5968_; 
v___x_5959_ = lean_unsigned_to_nat(1u);
v_size_x27_5960_ = lean_nat_add(v_size_5939_, v___x_5959_);
lean_dec(v_size_5939_);
lean_inc(v_bkt_5957_);
v___x_5961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5961_, 0, v_a_5938_);
lean_ctor_set(v___x_5961_, 1, v___x_5959_);
lean_ctor_set(v___x_5961_, 2, v_bkt_5957_);
v_buckets_x27_5962_ = lean_array_uset(v_buckets_5940_, v___x_5956_, v___x_5961_);
v___x_5963_ = lean_unsigned_to_nat(4u);
v___x_5964_ = lean_nat_mul(v_size_x27_5960_, v___x_5963_);
v___x_5965_ = lean_unsigned_to_nat(3u);
v___x_5966_ = lean_nat_div(v___x_5964_, v___x_5965_);
lean_dec(v___x_5964_);
v___x_5967_ = lean_array_get_size(v_buckets_x27_5962_);
v___x_5968_ = lean_nat_dec_le(v___x_5966_, v___x_5967_);
lean_dec(v___x_5966_);
if (v___x_5968_ == 0)
{
lean_object* v_val_5969_; lean_object* v___x_5971_; 
v_val_5969_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_buckets_x27_5962_);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v_val_5969_);
lean_ctor_set(v___x_5942_, 0, v_size_x27_5960_);
v___x_5971_ = v___x_5942_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_size_x27_5960_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v_val_5969_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
return v___x_5971_;
}
}
else
{
lean_object* v___x_5974_; 
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v_buckets_x27_5962_);
lean_ctor_set(v___x_5942_, 0, v_size_x27_5960_);
v___x_5974_ = v___x_5942_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_size_x27_5960_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v_buckets_x27_5962_);
v___x_5974_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
return v___x_5974_;
}
}
}
else
{
lean_object* v___x_5976_; lean_object* v_buckets_x27_5977_; lean_object* v_bkt_x27_5978_; lean_object* v___y_5980_; uint8_t v___x_5985_; 
lean_inc(v_bkt_5957_);
v___x_5976_ = lean_box(0);
v_buckets_x27_5977_ = lean_array_uset(v_buckets_5940_, v___x_5956_, v___x_5976_);
lean_inc(v_a_5938_);
v_bkt_x27_5978_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5938_, v_bkt_5957_);
v___x_5985_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5938_, v_bkt_x27_5978_);
lean_dec(v_a_5938_);
if (v___x_5985_ == 0)
{
lean_object* v___x_5986_; lean_object* v___x_5987_; 
v___x_5986_ = lean_unsigned_to_nat(1u);
v___x_5987_ = lean_nat_sub(v_size_5939_, v___x_5986_);
lean_dec(v_size_5939_);
v___y_5980_ = v___x_5987_;
goto v___jp_5979_;
}
else
{
v___y_5980_ = v_size_5939_;
goto v___jp_5979_;
}
v___jp_5979_:
{
lean_object* v___x_5981_; lean_object* v___x_5983_; 
v___x_5981_ = lean_array_uset(v_buckets_x27_5977_, v___x_5956_, v_bkt_x27_5978_);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v___x_5981_);
lean_ctor_set(v___x_5942_, 0, v___y_5980_);
v___x_5983_ = v___x_5942_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v___y_5980_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v___x_5981_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
return v___x_5983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object* v_fst_5989_, lean_object* v___x_5990_, lean_object* v_____r_5991_){
_start:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; 
lean_inc(v___x_5990_);
v___x_5992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(v_fst_5989_, v___x_5990_);
v___x_5993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5992_);
lean_ctor_set(v___x_5993_, 1, v___x_5990_);
v___x_5994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5994_, 0, v___x_5993_);
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object* v_comments_5995_, lean_object* v_whitespace_5996_, lean_object* v_a_5997_, lean_object* v_b_5998_){
_start:
{
lean_object* v_str_5999_; lean_object* v_startInclusive_6000_; lean_object* v_endExclusive_6001_; lean_object* v___x_6002_; uint8_t v_decide_6003_; 
v_str_5999_ = lean_ctor_get(v_whitespace_5996_, 0);
v_startInclusive_6000_ = lean_ctor_get(v_whitespace_5996_, 1);
v_endExclusive_6001_ = lean_ctor_get(v_whitespace_5996_, 2);
v___x_6002_ = lean_nat_sub(v_endExclusive_6001_, v_startInclusive_6000_);
v_decide_6003_ = lean_nat_dec_eq(v_a_5997_, v___x_6002_);
lean_dec(v___x_6002_);
if (v_decide_6003_ == 0)
{
uint32_t v___x_6004_; lean_object* v___x_6005_; uint32_t v___x_6006_; uint8_t v___x_6007_; 
v___x_6004_ = 10;
v___x_6005_ = lean_nat_add(v_startInclusive_6000_, v_a_5997_);
v___x_6006_ = lean_string_utf8_get_fast(v_str_5999_, v___x_6005_);
v___x_6007_ = lean_uint32_dec_eq(v___x_6006_, v___x_6004_);
if (v___x_6007_ == 0)
{
lean_object* v___x_6008_; lean_object* v___x_6009_; 
lean_dec(v_a_5997_);
v___x_6008_ = lean_string_utf8_next_fast(v_str_5999_, v___x_6005_);
lean_dec(v___x_6005_);
v___x_6009_ = lean_nat_sub(v___x_6008_, v_startInclusive_6000_);
v_a_5997_ = v___x_6009_;
goto _start;
}
else
{
lean_object* v_fst_6011_; lean_object* v_snd_6012_; lean_object* v___x_6014_; uint8_t v_isShared_6015_; uint8_t v_isSharedCheck_6038_; 
v_fst_6011_ = lean_ctor_get(v_b_5998_, 0);
v_snd_6012_ = lean_ctor_get(v_b_5998_, 1);
v_isSharedCheck_6038_ = !lean_is_exclusive(v_b_5998_);
if (v_isSharedCheck_6038_ == 0)
{
v___x_6014_ = v_b_5998_;
v_isShared_6015_ = v_isSharedCheck_6038_;
goto v_resetjp_6013_;
}
else
{
lean_inc(v_snd_6012_);
lean_inc(v_fst_6011_);
lean_dec(v_b_5998_);
v___x_6014_ = lean_box(0);
v_isShared_6015_ = v_isSharedCheck_6038_;
goto v_resetjp_6013_;
}
v_resetjp_6013_:
{
lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v_val_6020_; lean_object* v___x_6024_; lean_object* v___x_6025_; uint8_t v___x_6026_; 
v___x_6016_ = lean_string_utf8_next_fast(v_str_5999_, v___x_6005_);
v___x_6017_ = lean_nat_sub(v___x_6016_, v___x_6005_);
v___x_6018_ = lean_nat_add(v_a_5997_, v___x_6017_);
lean_dec(v___x_6017_);
lean_dec(v_a_5997_);
v___x_6024_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5995_, v___x_6005_, v_snd_6012_);
v___x_6025_ = lean_array_get_size(v_comments_5995_);
v___x_6026_ = lean_nat_dec_lt(v___x_6024_, v___x_6025_);
if (v___x_6026_ == 0)
{
lean_object* v___x_6027_; lean_object* v___x_6028_; 
lean_del_object(v___x_6014_);
lean_dec(v___x_6005_);
v___x_6027_ = lean_box(0);
v___x_6028_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_6011_, v___x_6024_, v___x_6027_);
v_val_6020_ = v___x_6028_;
goto v___jp_6019_;
}
else
{
lean_object* v___x_6029_; lean_object* v_originalWhitespaceRange_6030_; uint8_t v___x_6031_; 
v___x_6029_ = lean_array_fget_borrowed(v_comments_5995_, v___x_6024_);
v_originalWhitespaceRange_6030_ = lean_ctor_get(v___x_6029_, 1);
v___x_6031_ = l_Lean_Syntax_Range_contains(v_originalWhitespaceRange_6030_, v___x_6005_, v_decide_6003_);
lean_dec(v___x_6005_);
if (v___x_6031_ == 0)
{
lean_object* v___x_6032_; lean_object* v___x_6033_; 
lean_del_object(v___x_6014_);
v___x_6032_ = lean_box(0);
v___x_6033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_6011_, v___x_6024_, v___x_6032_);
v_val_6020_ = v___x_6033_;
goto v___jp_6019_;
}
else
{
lean_object* v___x_6035_; 
if (v_isShared_6015_ == 0)
{
lean_ctor_set(v___x_6014_, 1, v___x_6024_);
v___x_6035_ = v___x_6014_;
goto v_reusejp_6034_;
}
else
{
lean_object* v_reuseFailAlloc_6037_; 
v_reuseFailAlloc_6037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6037_, 0, v_fst_6011_);
lean_ctor_set(v_reuseFailAlloc_6037_, 1, v___x_6024_);
v___x_6035_ = v_reuseFailAlloc_6037_;
goto v_reusejp_6034_;
}
v_reusejp_6034_:
{
v_a_5997_ = v___x_6018_;
v_b_5998_ = v___x_6035_;
goto _start;
}
}
}
v___jp_6019_:
{
if (lean_obj_tag(v_val_6020_) == 0)
{
lean_object* v_a_6021_; 
lean_dec(v___x_6018_);
v_a_6021_ = lean_ctor_get(v_val_6020_, 0);
lean_inc(v_a_6021_);
lean_dec_ref_known(v_val_6020_, 1);
return v_a_6021_;
}
else
{
lean_object* v_a_6022_; 
v_a_6022_ = lean_ctor_get(v_val_6020_, 0);
lean_inc(v_a_6022_);
lean_dec_ref_known(v_val_6020_, 1);
v_a_5997_ = v___x_6018_;
v_b_5998_ = v_a_6022_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_5997_);
return v_b_5998_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object* v_comments_6039_, lean_object* v_whitespace_6040_, lean_object* v_a_6041_, lean_object* v_b_6042_){
_start:
{
lean_object* v_res_6043_; 
v_res_6043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_6039_, v_whitespace_6040_, v_a_6041_, v_b_6042_);
lean_dec_ref(v_whitespace_6040_);
lean_dec_ref(v_comments_6039_);
return v_res_6043_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0(void){
_start:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___x_6044_ = lean_box(0);
v___x_6045_ = lean_unsigned_to_nat(16u);
v___x_6046_ = lean_mk_array(v___x_6045_, v___x_6044_);
return v___x_6046_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1(void){
_start:
{
lean_object* v___x_6047_; lean_object* v_newlinePositions_6048_; lean_object* v_newlinesBeforeComment_6049_; 
v___x_6047_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0);
v_newlinePositions_6048_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_newlinesBeforeComment_6049_, 0, v_newlinePositions_6048_);
lean_ctor_set(v_newlinesBeforeComment_6049_, 1, v___x_6047_);
return v_newlinesBeforeComment_6049_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2(void){
_start:
{
lean_object* v_newlinePositions_6050_; lean_object* v_newlinesBeforeComment_6051_; lean_object* v___x_6052_; 
v_newlinePositions_6050_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_6051_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1);
v___x_6052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6052_, 0, v_newlinesBeforeComment_6051_);
lean_ctor_set(v___x_6052_, 1, v_newlinePositions_6050_);
return v___x_6052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object* v_comments_6053_, lean_object* v_whitespace_6054_){
_start:
{
lean_object* v_newlinePositions_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v_fst_6058_; 
v_newlinePositions_6055_ = lean_unsigned_to_nat(0u);
v___x_6056_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2);
v___x_6057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_6053_, v_whitespace_6054_, v_newlinePositions_6055_, v___x_6056_);
v_fst_6058_ = lean_ctor_get(v___x_6057_, 0);
lean_inc(v_fst_6058_);
lean_dec_ref(v___x_6057_);
return v_fst_6058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object* v_comments_6059_, lean_object* v_whitespace_6060_){
_start:
{
lean_object* v_res_6061_; 
v_res_6061_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v_comments_6059_, v_whitespace_6060_);
lean_dec_ref(v_whitespace_6060_);
lean_dec_ref(v_comments_6059_);
return v_res_6061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object* v_comments_6062_, lean_object* v_out_6063_, lean_object* v_inst_6064_, lean_object* v_a_6065_){
_start:
{
lean_object* v___x_6066_; 
v___x_6066_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_6062_, v_out_6063_, v_a_6065_);
return v___x_6066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object* v_comments_6067_, lean_object* v_out_6068_, lean_object* v_inst_6069_, lean_object* v_a_6070_){
_start:
{
lean_object* v_res_6071_; 
v_res_6071_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(v_comments_6067_, v_out_6068_, v_inst_6069_, v_a_6070_);
lean_dec(v_out_6068_);
lean_dec_ref(v_comments_6067_);
return v_res_6071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object* v_comments_6072_, lean_object* v_whitespace_6073_, lean_object* v_inst_6074_, lean_object* v_R_6075_, lean_object* v_a_6076_, lean_object* v_b_6077_, lean_object* v_c_6078_){
_start:
{
lean_object* v___x_6079_; 
v___x_6079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_6072_, v_whitespace_6073_, v_a_6076_, v_b_6077_);
return v___x_6079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object* v_comments_6080_, lean_object* v_whitespace_6081_, lean_object* v_inst_6082_, lean_object* v_R_6083_, lean_object* v_a_6084_, lean_object* v_b_6085_, lean_object* v_c_6086_){
_start:
{
lean_object* v_res_6087_; 
v_res_6087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(v_comments_6080_, v_whitespace_6081_, v_inst_6082_, v_R_6083_, v_a_6084_, v_b_6085_, v_c_6086_);
lean_dec_ref(v_whitespace_6081_);
lean_dec_ref(v_comments_6080_);
return v_res_6087_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object* v_00_u03b2_6088_, lean_object* v_a_6089_, lean_object* v_x_6090_){
_start:
{
uint8_t v___x_6091_; 
v___x_6091_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_6089_, v_x_6090_);
return v___x_6091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6092_, lean_object* v_a_6093_, lean_object* v_x_6094_){
_start:
{
uint8_t v_res_6095_; lean_object* v_r_6096_; 
v_res_6095_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(v_00_u03b2_6092_, v_a_6093_, v_x_6094_);
lean_dec(v_x_6094_);
lean_dec(v_a_6093_);
v_r_6096_ = lean_box(v_res_6095_);
return v_r_6096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object* v_00_u03b2_6097_, lean_object* v_data_6098_){
_start:
{
lean_object* v___x_6099_; 
v___x_6099_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_data_6098_);
return v___x_6099_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_6100_, lean_object* v_i_6101_, lean_object* v_source_6102_, lean_object* v_target_6103_){
_start:
{
lean_object* v___x_6104_; 
v___x_6104_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v_i_6101_, v_source_6102_, v_target_6103_);
return v___x_6104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_6105_, lean_object* v_x_6106_, lean_object* v_x_6107_){
_start:
{
lean_object* v___x_6108_; 
v___x_6108_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_x_6106_, v_x_6107_);
return v___x_6108_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_6112_; 
v___x_6112_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0));
return v___x_6112_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___dummy_6113_){
_start:
{
lean_object* v_res_6114_; 
v_res_6114_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v_res_6114_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6115_; 
v___x_6115_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v___x_6115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object* v_s_6116_){
_start:
{
lean_object* v___x_6117_; 
v___x_6117_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
return v___x_6117_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object* v_s_6118_){
_start:
{
lean_object* v_res_6119_; 
v_res_6119_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(v_s_6118_);
lean_dec_ref(v_s_6118_);
return v_res_6119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t v_sz_6120_, size_t v_i_6121_, lean_object* v_bs_6122_){
_start:
{
uint8_t v___x_6123_; 
v___x_6123_ = lean_usize_dec_lt(v_i_6121_, v_sz_6120_);
if (v___x_6123_ == 0)
{
return v_bs_6122_;
}
else
{
lean_object* v_v_6124_; lean_object* v_rendered_6125_; lean_object* v___x_6126_; lean_object* v_bs_x27_6127_; size_t v___x_6128_; size_t v___x_6129_; lean_object* v___x_6130_; 
v_v_6124_ = lean_array_uget_borrowed(v_bs_6122_, v_i_6121_);
v_rendered_6125_ = lean_ctor_get(v_v_6124_, 0);
lean_inc_ref(v_rendered_6125_);
v___x_6126_ = lean_unsigned_to_nat(0u);
v_bs_x27_6127_ = lean_array_uset(v_bs_6122_, v_i_6121_, v___x_6126_);
v___x_6128_ = ((size_t)1ULL);
v___x_6129_ = lean_usize_add(v_i_6121_, v___x_6128_);
v___x_6130_ = lean_array_uset(v_bs_x27_6127_, v_i_6121_, v_rendered_6125_);
v_i_6121_ = v___x_6129_;
v_bs_6122_ = v___x_6130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object* v_sz_6132_, lean_object* v_i_6133_, lean_object* v_bs_6134_){
_start:
{
size_t v_sz_boxed_6135_; size_t v_i_boxed_6136_; lean_object* v_res_6137_; 
v_sz_boxed_6135_ = lean_unbox_usize(v_sz_6132_);
lean_dec(v_sz_6132_);
v_i_boxed_6136_ = lean_unbox_usize(v_i_6133_);
lean_dec(v_i_6133_);
v_res_6137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_boxed_6135_, v_i_boxed_6136_, v_bs_6134_);
return v_res_6137_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; 
v___x_6138_ = lean_box(0);
v___x_6139_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6139_);
lean_ctor_set(v___x_6140_, 1, v___x_6138_);
return v___x_6140_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object* v_upperBound_6141_, lean_object* v_next_6142_, lean_object* v_upperBound_6143_, lean_object* v_a_6144_, lean_object* v_b_6145_){
_start:
{
uint8_t v___x_6146_; 
v___x_6146_ = lean_nat_dec_lt(v_a_6144_, v_upperBound_6141_);
if (v___x_6146_ == 0)
{
lean_dec(v_a_6144_);
return v_b_6145_;
}
else
{
lean_object* v_fst_6147_; lean_object* v___x_6149_; uint8_t v_isShared_6150_; uint8_t v_isSharedCheck_6161_; 
v_fst_6147_ = lean_ctor_get(v_b_6145_, 0);
v_isSharedCheck_6161_ = !lean_is_exclusive(v_b_6145_);
if (v_isSharedCheck_6161_ == 0)
{
lean_object* v_unused_6162_; 
v_unused_6162_ = lean_ctor_get(v_b_6145_, 1);
lean_dec(v_unused_6162_);
v___x_6149_ = v_b_6145_;
v_isShared_6150_ = v_isSharedCheck_6161_;
goto v_resetjp_6148_;
}
else
{
lean_inc(v_fst_6147_);
lean_dec(v_b_6145_);
v___x_6149_ = lean_box(0);
v_isShared_6150_ = v_isSharedCheck_6161_;
goto v_resetjp_6148_;
}
v_resetjp_6148_:
{
uint8_t v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6156_; 
v___x_6151_ = lean_nat_dec_lt(v_next_6142_, v_upperBound_6143_);
v___x_6152_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6153_ = lean_array_push(v_fst_6147_, v___x_6152_);
v___x_6154_ = lean_box(v___x_6151_);
if (v_isShared_6150_ == 0)
{
lean_ctor_set(v___x_6149_, 1, v___x_6154_);
lean_ctor_set(v___x_6149_, 0, v___x_6153_);
v___x_6156_ = v___x_6149_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6160_; 
v_reuseFailAlloc_6160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6160_, 0, v___x_6153_);
lean_ctor_set(v_reuseFailAlloc_6160_, 1, v___x_6154_);
v___x_6156_ = v_reuseFailAlloc_6160_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
lean_object* v___x_6157_; lean_object* v___x_6158_; 
v___x_6157_ = lean_unsigned_to_nat(1u);
v___x_6158_ = lean_nat_add(v_a_6144_, v___x_6157_);
lean_dec(v_a_6144_);
v_a_6144_ = v___x_6158_;
v_b_6145_ = v___x_6156_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object* v_upperBound_6163_, lean_object* v_next_6164_, lean_object* v_upperBound_6165_, lean_object* v_a_6166_, lean_object* v_b_6167_){
_start:
{
lean_object* v_res_6168_; 
v_res_6168_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6163_, v_next_6164_, v_upperBound_6165_, v_a_6166_, v_b_6167_);
lean_dec(v_upperBound_6165_);
lean_dec(v_next_6164_);
lean_dec(v_upperBound_6163_);
return v_res_6168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(lean_object* v_originalWhitespaceRange_6169_, lean_object* v_fst_6170_, lean_object* v_____r_6171_, uint8_t v_insertedAnyNewlines_6172_, lean_object* v_d_6173_){
_start:
{
lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; 
v___x_6174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6174_, 0, v_originalWhitespaceRange_6169_);
v___x_6175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6175_, 0, v_d_6173_);
lean_ctor_set(v___x_6175_, 1, v___x_6174_);
v___x_6176_ = lean_array_push(v_fst_6170_, v___x_6175_);
v___x_6177_ = lean_box(v_insertedAnyNewlines_6172_);
v___x_6178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6178_, 0, v___x_6176_);
lean_ctor_set(v___x_6178_, 1, v___x_6177_);
v___x_6179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6178_);
return v___x_6179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed(lean_object* v_originalWhitespaceRange_6180_, lean_object* v_fst_6181_, lean_object* v_____r_6182_, lean_object* v_insertedAnyNewlines_6183_, lean_object* v_d_6184_){
_start:
{
uint8_t v_insertedAnyNewlines_boxed_6185_; lean_object* v_res_6186_; 
v_insertedAnyNewlines_boxed_6185_ = lean_unbox(v_insertedAnyNewlines_6183_);
v_res_6186_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6180_, v_fst_6181_, v_____r_6182_, v_insertedAnyNewlines_boxed_6185_, v_d_6184_);
return v_res_6186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object* v_a_6187_, lean_object* v___x_6188_, lean_object* v___x_6189_, lean_object* v_a_6190_, lean_object* v_b_6191_){
_start:
{
lean_object* v_it_6193_; lean_object* v_startInclusive_6194_; lean_object* v_endExclusive_6195_; 
if (lean_obj_tag(v_a_6190_) == 0)
{
lean_object* v_currPos_6201_; lean_object* v_searcher_6202_; lean_object* v___x_6204_; uint8_t v_isShared_6205_; uint8_t v_isSharedCheck_6225_; 
v_currPos_6201_ = lean_ctor_get(v_a_6190_, 0);
v_searcher_6202_ = lean_ctor_get(v_a_6190_, 1);
v_isSharedCheck_6225_ = !lean_is_exclusive(v_a_6190_);
if (v_isSharedCheck_6225_ == 0)
{
v___x_6204_ = v_a_6190_;
v_isShared_6205_ = v_isSharedCheck_6225_;
goto v_resetjp_6203_;
}
else
{
lean_inc(v_searcher_6202_);
lean_inc(v_currPos_6201_);
lean_dec(v_a_6190_);
v___x_6204_ = lean_box(0);
v_isShared_6205_ = v_isSharedCheck_6225_;
goto v_resetjp_6203_;
}
v_resetjp_6203_:
{
uint8_t v_decide_6206_; 
v_decide_6206_ = lean_nat_dec_eq(v_searcher_6202_, v___x_6189_);
if (v_decide_6206_ == 0)
{
uint32_t v___x_6207_; uint32_t v___x_6208_; uint8_t v___x_6209_; 
v___x_6207_ = 10;
v___x_6208_ = lean_string_utf8_get_fast(v_a_6187_, v_searcher_6202_);
v___x_6209_ = lean_uint32_dec_eq(v___x_6208_, v___x_6207_);
if (v___x_6209_ == 0)
{
lean_object* v___x_6210_; lean_object* v___x_6212_; 
v___x_6210_ = lean_string_utf8_next_fast(v_a_6187_, v_searcher_6202_);
lean_dec(v_searcher_6202_);
if (v_isShared_6205_ == 0)
{
lean_ctor_set(v___x_6204_, 1, v___x_6210_);
v___x_6212_ = v___x_6204_;
goto v_reusejp_6211_;
}
else
{
lean_object* v_reuseFailAlloc_6214_; 
v_reuseFailAlloc_6214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6214_, 0, v_currPos_6201_);
lean_ctor_set(v_reuseFailAlloc_6214_, 1, v___x_6210_);
v___x_6212_ = v_reuseFailAlloc_6214_;
goto v_reusejp_6211_;
}
v_reusejp_6211_:
{
v_a_6190_ = v___x_6212_;
goto _start;
}
}
else
{
lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v_slice_6218_; lean_object* v_nextIt_6220_; 
v___x_6215_ = lean_string_utf8_next_fast(v_a_6187_, v_searcher_6202_);
v___x_6216_ = lean_nat_sub(v___x_6215_, v_searcher_6202_);
v___x_6217_ = lean_nat_add(v_searcher_6202_, v___x_6216_);
lean_dec(v___x_6216_);
v_slice_6218_ = l_String_Slice_subslice_x21(v___x_6188_, v_currPos_6201_, v_searcher_6202_);
lean_inc(v___x_6217_);
if (v_isShared_6205_ == 0)
{
lean_ctor_set(v___x_6204_, 1, v___x_6217_);
lean_ctor_set(v___x_6204_, 0, v___x_6217_);
v_nextIt_6220_ = v___x_6204_;
goto v_reusejp_6219_;
}
else
{
lean_object* v_reuseFailAlloc_6223_; 
v_reuseFailAlloc_6223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6223_, 0, v___x_6217_);
lean_ctor_set(v_reuseFailAlloc_6223_, 1, v___x_6217_);
v_nextIt_6220_ = v_reuseFailAlloc_6223_;
goto v_reusejp_6219_;
}
v_reusejp_6219_:
{
lean_object* v_startInclusive_6221_; lean_object* v_endExclusive_6222_; 
v_startInclusive_6221_ = lean_ctor_get(v_slice_6218_, 0);
lean_inc(v_startInclusive_6221_);
v_endExclusive_6222_ = lean_ctor_get(v_slice_6218_, 1);
lean_inc(v_endExclusive_6222_);
lean_dec_ref(v_slice_6218_);
v_it_6193_ = v_nextIt_6220_;
v_startInclusive_6194_ = v_startInclusive_6221_;
v_endExclusive_6195_ = v_endExclusive_6222_;
goto v___jp_6192_;
}
}
}
else
{
lean_object* v___x_6224_; 
lean_del_object(v___x_6204_);
lean_dec(v_searcher_6202_);
v___x_6224_ = lean_box(1);
lean_inc(v___x_6189_);
v_it_6193_ = v___x_6224_;
v_startInclusive_6194_ = v_currPos_6201_;
v_endExclusive_6195_ = v___x_6189_;
goto v___jp_6192_;
}
}
}
else
{
lean_dec(v___x_6189_);
lean_dec_ref(v_a_6187_);
return v_b_6191_;
}
v___jp_6192_:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; 
lean_inc_ref(v_a_6187_);
v___x_6196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6196_, 0, v_a_6187_);
lean_ctor_set(v___x_6196_, 1, v_startInclusive_6194_);
lean_ctor_set(v___x_6196_, 2, v_endExclusive_6195_);
v___x_6197_ = l_String_Slice_toString(v___x_6196_);
lean_dec_ref_known(v___x_6196_, 3);
v___x_6198_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_6197_);
v___x_6199_ = lean_array_push(v_b_6191_, v___x_6198_);
v_a_6190_ = v_it_6193_;
v_b_6191_ = v___x_6199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object* v_a_6226_, lean_object* v___x_6227_, lean_object* v___x_6228_, lean_object* v_a_6229_, lean_object* v_b_6230_){
_start:
{
lean_object* v_res_6231_; 
v_res_6231_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6226_, v___x_6227_, v___x_6228_, v_a_6229_, v_b_6230_);
lean_dec_ref(v___x_6227_);
return v_res_6231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(size_t v_sz_6232_, size_t v_i_6233_, lean_object* v_bs_6234_){
_start:
{
uint8_t v___x_6235_; 
v___x_6235_ = lean_usize_dec_lt(v_i_6233_, v_sz_6232_);
if (v___x_6235_ == 0)
{
return v_bs_6234_;
}
else
{
lean_object* v_v_6236_; lean_object* v___x_6237_; lean_object* v_bs_x27_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; size_t v___x_6247_; size_t v___x_6248_; lean_object* v___x_6249_; 
v_v_6236_ = lean_array_uget(v_bs_6234_, v_i_6233_);
v___x_6237_ = lean_unsigned_to_nat(0u);
v_bs_x27_6238_ = lean_array_uset(v_bs_6234_, v_i_6233_, v___x_6237_);
v___x_6239_ = lean_string_utf8_byte_size(v_v_6236_);
lean_inc(v_v_6236_);
v___x_6240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6240_, 0, v_v_6236_);
lean_ctor_set(v___x_6240_, 1, v___x_6237_);
lean_ctor_set(v___x_6240_, 2, v___x_6239_);
v___x_6241_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
v___x_6242_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_6243_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_v_6236_, v___x_6240_, v___x_6239_, v___x_6241_, v___x_6242_);
lean_dec_ref_known(v___x_6240_, 3);
v___x_6244_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_6245_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_6244_, v___x_6243_);
v___x_6246_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6245_);
v___x_6247_ = ((size_t)1ULL);
v___x_6248_ = lean_usize_add(v_i_6233_, v___x_6247_);
v___x_6249_ = lean_array_uset(v_bs_x27_6238_, v_i_6233_, v___x_6246_);
v_i_6233_ = v___x_6248_;
v_bs_6234_ = v___x_6249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg___boxed(lean_object* v_sz_6251_, lean_object* v_i_6252_, lean_object* v_bs_6253_){
_start:
{
size_t v_sz_boxed_6254_; size_t v_i_boxed_6255_; lean_object* v_res_6256_; 
v_sz_boxed_6254_ = lean_unbox_usize(v_sz_6251_);
lean_dec(v_sz_6251_);
v_i_boxed_6255_ = lean_unbox_usize(v_i_6252_);
lean_dec(v_i_6252_);
v_res_6256_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_boxed_6254_, v_i_boxed_6255_, v_bs_6253_);
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object* v_a_6257_, lean_object* v_x_6258_){
_start:
{
if (lean_obj_tag(v_x_6258_) == 0)
{
lean_object* v___x_6259_; 
v___x_6259_ = lean_box(0);
return v___x_6259_;
}
else
{
lean_object* v_key_6260_; lean_object* v_value_6261_; lean_object* v_tail_6262_; uint8_t v___x_6263_; 
v_key_6260_ = lean_ctor_get(v_x_6258_, 0);
v_value_6261_ = lean_ctor_get(v_x_6258_, 1);
v_tail_6262_ = lean_ctor_get(v_x_6258_, 2);
v___x_6263_ = lean_nat_dec_eq(v_key_6260_, v_a_6257_);
if (v___x_6263_ == 0)
{
v_x_6258_ = v_tail_6262_;
goto _start;
}
else
{
lean_object* v___x_6265_; 
lean_inc(v_value_6261_);
v___x_6265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6265_, 0, v_value_6261_);
return v___x_6265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object* v_a_6266_, lean_object* v_x_6267_){
_start:
{
lean_object* v_res_6268_; 
v_res_6268_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6266_, v_x_6267_);
lean_dec(v_x_6267_);
lean_dec(v_a_6266_);
return v_res_6268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object* v_m_6269_, lean_object* v_a_6270_){
_start:
{
lean_object* v_buckets_6271_; lean_object* v___x_6272_; uint64_t v___x_6273_; uint64_t v___x_6274_; uint64_t v___x_6275_; uint64_t v_fold_6276_; uint64_t v___x_6277_; uint64_t v___x_6278_; uint64_t v___x_6279_; size_t v___x_6280_; size_t v___x_6281_; size_t v___x_6282_; size_t v___x_6283_; size_t v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; 
v_buckets_6271_ = lean_ctor_get(v_m_6269_, 1);
v___x_6272_ = lean_array_get_size(v_buckets_6271_);
v___x_6273_ = lean_uint64_of_nat(v_a_6270_);
v___x_6274_ = 32ULL;
v___x_6275_ = lean_uint64_shift_right(v___x_6273_, v___x_6274_);
v_fold_6276_ = lean_uint64_xor(v___x_6273_, v___x_6275_);
v___x_6277_ = 16ULL;
v___x_6278_ = lean_uint64_shift_right(v_fold_6276_, v___x_6277_);
v___x_6279_ = lean_uint64_xor(v_fold_6276_, v___x_6278_);
v___x_6280_ = lean_uint64_to_usize(v___x_6279_);
v___x_6281_ = lean_usize_of_nat(v___x_6272_);
v___x_6282_ = ((size_t)1ULL);
v___x_6283_ = lean_usize_sub(v___x_6281_, v___x_6282_);
v___x_6284_ = lean_usize_land(v___x_6280_, v___x_6283_);
v___x_6285_ = lean_array_uget_borrowed(v_buckets_6271_, v___x_6284_);
v___x_6286_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6270_, v___x_6285_);
return v___x_6286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object* v_m_6287_, lean_object* v_a_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6287_, v_a_6288_);
lean_dec(v_a_6288_);
lean_dec_ref(v_m_6287_);
return v_res_6289_;
}
}
static uint8_t _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_6290_; uint8_t v___x_6291_; 
v___x_6290_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6291_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6290_);
return v___x_6291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(lean_object* v_upperBound_6292_, lean_object* v_comments_6293_, lean_object* v_numNewlinesBeforeComments_6294_, lean_object* v_a_6295_, lean_object* v_b_6296_){
_start:
{
lean_object* v___y_6298_; uint8_t v___x_6304_; lean_object* v___y_6306_; lean_object* v___y_6307_; 
v___x_6304_ = lean_nat_dec_lt(v_a_6295_, v_upperBound_6292_);
if (v___x_6304_ == 0)
{
lean_dec(v_a_6295_);
return v_b_6296_;
}
else
{
lean_object* v_fst_6311_; lean_object* v_snd_6312_; lean_object* v___x_6314_; uint8_t v_isShared_6315_; uint8_t v_isSharedCheck_6378_; 
v_fst_6311_ = lean_ctor_get(v_b_6296_, 0);
v_snd_6312_ = lean_ctor_get(v_b_6296_, 1);
v_isSharedCheck_6378_ = !lean_is_exclusive(v_b_6296_);
if (v_isSharedCheck_6378_ == 0)
{
v___x_6314_ = v_b_6296_;
v_isShared_6315_ = v_isSharedCheck_6378_;
goto v_resetjp_6313_;
}
else
{
lean_inc(v_snd_6312_);
lean_inc(v_fst_6311_);
lean_dec(v_b_6296_);
v___x_6314_ = lean_box(0);
v_isShared_6315_ = v_isSharedCheck_6378_;
goto v_resetjp_6313_;
}
v_resetjp_6313_:
{
lean_object* v___x_6316_; lean_object* v___y_6318_; lean_object* v___y_6352_; lean_object* v___y_6353_; lean_object* v___y_6356_; uint8_t v___y_6359_; lean_object* v___y_6360_; uint8_t v___y_6364_; lean_object* v___y_6365_; uint8_t v___y_6369_; uint8_t v_insertedAnyNewlines_6372_; uint8_t v___x_6373_; 
v___x_6316_ = lean_unsigned_to_nat(0u);
v_insertedAnyNewlines_6372_ = 0;
v___x_6373_ = lean_nat_dec_eq(v_a_6295_, v___x_6316_);
if (v___x_6373_ == 0)
{
lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; uint8_t v_kind_6377_; 
v___x_6374_ = lean_unsigned_to_nat(1u);
v___x_6375_ = lean_nat_sub(v_a_6295_, v___x_6374_);
v___x_6376_ = lean_array_fget_borrowed(v_comments_6293_, v___x_6375_);
lean_dec(v___x_6375_);
v_kind_6377_ = lean_ctor_get_uint8(v___x_6376_, sizeof(void*)*3);
if (v_kind_6377_ == 1)
{
v___y_6369_ = v___x_6304_;
goto v___jp_6368_;
}
else
{
v___y_6369_ = v_insertedAnyNewlines_6372_;
goto v___jp_6368_;
}
}
else
{
v___y_6369_ = v_insertedAnyNewlines_6372_;
goto v___jp_6368_;
}
v___jp_6317_:
{
lean_object* v___x_6320_; 
if (v_isShared_6315_ == 0)
{
v___x_6320_ = v___x_6314_;
goto v_reusejp_6319_;
}
else
{
lean_object* v_reuseFailAlloc_6350_; 
v_reuseFailAlloc_6350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_fst_6311_);
lean_ctor_set(v_reuseFailAlloc_6350_, 1, v_snd_6312_);
v___x_6320_ = v_reuseFailAlloc_6350_;
goto v_reusejp_6319_;
}
v_reusejp_6319_:
{
lean_object* v___x_6321_; lean_object* v_fst_6322_; lean_object* v_snd_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; size_t v_sz_6326_; size_t v___x_6327_; lean_object* v___x_6328_; size_t v_sz_6329_; uint8_t v_kind_6330_; lean_object* v_originalWhitespaceRange_6331_; lean_object* v___x_6332_; lean_object* v___f_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6321_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v___y_6318_, v_a_6295_, v_upperBound_6292_, v___x_6316_, v___x_6320_);
lean_dec(v___y_6318_);
v_fst_6322_ = lean_ctor_get(v___x_6321_, 0);
lean_inc_n(v_fst_6322_, 2);
v_snd_6323_ = lean_ctor_get(v___x_6321_, 1);
lean_inc(v_snd_6323_);
lean_dec_ref(v___x_6321_);
v___x_6324_ = lean_array_fget_borrowed(v_comments_6293_, v_a_6295_);
lean_inc(v___x_6324_);
v___x_6325_ = l_Lean_Fmt_Comment_render(v___x_6324_);
v_sz_6326_ = lean_array_size(v___x_6325_);
v___x_6327_ = ((size_t)0ULL);
v___x_6328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_6326_, v___x_6327_, v___x_6325_);
v_sz_6329_ = lean_array_size(v___x_6328_);
v_kind_6330_ = lean_ctor_get_uint8(v___x_6324_, sizeof(void*)*3);
v_originalWhitespaceRange_6331_ = lean_ctor_get(v___x_6324_, 1);
v___x_6332_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6329_, v___x_6327_, v___x_6328_);
lean_inc_ref(v_originalWhitespaceRange_6331_);
v___f_6333_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_6333_, 0, v_originalWhitespaceRange_6331_);
lean_closure_set(v___f_6333_, 1, v_fst_6322_);
v___x_6334_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_6332_);
v___x_6335_ = l_Lean_Fmt_TaggedDoc_free(v___x_6334_);
if (v_kind_6330_ == 0)
{
lean_object* v___x_6336_; uint8_t v___x_6337_; 
lean_dec(v_snd_6323_);
lean_dec(v_fst_6322_);
v___x_6336_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6337_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6335_);
if (v___x_6337_ == 0)
{
uint8_t v___x_6338_; 
v___x_6338_ = lean_uint8_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0);
if (v___x_6338_ == 0)
{
lean_object* v_doc_6339_; lean_object* v_doc_6340_; uint8_t v___x_6341_; 
v_doc_6339_ = lean_ctor_get(v___x_6335_, 0);
lean_inc(v_doc_6339_);
lean_dec_ref(v___x_6335_);
v_doc_6340_ = lean_ctor_get(v___x_6336_, 0);
v___x_6341_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6339_);
if (v___x_6341_ == 0)
{
uint8_t v___x_6342_; 
v___x_6342_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6340_);
if (v___x_6342_ == 0)
{
lean_object* v___x_6343_; lean_object* v___x_6344_; 
lean_inc(v_doc_6340_);
v___x_6343_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_6339_, v_doc_6340_);
v___x_6344_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6343_);
v___y_6306_ = v___f_6333_;
v___y_6307_ = v___x_6344_;
goto v___jp_6305_;
}
else
{
lean_object* v___x_6345_; 
v___x_6345_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6339_);
v___y_6306_ = v___f_6333_;
v___y_6307_ = v___x_6345_;
goto v___jp_6305_;
}
}
else
{
lean_object* v___x_6346_; 
lean_dec(v_doc_6339_);
lean_inc(v_doc_6340_);
v___x_6346_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6340_);
v___y_6306_ = v___f_6333_;
v___y_6307_ = v___x_6346_;
goto v___jp_6305_;
}
}
else
{
v___y_6306_ = v___f_6333_;
v___y_6307_ = v___x_6335_;
goto v___jp_6305_;
}
}
else
{
lean_dec_ref(v___x_6335_);
v___y_6306_ = v___f_6333_;
v___y_6307_ = v___x_6336_;
goto v___jp_6305_;
}
}
else
{
lean_object* v___x_6347_; uint8_t v___x_6348_; lean_object* v___x_6349_; 
lean_dec_ref(v___f_6333_);
v___x_6347_ = lean_box(0);
v___x_6348_ = lean_unbox(v_snd_6323_);
lean_dec(v_snd_6323_);
lean_inc_ref(v_originalWhitespaceRange_6331_);
v___x_6349_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6331_, v_fst_6322_, v___x_6347_, v___x_6348_, v___x_6335_);
v___y_6298_ = v___x_6349_;
goto v___jp_6297_;
}
}
}
v___jp_6351_:
{
uint8_t v___x_6354_; 
v___x_6354_ = lean_nat_dec_le(v___y_6352_, v___y_6353_);
if (v___x_6354_ == 0)
{
lean_dec(v___y_6352_);
v___y_6318_ = v___y_6353_;
goto v___jp_6317_;
}
else
{
lean_dec(v___y_6353_);
v___y_6318_ = v___y_6352_;
goto v___jp_6317_;
}
}
v___jp_6355_:
{
lean_object* v___x_6357_; 
v___x_6357_ = lean_unsigned_to_nat(2u);
v___y_6352_ = v___y_6356_;
v___y_6353_ = v___x_6357_;
goto v___jp_6351_;
}
v___jp_6358_:
{
uint8_t v___x_6361_; 
v___x_6361_ = lean_nat_dec_eq(v_a_6295_, v___x_6316_);
if (v___x_6361_ == 0)
{
if (v___y_6359_ == 0)
{
lean_object* v___x_6362_; 
v___x_6362_ = lean_unsigned_to_nat(1u);
v___y_6352_ = v___y_6360_;
v___y_6353_ = v___x_6362_;
goto v___jp_6351_;
}
else
{
v___y_6356_ = v___y_6360_;
goto v___jp_6355_;
}
}
else
{
v___y_6356_ = v___y_6360_;
goto v___jp_6355_;
}
}
v___jp_6363_:
{
if (v___y_6364_ == 0)
{
v___y_6359_ = v___y_6364_;
v___y_6360_ = v___y_6365_;
goto v___jp_6358_;
}
else
{
lean_object* v___x_6366_; uint8_t v___x_6367_; 
v___x_6366_ = lean_unsigned_to_nat(1u);
v___x_6367_ = lean_nat_dec_le(v___y_6365_, v___x_6366_);
if (v___x_6367_ == 0)
{
v___y_6359_ = v___y_6364_;
v___y_6360_ = v___y_6365_;
goto v___jp_6358_;
}
else
{
lean_dec(v___y_6365_);
v___y_6359_ = v___y_6364_;
v___y_6360_ = v___x_6366_;
goto v___jp_6358_;
}
}
}
v___jp_6368_:
{
lean_object* v___x_6370_; 
v___x_6370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_numNewlinesBeforeComments_6294_, v_a_6295_);
if (lean_obj_tag(v___x_6370_) == 0)
{
v___y_6364_ = v___y_6369_;
v___y_6365_ = v___x_6316_;
goto v___jp_6363_;
}
else
{
lean_object* v_val_6371_; 
v_val_6371_ = lean_ctor_get(v___x_6370_, 0);
lean_inc(v_val_6371_);
lean_dec_ref_known(v___x_6370_, 1);
v___y_6364_ = v___y_6369_;
v___y_6365_ = v_val_6371_;
goto v___jp_6363_;
}
}
}
}
v___jp_6297_:
{
if (lean_obj_tag(v___y_6298_) == 0)
{
lean_object* v_a_6299_; 
lean_dec(v_a_6295_);
v_a_6299_ = lean_ctor_get(v___y_6298_, 0);
lean_inc(v_a_6299_);
lean_dec_ref_known(v___y_6298_, 1);
return v_a_6299_;
}
else
{
lean_object* v_a_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; 
v_a_6300_ = lean_ctor_get(v___y_6298_, 0);
lean_inc(v_a_6300_);
lean_dec_ref_known(v___y_6298_, 1);
v___x_6301_ = lean_unsigned_to_nat(1u);
v___x_6302_ = lean_nat_add(v_a_6295_, v___x_6301_);
lean_dec(v_a_6295_);
v_a_6295_ = v___x_6302_;
v_b_6296_ = v_a_6300_;
goto _start;
}
}
v___jp_6305_:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6308_ = lean_box(0);
v___x_6309_ = lean_box(v___x_6304_);
v___x_6310_ = lean_apply_3(v___y_6306_, v___x_6308_, v___x_6309_, v___y_6307_);
v___y_6298_ = v___x_6310_;
goto v___jp_6297_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___boxed(lean_object* v_upperBound_6379_, lean_object* v_comments_6380_, lean_object* v_numNewlinesBeforeComments_6381_, lean_object* v_a_6382_, lean_object* v_b_6383_){
_start:
{
lean_object* v_res_6384_; 
v_res_6384_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6379_, v_comments_6380_, v_numNewlinesBeforeComments_6381_, v_a_6382_, v_b_6383_);
lean_dec_ref(v_numNewlinesBeforeComments_6381_);
lean_dec_ref(v_comments_6380_);
lean_dec(v_upperBound_6379_);
return v_res_6384_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object* v_upperBound_6385_, lean_object* v_a_6386_, lean_object* v_b_6387_){
_start:
{
uint8_t v___x_6388_; 
v___x_6388_ = lean_nat_dec_lt(v_a_6386_, v_upperBound_6385_);
if (v___x_6388_ == 0)
{
lean_dec(v_a_6386_);
return v_b_6387_;
}
else
{
lean_object* v_fst_6389_; lean_object* v___x_6391_; uint8_t v_isShared_6392_; uint8_t v_isSharedCheck_6402_; 
v_fst_6389_ = lean_ctor_get(v_b_6387_, 0);
v_isSharedCheck_6402_ = !lean_is_exclusive(v_b_6387_);
if (v_isSharedCheck_6402_ == 0)
{
lean_object* v_unused_6403_; 
v_unused_6403_ = lean_ctor_get(v_b_6387_, 1);
lean_dec(v_unused_6403_);
v___x_6391_ = v_b_6387_;
v_isShared_6392_ = v_isSharedCheck_6402_;
goto v_resetjp_6390_;
}
else
{
lean_inc(v_fst_6389_);
lean_dec(v_b_6387_);
v___x_6391_ = lean_box(0);
v_isShared_6392_ = v_isSharedCheck_6402_;
goto v_resetjp_6390_;
}
v_resetjp_6390_:
{
lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6397_; 
v___x_6393_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6394_ = lean_array_push(v_fst_6389_, v___x_6393_);
v___x_6395_ = lean_box(v___x_6388_);
if (v_isShared_6392_ == 0)
{
lean_ctor_set(v___x_6391_, 1, v___x_6395_);
lean_ctor_set(v___x_6391_, 0, v___x_6394_);
v___x_6397_ = v___x_6391_;
goto v_reusejp_6396_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v___x_6394_);
lean_ctor_set(v_reuseFailAlloc_6401_, 1, v___x_6395_);
v___x_6397_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6396_;
}
v_reusejp_6396_:
{
lean_object* v___x_6398_; lean_object* v___x_6399_; 
v___x_6398_ = lean_unsigned_to_nat(1u);
v___x_6399_ = lean_nat_add(v_a_6386_, v___x_6398_);
lean_dec(v_a_6386_);
v_a_6386_ = v___x_6399_;
v_b_6387_ = v___x_6397_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object* v_upperBound_6404_, lean_object* v_a_6405_, lean_object* v_b_6406_){
_start:
{
lean_object* v_res_6407_; 
v_res_6407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6404_, v_a_6405_, v_b_6406_);
lean_dec(v_upperBound_6404_);
return v_res_6407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(lean_object* v_as_6408_, size_t v_i_6409_, size_t v_stop_6410_, lean_object* v_b_6411_){
_start:
{
lean_object* v___y_6413_; uint8_t v___x_6417_; 
v___x_6417_ = lean_usize_dec_eq(v_i_6409_, v_stop_6410_);
if (v___x_6417_ == 0)
{
lean_object* v___x_6418_; uint8_t v_placement_6419_; 
v___x_6418_ = lean_array_uget_borrowed(v_as_6408_, v_i_6409_);
v_placement_6419_ = lean_ctor_get_uint8(v___x_6418_, sizeof(void*)*3 + 1);
if (v_placement_6419_ == 0)
{
v___y_6413_ = v_b_6411_;
goto v___jp_6412_;
}
else
{
lean_object* v___x_6420_; 
lean_inc(v___x_6418_);
v___x_6420_ = lean_array_push(v_b_6411_, v___x_6418_);
v___y_6413_ = v___x_6420_;
goto v___jp_6412_;
}
}
else
{
return v_b_6411_;
}
v___jp_6412_:
{
size_t v___x_6414_; size_t v___x_6415_; 
v___x_6414_ = ((size_t)1ULL);
v___x_6415_ = lean_usize_add(v_i_6409_, v___x_6414_);
v_i_6409_ = v___x_6415_;
v_b_6411_ = v___y_6413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8___boxed(lean_object* v_as_6421_, lean_object* v_i_6422_, lean_object* v_stop_6423_, lean_object* v_b_6424_){
_start:
{
size_t v_i_boxed_6425_; size_t v_stop_boxed_6426_; lean_object* v_res_6427_; 
v_i_boxed_6425_ = lean_unbox_usize(v_i_6422_);
lean_dec(v_i_6422_);
v_stop_boxed_6426_ = lean_unbox_usize(v_stop_6423_);
lean_dec(v_stop_6423_);
v_res_6427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_as_6421_, v_i_boxed_6425_, v_stop_boxed_6426_, v_b_6424_);
lean_dec_ref(v_as_6421_);
return v_res_6427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object* v_comments_6434_, lean_object* v_whitespace_6435_, uint8_t v_isLeading_6436_){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___y_6440_; lean_object* v___y_6441_; lean_object* v___y_6442_; lean_object* v___y_6455_; lean_object* v___y_6456_; lean_object* v___y_6457_; lean_object* v___y_6458_; lean_object* v___x_6460_; uint8_t v___y_6462_; lean_object* v___y_6463_; lean_object* v___y_6464_; lean_object* v___y_6465_; uint8_t v___y_6471_; lean_object* v___y_6472_; lean_object* v___y_6473_; lean_object* v___y_6474_; lean_object* v___y_6478_; lean_object* v___y_6479_; lean_object* v___y_6480_; uint8_t v___y_6481_; lean_object* v___y_6485_; lean_object* v___x_6498_; uint8_t v___x_6499_; 
v___x_6437_ = l_Lean_Fmt_instInhabitedComment_default;
v___x_6438_ = lean_unsigned_to_nat(0u);
v___x_6460_ = lean_array_get_size(v_comments_6434_);
v___x_6498_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6499_ = lean_nat_dec_lt(v___x_6438_, v___x_6460_);
if (v___x_6499_ == 0)
{
v___y_6485_ = v___x_6498_;
goto v___jp_6484_;
}
else
{
size_t v___x_6500_; size_t v___x_6501_; lean_object* v___x_6502_; 
v___x_6500_ = ((size_t)0ULL);
v___x_6501_ = lean_usize_of_nat(v___x_6460_);
v___x_6502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_comments_6434_, v___x_6500_, v___x_6501_, v___x_6498_);
v___y_6485_ = v___x_6502_;
goto v___jp_6484_;
}
v___jp_6439_:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v_fst_6445_; lean_object* v_snd_6446_; lean_object* v___x_6448_; uint8_t v_isShared_6449_; uint8_t v_isSharedCheck_6453_; 
v___x_6443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6443_, 0, v___y_6441_);
lean_ctor_set(v___x_6443_, 1, v___y_6440_);
v___x_6444_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v___y_6442_, v___x_6438_, v___x_6443_);
lean_dec(v___y_6442_);
v_fst_6445_ = lean_ctor_get(v___x_6444_, 0);
v_snd_6446_ = lean_ctor_get(v___x_6444_, 1);
v_isSharedCheck_6453_ = !lean_is_exclusive(v___x_6444_);
if (v_isSharedCheck_6453_ == 0)
{
v___x_6448_ = v___x_6444_;
v_isShared_6449_ = v_isSharedCheck_6453_;
goto v_resetjp_6447_;
}
else
{
lean_inc(v_snd_6446_);
lean_inc(v_fst_6445_);
lean_dec(v___x_6444_);
v___x_6448_ = lean_box(0);
v_isShared_6449_ = v_isSharedCheck_6453_;
goto v_resetjp_6447_;
}
v_resetjp_6447_:
{
lean_object* v___x_6451_; 
if (v_isShared_6449_ == 0)
{
v___x_6451_ = v___x_6448_;
goto v_reusejp_6450_;
}
else
{
lean_object* v_reuseFailAlloc_6452_; 
v_reuseFailAlloc_6452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6452_, 0, v_fst_6445_);
lean_ctor_set(v_reuseFailAlloc_6452_, 1, v_snd_6446_);
v___x_6451_ = v_reuseFailAlloc_6452_;
goto v_reusejp_6450_;
}
v_reusejp_6450_:
{
return v___x_6451_;
}
}
}
v___jp_6454_:
{
uint8_t v___x_6459_; 
v___x_6459_ = lean_nat_dec_le(v___y_6455_, v___y_6458_);
if (v___x_6459_ == 0)
{
lean_dec(v___y_6455_);
v___y_6440_ = v___y_6457_;
v___y_6441_ = v___y_6456_;
v___y_6442_ = v___y_6458_;
goto v___jp_6439_;
}
else
{
lean_dec(v___y_6458_);
v___y_6440_ = v___y_6457_;
v___y_6441_ = v___y_6456_;
v___y_6442_ = v___y_6455_;
goto v___jp_6439_;
}
}
v___jp_6461_:
{
uint8_t v___x_6466_; 
v___x_6466_ = lean_nat_dec_eq(v___x_6460_, v___x_6438_);
if (v___x_6466_ == 0)
{
if (v___y_6462_ == 0)
{
lean_object* v___x_6467_; 
v___x_6467_ = lean_unsigned_to_nat(1u);
v___y_6455_ = v___y_6465_;
v___y_6456_ = v___y_6464_;
v___y_6457_ = v___y_6463_;
v___y_6458_ = v___x_6467_;
goto v___jp_6454_;
}
else
{
lean_object* v___x_6468_; 
v___x_6468_ = lean_unsigned_to_nat(2u);
v___y_6455_ = v___y_6465_;
v___y_6456_ = v___y_6464_;
v___y_6457_ = v___y_6463_;
v___y_6458_ = v___x_6468_;
goto v___jp_6454_;
}
}
else
{
if (v_isLeading_6436_ == 0)
{
lean_object* v___x_6469_; 
v___x_6469_ = lean_unsigned_to_nat(2u);
v___y_6455_ = v___y_6465_;
v___y_6456_ = v___y_6464_;
v___y_6457_ = v___y_6463_;
v___y_6458_ = v___x_6469_;
goto v___jp_6454_;
}
else
{
v___y_6455_ = v___y_6465_;
v___y_6456_ = v___y_6464_;
v___y_6457_ = v___y_6463_;
v___y_6458_ = v___x_6438_;
goto v___jp_6454_;
}
}
}
v___jp_6470_:
{
if (v___y_6471_ == 0)
{
v___y_6462_ = v___y_6471_;
v___y_6463_ = v___y_6473_;
v___y_6464_ = v___y_6472_;
v___y_6465_ = v___y_6474_;
goto v___jp_6461_;
}
else
{
lean_object* v___x_6475_; uint8_t v___x_6476_; 
v___x_6475_ = lean_unsigned_to_nat(1u);
v___x_6476_ = lean_nat_dec_le(v___y_6474_, v___x_6475_);
if (v___x_6476_ == 0)
{
v___y_6462_ = v___y_6471_;
v___y_6463_ = v___y_6473_;
v___y_6464_ = v___y_6472_;
v___y_6465_ = v___y_6474_;
goto v___jp_6461_;
}
else
{
lean_dec(v___y_6474_);
v___y_6462_ = v___y_6471_;
v___y_6463_ = v___y_6473_;
v___y_6464_ = v___y_6472_;
v___y_6465_ = v___x_6475_;
goto v___jp_6461_;
}
}
}
v___jp_6477_:
{
lean_object* v___x_6482_; 
v___x_6482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v___y_6480_, v___x_6460_);
lean_dec_ref(v___y_6480_);
if (lean_obj_tag(v___x_6482_) == 0)
{
v___y_6471_ = v___y_6481_;
v___y_6472_ = v___y_6479_;
v___y_6473_ = v___y_6478_;
v___y_6474_ = v___x_6438_;
goto v___jp_6470_;
}
else
{
lean_object* v_val_6483_; 
v_val_6483_ = lean_ctor_get(v___x_6482_, 0);
lean_inc(v_val_6483_);
lean_dec_ref_known(v___x_6482_, 1);
v___y_6471_ = v___y_6481_;
v___y_6472_ = v___y_6479_;
v___y_6473_ = v___y_6478_;
v___y_6474_ = v_val_6483_;
goto v___jp_6470_;
}
}
v___jp_6484_:
{
lean_object* v_numNewlinesBeforeComments_6486_; uint8_t v_insertedAnyNewlines_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v_fst_6490_; lean_object* v_snd_6491_; uint8_t v___x_6492_; 
v_numNewlinesBeforeComments_6486_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v___y_6485_, v_whitespace_6435_);
lean_dec_ref(v___y_6485_);
v_insertedAnyNewlines_6487_ = 0;
v___x_6488_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0));
v___x_6489_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v___x_6460_, v_comments_6434_, v_numNewlinesBeforeComments_6486_, v___x_6438_, v___x_6488_);
v_fst_6490_ = lean_ctor_get(v___x_6489_, 0);
lean_inc(v_fst_6490_);
v_snd_6491_ = lean_ctor_get(v___x_6489_, 1);
lean_inc(v_snd_6491_);
lean_dec_ref(v___x_6489_);
v___x_6492_ = lean_nat_dec_eq(v___x_6460_, v___x_6438_);
if (v___x_6492_ == 0)
{
lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; uint8_t v_kind_6496_; 
v___x_6493_ = lean_unsigned_to_nat(1u);
v___x_6494_ = lean_nat_sub(v___x_6460_, v___x_6493_);
v___x_6495_ = lean_array_get_borrowed(v___x_6437_, v_comments_6434_, v___x_6494_);
lean_dec(v___x_6494_);
v_kind_6496_ = lean_ctor_get_uint8(v___x_6495_, sizeof(void*)*3);
if (v_kind_6496_ == 1)
{
uint8_t v___x_6497_; 
v___x_6497_ = 1;
v___y_6478_ = v_snd_6491_;
v___y_6479_ = v_fst_6490_;
v___y_6480_ = v_numNewlinesBeforeComments_6486_;
v___y_6481_ = v___x_6497_;
goto v___jp_6477_;
}
else
{
v___y_6478_ = v_snd_6491_;
v___y_6479_ = v_fst_6490_;
v___y_6480_ = v_numNewlinesBeforeComments_6486_;
v___y_6481_ = v_insertedAnyNewlines_6487_;
goto v___jp_6477_;
}
}
else
{
v___y_6478_ = v_snd_6491_;
v___y_6479_ = v_fst_6490_;
v___y_6480_ = v_numNewlinesBeforeComments_6486_;
v___y_6481_ = v_insertedAnyNewlines_6487_;
goto v___jp_6477_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object* v_comments_6503_, lean_object* v_whitespace_6504_, lean_object* v_isLeading_6505_){
_start:
{
uint8_t v_isLeading_boxed_6506_; lean_object* v_res_6507_; 
v_isLeading_boxed_6506_ = lean_unbox(v_isLeading_6505_);
v_res_6507_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v_comments_6503_, v_whitespace_6504_, v_isLeading_boxed_6506_);
lean_dec_ref(v_whitespace_6504_);
lean_dec_ref(v_comments_6503_);
return v_res_6507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object* v_a_6508_, lean_object* v___x_6509_, lean_object* v___x_6510_, lean_object* v_inst_6511_, lean_object* v_R_6512_, lean_object* v_a_6513_, lean_object* v_b_6514_){
_start:
{
lean_object* v___x_6515_; 
v___x_6515_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6508_, v___x_6509_, v___x_6510_, v_a_6513_, v_b_6514_);
return v___x_6515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object* v_a_6516_, lean_object* v___x_6517_, lean_object* v___x_6518_, lean_object* v_inst_6519_, lean_object* v_R_6520_, lean_object* v_a_6521_, lean_object* v_b_6522_){
_start:
{
lean_object* v_res_6523_; 
v_res_6523_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(v_a_6516_, v___x_6517_, v___x_6518_, v_inst_6519_, v_R_6520_, v_a_6521_, v_b_6522_);
lean_dec_ref(v___x_6517_);
return v_res_6523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(lean_object* v_as_6524_, size_t v_sz_6525_, size_t v_i_6526_, lean_object* v_bs_6527_){
_start:
{
lean_object* v___x_6528_; 
v___x_6528_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6525_, v_i_6526_, v_bs_6527_);
return v___x_6528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object* v_as_6529_, lean_object* v_sz_6530_, lean_object* v_i_6531_, lean_object* v_bs_6532_){
_start:
{
size_t v_sz_boxed_6533_; size_t v_i_boxed_6534_; lean_object* v_res_6535_; 
v_sz_boxed_6533_ = lean_unbox_usize(v_sz_6530_);
lean_dec(v_sz_6530_);
v_i_boxed_6534_ = lean_unbox_usize(v_i_6531_);
lean_dec(v_i_6531_);
v_res_6535_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(v_as_6529_, v_sz_boxed_6533_, v_i_boxed_6534_, v_bs_6532_);
lean_dec_ref(v_as_6529_);
return v_res_6535_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object* v_upperBound_6536_, lean_object* v_next_6537_, lean_object* v_upperBound_6538_, lean_object* v_inst_6539_, lean_object* v_R_6540_, lean_object* v_a_6541_, lean_object* v_b_6542_, lean_object* v_c_6543_){
_start:
{
lean_object* v___x_6544_; 
v___x_6544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6536_, v_next_6537_, v_upperBound_6538_, v_a_6541_, v_b_6542_);
return v___x_6544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object* v_upperBound_6545_, lean_object* v_next_6546_, lean_object* v_upperBound_6547_, lean_object* v_inst_6548_, lean_object* v_R_6549_, lean_object* v_a_6550_, lean_object* v_b_6551_, lean_object* v_c_6552_){
_start:
{
lean_object* v_res_6553_; 
v_res_6553_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(v_upperBound_6545_, v_next_6546_, v_upperBound_6547_, v_inst_6548_, v_R_6549_, v_a_6550_, v_b_6551_, v_c_6552_);
lean_dec(v_upperBound_6547_);
lean_dec(v_next_6546_);
lean_dec(v_upperBound_6545_);
return v_res_6553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object* v_00_u03b2_6554_, lean_object* v_m_6555_, lean_object* v_a_6556_){
_start:
{
lean_object* v___x_6557_; 
v___x_6557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6555_, v_a_6556_);
return v___x_6557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object* v_00_u03b2_6558_, lean_object* v_m_6559_, lean_object* v_a_6560_){
_start:
{
lean_object* v_res_6561_; 
v_res_6561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(v_00_u03b2_6558_, v_m_6559_, v_a_6560_);
lean_dec(v_a_6560_);
lean_dec_ref(v_m_6559_);
return v_res_6561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object* v_upperBound_6562_, lean_object* v_inst_6563_, lean_object* v_R_6564_, lean_object* v_a_6565_, lean_object* v_b_6566_, lean_object* v_c_6567_){
_start:
{
lean_object* v___x_6568_; 
v___x_6568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6562_, v_a_6565_, v_b_6566_);
return v___x_6568_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object* v_upperBound_6569_, lean_object* v_inst_6570_, lean_object* v_R_6571_, lean_object* v_a_6572_, lean_object* v_b_6573_, lean_object* v_c_6574_){
_start:
{
lean_object* v_res_6575_; 
v_res_6575_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(v_upperBound_6569_, v_inst_6570_, v_R_6571_, v_a_6572_, v_b_6573_, v_c_6574_);
lean_dec(v_upperBound_6569_);
return v_res_6575_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object* v_upperBound_6576_, lean_object* v_comments_6577_, lean_object* v_numNewlinesBeforeComments_6578_, lean_object* v_inst_6579_, lean_object* v_R_6580_, lean_object* v_a_6581_, lean_object* v_b_6582_, lean_object* v_c_6583_){
_start:
{
lean_object* v___x_6584_; 
v___x_6584_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6576_, v_comments_6577_, v_numNewlinesBeforeComments_6578_, v_a_6581_, v_b_6582_);
return v___x_6584_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object* v_upperBound_6585_, lean_object* v_comments_6586_, lean_object* v_numNewlinesBeforeComments_6587_, lean_object* v_inst_6588_, lean_object* v_R_6589_, lean_object* v_a_6590_, lean_object* v_b_6591_, lean_object* v_c_6592_){
_start:
{
lean_object* v_res_6593_; 
v_res_6593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_upperBound_6585_, v_comments_6586_, v_numNewlinesBeforeComments_6587_, v_inst_6588_, v_R_6589_, v_a_6590_, v_b_6591_, v_c_6592_);
lean_dec_ref(v_numNewlinesBeforeComments_6587_);
lean_dec_ref(v_comments_6586_);
lean_dec(v_upperBound_6585_);
return v_res_6593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object* v_00_u03b2_6594_, lean_object* v_a_6595_, lean_object* v_x_6596_){
_start:
{
lean_object* v___x_6597_; 
v___x_6597_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6595_, v_x_6596_);
return v___x_6597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object* v_00_u03b2_6598_, lean_object* v_a_6599_, lean_object* v_x_6600_){
_start:
{
lean_object* v_res_6601_; 
v_res_6601_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(v_00_u03b2_6598_, v_a_6599_, v_x_6600_);
lean_dec(v_x_6600_);
lean_dec(v_a_6599_);
return v_res_6601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object* v_leadingTk_6604_, lean_object* v_leading_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_){
_start:
{
uint8_t v___x_6614_; lean_object* v___x_6615_; 
v___x_6614_ = 0;
v___x_6615_ = l_Lean_Syntax_getRange_x3f(v_leadingTk_6604_, v___x_6614_);
if (lean_obj_tag(v___x_6615_) == 1)
{
lean_object* v_val_6616_; lean_object* v_str_6617_; lean_object* v_startPos_6618_; lean_object* v_stopPos_6619_; lean_object* v___x_6621_; uint8_t v_isShared_6622_; uint8_t v_isSharedCheck_6642_; 
v_val_6616_ = lean_ctor_get(v___x_6615_, 0);
lean_inc(v_val_6616_);
lean_dec_ref_known(v___x_6615_, 1);
v_str_6617_ = lean_ctor_get(v_leading_6605_, 0);
v_startPos_6618_ = lean_ctor_get(v_leading_6605_, 1);
v_stopPos_6619_ = lean_ctor_get(v_leading_6605_, 2);
v_isSharedCheck_6642_ = !lean_is_exclusive(v_leading_6605_);
if (v_isSharedCheck_6642_ == 0)
{
v___x_6621_ = v_leading_6605_;
v_isShared_6622_ = v_isSharedCheck_6642_;
goto v_resetjp_6620_;
}
else
{
lean_inc(v_stopPos_6619_);
lean_inc(v_startPos_6618_);
lean_inc(v_str_6617_);
lean_dec(v_leading_6605_);
v___x_6621_ = lean_box(0);
v_isShared_6622_ = v_isSharedCheck_6642_;
goto v_resetjp_6620_;
}
v_resetjp_6620_:
{
uint8_t v___x_6623_; 
v___x_6623_ = lean_string_is_valid_pos(v_str_6617_, v_startPos_6618_);
if (v___x_6623_ == 0)
{
lean_del_object(v___x_6621_);
lean_dec(v_stopPos_6619_);
lean_dec(v_startPos_6618_);
lean_dec_ref(v_str_6617_);
lean_dec(v_val_6616_);
goto v___jp_6608_;
}
else
{
uint8_t v___x_6624_; 
v___x_6624_ = lean_string_is_valid_pos(v_str_6617_, v_stopPos_6619_);
if (v___x_6624_ == 0)
{
lean_del_object(v___x_6621_);
lean_dec(v_stopPos_6619_);
lean_dec(v_startPos_6618_);
lean_dec_ref(v_str_6617_);
lean_dec(v_val_6616_);
goto v___jp_6608_;
}
else
{
uint8_t v___x_6625_; 
v___x_6625_ = lean_nat_dec_le(v_startPos_6618_, v_stopPos_6619_);
if (v___x_6625_ == 0)
{
lean_del_object(v___x_6621_);
lean_dec(v_stopPos_6619_);
lean_dec(v_startPos_6618_);
lean_dec_ref(v_str_6617_);
lean_dec(v_val_6616_);
goto v___jp_6608_;
}
else
{
lean_object* v_lineInfos_6626_; lean_object* v___x_6628_; 
lean_dec(v_leadingTk_6604_);
v_lineInfos_6626_ = lean_ctor_get(v___y_6606_, 4);
if (v_isShared_6622_ == 0)
{
v___x_6628_ = v___x_6621_;
goto v_reusejp_6627_;
}
else
{
lean_object* v_reuseFailAlloc_6641_; 
v_reuseFailAlloc_6641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6641_, 0, v_str_6617_);
lean_ctor_set(v_reuseFailAlloc_6641_, 1, v_startPos_6618_);
lean_ctor_set(v_reuseFailAlloc_6641_, 2, v_stopPos_6619_);
v___x_6628_ = v_reuseFailAlloc_6641_;
goto v_reusejp_6627_;
}
v_reusejp_6627_:
{
uint8_t v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v_fst_6632_; lean_object* v___x_6634_; uint8_t v_isShared_6635_; uint8_t v_isSharedCheck_6639_; 
v___x_6629_ = 0;
lean_inc_ref(v___x_6628_);
v___x_6630_ = l_Lean_Fmt_parseComments(v_lineInfos_6626_, v_val_6616_, v___x_6629_, v___x_6628_);
v___x_6631_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___x_6630_, v___x_6628_, v___x_6625_);
lean_dec_ref(v___x_6628_);
lean_dec_ref(v___x_6630_);
v_fst_6632_ = lean_ctor_get(v___x_6631_, 0);
v_isSharedCheck_6639_ = !lean_is_exclusive(v___x_6631_);
if (v_isSharedCheck_6639_ == 0)
{
lean_object* v_unused_6640_; 
v_unused_6640_ = lean_ctor_get(v___x_6631_, 1);
lean_dec(v_unused_6640_);
v___x_6634_ = v___x_6631_;
v_isShared_6635_ = v_isSharedCheck_6639_;
goto v_resetjp_6633_;
}
else
{
lean_inc(v_fst_6632_);
lean_dec(v___x_6631_);
v___x_6634_ = lean_box(0);
v_isShared_6635_ = v_isSharedCheck_6639_;
goto v_resetjp_6633_;
}
v_resetjp_6633_:
{
lean_object* v___x_6637_; 
if (v_isShared_6635_ == 0)
{
lean_ctor_set(v___x_6634_, 1, v___y_6607_);
v___x_6637_ = v___x_6634_;
goto v_reusejp_6636_;
}
else
{
lean_object* v_reuseFailAlloc_6638_; 
v_reuseFailAlloc_6638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_fst_6632_);
lean_ctor_set(v_reuseFailAlloc_6638_, 1, v___y_6607_);
v___x_6637_ = v_reuseFailAlloc_6638_;
goto v_reusejp_6636_;
}
v_reusejp_6636_:
{
return v___x_6637_;
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
lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; 
lean_dec(v___x_6615_);
lean_dec_ref(v_leading_6605_);
v___x_6643_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6644_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6645_, 0, v_leadingTk_6604_);
lean_ctor_set(v___x_6645_, 1, v___x_6643_);
lean_ctor_set(v___x_6645_, 2, v___x_6644_);
v___x_6646_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6646_, 0, v___x_6645_);
v___x_6647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6647_, 0, v___x_6646_);
lean_ctor_set(v___x_6647_, 1, v___y_6607_);
return v___x_6647_;
}
v___jp_6608_:
{
lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; 
v___x_6609_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6610_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6611_, 0, v_leadingTk_6604_);
lean_ctor_set(v___x_6611_, 1, v___x_6609_);
lean_ctor_set(v___x_6611_, 2, v___x_6610_);
v___x_6612_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6612_, 0, v___x_6611_);
v___x_6613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6613_, 0, v___x_6612_);
lean_ctor_set(v___x_6613_, 1, v___y_6607_);
return v___x_6613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_leadingTk_6648_, lean_object* v_leading_6649_, lean_object* v___y_6650_, lean_object* v___y_6651_){
_start:
{
lean_object* v_res_6652_; 
v_res_6652_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(v_leadingTk_6648_, v_leading_6649_, v___y_6650_, v___y_6651_);
lean_dec_ref(v___y_6650_);
return v_res_6652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object* v_stx_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_){
_start:
{
lean_object* v___f_6657_; lean_object* v___x_6658_; 
v___f_6657_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0));
v___x_6658_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_6654_, v___f_6657_, v_a_6655_, v_a_6656_);
return v___x_6658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_){
_start:
{
lean_object* v_res_6662_; 
v_res_6662_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v_stx_6659_, v_a_6660_, v_a_6661_);
lean_dec_ref(v_a_6660_);
return v_res_6662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t v_atleastOneNewline_6663_, lean_object* v_trailingTk_6664_, lean_object* v_trailing_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_){
_start:
{
uint8_t v___x_6674_; lean_object* v___x_6675_; 
v___x_6674_ = 0;
v___x_6675_ = l_Lean_Syntax_getRange_x3f(v_trailingTk_6664_, v___x_6674_);
if (lean_obj_tag(v___x_6675_) == 1)
{
lean_object* v_val_6676_; lean_object* v_str_6677_; lean_object* v_startPos_6678_; lean_object* v_stopPos_6679_; lean_object* v___x_6681_; uint8_t v_isShared_6682_; uint8_t v_isSharedCheck_6733_; 
v_val_6676_ = lean_ctor_get(v___x_6675_, 0);
lean_inc(v_val_6676_);
lean_dec_ref_known(v___x_6675_, 1);
v_str_6677_ = lean_ctor_get(v_trailing_6665_, 0);
v_startPos_6678_ = lean_ctor_get(v_trailing_6665_, 1);
v_stopPos_6679_ = lean_ctor_get(v_trailing_6665_, 2);
v_isSharedCheck_6733_ = !lean_is_exclusive(v_trailing_6665_);
if (v_isSharedCheck_6733_ == 0)
{
v___x_6681_ = v_trailing_6665_;
v_isShared_6682_ = v_isSharedCheck_6733_;
goto v_resetjp_6680_;
}
else
{
lean_inc(v_stopPos_6679_);
lean_inc(v_startPos_6678_);
lean_inc(v_str_6677_);
lean_dec(v_trailing_6665_);
v___x_6681_ = lean_box(0);
v_isShared_6682_ = v_isSharedCheck_6733_;
goto v_resetjp_6680_;
}
v_resetjp_6680_:
{
uint8_t v___x_6683_; 
v___x_6683_ = lean_string_is_valid_pos(v_str_6677_, v_startPos_6678_);
if (v___x_6683_ == 0)
{
lean_del_object(v___x_6681_);
lean_dec(v_stopPos_6679_);
lean_dec(v_startPos_6678_);
lean_dec_ref(v_str_6677_);
lean_dec(v_val_6676_);
goto v___jp_6668_;
}
else
{
uint8_t v___x_6684_; 
v___x_6684_ = lean_string_is_valid_pos(v_str_6677_, v_stopPos_6679_);
if (v___x_6684_ == 0)
{
lean_del_object(v___x_6681_);
lean_dec(v_stopPos_6679_);
lean_dec(v_startPos_6678_);
lean_dec_ref(v_str_6677_);
lean_dec(v_val_6676_);
goto v___jp_6668_;
}
else
{
uint8_t v___x_6685_; 
v___x_6685_ = lean_nat_dec_le(v_startPos_6678_, v_stopPos_6679_);
if (v___x_6685_ == 0)
{
lean_del_object(v___x_6681_);
lean_dec(v_stopPos_6679_);
lean_dec(v_startPos_6678_);
lean_dec_ref(v_str_6677_);
lean_dec(v_val_6676_);
goto v___jp_6668_;
}
else
{
lean_object* v_lineInfos_6686_; lean_object* v___x_6688_; 
lean_dec(v_trailingTk_6664_);
v_lineInfos_6686_ = lean_ctor_get(v___y_6666_, 4);
if (v_isShared_6682_ == 0)
{
v___x_6688_ = v___x_6681_;
goto v_reusejp_6687_;
}
else
{
lean_object* v_reuseFailAlloc_6732_; 
v_reuseFailAlloc_6732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6732_, 0, v_str_6677_);
lean_ctor_set(v_reuseFailAlloc_6732_, 1, v_startPos_6678_);
lean_ctor_set(v_reuseFailAlloc_6732_, 2, v_stopPos_6679_);
v___x_6688_ = v_reuseFailAlloc_6732_;
goto v_reusejp_6687_;
}
v_reusejp_6687_:
{
lean_object* v___y_6690_; uint8_t v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; lean_object* v___x_6727_; uint8_t v___x_6728_; 
v___x_6723_ = 1;
lean_inc_ref(v___x_6688_);
v___x_6724_ = l_Lean_Fmt_parseComments(v_lineInfos_6686_, v_val_6676_, v___x_6723_, v___x_6688_);
v___x_6725_ = lean_unsigned_to_nat(0u);
v___x_6726_ = lean_array_get_size(v___x_6724_);
v___x_6727_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6728_ = lean_nat_dec_lt(v___x_6725_, v___x_6726_);
if (v___x_6728_ == 0)
{
lean_dec_ref(v___x_6724_);
v___y_6690_ = v___x_6727_;
goto v___jp_6689_;
}
else
{
size_t v___x_6729_; size_t v___x_6730_; lean_object* v___x_6731_; 
v___x_6729_ = ((size_t)0ULL);
v___x_6730_ = lean_usize_of_nat(v___x_6726_);
v___x_6731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v___x_6724_, v___x_6729_, v___x_6730_, v___x_6727_);
lean_dec_ref(v___x_6724_);
v___y_6690_ = v___x_6731_;
goto v___jp_6689_;
}
v___jp_6689_:
{
lean_object* v___x_6691_; lean_object* v_snd_6692_; uint8_t v___x_6693_; 
v___x_6691_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___y_6690_, v___x_6688_, v___x_6674_);
lean_dec_ref(v___x_6688_);
lean_dec_ref(v___y_6690_);
v_snd_6692_ = lean_ctor_get(v___x_6691_, 1);
v___x_6693_ = lean_unbox(v_snd_6692_);
if (v___x_6693_ == 0)
{
if (v_atleastOneNewline_6663_ == 0)
{
lean_object* v_fst_6694_; lean_object* v___x_6696_; uint8_t v_isShared_6697_; uint8_t v_isSharedCheck_6701_; 
v_fst_6694_ = lean_ctor_get(v___x_6691_, 0);
v_isSharedCheck_6701_ = !lean_is_exclusive(v___x_6691_);
if (v_isSharedCheck_6701_ == 0)
{
lean_object* v_unused_6702_; 
v_unused_6702_ = lean_ctor_get(v___x_6691_, 1);
lean_dec(v_unused_6702_);
v___x_6696_ = v___x_6691_;
v_isShared_6697_ = v_isSharedCheck_6701_;
goto v_resetjp_6695_;
}
else
{
lean_inc(v_fst_6694_);
lean_dec(v___x_6691_);
v___x_6696_ = lean_box(0);
v_isShared_6697_ = v_isSharedCheck_6701_;
goto v_resetjp_6695_;
}
v_resetjp_6695_:
{
lean_object* v___x_6699_; 
if (v_isShared_6697_ == 0)
{
lean_ctor_set(v___x_6696_, 1, v___y_6667_);
v___x_6699_ = v___x_6696_;
goto v_reusejp_6698_;
}
else
{
lean_object* v_reuseFailAlloc_6700_; 
v_reuseFailAlloc_6700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6700_, 0, v_fst_6694_);
lean_ctor_set(v_reuseFailAlloc_6700_, 1, v___y_6667_);
v___x_6699_ = v_reuseFailAlloc_6700_;
goto v_reusejp_6698_;
}
v_reusejp_6698_:
{
return v___x_6699_;
}
}
}
else
{
lean_object* v_fst_6703_; lean_object* v___x_6705_; uint8_t v_isShared_6706_; uint8_t v_isSharedCheck_6712_; 
v_fst_6703_ = lean_ctor_get(v___x_6691_, 0);
v_isSharedCheck_6712_ = !lean_is_exclusive(v___x_6691_);
if (v_isSharedCheck_6712_ == 0)
{
lean_object* v_unused_6713_; 
v_unused_6713_ = lean_ctor_get(v___x_6691_, 1);
lean_dec(v_unused_6713_);
v___x_6705_ = v___x_6691_;
v_isShared_6706_ = v_isSharedCheck_6712_;
goto v_resetjp_6704_;
}
else
{
lean_inc(v_fst_6703_);
lean_dec(v___x_6691_);
v___x_6705_ = lean_box(0);
v_isShared_6706_ = v_isSharedCheck_6712_;
goto v_resetjp_6704_;
}
v_resetjp_6704_:
{
lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6710_; 
v___x_6707_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6708_ = lean_array_push(v_fst_6703_, v___x_6707_);
if (v_isShared_6706_ == 0)
{
lean_ctor_set(v___x_6705_, 1, v___y_6667_);
lean_ctor_set(v___x_6705_, 0, v___x_6708_);
v___x_6710_ = v___x_6705_;
goto v_reusejp_6709_;
}
else
{
lean_object* v_reuseFailAlloc_6711_; 
v_reuseFailAlloc_6711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6711_, 0, v___x_6708_);
lean_ctor_set(v_reuseFailAlloc_6711_, 1, v___y_6667_);
v___x_6710_ = v_reuseFailAlloc_6711_;
goto v_reusejp_6709_;
}
v_reusejp_6709_:
{
return v___x_6710_;
}
}
}
}
else
{
lean_object* v_fst_6714_; lean_object* v___x_6716_; uint8_t v_isShared_6717_; uint8_t v_isSharedCheck_6721_; 
v_fst_6714_ = lean_ctor_get(v___x_6691_, 0);
v_isSharedCheck_6721_ = !lean_is_exclusive(v___x_6691_);
if (v_isSharedCheck_6721_ == 0)
{
lean_object* v_unused_6722_; 
v_unused_6722_ = lean_ctor_get(v___x_6691_, 1);
lean_dec(v_unused_6722_);
v___x_6716_ = v___x_6691_;
v_isShared_6717_ = v_isSharedCheck_6721_;
goto v_resetjp_6715_;
}
else
{
lean_inc(v_fst_6714_);
lean_dec(v___x_6691_);
v___x_6716_ = lean_box(0);
v_isShared_6717_ = v_isSharedCheck_6721_;
goto v_resetjp_6715_;
}
v_resetjp_6715_:
{
lean_object* v___x_6719_; 
if (v_isShared_6717_ == 0)
{
lean_ctor_set(v___x_6716_, 1, v___y_6667_);
v___x_6719_ = v___x_6716_;
goto v_reusejp_6718_;
}
else
{
lean_object* v_reuseFailAlloc_6720_; 
v_reuseFailAlloc_6720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6720_, 0, v_fst_6714_);
lean_ctor_set(v_reuseFailAlloc_6720_, 1, v___y_6667_);
v___x_6719_ = v_reuseFailAlloc_6720_;
goto v_reusejp_6718_;
}
v_reusejp_6718_:
{
return v___x_6719_;
}
}
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
lean_object* v___x_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; 
lean_dec(v___x_6675_);
lean_dec_ref(v_trailing_6665_);
v___x_6734_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6735_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6736_, 0, v_trailingTk_6664_);
lean_ctor_set(v___x_6736_, 1, v___x_6734_);
lean_ctor_set(v___x_6736_, 2, v___x_6735_);
v___x_6737_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6737_, 0, v___x_6736_);
v___x_6738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6738_, 0, v___x_6737_);
lean_ctor_set(v___x_6738_, 1, v___y_6667_);
return v___x_6738_;
}
v___jp_6668_:
{
lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; 
v___x_6669_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6670_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6671_, 0, v_trailingTk_6664_);
lean_ctor_set(v___x_6671_, 1, v___x_6669_);
lean_ctor_set(v___x_6671_, 2, v___x_6670_);
v___x_6672_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6672_, 0, v___x_6671_);
v___x_6673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6673_, 0, v___x_6672_);
lean_ctor_set(v___x_6673_, 1, v___y_6667_);
return v___x_6673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_atleastOneNewline_6739_, lean_object* v_trailingTk_6740_, lean_object* v_trailing_6741_, lean_object* v___y_6742_, lean_object* v___y_6743_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6744_; lean_object* v_res_6745_; 
v_atleastOneNewline_boxed_6744_ = lean_unbox(v_atleastOneNewline_6739_);
v_res_6745_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(v_atleastOneNewline_boxed_6744_, v_trailingTk_6740_, v_trailing_6741_, v___y_6742_, v___y_6743_);
lean_dec_ref(v___y_6742_);
return v_res_6745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object* v_stx_6746_, uint8_t v_atleastOneNewline_6747_, lean_object* v_a_6748_, lean_object* v_a_6749_){
_start:
{
lean_object* v___x_6750_; lean_object* v___f_6751_; lean_object* v___x_6752_; 
v___x_6750_ = lean_box(v_atleastOneNewline_6747_);
v___f_6751_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed), 5, 1);
lean_closure_set(v___f_6751_, 0, v___x_6750_);
v___x_6752_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_6746_, v___f_6751_, v_a_6748_, v_a_6749_);
return v___x_6752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6753_, lean_object* v_atleastOneNewline_6754_, lean_object* v_a_6755_, lean_object* v_a_6756_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6757_; lean_object* v_res_6758_; 
v_atleastOneNewline_boxed_6757_ = lean_unbox(v_atleastOneNewline_6754_);
v_res_6758_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_stx_6753_, v_atleastOneNewline_boxed_6757_, v_a_6755_, v_a_6756_);
lean_dec_ref(v_a_6755_);
return v_res_6758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object* v_upperBound_6759_, lean_object* v_stxs_6760_, lean_object* v_f_6761_, lean_object* v___x_6762_, lean_object* v_a_6763_, lean_object* v_b_6764_, lean_object* v___y_6765_, lean_object* v___y_6766_){
_start:
{
uint8_t v___x_6767_; 
v___x_6767_ = lean_nat_dec_lt(v_a_6763_, v_upperBound_6759_);
if (v___x_6767_ == 0)
{
lean_object* v___x_6768_; 
lean_dec(v_a_6763_);
lean_dec_ref(v_f_6761_);
v___x_6768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6768_, 0, v_b_6764_);
lean_ctor_set(v___x_6768_, 1, v___y_6766_);
return v___x_6768_;
}
else
{
lean_object* v___x_6769_; lean_object* v___x_6770_; 
v___x_6769_ = lean_array_fget_borrowed(v_stxs_6760_, v_a_6763_);
lean_inc_ref(v_f_6761_);
lean_inc_ref(v___y_6765_);
lean_inc(v___x_6769_);
v___x_6770_ = lean_apply_3(v_f_6761_, v___x_6769_, v___y_6765_, v___y_6766_);
if (lean_obj_tag(v___x_6770_) == 0)
{
lean_object* v_a_6771_; lean_object* v_a_6772_; lean_object* v___x_6773_; lean_object* v___y_6775_; lean_object* v___x_6800_; uint8_t v___x_6801_; 
v_a_6771_ = lean_ctor_get(v___x_6770_, 0);
lean_inc(v_a_6771_);
v_a_6772_ = lean_ctor_get(v___x_6770_, 1);
lean_inc(v_a_6772_);
lean_dec_ref_known(v___x_6770_, 2);
v___x_6773_ = lean_unsigned_to_nat(1u);
v___x_6800_ = lean_nat_sub(v___x_6762_, v___x_6773_);
v___x_6801_ = lean_nat_dec_lt(v_a_6763_, v___x_6800_);
lean_dec(v___x_6800_);
if (v___x_6801_ == 0)
{
lean_object* v___x_6802_; lean_object* v___x_6803_; 
v___x_6802_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_6803_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6764_, v_a_6771_, v___x_6802_, v___y_6765_, v_a_6772_);
v___y_6775_ = v___x_6803_;
goto v___jp_6774_;
}
else
{
lean_object* v___x_6804_; 
lean_inc(v___x_6769_);
v___x_6804_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_6769_, v___x_6801_, v___y_6765_, v_a_6772_);
if (lean_obj_tag(v___x_6804_) == 0)
{
lean_object* v_a_6805_; lean_object* v_a_6806_; lean_object* v___x_6807_; 
v_a_6805_ = lean_ctor_get(v___x_6804_, 0);
lean_inc(v_a_6805_);
v_a_6806_ = lean_ctor_get(v___x_6804_, 1);
lean_inc(v_a_6806_);
lean_dec_ref_known(v___x_6804_, 2);
v___x_6807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6764_, v_a_6771_, v_a_6805_, v___y_6765_, v_a_6806_);
v___y_6775_ = v___x_6807_;
goto v___jp_6774_;
}
else
{
lean_object* v_a_6808_; lean_object* v_a_6809_; lean_object* v___x_6811_; uint8_t v_isShared_6812_; uint8_t v_isSharedCheck_6816_; 
lean_dec(v_a_6771_);
lean_dec_ref(v_b_6764_);
lean_dec(v_a_6763_);
lean_dec_ref(v_f_6761_);
v_a_6808_ = lean_ctor_get(v___x_6804_, 0);
v_a_6809_ = lean_ctor_get(v___x_6804_, 1);
v_isSharedCheck_6816_ = !lean_is_exclusive(v___x_6804_);
if (v_isSharedCheck_6816_ == 0)
{
v___x_6811_ = v___x_6804_;
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
else
{
lean_inc(v_a_6809_);
lean_inc(v_a_6808_);
lean_dec(v___x_6804_);
v___x_6811_ = lean_box(0);
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
v_resetjp_6810_:
{
lean_object* v___x_6814_; 
if (v_isShared_6812_ == 0)
{
v___x_6814_ = v___x_6811_;
goto v_reusejp_6813_;
}
else
{
lean_object* v_reuseFailAlloc_6815_; 
v_reuseFailAlloc_6815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_a_6808_);
lean_ctor_set(v_reuseFailAlloc_6815_, 1, v_a_6809_);
v___x_6814_ = v_reuseFailAlloc_6815_;
goto v_reusejp_6813_;
}
v_reusejp_6813_:
{
return v___x_6814_;
}
}
}
}
v___jp_6774_:
{
if (lean_obj_tag(v___y_6775_) == 0)
{
lean_object* v_a_6776_; 
v_a_6776_ = lean_ctor_get(v___y_6775_, 0);
lean_inc(v_a_6776_);
if (lean_obj_tag(v_a_6776_) == 0)
{
lean_object* v_a_6777_; lean_object* v___x_6779_; uint8_t v_isShared_6780_; uint8_t v_isSharedCheck_6785_; 
lean_dec(v_a_6763_);
lean_dec_ref(v_f_6761_);
v_a_6777_ = lean_ctor_get(v___y_6775_, 1);
v_isSharedCheck_6785_ = !lean_is_exclusive(v___y_6775_);
if (v_isSharedCheck_6785_ == 0)
{
lean_object* v_unused_6786_; 
v_unused_6786_ = lean_ctor_get(v___y_6775_, 0);
lean_dec(v_unused_6786_);
v___x_6779_ = v___y_6775_;
v_isShared_6780_ = v_isSharedCheck_6785_;
goto v_resetjp_6778_;
}
else
{
lean_inc(v_a_6777_);
lean_dec(v___y_6775_);
v___x_6779_ = lean_box(0);
v_isShared_6780_ = v_isSharedCheck_6785_;
goto v_resetjp_6778_;
}
v_resetjp_6778_:
{
lean_object* v_a_6781_; lean_object* v___x_6783_; 
v_a_6781_ = lean_ctor_get(v_a_6776_, 0);
lean_inc(v_a_6781_);
lean_dec_ref_known(v_a_6776_, 1);
if (v_isShared_6780_ == 0)
{
lean_ctor_set(v___x_6779_, 0, v_a_6781_);
v___x_6783_ = v___x_6779_;
goto v_reusejp_6782_;
}
else
{
lean_object* v_reuseFailAlloc_6784_; 
v_reuseFailAlloc_6784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_a_6781_);
lean_ctor_set(v_reuseFailAlloc_6784_, 1, v_a_6777_);
v___x_6783_ = v_reuseFailAlloc_6784_;
goto v_reusejp_6782_;
}
v_reusejp_6782_:
{
return v___x_6783_;
}
}
}
else
{
lean_object* v_a_6787_; lean_object* v_a_6788_; lean_object* v___x_6789_; 
v_a_6787_ = lean_ctor_get(v___y_6775_, 1);
lean_inc(v_a_6787_);
lean_dec_ref_known(v___y_6775_, 2);
v_a_6788_ = lean_ctor_get(v_a_6776_, 0);
lean_inc(v_a_6788_);
lean_dec_ref_known(v_a_6776_, 1);
v___x_6789_ = lean_nat_add(v_a_6763_, v___x_6773_);
lean_dec(v_a_6763_);
v_a_6763_ = v___x_6789_;
v_b_6764_ = v_a_6788_;
v___y_6766_ = v_a_6787_;
goto _start;
}
}
else
{
lean_object* v_a_6791_; lean_object* v_a_6792_; lean_object* v___x_6794_; uint8_t v_isShared_6795_; uint8_t v_isSharedCheck_6799_; 
lean_dec(v_a_6763_);
lean_dec_ref(v_f_6761_);
v_a_6791_ = lean_ctor_get(v___y_6775_, 0);
v_a_6792_ = lean_ctor_get(v___y_6775_, 1);
v_isSharedCheck_6799_ = !lean_is_exclusive(v___y_6775_);
if (v_isSharedCheck_6799_ == 0)
{
v___x_6794_ = v___y_6775_;
v_isShared_6795_ = v_isSharedCheck_6799_;
goto v_resetjp_6793_;
}
else
{
lean_inc(v_a_6792_);
lean_inc(v_a_6791_);
lean_dec(v___y_6775_);
v___x_6794_ = lean_box(0);
v_isShared_6795_ = v_isSharedCheck_6799_;
goto v_resetjp_6793_;
}
v_resetjp_6793_:
{
lean_object* v___x_6797_; 
if (v_isShared_6795_ == 0)
{
v___x_6797_ = v___x_6794_;
goto v_reusejp_6796_;
}
else
{
lean_object* v_reuseFailAlloc_6798_; 
v_reuseFailAlloc_6798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6798_, 0, v_a_6791_);
lean_ctor_set(v_reuseFailAlloc_6798_, 1, v_a_6792_);
v___x_6797_ = v_reuseFailAlloc_6798_;
goto v_reusejp_6796_;
}
v_reusejp_6796_:
{
return v___x_6797_;
}
}
}
}
}
else
{
lean_object* v_a_6817_; lean_object* v_a_6818_; lean_object* v___x_6820_; uint8_t v_isShared_6821_; uint8_t v_isSharedCheck_6825_; 
lean_dec_ref(v_b_6764_);
lean_dec(v_a_6763_);
lean_dec_ref(v_f_6761_);
v_a_6817_ = lean_ctor_get(v___x_6770_, 0);
v_a_6818_ = lean_ctor_get(v___x_6770_, 1);
v_isSharedCheck_6825_ = !lean_is_exclusive(v___x_6770_);
if (v_isSharedCheck_6825_ == 0)
{
v___x_6820_ = v___x_6770_;
v_isShared_6821_ = v_isSharedCheck_6825_;
goto v_resetjp_6819_;
}
else
{
lean_inc(v_a_6818_);
lean_inc(v_a_6817_);
lean_dec(v___x_6770_);
v___x_6820_ = lean_box(0);
v_isShared_6821_ = v_isSharedCheck_6825_;
goto v_resetjp_6819_;
}
v_resetjp_6819_:
{
lean_object* v___x_6823_; 
if (v_isShared_6821_ == 0)
{
v___x_6823_ = v___x_6820_;
goto v_reusejp_6822_;
}
else
{
lean_object* v_reuseFailAlloc_6824_; 
v_reuseFailAlloc_6824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6824_, 0, v_a_6817_);
lean_ctor_set(v_reuseFailAlloc_6824_, 1, v_a_6818_);
v___x_6823_ = v_reuseFailAlloc_6824_;
goto v_reusejp_6822_;
}
v_reusejp_6822_:
{
return v___x_6823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object* v_upperBound_6826_, lean_object* v_stxs_6827_, lean_object* v_f_6828_, lean_object* v___x_6829_, lean_object* v_a_6830_, lean_object* v_b_6831_, lean_object* v___y_6832_, lean_object* v___y_6833_){
_start:
{
lean_object* v_res_6834_; 
v_res_6834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6826_, v_stxs_6827_, v_f_6828_, v___x_6829_, v_a_6830_, v_b_6831_, v___y_6832_, v___y_6833_);
lean_dec_ref(v___y_6832_);
lean_dec(v___x_6829_);
lean_dec_ref(v_stxs_6827_);
lean_dec(v_upperBound_6826_);
return v_res_6834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object* v_f_6835_, lean_object* v_stxs_6836_, lean_object* v_a_6837_, lean_object* v_a_6838_){
_start:
{
lean_object* v___x_6839_; lean_object* v___x_6840_; uint8_t v___x_6841_; 
v___x_6839_ = lean_array_get_size(v_stxs_6836_);
v___x_6840_ = lean_unsigned_to_nat(1u);
v___x_6841_ = lean_nat_dec_eq(v___x_6839_, v___x_6840_);
if (v___x_6841_ == 0)
{
lean_object* v___x_6842_; lean_object* v_acc_6843_; lean_object* v___x_6844_; 
v___x_6842_ = lean_unsigned_to_nat(0u);
v_acc_6843_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_6844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v___x_6839_, v_stxs_6836_, v_f_6835_, v___x_6839_, v___x_6842_, v_acc_6843_, v_a_6837_, v_a_6838_);
if (lean_obj_tag(v___x_6844_) == 0)
{
lean_object* v_a_6845_; lean_object* v_a_6846_; lean_object* v___x_6848_; uint8_t v_isShared_6849_; uint8_t v_isSharedCheck_6854_; 
v_a_6845_ = lean_ctor_get(v___x_6844_, 0);
v_a_6846_ = lean_ctor_get(v___x_6844_, 1);
v_isSharedCheck_6854_ = !lean_is_exclusive(v___x_6844_);
if (v_isSharedCheck_6854_ == 0)
{
v___x_6848_ = v___x_6844_;
v_isShared_6849_ = v_isSharedCheck_6854_;
goto v_resetjp_6847_;
}
else
{
lean_inc(v_a_6846_);
lean_inc(v_a_6845_);
lean_dec(v___x_6844_);
v___x_6848_ = lean_box(0);
v_isShared_6849_ = v_isSharedCheck_6854_;
goto v_resetjp_6847_;
}
v_resetjp_6847_:
{
lean_object* v___x_6850_; lean_object* v___x_6852_; 
v___x_6850_ = l_Lean_Fmt_TaggedDoc_join(v_a_6845_);
if (v_isShared_6849_ == 0)
{
lean_ctor_set(v___x_6848_, 0, v___x_6850_);
v___x_6852_ = v___x_6848_;
goto v_reusejp_6851_;
}
else
{
lean_object* v_reuseFailAlloc_6853_; 
v_reuseFailAlloc_6853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6853_, 0, v___x_6850_);
lean_ctor_set(v_reuseFailAlloc_6853_, 1, v_a_6846_);
v___x_6852_ = v_reuseFailAlloc_6853_;
goto v_reusejp_6851_;
}
v_reusejp_6851_:
{
return v___x_6852_;
}
}
}
else
{
lean_object* v_a_6855_; lean_object* v_a_6856_; lean_object* v___x_6858_; uint8_t v_isShared_6859_; uint8_t v_isSharedCheck_6863_; 
v_a_6855_ = lean_ctor_get(v___x_6844_, 0);
v_a_6856_ = lean_ctor_get(v___x_6844_, 1);
v_isSharedCheck_6863_ = !lean_is_exclusive(v___x_6844_);
if (v_isSharedCheck_6863_ == 0)
{
v___x_6858_ = v___x_6844_;
v_isShared_6859_ = v_isSharedCheck_6863_;
goto v_resetjp_6857_;
}
else
{
lean_inc(v_a_6856_);
lean_inc(v_a_6855_);
lean_dec(v___x_6844_);
v___x_6858_ = lean_box(0);
v_isShared_6859_ = v_isSharedCheck_6863_;
goto v_resetjp_6857_;
}
v_resetjp_6857_:
{
lean_object* v___x_6861_; 
if (v_isShared_6859_ == 0)
{
v___x_6861_ = v___x_6858_;
goto v_reusejp_6860_;
}
else
{
lean_object* v_reuseFailAlloc_6862_; 
v_reuseFailAlloc_6862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6862_, 0, v_a_6855_);
lean_ctor_set(v_reuseFailAlloc_6862_, 1, v_a_6856_);
v___x_6861_ = v_reuseFailAlloc_6862_;
goto v_reusejp_6860_;
}
v_reusejp_6860_:
{
return v___x_6861_;
}
}
}
}
else
{
lean_object* v___x_6864_; lean_object* v___x_6865_; lean_object* v___x_6866_; lean_object* v___x_6867_; 
v___x_6864_ = lean_box(0);
v___x_6865_ = lean_unsigned_to_nat(0u);
v___x_6866_ = lean_array_get_borrowed(v___x_6864_, v_stxs_6836_, v___x_6865_);
lean_inc_ref(v_a_6837_);
lean_inc(v___x_6866_);
v___x_6867_ = lean_apply_3(v_f_6835_, v___x_6866_, v_a_6837_, v_a_6838_);
return v___x_6867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object* v_f_6868_, lean_object* v_stxs_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_){
_start:
{
lean_object* v_res_6872_; 
v_res_6872_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v_f_6868_, v_stxs_6869_, v_a_6870_, v_a_6871_);
lean_dec_ref(v_a_6870_);
lean_dec_ref(v_stxs_6869_);
return v_res_6872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object* v_upperBound_6873_, lean_object* v_stxs_6874_, lean_object* v_f_6875_, lean_object* v___x_6876_, lean_object* v_inst_6877_, lean_object* v_R_6878_, lean_object* v_a_6879_, lean_object* v_b_6880_, lean_object* v_c_6881_, lean_object* v___y_6882_, lean_object* v___y_6883_){
_start:
{
lean_object* v___x_6884_; 
v___x_6884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6873_, v_stxs_6874_, v_f_6875_, v___x_6876_, v_a_6879_, v_b_6880_, v___y_6882_, v___y_6883_);
return v___x_6884_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object* v_upperBound_6885_, lean_object* v_stxs_6886_, lean_object* v_f_6887_, lean_object* v___x_6888_, lean_object* v_inst_6889_, lean_object* v_R_6890_, lean_object* v_a_6891_, lean_object* v_b_6892_, lean_object* v_c_6893_, lean_object* v___y_6894_, lean_object* v___y_6895_){
_start:
{
lean_object* v_res_6896_; 
v_res_6896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(v_upperBound_6885_, v_stxs_6886_, v_f_6887_, v___x_6888_, v_inst_6889_, v_R_6890_, v_a_6891_, v_b_6892_, v_c_6893_, v___y_6894_, v___y_6895_);
lean_dec_ref(v___y_6894_);
lean_dec(v___x_6888_);
lean_dec_ref(v_stxs_6886_);
lean_dec(v_upperBound_6885_);
return v_res_6896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_stxs_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_){
_start:
{
lean_object* v___x_6900_; lean_object* v___x_6901_; 
v___x_6900_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 0);
v___x_6901_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v___x_6900_, v_stxs_6897_, v_a_6898_, v_a_6899_);
return v___x_6901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_stxs_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_){
_start:
{
lean_object* v_res_6905_; 
v_res_6905_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_stxs_6902_, v_a_6903_, v_a_6904_);
lean_dec_ref(v_a_6903_);
lean_dec_ref(v_stxs_6902_);
return v_res_6905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(lean_object* v_x_6906_){
_start:
{
lean_object* v___x_6907_; 
v___x_6907_ = lean_obj_tag_nat(v_x_6906_);
return v___x_6907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg___boxed(lean_object* v_x_6908_){
_start:
{
lean_object* v_res_6909_; 
v_res_6909_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(v_x_6908_);
lean_dec_ref(v_x_6908_);
return v_res_6909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl(lean_object* v_sep_6910_, lean_object* v_x_6911_){
_start:
{
lean_object* v___x_6912_; 
v___x_6912_ = lean_obj_tag_nat(v_x_6911_);
return v___x_6912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___boxed(lean_object* v_sep_6913_, lean_object* v_x_6914_){
_start:
{
lean_object* v_res_6915_; 
v_res_6915_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl(v_sep_6913_, v_x_6914_);
lean_dec_ref(v_x_6914_);
lean_dec_ref(v_sep_6913_);
return v_res_6915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object* v_t_6916_, lean_object* v_k_6917_){
_start:
{
lean_object* v_g_6918_; lean_object* v___x_6919_; 
v_g_6918_ = lean_ctor_get(v_t_6916_, 0);
lean_inc_ref(v_g_6918_);
lean_dec_ref(v_t_6916_);
v___x_6919_ = lean_apply_1(v_k_6917_, v_g_6918_);
return v___x_6919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim(lean_object* v_sep_6920_, lean_object* v_motive_6921_, lean_object* v_ctorIdx_6922_, lean_object* v_t_6923_, lean_object* v_h_6924_, lean_object* v_k_6925_){
_start:
{
lean_object* v___x_6926_; 
v___x_6926_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6923_, v_k_6925_);
return v___x_6926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object* v_sep_6927_, lean_object* v_motive_6928_, lean_object* v_ctorIdx_6929_, lean_object* v_t_6930_, lean_object* v_h_6931_, lean_object* v_k_6932_){
_start:
{
lean_object* v_res_6933_; 
v_res_6933_ = l_Lean_Fmt_TrailingGroup_ctorElim(v_sep_6927_, v_motive_6928_, v_ctorIdx_6929_, v_t_6930_, v_h_6931_, v_k_6932_);
lean_dec(v_ctorIdx_6929_);
lean_dec_ref(v_sep_6927_);
return v_res_6933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object* v_t_6934_, lean_object* v_group_6935_){
_start:
{
lean_object* v___x_6936_; 
v___x_6936_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6934_, v_group_6935_);
return v___x_6936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim(lean_object* v_sep_6937_, lean_object* v_motive_6938_, lean_object* v_t_6939_, lean_object* v_h_6940_, lean_object* v_group_6941_){
_start:
{
lean_object* v___x_6942_; 
v___x_6942_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6939_, v_group_6941_);
return v___x_6942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object* v_sep_6943_, lean_object* v_motive_6944_, lean_object* v_t_6945_, lean_object* v_h_6946_, lean_object* v_group_6947_){
_start:
{
lean_object* v_res_6948_; 
v_res_6948_ = l_Lean_Fmt_TrailingGroup_group_elim(v_sep_6943_, v_motive_6944_, v_t_6945_, v_h_6946_, v_group_6947_);
lean_dec_ref(v_sep_6943_);
return v_res_6948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object* v_t_6949_, lean_object* v_trailing_6950_){
_start:
{
lean_object* v___x_6951_; 
v___x_6951_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6949_, v_trailing_6950_);
return v___x_6951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim(lean_object* v_sep_6952_, lean_object* v_motive_6953_, lean_object* v_t_6954_, lean_object* v_h_6955_, lean_object* v_trailing_6956_){
_start:
{
lean_object* v___x_6957_; 
v___x_6957_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6954_, v_trailing_6956_);
return v___x_6957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object* v_sep_6958_, lean_object* v_motive_6959_, lean_object* v_t_6960_, lean_object* v_h_6961_, lean_object* v_trailing_6962_){
_start:
{
lean_object* v_res_6963_; 
v_res_6963_ = l_Lean_Fmt_TrailingGroup_trailing_elim(v_sep_6958_, v_motive_6959_, v_t_6960_, v_h_6961_, v_trailing_6962_);
lean_dec_ref(v_sep_6958_);
return v_res_6963_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_6964_; lean_object* v___x_6965_; 
v___x_6964_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_6965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6965_, 0, v___x_6964_);
return v___x_6965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg(){
_start:
{
lean_object* v___x_6967_; 
v___x_6967_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0);
return v___x_6967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___boxed(lean_object* v___dummy_6968_){
_start:
{
lean_object* v_res_6969_; 
v_res_6969_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v_res_6969_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0(void){
_start:
{
lean_object* v___x_6970_; 
v___x_6970_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v___x_6970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object* v_sep_6971_){
_start:
{
lean_object* v___x_6972_; 
v___x_6972_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object* v_sep_6973_){
_start:
{
lean_object* v_res_6974_; 
v_res_6974_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6973_);
lean_dec_ref(v_sep_6973_);
return v_res_6974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg(){
_start:
{
lean_object* v___x_6976_; 
v___x_6976_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg___boxed(lean_object* v___dummy_6977_){
_start:
{
lean_object* v_res_6978_; 
v_res_6978_ = l_Lean_Fmt_instInhabitedTrailingGroup___redArg();
return v_res_6978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup(lean_object* v_a_6979_){
_start:
{
lean_object* v___x_6980_; 
v___x_6980_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object* v_a_6981_){
_start:
{
lean_object* v_res_6982_; 
v_res_6982_ = l_Lean_Fmt_instInhabitedTrailingGroup(v_a_6981_);
lean_dec_ref(v_a_6981_);
return v_res_6982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object* v_upperBound_6983_, lean_object* v_elemsAndSeps_6984_, lean_object* v_pendingGroup_6985_, lean_object* v___x_6986_, lean_object* v_a_6987_, lean_object* v_b_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_){
_start:
{
lean_object* v_a_6992_; lean_object* v_a_6993_; uint8_t v___x_6997_; 
v___x_6997_ = lean_nat_dec_lt(v_a_6987_, v_upperBound_6983_);
if (v___x_6997_ == 0)
{
lean_object* v___x_6998_; 
lean_dec(v_a_6987_);
lean_dec_ref(v_pendingGroup_6985_);
v___x_6998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6998_, 0, v_b_6988_);
lean_ctor_set(v___x_6998_, 1, v___y_6990_);
return v___x_6998_;
}
else
{
lean_object* v___x_6999_; lean_object* v___x_7000_; 
v___x_6999_ = lean_array_fget_borrowed(v_elemsAndSeps_6984_, v_a_6987_);
lean_inc(v___x_6999_);
v___x_7000_ = l_Lean_Fmt_fmt(v___x_6999_, v___y_6989_, v___y_6990_);
if (lean_obj_tag(v___x_7000_) == 0)
{
lean_object* v_a_7001_; lean_object* v_a_7002_; lean_object* v_fst_7003_; lean_object* v_snd_7004_; lean_object* v___x_7006_; uint8_t v_isShared_7007_; uint8_t v_isSharedCheck_7051_; 
v_a_7001_ = lean_ctor_get(v___x_7000_, 0);
lean_inc(v_a_7001_);
v_a_7002_ = lean_ctor_get(v___x_7000_, 1);
lean_inc(v_a_7002_);
lean_dec_ref_known(v___x_7000_, 2);
v_fst_7003_ = lean_ctor_get(v_b_6988_, 0);
v_snd_7004_ = lean_ctor_get(v_b_6988_, 1);
v_isSharedCheck_7051_ = !lean_is_exclusive(v_b_6988_);
if (v_isSharedCheck_7051_ == 0)
{
v___x_7006_ = v_b_6988_;
v_isShared_7007_ = v_isSharedCheck_7051_;
goto v_resetjp_7005_;
}
else
{
lean_inc(v_snd_7004_);
lean_inc(v_fst_7003_);
lean_dec(v_b_6988_);
v___x_7006_ = lean_box(0);
v_isShared_7007_ = v_isSharedCheck_7051_;
goto v_resetjp_7005_;
}
v_resetjp_7005_:
{
lean_object* v___x_7008_; lean_object* v___x_7009_; lean_object* v___x_7010_; lean_object* v___y_7012_; uint8_t v___y_7040_; lean_object* v___x_7047_; lean_object* v___x_7048_; uint8_t v___x_7049_; 
v___x_7008_ = lean_unsigned_to_nat(0u);
v___x_7009_ = lean_box(0);
v___x_7010_ = lean_array_push(v_snd_7004_, v_a_7001_);
v___x_7047_ = lean_unsigned_to_nat(2u);
v___x_7048_ = lean_nat_mod(v_a_6987_, v___x_7047_);
v___x_7049_ = lean_nat_dec_eq(v___x_7048_, v___x_7008_);
lean_dec(v___x_7048_);
if (v___x_7049_ == 0)
{
v___y_7040_ = v___x_6997_;
goto v___jp_7039_;
}
else
{
uint8_t v___x_7050_; 
v___x_7050_ = 0;
v___y_7040_ = v___x_7050_;
goto v___jp_7039_;
}
v___jp_7011_:
{
uint8_t v___x_7013_; lean_object* v___x_7014_; 
v___x_7013_ = 0;
v___x_7014_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___y_7012_, v___x_7013_, v___y_6989_, v_a_7002_);
if (lean_obj_tag(v___x_7014_) == 0)
{
lean_object* v_a_7015_; lean_object* v_a_7016_; uint8_t v___x_7017_; 
v_a_7015_ = lean_ctor_get(v___x_7014_, 0);
lean_inc(v_a_7015_);
v_a_7016_ = lean_ctor_get(v___x_7014_, 1);
lean_inc(v_a_7016_);
lean_dec_ref_known(v___x_7014_, 2);
v___x_7017_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_7015_);
if (v___x_7017_ == 0)
{
lean_object* v___x_7018_; lean_object* v___x_7019_; lean_object* v___x_7020_; lean_object* v___x_7021_; lean_object* v___x_7023_; 
v___x_7018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7018_, 0, v___x_7010_);
v___x_7019_ = lean_array_push(v_fst_7003_, v___x_7018_);
v___x_7020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7020_, 0, v_a_7015_);
v___x_7021_ = lean_array_push(v___x_7019_, v___x_7020_);
lean_inc_ref(v_pendingGroup_6985_);
if (v_isShared_7007_ == 0)
{
lean_ctor_set(v___x_7006_, 1, v_pendingGroup_6985_);
lean_ctor_set(v___x_7006_, 0, v___x_7021_);
v___x_7023_ = v___x_7006_;
goto v_reusejp_7022_;
}
else
{
lean_object* v_reuseFailAlloc_7024_; 
v_reuseFailAlloc_7024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7024_, 0, v___x_7021_);
lean_ctor_set(v_reuseFailAlloc_7024_, 1, v_pendingGroup_6985_);
v___x_7023_ = v_reuseFailAlloc_7024_;
goto v_reusejp_7022_;
}
v_reusejp_7022_:
{
v_a_6992_ = v___x_7023_;
v_a_6993_ = v_a_7016_;
goto v___jp_6991_;
}
}
else
{
lean_object* v___x_7026_; 
lean_dec(v_a_7015_);
if (v_isShared_7007_ == 0)
{
lean_ctor_set(v___x_7006_, 1, v___x_7010_);
v___x_7026_ = v___x_7006_;
goto v_reusejp_7025_;
}
else
{
lean_object* v_reuseFailAlloc_7027_; 
v_reuseFailAlloc_7027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7027_, 0, v_fst_7003_);
lean_ctor_set(v_reuseFailAlloc_7027_, 1, v___x_7010_);
v___x_7026_ = v_reuseFailAlloc_7027_;
goto v_reusejp_7025_;
}
v_reusejp_7025_:
{
v_a_6992_ = v___x_7026_;
v_a_6993_ = v_a_7016_;
goto v___jp_6991_;
}
}
}
else
{
lean_object* v_a_7028_; lean_object* v_a_7029_; lean_object* v___x_7031_; uint8_t v_isShared_7032_; uint8_t v_isSharedCheck_7036_; 
lean_dec_ref(v___x_7010_);
lean_del_object(v___x_7006_);
lean_dec(v_fst_7003_);
lean_dec(v_a_6987_);
lean_dec_ref(v_pendingGroup_6985_);
v_a_7028_ = lean_ctor_get(v___x_7014_, 0);
v_a_7029_ = lean_ctor_get(v___x_7014_, 1);
v_isSharedCheck_7036_ = !lean_is_exclusive(v___x_7014_);
if (v_isSharedCheck_7036_ == 0)
{
v___x_7031_ = v___x_7014_;
v_isShared_7032_ = v_isSharedCheck_7036_;
goto v_resetjp_7030_;
}
else
{
lean_inc(v_a_7029_);
lean_inc(v_a_7028_);
lean_dec(v___x_7014_);
v___x_7031_ = lean_box(0);
v_isShared_7032_ = v_isSharedCheck_7036_;
goto v_resetjp_7030_;
}
v_resetjp_7030_:
{
lean_object* v___x_7034_; 
if (v_isShared_7032_ == 0)
{
v___x_7034_ = v___x_7031_;
goto v_reusejp_7033_;
}
else
{
lean_object* v_reuseFailAlloc_7035_; 
v_reuseFailAlloc_7035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7035_, 0, v_a_7028_);
lean_ctor_set(v_reuseFailAlloc_7035_, 1, v_a_7029_);
v___x_7034_ = v_reuseFailAlloc_7035_;
goto v_reusejp_7033_;
}
v_reusejp_7033_:
{
return v___x_7034_;
}
}
}
}
v___jp_7037_:
{
lean_object* v___x_7038_; 
v___x_7038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7038_, 0, v_fst_7003_);
lean_ctor_set(v___x_7038_, 1, v___x_7010_);
v_a_6992_ = v___x_7038_;
v_a_6993_ = v_a_7002_;
goto v___jp_6991_;
}
v___jp_7039_:
{
lean_object* v___x_7041_; lean_object* v___x_7042_; uint8_t v___x_7043_; 
v___x_7041_ = lean_unsigned_to_nat(1u);
v___x_7042_ = lean_nat_sub(v___x_6986_, v___x_7041_);
v___x_7043_ = lean_nat_dec_lt(v_a_6987_, v___x_7042_);
lean_dec(v___x_7042_);
if (v___x_7043_ == 0)
{
lean_del_object(v___x_7006_);
goto v___jp_7037_;
}
else
{
if (v___y_7040_ == 0)
{
lean_del_object(v___x_7006_);
goto v___jp_7037_;
}
else
{
uint8_t v___x_7044_; 
lean_inc(v___x_6999_);
v___x_7044_ = l_Lean_Syntax_matchesNull(v___x_6999_, v___x_7008_);
if (v___x_7044_ == 0)
{
lean_inc(v___x_6999_);
v___y_7012_ = v___x_6999_;
goto v___jp_7011_;
}
else
{
lean_object* v___x_7045_; lean_object* v___x_7046_; 
v___x_7045_ = lean_nat_sub(v_a_6987_, v___x_7041_);
v___x_7046_ = lean_array_get_borrowed(v___x_7009_, v_elemsAndSeps_6984_, v___x_7045_);
lean_dec(v___x_7045_);
lean_inc(v___x_7046_);
v___y_7012_ = v___x_7046_;
goto v___jp_7011_;
}
}
}
}
}
}
else
{
lean_object* v_a_7052_; lean_object* v_a_7053_; lean_object* v___x_7055_; uint8_t v_isShared_7056_; uint8_t v_isSharedCheck_7060_; 
lean_dec_ref(v_b_6988_);
lean_dec(v_a_6987_);
lean_dec_ref(v_pendingGroup_6985_);
v_a_7052_ = lean_ctor_get(v___x_7000_, 0);
v_a_7053_ = lean_ctor_get(v___x_7000_, 1);
v_isSharedCheck_7060_ = !lean_is_exclusive(v___x_7000_);
if (v_isSharedCheck_7060_ == 0)
{
v___x_7055_ = v___x_7000_;
v_isShared_7056_ = v_isSharedCheck_7060_;
goto v_resetjp_7054_;
}
else
{
lean_inc(v_a_7053_);
lean_inc(v_a_7052_);
lean_dec(v___x_7000_);
v___x_7055_ = lean_box(0);
v_isShared_7056_ = v_isSharedCheck_7060_;
goto v_resetjp_7054_;
}
v_resetjp_7054_:
{
lean_object* v___x_7058_; 
if (v_isShared_7056_ == 0)
{
v___x_7058_ = v___x_7055_;
goto v_reusejp_7057_;
}
else
{
lean_object* v_reuseFailAlloc_7059_; 
v_reuseFailAlloc_7059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7059_, 0, v_a_7052_);
lean_ctor_set(v_reuseFailAlloc_7059_, 1, v_a_7053_);
v___x_7058_ = v_reuseFailAlloc_7059_;
goto v_reusejp_7057_;
}
v_reusejp_7057_:
{
return v___x_7058_;
}
}
}
}
v___jp_6991_:
{
lean_object* v___x_6994_; lean_object* v___x_6995_; 
v___x_6994_ = lean_unsigned_to_nat(1u);
v___x_6995_ = lean_nat_add(v_a_6987_, v___x_6994_);
lean_dec(v_a_6987_);
v_a_6987_ = v___x_6995_;
v_b_6988_ = v_a_6992_;
v___y_6990_ = v_a_6993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object* v_upperBound_7061_, lean_object* v_elemsAndSeps_7062_, lean_object* v_pendingGroup_7063_, lean_object* v___x_7064_, lean_object* v_a_7065_, lean_object* v_b_7066_, lean_object* v___y_7067_, lean_object* v___y_7068_){
_start:
{
lean_object* v_res_7069_; 
v_res_7069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7061_, v_elemsAndSeps_7062_, v_pendingGroup_7063_, v___x_7064_, v_a_7065_, v_b_7066_, v___y_7067_, v___y_7068_);
lean_dec_ref(v___y_7067_);
lean_dec(v___x_7064_);
lean_dec_ref(v_elemsAndSeps_7062_);
lean_dec(v_upperBound_7061_);
return v_res_7069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object* v_sep_7074_, lean_object* v_stxs_7075_, lean_object* v_a_7076_, lean_object* v_a_7077_){
_start:
{
lean_object* v___x_7078_; lean_object* v___x_7079_; lean_object* v_acc_7080_; lean_object* v___x_7081_; lean_object* v___x_7082_; 
v___x_7078_ = lean_unsigned_to_nat(0u);
v___x_7079_ = lean_array_get_size(v_stxs_7075_);
v_acc_7080_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0));
v___x_7081_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1));
v___x_7082_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v___x_7079_, v_stxs_7075_, v_acc_7080_, v___x_7079_, v___x_7078_, v___x_7081_, v_a_7076_, v_a_7077_);
if (lean_obj_tag(v___x_7082_) == 0)
{
lean_object* v_a_7083_; lean_object* v_a_7084_; lean_object* v___x_7086_; uint8_t v_isShared_7087_; uint8_t v_isSharedCheck_7100_; 
v_a_7083_ = lean_ctor_get(v___x_7082_, 0);
v_a_7084_ = lean_ctor_get(v___x_7082_, 1);
v_isSharedCheck_7100_ = !lean_is_exclusive(v___x_7082_);
if (v_isSharedCheck_7100_ == 0)
{
v___x_7086_ = v___x_7082_;
v_isShared_7087_ = v_isSharedCheck_7100_;
goto v_resetjp_7085_;
}
else
{
lean_inc(v_a_7084_);
lean_inc(v_a_7083_);
lean_dec(v___x_7082_);
v___x_7086_ = lean_box(0);
v_isShared_7087_ = v_isSharedCheck_7100_;
goto v_resetjp_7085_;
}
v_resetjp_7085_:
{
lean_object* v_fst_7088_; lean_object* v_snd_7089_; lean_object* v___x_7090_; uint8_t v___x_7091_; 
v_fst_7088_ = lean_ctor_get(v_a_7083_, 0);
lean_inc(v_fst_7088_);
v_snd_7089_ = lean_ctor_get(v_a_7083_, 1);
lean_inc(v_snd_7089_);
lean_dec(v_a_7083_);
v___x_7090_ = lean_array_get_size(v_snd_7089_);
v___x_7091_ = lean_nat_dec_eq(v___x_7090_, v___x_7078_);
if (v___x_7091_ == 0)
{
lean_object* v___x_7092_; lean_object* v___x_7093_; lean_object* v___x_7095_; 
v___x_7092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7092_, 0, v_snd_7089_);
v___x_7093_ = lean_array_push(v_fst_7088_, v___x_7092_);
if (v_isShared_7087_ == 0)
{
lean_ctor_set(v___x_7086_, 0, v___x_7093_);
v___x_7095_ = v___x_7086_;
goto v_reusejp_7094_;
}
else
{
lean_object* v_reuseFailAlloc_7096_; 
v_reuseFailAlloc_7096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7096_, 0, v___x_7093_);
lean_ctor_set(v_reuseFailAlloc_7096_, 1, v_a_7084_);
v___x_7095_ = v_reuseFailAlloc_7096_;
goto v_reusejp_7094_;
}
v_reusejp_7094_:
{
return v___x_7095_;
}
}
else
{
lean_object* v___x_7098_; 
lean_dec(v_snd_7089_);
if (v_isShared_7087_ == 0)
{
lean_ctor_set(v___x_7086_, 0, v_fst_7088_);
v___x_7098_ = v___x_7086_;
goto v_reusejp_7097_;
}
else
{
lean_object* v_reuseFailAlloc_7099_; 
v_reuseFailAlloc_7099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7099_, 0, v_fst_7088_);
lean_ctor_set(v_reuseFailAlloc_7099_, 1, v_a_7084_);
v___x_7098_ = v_reuseFailAlloc_7099_;
goto v_reusejp_7097_;
}
v_reusejp_7097_:
{
return v___x_7098_;
}
}
}
}
else
{
lean_object* v_a_7101_; lean_object* v_a_7102_; lean_object* v___x_7104_; uint8_t v_isShared_7105_; uint8_t v_isSharedCheck_7109_; 
v_a_7101_ = lean_ctor_get(v___x_7082_, 0);
v_a_7102_ = lean_ctor_get(v___x_7082_, 1);
v_isSharedCheck_7109_ = !lean_is_exclusive(v___x_7082_);
if (v_isSharedCheck_7109_ == 0)
{
v___x_7104_ = v___x_7082_;
v_isShared_7105_ = v_isSharedCheck_7109_;
goto v_resetjp_7103_;
}
else
{
lean_inc(v_a_7102_);
lean_inc(v_a_7101_);
lean_dec(v___x_7082_);
v___x_7104_ = lean_box(0);
v_isShared_7105_ = v_isSharedCheck_7109_;
goto v_resetjp_7103_;
}
v_resetjp_7103_:
{
lean_object* v___x_7107_; 
if (v_isShared_7105_ == 0)
{
v___x_7107_ = v___x_7104_;
goto v_reusejp_7106_;
}
else
{
lean_object* v_reuseFailAlloc_7108_; 
v_reuseFailAlloc_7108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7108_, 0, v_a_7101_);
lean_ctor_set(v_reuseFailAlloc_7108_, 1, v_a_7102_);
v___x_7107_ = v_reuseFailAlloc_7108_;
goto v_reusejp_7106_;
}
v_reusejp_7106_:
{
return v___x_7107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object* v_sep_7110_, lean_object* v_stxs_7111_, lean_object* v_a_7112_, lean_object* v_a_7113_){
_start:
{
lean_object* v_res_7114_; 
v_res_7114_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7110_, v_stxs_7111_, v_a_7112_, v_a_7113_);
lean_dec_ref(v_a_7112_);
lean_dec_ref(v_stxs_7111_);
lean_dec_ref(v_sep_7110_);
return v_res_7114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object* v_ks_7115_, lean_object* v_sep_7116_, lean_object* v_stxs_7117_, lean_object* v_a_7118_, lean_object* v_a_7119_){
_start:
{
lean_object* v___x_7120_; 
v___x_7120_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7116_, v_stxs_7117_, v_a_7118_, v_a_7119_);
return v___x_7120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object* v_ks_7121_, lean_object* v_sep_7122_, lean_object* v_stxs_7123_, lean_object* v_a_7124_, lean_object* v_a_7125_){
_start:
{
lean_object* v_res_7126_; 
v_res_7126_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups(v_ks_7121_, v_sep_7122_, v_stxs_7123_, v_a_7124_, v_a_7125_);
lean_dec_ref(v_a_7124_);
lean_dec_ref(v_stxs_7123_);
lean_dec_ref(v_sep_7122_);
lean_dec(v_ks_7121_);
return v_res_7126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object* v_upperBound_7127_, lean_object* v_elemsAndSeps_7128_, lean_object* v_sep_7129_, lean_object* v_pendingGroup_7130_, lean_object* v___x_7131_, lean_object* v_inst_7132_, lean_object* v_R_7133_, lean_object* v_a_7134_, lean_object* v_b_7135_, lean_object* v_c_7136_, lean_object* v___y_7137_, lean_object* v___y_7138_){
_start:
{
lean_object* v___x_7139_; 
v___x_7139_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7127_, v_elemsAndSeps_7128_, v_pendingGroup_7130_, v___x_7131_, v_a_7134_, v_b_7135_, v___y_7137_, v___y_7138_);
return v___x_7139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object* v_upperBound_7140_, lean_object* v_elemsAndSeps_7141_, lean_object* v_sep_7142_, lean_object* v_pendingGroup_7143_, lean_object* v___x_7144_, lean_object* v_inst_7145_, lean_object* v_R_7146_, lean_object* v_a_7147_, lean_object* v_b_7148_, lean_object* v_c_7149_, lean_object* v___y_7150_, lean_object* v___y_7151_){
_start:
{
lean_object* v_res_7152_; 
v_res_7152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(v_upperBound_7140_, v_elemsAndSeps_7141_, v_sep_7142_, v_pendingGroup_7143_, v___x_7144_, v_inst_7145_, v_R_7146_, v_a_7147_, v_b_7148_, v_c_7149_, v___y_7150_, v___y_7151_);
lean_dec_ref(v___y_7150_);
lean_dec(v___x_7144_);
lean_dec_ref(v_sep_7142_);
lean_dec_ref(v_elemsAndSeps_7141_);
lean_dec(v_upperBound_7140_);
return v_res_7152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object* v_sep_7156_, size_t v_sz_7157_, size_t v_i_7158_, lean_object* v_bs_7159_){
_start:
{
uint8_t v___x_7160_; 
v___x_7160_ = lean_usize_dec_lt(v_i_7158_, v_sz_7157_);
if (v___x_7160_ == 0)
{
lean_dec_ref(v_sep_7156_);
return v_bs_7159_;
}
else
{
lean_object* v_v_7161_; lean_object* v___x_7162_; lean_object* v_bs_x27_7163_; lean_object* v___y_7165_; 
v_v_7161_ = lean_array_uget(v_bs_7159_, v_i_7158_);
v___x_7162_ = lean_unsigned_to_nat(0u);
v_bs_x27_7163_ = lean_array_uset(v_bs_7159_, v_i_7158_, v___x_7162_);
if (lean_obj_tag(v_v_7161_) == 0)
{
lean_object* v_g_7170_; lean_object* v___x_7171_; lean_object* v___x_7172_; 
v_g_7170_ = lean_ctor_get(v_v_7161_, 0);
lean_inc_ref(v_g_7170_);
lean_dec_ref_known(v_v_7161_, 1);
v___x_7171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0));
lean_inc_ref(v_sep_7156_);
v___x_7172_ = l_Lean_Fmt_Layouts_sepArray(v_sep_7156_, v_g_7170_, v___x_7171_);
lean_dec_ref(v_g_7170_);
v___y_7165_ = v___x_7172_;
goto v___jp_7164_;
}
else
{
lean_object* v_t_7173_; 
v_t_7173_ = lean_ctor_get(v_v_7161_, 0);
lean_inc_ref(v_t_7173_);
lean_dec_ref_known(v_v_7161_, 1);
v___y_7165_ = v_t_7173_;
goto v___jp_7164_;
}
v___jp_7164_:
{
size_t v___x_7166_; size_t v___x_7167_; lean_object* v___x_7168_; 
v___x_7166_ = ((size_t)1ULL);
v___x_7167_ = lean_usize_add(v_i_7158_, v___x_7166_);
v___x_7168_ = lean_array_uset(v_bs_x27_7163_, v_i_7158_, v___y_7165_);
v_i_7158_ = v___x_7167_;
v_bs_7159_ = v___x_7168_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object* v_sep_7174_, lean_object* v_sz_7175_, lean_object* v_i_7176_, lean_object* v_bs_7177_){
_start:
{
size_t v_sz_boxed_7178_; size_t v_i_boxed_7179_; lean_object* v_res_7180_; 
v_sz_boxed_7178_ = lean_unbox_usize(v_sz_7175_);
lean_dec(v_sz_7175_);
v_i_boxed_7179_ = lean_unbox_usize(v_i_7176_);
lean_dec(v_i_7176_);
v_res_7180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7174_, v_sz_boxed_7178_, v_i_boxed_7179_, v_bs_7177_);
return v_res_7180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object* v_sep_7181_, lean_object* v_stxs_7182_, lean_object* v_a_7183_, lean_object* v_a_7184_){
_start:
{
lean_object* v___x_7185_; 
v___x_7185_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7181_, v_stxs_7182_, v_a_7183_, v_a_7184_);
if (lean_obj_tag(v___x_7185_) == 0)
{
lean_object* v_a_7186_; lean_object* v_a_7187_; lean_object* v___x_7189_; uint8_t v_isShared_7190_; uint8_t v_isSharedCheck_7198_; 
v_a_7186_ = lean_ctor_get(v___x_7185_, 0);
v_a_7187_ = lean_ctor_get(v___x_7185_, 1);
v_isSharedCheck_7198_ = !lean_is_exclusive(v___x_7185_);
if (v_isSharedCheck_7198_ == 0)
{
v___x_7189_ = v___x_7185_;
v_isShared_7190_ = v_isSharedCheck_7198_;
goto v_resetjp_7188_;
}
else
{
lean_inc(v_a_7187_);
lean_inc(v_a_7186_);
lean_dec(v___x_7185_);
v___x_7189_ = lean_box(0);
v_isShared_7190_ = v_isSharedCheck_7198_;
goto v_resetjp_7188_;
}
v_resetjp_7188_:
{
size_t v_sz_7191_; size_t v___x_7192_; lean_object* v___x_7193_; lean_object* v___x_7194_; lean_object* v___x_7196_; 
v_sz_7191_ = lean_array_size(v_a_7186_);
v___x_7192_ = ((size_t)0ULL);
v___x_7193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7181_, v_sz_7191_, v___x_7192_, v_a_7186_);
v___x_7194_ = l_Lean_Fmt_TaggedDoc_join(v___x_7193_);
if (v_isShared_7190_ == 0)
{
lean_ctor_set(v___x_7189_, 0, v___x_7194_);
v___x_7196_ = v___x_7189_;
goto v_reusejp_7195_;
}
else
{
lean_object* v_reuseFailAlloc_7197_; 
v_reuseFailAlloc_7197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7197_, 0, v___x_7194_);
lean_ctor_set(v_reuseFailAlloc_7197_, 1, v_a_7187_);
v___x_7196_ = v_reuseFailAlloc_7197_;
goto v_reusejp_7195_;
}
v_reusejp_7195_:
{
return v___x_7196_;
}
}
}
else
{
lean_object* v_a_7199_; lean_object* v_a_7200_; lean_object* v___x_7202_; uint8_t v_isShared_7203_; uint8_t v_isSharedCheck_7207_; 
lean_dec_ref(v_sep_7181_);
v_a_7199_ = lean_ctor_get(v___x_7185_, 0);
v_a_7200_ = lean_ctor_get(v___x_7185_, 1);
v_isSharedCheck_7207_ = !lean_is_exclusive(v___x_7185_);
if (v_isSharedCheck_7207_ == 0)
{
v___x_7202_ = v___x_7185_;
v_isShared_7203_ = v_isSharedCheck_7207_;
goto v_resetjp_7201_;
}
else
{
lean_inc(v_a_7200_);
lean_inc(v_a_7199_);
lean_dec(v___x_7185_);
v___x_7202_ = lean_box(0);
v_isShared_7203_ = v_isSharedCheck_7207_;
goto v_resetjp_7201_;
}
v_resetjp_7201_:
{
lean_object* v___x_7205_; 
if (v_isShared_7203_ == 0)
{
v___x_7205_ = v___x_7202_;
goto v_reusejp_7204_;
}
else
{
lean_object* v_reuseFailAlloc_7206_; 
v_reuseFailAlloc_7206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7199_);
lean_ctor_set(v_reuseFailAlloc_7206_, 1, v_a_7200_);
v___x_7205_ = v_reuseFailAlloc_7206_;
goto v_reusejp_7204_;
}
v_reusejp_7204_:
{
return v___x_7205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object* v_sep_7208_, lean_object* v_stxs_7209_, lean_object* v_a_7210_, lean_object* v_a_7211_){
_start:
{
lean_object* v_res_7212_; 
v_res_7212_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7208_, v_stxs_7209_, v_a_7210_, v_a_7211_);
lean_dec_ref(v_a_7210_);
lean_dec_ref(v_stxs_7209_);
return v_res_7212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_ks_7213_, lean_object* v_sep_7214_, lean_object* v_stxs_7215_, lean_object* v_a_7216_, lean_object* v_a_7217_){
_start:
{
lean_object* v___x_7218_; 
v___x_7218_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7214_, v_stxs_7215_, v_a_7216_, v_a_7217_);
return v___x_7218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_ks_7219_, lean_object* v_sep_7220_, lean_object* v_stxs_7221_, lean_object* v_a_7222_, lean_object* v_a_7223_){
_start:
{
lean_object* v_res_7224_; 
v_res_7224_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(v_ks_7219_, v_sep_7220_, v_stxs_7221_, v_a_7222_, v_a_7223_);
lean_dec_ref(v_a_7222_);
lean_dec_ref(v_stxs_7221_);
lean_dec(v_ks_7219_);
return v_res_7224_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Comments(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Comments(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
