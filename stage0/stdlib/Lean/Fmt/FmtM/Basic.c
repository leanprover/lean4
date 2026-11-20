// Lean compiler output
// Module: Lean.Fmt.FmtM.Basic
// Imports: public import Lean.Fmt.FmtM.Layouts import Lean.Fmt.Util.RangeTree import Lean.Fmt.Util.Basic import Lean.Fmt.FmtM.Comments meta import Lean.Parser.Term.Basic import Init.Data
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
lean_object* l_Lean_Syntax_Range_ofSubstring(lean_object*);
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
lean_object* l_ShareCommon_mkStateImpl(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(lean_object* v_as_1_, lean_object* v_i_2_){
_start:
{
lean_object* v_zero_3_; uint8_t v_isZero_4_; 
v_zero_3_ = lean_unsigned_to_nat(0u);
v_isZero_4_ = lean_nat_dec_eq(v_i_2_, v_zero_3_);
if (v_isZero_4_ == 1)
{
lean_object* v___x_5_; 
lean_dec(v_i_2_);
v___x_5_ = lean_box(0);
return v___x_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_i_2_, v_one_6_);
lean_dec(v_i_2_);
v___x_8_ = lean_array_fget_borrowed(v_as_1_, v_n_7_);
lean_inc(v___x_8_);
v___x_9_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v___x_8_);
if (lean_obj_tag(v___x_9_) == 0)
{
v_i_2_ = v_n_7_;
goto _start;
}
else
{
lean_dec(v_n_7_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(lean_object* v_stx_11_){
_start:
{
switch(lean_obj_tag(v_stx_11_))
{
case 0:
{
lean_object* v___x_12_; 
v___x_12_ = lean_box(0);
return v___x_12_;
}
case 1:
{
lean_object* v_args_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_args_13_ = lean_ctor_get(v_stx_11_, 2);
lean_inc_ref(v_args_13_);
lean_dec_ref_known(v_stx_11_, 3);
v___x_14_ = lean_array_get_size(v_args_13_);
v___x_15_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_args_13_, v___x_14_);
lean_dec_ref(v_args_13_);
return v___x_15_;
}
default: 
{
lean_object* v___x_16_; 
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v_stx_11_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg___boxed(lean_object* v_as_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_as_17_, v_i_18_);
lean_dec_ref(v_as_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(lean_object* v_as_20_, lean_object* v_i_21_, lean_object* v_a_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___redArg(v_as_20_, v_i_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0___boxed(lean_object* v_as_24_, lean_object* v_i_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f_spec__0(v_as_24_, v_i_25_, v_a_26_);
lean_dec_ref(v_as_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(lean_object* v_stx_31_){
_start:
{
switch(lean_obj_tag(v_stx_31_))
{
case 0:
{
lean_object* v___x_32_; 
v___x_32_ = lean_box(0);
return v___x_32_;
}
case 1:
{
lean_object* v_args_33_; lean_object* v___x_34_; lean_object* v___x_35_; size_t v_sz_36_; size_t v___x_37_; lean_object* v___x_38_; lean_object* v_fst_39_; 
v_args_33_ = lean_ctor_get(v_stx_31_, 2);
lean_inc_ref(v_args_33_);
lean_dec_ref_known(v_stx_31_, 3);
v___x_34_ = lean_box(0);
v___x_35_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0));
v_sz_36_ = lean_array_size(v_args_33_);
v___x_37_ = ((size_t)0ULL);
v___x_38_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(v_args_33_, v_sz_36_, v___x_37_, v___x_35_);
lean_dec_ref(v_args_33_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
lean_dec_ref(v___x_38_);
if (lean_obj_tag(v_fst_39_) == 0)
{
return v___x_34_;
}
else
{
lean_object* v_val_40_; 
v_val_40_ = lean_ctor_get(v_fst_39_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v_fst_39_, 1);
return v_val_40_;
}
}
default: 
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v_stx_31_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(lean_object* v_as_42_, size_t v_sz_43_, size_t v_i_44_, lean_object* v_b_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = lean_usize_dec_lt(v_i_44_, v_sz_43_);
if (v___x_46_ == 0)
{
lean_inc_ref(v_b_45_);
return v_b_45_;
}
else
{
lean_object* v___x_47_; lean_object* v_a_48_; lean_object* v___x_49_; 
v___x_47_ = lean_box(0);
v_a_48_ = lean_array_uget_borrowed(v_as_42_, v_i_44_);
lean_inc(v_a_48_);
v___x_49_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_a_48_);
if (lean_obj_tag(v___x_49_) == 1)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_47_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; size_t v___x_53_; size_t v___x_54_; 
lean_dec(v___x_49_);
v___x_52_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___closed__0));
v___x_53_ = ((size_t)1ULL);
v___x_54_ = lean_usize_add(v_i_44_, v___x_53_);
v_i_44_ = v___x_54_;
v_b_45_ = v___x_52_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0___boxed(lean_object* v_as_56_, lean_object* v_sz_57_, lean_object* v_i_58_, lean_object* v_b_59_){
_start:
{
size_t v_sz_boxed_60_; size_t v_i_boxed_61_; lean_object* v_res_62_; 
v_sz_boxed_60_ = lean_unbox_usize(v_sz_57_);
lean_dec(v_sz_57_);
v_i_boxed_61_ = lean_unbox_usize(v_i_58_);
lean_dec(v_i_58_);
v_res_62_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f_spec__0(v_as_56_, v_sz_boxed_60_, v_i_boxed_61_, v_b_59_);
lean_dec_ref(v_b_59_);
lean_dec_ref(v_as_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(lean_object* v_a_63_){
_start:
{
lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_105_; 
v_fst_64_ = lean_ctor_get(v_a_63_, 0);
v_snd_65_ = lean_ctor_get(v_a_63_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_a_63_);
if (v_isSharedCheck_105_ == 0)
{
v___x_67_ = v_a_63_;
v_isShared_68_ = v_isSharedCheck_105_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_snd_65_);
lean_inc(v_fst_64_);
lean_dec(v_a_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_105_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
uint32_t v___y_70_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_nat_dec_lt(v___x_98_, v_snd_65_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_del_object(v___x_67_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_fst_64_);
lean_ctor_set(v___x_100_, 1, v_snd_65_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = l_String_Slice_Pos_get_x3f(v_fst_64_, v___x_98_);
if (lean_obj_tag(v___x_101_) == 0)
{
uint32_t v___x_102_; 
v___x_102_ = 65;
v___y_70_ = v___x_102_;
goto v___jp_69_;
}
else
{
lean_object* v_val_103_; uint32_t v___x_104_; 
v_val_103_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_103_);
lean_dec_ref_known(v___x_101_, 1);
v___x_104_ = lean_unbox_uint32(v_val_103_);
lean_dec(v_val_103_);
v___y_70_ = v___x_104_;
goto v___jp_69_;
}
}
v___jp_69_:
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 32;
v___x_72_ = lean_uint32_dec_eq(v___y_70_, v___x_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_74_; 
if (v_isShared_68_ == 0)
{
v___x_74_ = v___x_67_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_fst_64_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_snd_65_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
lean_object* v_str_76_; lean_object* v_startInclusive_77_; lean_object* v_endExclusive_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_94_; 
v_str_76_ = lean_ctor_get(v_fst_64_, 0);
lean_inc_ref(v_str_76_);
v_startInclusive_77_ = lean_ctor_get(v_fst_64_, 1);
lean_inc(v_startInclusive_77_);
v_endExclusive_78_ = lean_ctor_get(v_fst_64_, 2);
lean_inc(v_endExclusive_78_);
v___x_79_ = lean_unsigned_to_nat(1u);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_String_Slice_Pos_nextn(v_fst_64_, v___x_80_, v___x_79_);
v_isSharedCheck_94_ = !lean_is_exclusive(v_fst_64_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; 
v_unused_95_ = lean_ctor_get(v_fst_64_, 2);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_fst_64_, 1);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_fst_64_, 0);
lean_dec(v_unused_97_);
v___x_83_ = v_fst_64_;
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_fst_64_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_85_ = lean_nat_add(v_startInclusive_77_, v___x_81_);
lean_dec(v___x_81_);
lean_dec(v_startInclusive_77_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v___x_85_);
v___x_87_ = v___x_83_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_str_76_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_endExclusive_78_);
v___x_87_ = v_reuseFailAlloc_93_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_nat_sub(v_snd_65_, v___x_79_);
lean_dec(v_snd_65_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_88_);
lean_ctor_set(v___x_67_, 0, v___x_87_);
v___x_90_ = v___x_67_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_88_);
v___x_90_ = v_reuseFailAlloc_92_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
v_a_63_ = v___x_90_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(lean_object* v_line_106_, lean_object* v_numSpaces_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_fst_110_; 
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_line_106_);
lean_ctor_set(v___x_108_, 1, v_numSpaces_107_);
v___x_109_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(v___x_108_);
v_fst_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_fst_110_);
lean_dec_ref(v___x_109_);
return v_fst_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0(lean_object* v_inst_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces_spec__0___redArg(v_a_112_);
return v___x_113_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1));
v___x_120_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2);
v___x_123_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1));
v___x_124_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
lean_ctor_set(v___x_124_, 3, v___x_121_);
return v___x_124_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg(){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___boxed(lean_object* v___dummy_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg();
return v_res_131_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg();
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(lean_object* v_s_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___boxed(lean_object* v_s_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v_s_135_);
lean_dec_ref(v_s_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(lean_object* v_numSpaces_137_, lean_object* v_s_138_, lean_object* v___x_139_, lean_object* v___x_140_, lean_object* v_a_141_, lean_object* v_b_142_){
_start:
{
lean_object* v_it_144_; lean_object* v_startInclusive_145_; lean_object* v_endExclusive_146_; 
if (lean_obj_tag(v_a_141_) == 0)
{
lean_object* v_currPos_152_; lean_object* v_searcher_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_259_; 
v_currPos_152_ = lean_ctor_get(v_a_141_, 0);
v_searcher_153_ = lean_ctor_get(v_a_141_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_a_141_);
if (v_isSharedCheck_259_ == 0)
{
v___x_155_ = v_a_141_;
v_isShared_156_ = v_isSharedCheck_259_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_searcher_153_);
lean_inc(v_currPos_152_);
lean_dec(v_a_141_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_259_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_it_158_; lean_object* v_it_164_; lean_object* v_startPos_165_; lean_object* v_endPos_166_; 
switch(lean_obj_tag(v_searcher_153_))
{
case 0:
{
lean_object* v_pos_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_191_; 
lean_del_object(v___x_155_);
v_pos_179_ = lean_ctor_get(v_searcher_153_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_searcher_153_);
if (v_isSharedCheck_191_ == 0)
{
v___x_181_ = v_searcher_153_;
v_isShared_182_ = v_isSharedCheck_191_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_pos_179_);
lean_dec(v_searcher_153_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_191_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_startInclusive_183_; lean_object* v_endExclusive_184_; lean_object* v___x_185_; uint8_t v_decide_186_; 
v_startInclusive_183_ = lean_ctor_get(v___x_139_, 1);
v_endExclusive_184_ = lean_ctor_get(v___x_139_, 2);
v___x_185_ = lean_nat_sub(v_endExclusive_184_, v_startInclusive_183_);
v_decide_186_ = lean_nat_dec_eq(v_pos_179_, v___x_185_);
lean_dec(v___x_185_);
if (v_decide_186_ == 0)
{
lean_object* v___x_188_; 
lean_inc(v_pos_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 1);
v___x_188_ = v___x_181_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_pos_179_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_inc(v_pos_179_);
v_it_164_ = v___x_188_;
v_startPos_165_ = v_pos_179_;
v_endPos_166_ = v_pos_179_;
goto v___jp_163_;
}
}
else
{
lean_object* v___x_190_; 
lean_del_object(v___x_181_);
v___x_190_ = lean_box(3);
lean_inc(v_pos_179_);
v_it_164_ = v___x_190_;
v_startPos_165_ = v_pos_179_;
v_endPos_166_ = v_pos_179_;
goto v___jp_163_;
}
}
}
case 1:
{
lean_object* v_pos_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_200_; 
v_pos_192_ = lean_ctor_get(v_searcher_153_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v_searcher_153_);
if (v_isSharedCheck_200_ == 0)
{
v___x_194_ = v_searcher_153_;
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_pos_192_);
lean_dec(v_searcher_153_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_200_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_196_ = lean_string_utf8_next_fast(v_s_138_, v_pos_192_);
lean_dec(v_pos_192_);
if (v_isShared_195_ == 0)
{
lean_ctor_set_tag(v___x_194_, 0);
lean_ctor_set(v___x_194_, 0, v___x_196_);
v___x_198_ = v___x_194_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
v_it_158_ = v___x_198_;
goto v___jp_157_;
}
}
}
case 2:
{
lean_object* v_needle_201_; lean_object* v_table_202_; lean_object* v_stackPos_203_; lean_object* v_needlePos_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_258_; 
v_needle_201_ = lean_ctor_get(v_searcher_153_, 0);
v_table_202_ = lean_ctor_get(v_searcher_153_, 1);
v_stackPos_203_ = lean_ctor_get(v_searcher_153_, 2);
v_needlePos_204_ = lean_ctor_get(v_searcher_153_, 3);
v_isSharedCheck_258_ = !lean_is_exclusive(v_searcher_153_);
if (v_isSharedCheck_258_ == 0)
{
v___x_206_ = v_searcher_153_;
v_isShared_207_ = v_isSharedCheck_258_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_needlePos_204_);
lean_inc(v_stackPos_203_);
lean_inc(v_table_202_);
lean_inc(v_needle_201_);
lean_dec(v_searcher_153_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_258_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_str_208_; lean_object* v_startInclusive_209_; lean_object* v_endExclusive_210_; lean_object* v_basePos_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_str_208_ = lean_ctor_get(v_needle_201_, 0);
v_startInclusive_209_ = lean_ctor_get(v_needle_201_, 1);
v_endExclusive_210_ = lean_ctor_get(v_needle_201_, 2);
v_basePos_211_ = lean_nat_sub(v_stackPos_203_, v_needlePos_204_);
v___x_212_ = lean_nat_sub(v_endExclusive_210_, v_startInclusive_209_);
v___x_213_ = lean_nat_add(v_basePos_211_, v___x_212_);
v___x_214_ = lean_nat_dec_le(v___x_213_, v___x_140_);
lean_dec(v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
lean_dec(v___x_212_);
lean_del_object(v___x_206_);
lean_dec(v_needlePos_204_);
lean_dec(v_stackPos_203_);
lean_dec_ref(v_table_202_);
lean_dec_ref(v_needle_201_);
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_add(v_basePos_211_, v___x_215_);
lean_dec(v_basePos_211_);
v___x_217_ = lean_nat_dec_le(v___x_216_, v___x_140_);
lean_dec(v___x_216_);
if (v___x_217_ == 0)
{
lean_del_object(v___x_155_);
goto v___jp_177_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(3);
v_it_158_ = v___x_218_;
goto v___jp_157_;
}
}
else
{
uint8_t v_stackByte_219_; lean_object* v___x_220_; uint8_t v_patByte_221_; uint8_t v___x_222_; 
lean_dec(v_basePos_211_);
lean_inc(v_stackPos_203_);
v_stackByte_219_ = lean_string_get_byte_fast(v_s_138_, v_stackPos_203_);
v___x_220_ = lean_nat_add(v_startInclusive_209_, v_needlePos_204_);
v_patByte_221_ = lean_string_get_byte_fast(v_str_208_, v___x_220_);
v___x_222_ = lean_uint8_dec_eq(v_stackByte_219_, v_patByte_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; uint8_t v_decide_224_; 
lean_dec(v___x_212_);
v___x_223_ = lean_unsigned_to_nat(0u);
v_decide_224_ = lean_nat_dec_eq(v_needlePos_204_, v___x_223_);
if (v_decide_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_newNeedlePos_227_; uint8_t v___x_228_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_sub(v_needlePos_204_, v___x_225_);
lean_dec(v_needlePos_204_);
v_newNeedlePos_227_ = lean_array_fget_borrowed(v_table_202_, v___x_226_);
lean_dec(v___x_226_);
v___x_228_ = lean_nat_dec_eq(v_newNeedlePos_227_, v___x_223_);
if (v___x_228_ == 0)
{
lean_object* v___x_230_; 
lean_inc(v_newNeedlePos_227_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 3, v_newNeedlePos_227_);
v___x_230_ = v___x_206_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_needle_201_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_table_202_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_stackPos_203_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_newNeedlePos_227_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
v_it_158_ = v___x_230_;
goto v___jp_157_;
}
}
else
{
lean_object* v_nextStackPos_232_; lean_object* v___x_234_; 
v_nextStackPos_232_ = l_String_Slice_posGE___redArg(v___x_139_, v_stackPos_203_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 3, v___x_223_);
lean_ctor_set(v___x_206_, 2, v_nextStackPos_232_);
v___x_234_ = v___x_206_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_needle_201_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_table_202_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_nextStackPos_232_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v___x_223_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
v_it_158_ = v___x_234_;
goto v___jp_157_;
}
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_nextStackPos_238_; lean_object* v___x_240_; 
lean_dec(v_needlePos_204_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_stackPos_203_, v___x_236_);
lean_dec(v_stackPos_203_);
v_nextStackPos_238_ = l_String_Slice_posGE___redArg(v___x_139_, v___x_237_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 3, v___x_223_);
lean_ctor_set(v___x_206_, 2, v_nextStackPos_238_);
v___x_240_ = v___x_206_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_needle_201_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_table_202_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_nextStackPos_238_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v___x_223_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
v_it_158_ = v___x_240_;
goto v___jp_157_;
}
}
}
else
{
lean_object* v___x_242_; lean_object* v_nextStackPos_243_; lean_object* v_nextNeedlePos_244_; uint8_t v_decide_245_; 
lean_del_object(v___x_155_);
v___x_242_ = lean_unsigned_to_nat(1u);
v_nextStackPos_243_ = lean_nat_add(v_stackPos_203_, v___x_242_);
lean_dec(v_stackPos_203_);
v_nextNeedlePos_244_ = lean_nat_add(v_needlePos_204_, v___x_242_);
lean_dec(v_needlePos_204_);
v_decide_245_ = lean_nat_dec_eq(v_nextNeedlePos_244_, v___x_212_);
lean_dec(v___x_212_);
if (v_decide_245_ == 0)
{
lean_object* v___x_247_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 3, v_nextNeedlePos_244_);
lean_ctor_set(v___x_206_, 2, v_nextStackPos_243_);
v___x_247_ = v___x_206_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_needle_201_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_table_202_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v_nextStackPos_243_);
lean_ctor_set(v_reuseFailAlloc_250_, 3, v_nextNeedlePos_244_);
v___x_247_ = v_reuseFailAlloc_250_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; 
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_currPos_152_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v_a_141_ = v___x_248_;
goto _start;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_251_ = lean_nat_sub(v_nextStackPos_243_, v_nextNeedlePos_244_);
lean_dec(v_nextNeedlePos_244_);
v___x_252_ = l_String_Slice_pos_x21(v___x_139_, v___x_251_);
lean_dec(v___x_251_);
v___x_253_ = l_String_Slice_pos_x21(v___x_139_, v_nextStackPos_243_);
v___x_254_ = lean_unsigned_to_nat(0u);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 3, v___x_254_);
lean_ctor_set(v___x_206_, 2, v_nextStackPos_243_);
v___x_256_ = v___x_206_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_needle_201_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_table_202_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_nextStackPos_243_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
v_it_164_ = v___x_256_;
v_startPos_165_ = v___x_252_;
v_endPos_166_ = v___x_253_;
goto v___jp_163_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_155_);
goto v___jp_177_;
}
}
v___jp_157_:
{
lean_object* v___x_160_; 
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v_it_158_);
v___x_160_ = v___x_155_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_currPos_152_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_it_158_);
v___x_160_ = v_reuseFailAlloc_162_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
v_a_141_ = v___x_160_;
goto _start;
}
}
v___jp_163_:
{
lean_object* v_slice_167_; lean_object* v_startInclusive_168_; lean_object* v_endExclusive_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_slice_167_ = l_String_Slice_subslice_x21(v___x_139_, v_currPos_152_, v_startPos_165_);
v_startInclusive_168_ = lean_ctor_get(v_slice_167_, 0);
v_endExclusive_169_ = lean_ctor_get(v_slice_167_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_slice_167_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v_slice_167_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_endExclusive_169_);
lean_inc(v_startInclusive_168_);
lean_dec(v_slice_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_nextIt_174_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v_it_164_);
lean_ctor_set(v___x_171_, 0, v_endPos_166_);
v_nextIt_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_endPos_166_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_it_164_);
v_nextIt_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
v_it_144_ = v_nextIt_174_;
v_startInclusive_145_ = v_startInclusive_168_;
v_endExclusive_146_ = v_endExclusive_169_;
goto v___jp_143_;
}
}
}
v___jp_177_:
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(1);
lean_inc(v___x_140_);
v_it_144_ = v___x_178_;
v_startInclusive_145_ = v_currPos_152_;
v_endExclusive_146_ = v___x_140_;
goto v___jp_143_;
}
}
}
else
{
lean_dec(v___x_140_);
lean_dec_ref(v_s_138_);
lean_dec(v_numSpaces_137_);
return v_b_142_;
}
v___jp_143_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc_ref(v_s_138_);
v___x_147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_147_, 0, v_s_138_);
lean_ctor_set(v___x_147_, 1, v_startInclusive_145_);
lean_ctor_set(v___x_147_, 2, v_endExclusive_146_);
lean_inc(v_numSpaces_137_);
v___x_148_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(v___x_147_, v_numSpaces_137_);
v___x_149_ = l_String_Slice_toString(v___x_148_);
lean_dec_ref(v___x_148_);
v___x_150_ = lean_array_push(v_b_142_, v___x_149_);
v_a_141_ = v_it_144_;
v_b_142_ = v___x_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg___boxed(lean_object* v_numSpaces_260_, lean_object* v_s_261_, lean_object* v___x_262_, lean_object* v___x_263_, lean_object* v_a_264_, lean_object* v_b_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_260_, v_s_261_, v___x_262_, v___x_263_, v_a_264_, v_b_265_);
lean_dec_ref(v___x_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(lean_object* v_s_269_, lean_object* v_numSpaces_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_271_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_string_utf8_byte_size(v_s_269_);
lean_inc_ref(v_s_269_);
v___x_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_274_, 0, v_s_269_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_273_);
v___x_275_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_276_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0));
v___x_277_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_270_, v_s_269_, v___x_274_, v___x_273_, v___x_275_, v___x_276_);
lean_dec_ref_known(v___x_274_, 3);
v___x_278_ = lean_array_to_list(v___x_277_);
v___x_279_ = l_String_intercalate(v___x_271_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(lean_object* v_numSpaces_280_, lean_object* v_s_281_, lean_object* v___x_282_, lean_object* v___x_283_, lean_object* v_inst_284_, lean_object* v_R_285_, lean_object* v_a_286_, lean_object* v_b_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_280_, v_s_281_, v___x_282_, v___x_283_, v_a_286_, v_b_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___boxed(lean_object* v_numSpaces_289_, lean_object* v_s_290_, lean_object* v___x_291_, lean_object* v___x_292_, lean_object* v_inst_293_, lean_object* v_R_294_, lean_object* v_a_295_, lean_object* v_b_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(v_numSpaces_289_, v_s_290_, v___x_291_, v___x_292_, v_inst_293_, v_R_294_, v_a_295_, v_b_296_);
lean_dec_ref(v___x_291_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState___redArg(lean_object* v_value_298_, lean_object* v_s_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v_s_299_);
lean_ctor_set(v___x_300_, 1, v_value_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState(lean_object* v_00_u03b1_301_, lean_object* v_value_302_, lean_object* v_s_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_s_303_);
lean_ctor_set(v___x_304_, 1, v_value_302_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
v___x_306_ = lean_unsigned_to_nat(16u);
v___x_307_ = lean_mk_array(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__0, &l_Lean_FmtM_run___redArg___closed__0_once, _init_l_Lean_FmtM_run___redArg___closed__0);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_Lean_ShareCommon_objectFactory;
v___x_312_ = l_ShareCommon_mkStateImpl(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = l_Lean_Fmt_firstSyntaxTagId;
v___x_314_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__2, &l_Lean_FmtM_run___redArg___closed__2_once, _init_l_Lean_FmtM_run___redArg___closed__2);
v___x_315_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__1, &l_Lean_FmtM_run___redArg___closed__1_once, _init_l_Lean_FmtM_run___redArg___closed__1);
v___x_316_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
lean_ctor_set(v___x_316_, 3, v___x_315_);
lean_ctor_set(v___x_316_, 4, v___x_315_);
lean_ctor_set(v___x_316_, 5, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run___redArg(lean_object* v_ctx_317_, lean_object* v_act_318_){
_start:
{
lean_object* v___x_319_; lean_object* v_r_320_; 
v___x_319_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__3, &l_Lean_FmtM_run___redArg___closed__3_once, _init_l_Lean_FmtM_run___redArg___closed__3);
v_r_320_ = lean_apply_2(v_act_318_, v_ctx_317_, v___x_319_);
if (lean_obj_tag(v_r_320_) == 0)
{
lean_object* v_a_321_; lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_a_321_ = lean_ctor_get(v_r_320_, 0);
v_a_322_ = lean_ctor_get(v_r_320_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_r_320_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v_r_320_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_inc(v_a_321_);
lean_dec(v_r_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v_a_321_);
lean_ctor_set(v___x_324_, 0, v_a_322_);
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_a_321_);
v___x_327_ = v_reuseFailAlloc_329_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; 
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_332_; 
v_a_331_ = lean_ctor_get(v_r_320_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v_r_320_, 2);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_a_331_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run(lean_object* v_00_u03b1_333_, lean_object* v_ctx_334_, lean_object* v_act_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_FmtM_run___redArg(v_ctx_334_, v_act_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(lean_object* v_00_u03b1_337_, lean_object* v_v_338_, lean_object* v_x_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_toBacktrackableState_341_; lean_object* v_shareCommonState_342_; lean_object* v_freshTagId_343_; lean_object* v_missingFormatters_344_; lean_object* v_partialFormatters_345_; lean_object* v_missingChoiceResolutions_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_364_; 
v_toBacktrackableState_341_ = lean_ctor_get(v___y_340_, 0);
v_shareCommonState_342_ = lean_ctor_get(v___y_340_, 1);
v_freshTagId_343_ = lean_ctor_get(v___y_340_, 2);
v_missingFormatters_344_ = lean_ctor_get(v___y_340_, 3);
v_partialFormatters_345_ = lean_ctor_get(v___y_340_, 4);
v_missingChoiceResolutions_346_ = lean_ctor_get(v___y_340_, 5);
v_isSharedCheck_364_ = !lean_is_exclusive(v___y_340_);
if (v_isSharedCheck_364_ == 0)
{
v___x_348_ = v___y_340_;
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_missingChoiceResolutions_346_);
lean_inc(v_partialFormatters_345_);
lean_inc(v_missingFormatters_344_);
lean_inc(v_freshTagId_343_);
lean_inc(v_shareCommonState_342_);
lean_inc(v_toBacktrackableState_341_);
lean_dec(v___y_340_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_fst_352_; lean_object* v_snd_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_363_; 
v___x_350_ = l_Lean_ShareCommon_objectFactory;
v___x_351_ = lean_state_sharecommon(v___x_350_, v_shareCommonState_342_, v_v_338_);
v_fst_352_ = lean_ctor_get(v___x_351_, 0);
v_snd_353_ = lean_ctor_get(v___x_351_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_363_ == 0)
{
v___x_355_ = v___x_351_;
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_snd_353_);
lean_inc(v_fst_352_);
lean_dec(v___x_351_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_363_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v_snd_353_);
v___x_358_ = v___x_348_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_toBacktrackableState_341_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_snd_353_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_freshTagId_343_);
lean_ctor_set(v_reuseFailAlloc_362_, 3, v_missingFormatters_344_);
lean_ctor_set(v_reuseFailAlloc_362_, 4, v_partialFormatters_345_);
lean_ctor_set(v_reuseFailAlloc_362_, 5, v_missingChoiceResolutions_346_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_fst_352_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed(lean_object* v_00_u03b1_365_, lean_object* v_v_366_, lean_object* v_x_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(v_00_u03b1_365_, v_v_366_, v_x_367_, v___y_368_);
lean_dec_ref(v_x_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_FormattedWhitespace_merge(lean_object* v_t1_372_, lean_object* v_t2_373_){
_start:
{
lean_object* v_formattedLeadingRanges_374_; lean_object* v_formattedTrailingRanges_375_; lean_object* v_formattedLeadingRanges_376_; lean_object* v_formattedTrailingRanges_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_386_; 
v_formattedLeadingRanges_374_ = lean_ctor_get(v_t1_372_, 0);
lean_inc_ref(v_formattedLeadingRanges_374_);
v_formattedTrailingRanges_375_ = lean_ctor_get(v_t1_372_, 1);
lean_inc_ref(v_formattedTrailingRanges_375_);
lean_dec_ref(v_t1_372_);
v_formattedLeadingRanges_376_ = lean_ctor_get(v_t2_373_, 0);
v_formattedTrailingRanges_377_ = lean_ctor_get(v_t2_373_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_t2_373_);
if (v_isSharedCheck_386_ == 0)
{
v___x_379_ = v_t2_373_;
v_isShared_380_ = v_isSharedCheck_386_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_formattedTrailingRanges_377_);
lean_inc(v_formattedLeadingRanges_376_);
lean_dec(v_t2_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_386_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_384_; 
v___x_381_ = l_Array_append___redArg(v_formattedLeadingRanges_374_, v_formattedLeadingRanges_376_);
lean_dec_ref(v_formattedLeadingRanges_376_);
v___x_382_ = l_Array_append___redArg(v_formattedTrailingRanges_375_, v_formattedTrailingRanges_377_);
lean_dec_ref(v_formattedTrailingRanges_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_382_);
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_384_ = v___x_379_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_382_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object* v_stx_387_, lean_object* v_i_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_arg_390_; uint8_t v___x_391_; 
v_arg_390_ = l_Lean_Syntax_getArg(v_stx_387_, v_i_388_);
v___x_391_ = l_Lean_Syntax_isMissing(v_arg_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_arg_390_);
lean_ctor_set(v___x_392_, 1, v_a_389_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_arg_390_);
v___x_393_ = l_Lean_Fmt_Error_partialFormatter;
v___x_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v_a_389_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg___boxed(lean_object* v_stx_395_, lean_object* v_i_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_395_, v_i_396_, v_a_397_);
lean_dec(v_i_396_);
lean_dec(v_stx_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21(lean_object* v_stx_399_, lean_object* v_i_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_399_, v_i_400_, v_a_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___boxed(lean_object* v_stx_404_, lean_object* v_i_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Fmt_getStxArg_x21(v_stx_404_, v_i_405_, v_a_406_, v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_i_405_);
lean_dec(v_stx_404_);
return v_res_408_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0(void){
_start:
{
lean_object* v___x_409_; lean_object* v___f_410_; 
v___x_409_ = l_Lean_Fmt_instInhabitedError_default;
v___f_410_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_410_, 0, v___x_409_);
return v___f_410_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___f_414_; lean_object* v___f_415_; lean_object* v___x_703__overap_416_; lean_object* v___x_417_; 
v___f_414_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_415_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_415_, 0, v___f_414_);
v___x_703__overap_416_ = lean_panic_fn_borrowed(v___f_415_, v_msg_411_);
lean_dec_ref(v___f_415_);
lean_inc_ref(v___y_412_);
v___x_417_ = lean_apply_2(v___x_703__overap_416_, v___y_412_, v___y_413_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___boxed(lean_object* v_msg_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v_msg_418_, v___y_419_, v___y_420_);
lean_dec_ref(v___y_419_);
return v_res_421_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(lean_object* v_msg_425_){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0);
v___x_427_ = lean_panic_fn_borrowed(v___x_426_, v_msg_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object* v_x_428_){
_start:
{
lean_object* v_startPos_429_; 
v_startPos_429_ = lean_ctor_get(v_x_428_, 4);
lean_inc(v_startPos_429_);
return v_startPos_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Fmt_getLineInfo_x21___lam__0(v_x_430_);
lean_dec_ref(v_x_430_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_getLineInfo_x21___lam__1(lean_object* v_x1_432_, lean_object* v_x2_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_x1_432_, v___x_434_);
v___x_436_ = lean_nat_dec_le(v___x_435_, v_x2_433_);
lean_dec(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1___boxed(lean_object* v_x1_437_, lean_object* v_x2_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Lean_Fmt_getLineInfo_x21___lam__1(v_x1_437_, v_x2_438_);
lean_dec(v_x2_438_);
lean_dec(v_x1_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__3(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_444_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__2));
v___x_445_ = lean_unsigned_to_nat(2u);
v___x_446_ = lean_unsigned_to_nat(85u);
v___x_447_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__1));
v___x_448_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_449_ = l_mkPanicMessageWithDecl(v___x_448_, v___x_447_, v___x_446_, v___x_445_, v___x_444_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__9(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_455_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__8));
v___x_456_ = lean_unsigned_to_nat(14u);
v___x_457_ = lean_unsigned_to_nat(22u);
v___x_458_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__7));
v___x_459_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__6));
v___x_460_ = l_mkPanicMessageWithDecl(v___x_459_, v___x_458_, v___x_457_, v___x_456_, v___x_455_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21(lean_object* v_pos_461_, lean_object* v_a_462_, lean_object* v_a_463_){
_start:
{
lean_object* v___y_468_; lean_object* v_lineInfos_482_; lean_object* v___f_483_; lean_object* v___f_484_; lean_object* v___x_485_; 
v_lineInfos_482_ = lean_ctor_get(v_a_462_, 4);
v___f_483_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_484_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
lean_inc(v_pos_461_);
v___x_485_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_482_, v_pos_461_, v___f_483_, v___f_484_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_487_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_486_);
v___y_468_ = v___x_487_;
goto v___jp_467_;
}
else
{
lean_object* v_val_488_; 
v_val_488_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v___x_485_, 1);
v___y_468_ = v_val_488_;
goto v___jp_467_;
}
v___jp_464_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__3, &l_Lean_Fmt_getLineInfo_x21___closed__3_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__3);
v___x_466_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v___x_465_, v_a_462_, v_a_463_);
return v___x_466_;
}
v___jp_467_:
{
lean_object* v_snd_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_480_; 
v_snd_469_ = lean_ctor_get(v___y_468_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v___y_468_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v___y_468_, 0);
lean_dec(v_unused_481_);
v___x_471_ = v___y_468_;
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snd_469_);
lean_dec(v___y_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_480_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v_startPos_473_; lean_object* v_endPos_474_; uint8_t v___x_475_; 
v_startPos_473_ = lean_ctor_get(v_snd_469_, 4);
v_endPos_474_ = lean_ctor_get(v_snd_469_, 5);
v___x_475_ = lean_nat_dec_le(v_startPos_473_, v_pos_461_);
if (v___x_475_ == 0)
{
lean_del_object(v___x_471_);
lean_dec(v_snd_469_);
lean_dec(v_pos_461_);
goto v___jp_464_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_le(v_pos_461_, v_endPos_474_);
lean_dec(v_pos_461_);
if (v___x_476_ == 0)
{
lean_del_object(v___x_471_);
lean_dec(v_snd_469_);
goto v___jp_464_;
}
else
{
lean_object* v___x_478_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v_a_463_);
lean_ctor_set(v___x_471_, 0, v_snd_469_);
v___x_478_ = v___x_471_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_snd_469_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_a_463_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___boxed(lean_object* v_pos_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Fmt_getLineInfo_x21(v_pos_489_, v_a_490_, v_a_491_);
lean_dec_ref(v_a_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1(lean_object* v_msg_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___x_1262__overap_498_; lean_object* v___x_499_; 
v___f_496_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_497_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_497_, 0, v___f_496_);
v___x_1262__overap_498_ = lean_panic_fn_borrowed(v___f_497_, v_msg_493_);
lean_dec_ref(v___f_497_);
lean_inc_ref(v___y_494_);
v___x_499_ = lean_apply_2(v___x_1262__overap_498_, v___y_494_, v___y_495_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1___boxed(lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v_msg_500_, v___y_501_, v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
lean_object* v_array_506_; lean_object* v_start_507_; lean_object* v_stop_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_521_; 
v_array_506_ = lean_ctor_get(v_a_504_, 0);
v_start_507_ = lean_ctor_get(v_a_504_, 1);
v_stop_508_ = lean_ctor_get(v_a_504_, 2);
v_isSharedCheck_521_ = !lean_is_exclusive(v_a_504_);
if (v_isSharedCheck_521_ == 0)
{
v___x_510_ = v_a_504_;
v_isShared_511_ = v_isSharedCheck_521_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_stop_508_);
lean_inc(v_start_507_);
lean_inc(v_array_506_);
lean_dec(v_a_504_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_521_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; 
v___x_512_ = lean_nat_dec_lt(v_start_507_, v_stop_508_);
if (v___x_512_ == 0)
{
lean_del_object(v___x_510_);
lean_dec(v_stop_508_);
lean_dec(v_start_507_);
lean_dec_ref(v_array_506_);
return v_b_505_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_513_ = lean_unsigned_to_nat(1u);
v___x_514_ = lean_nat_add(v_start_507_, v___x_513_);
lean_inc_ref(v_array_506_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_514_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_array_506_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_stop_508_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_array_fget(v_array_506_, v_start_507_);
lean_dec(v_start_507_);
lean_dec_ref(v_array_506_);
v___x_518_ = lean_array_push(v_b_505_, v___x_517_);
v_a_504_ = v___x_516_;
v_b_505_ = v___x_518_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfos___closed__3(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_526_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__2));
v___x_527_ = lean_unsigned_to_nat(2u);
v___x_528_ = lean_unsigned_to_nat(93u);
v___x_529_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__1));
v___x_530_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_531_ = l_mkPanicMessageWithDecl(v___x_530_, v___x_529_, v___x_528_, v___x_527_, v___x_526_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos(lean_object* v_pos_532_, lean_object* v_tailPos_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_lineInfos_536_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___f_559_; lean_object* v___f_560_; lean_object* v___y_562_; lean_object* v___x_568_; 
v_lineInfos_536_ = lean_ctor_get(v_a_534_, 4);
v___f_559_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_560_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_568_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_536_, v_pos_532_, v___f_559_, v___f_560_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_570_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_569_);
v___y_562_ = v___x_570_;
goto v___jp_561_;
}
else
{
lean_object* v_val_571_; 
v_val_571_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_val_571_);
lean_dec_ref_known(v___x_568_, 1);
v___y_562_ = v_val_571_;
goto v___jp_561_;
}
v___jp_537_:
{
lean_object* v_fst_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_557_; 
v_fst_540_ = lean_ctor_get(v___y_539_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___y_539_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v___y_539_, 1);
lean_dec(v_unused_558_);
v___x_542_ = v___y_539_;
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_fst_540_);
lean_dec(v___y_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_557_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_add(v_fst_540_, v___x_544_);
lean_dec(v_fst_540_);
lean_inc_ref(v_lineInfos_536_);
v___x_546_ = l_Array_toSubarray___redArg(v_lineInfos_536_, v___y_538_, v___x_545_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_549_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_546_, v___x_548_);
v___x_550_ = lean_array_get_size(v___x_549_);
v___x_551_ = lean_nat_dec_eq(v___x_550_, v___x_547_);
if (v___x_551_ == 0)
{
lean_object* v___x_553_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_a_535_);
lean_ctor_set(v___x_542_, 0, v___x_549_);
v___x_553_ = v___x_542_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_a_535_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___x_549_);
lean_del_object(v___x_542_);
v___x_555_ = lean_obj_once(&l_Lean_Fmt_getLineInfos___closed__3, &l_Lean_Fmt_getLineInfos___closed__3_once, _init_l_Lean_Fmt_getLineInfos___closed__3);
v___x_556_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v___x_555_, v_a_534_, v_a_535_);
return v___x_556_;
}
}
}
v___jp_561_:
{
lean_object* v_fst_563_; lean_object* v___x_564_; 
v_fst_563_ = lean_ctor_get(v___y_562_, 0);
lean_inc(v_fst_563_);
lean_dec_ref(v___y_562_);
v___x_564_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_536_, v_tailPos_533_, v___f_559_, v___f_560_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_566_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_565_);
v___y_538_ = v_fst_563_;
v___y_539_ = v___x_566_;
goto v___jp_537_;
}
else
{
lean_object* v_val_567_; 
v_val_567_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_567_);
lean_dec_ref_known(v___x_564_, 1);
v___y_538_ = v_fst_563_;
v___y_539_ = v_val_567_;
goto v___jp_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos___boxed(lean_object* v_pos_572_, lean_object* v_tailPos_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Fmt_getLineInfos(v_pos_572_, v_tailPos_573_, v_a_574_, v_a_575_);
lean_dec_ref(v_a_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0(lean_object* v_inst_577_, lean_object* v_R_578_, lean_object* v_a_579_, lean_object* v_b_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v_a_579_, v_b_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f(lean_object* v_pos_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_lineInfos_585_; lean_object* v___y_587_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___x_609_; 
v_lineInfos_585_ = lean_ctor_get(v_a_583_, 4);
v___f_607_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_608_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_609_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_585_, v_pos_582_, v___f_607_, v___f_608_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_611_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_610_);
v___y_587_ = v___x_611_;
goto v___jp_586_;
}
else
{
lean_object* v_val_612_; 
v_val_612_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_val_612_);
lean_dec_ref_known(v___x_609_, 1);
v___y_587_ = v_val_612_;
goto v___jp_586_;
}
v___jp_586_:
{
lean_object* v_fst_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_605_; 
v_fst_588_ = lean_ctor_get(v___y_587_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___y_587_);
if (v_isSharedCheck_605_ == 0)
{
lean_object* v_unused_606_; 
v_unused_606_ = lean_ctor_get(v___y_587_, 1);
lean_dec(v_unused_606_);
v___x_590_ = v___y_587_;
v_isShared_591_ = v_isSharedCheck_605_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_fst_588_);
lean_dec(v___y_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_605_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_fst_588_, v___x_592_);
lean_dec(v_fst_588_);
v___x_594_ = lean_array_get_size(v_lineInfos_585_);
v___x_595_ = lean_nat_dec_lt(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_a_584_);
lean_ctor_set(v___x_590_, 0, v___x_596_);
v___x_598_ = v___x_590_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_a_584_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = lean_array_fget_borrowed(v_lineInfos_585_, v___x_593_);
lean_dec(v___x_593_);
lean_inc(v___x_600_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_a_584_);
lean_ctor_set(v___x_590_, 0, v___x_601_);
v___x_603_ = v___x_590_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_a_584_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f___boxed(lean_object* v_pos_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Fmt_getNextLineInfo_x3f(v_pos_613_, v_a_614_, v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(size_t v_sz_617_, size_t v_i_618_, lean_object* v_bs_619_, lean_object* v___y_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_lt(v_i_618_, v_sz_617_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v_bs_619_);
lean_ctor_set(v___x_622_, 1, v___y_620_);
return v___x_622_;
}
else
{
lean_object* v_v_623_; lean_object* v_fst_624_; lean_object* v_snd_625_; lean_object* v___x_626_; lean_object* v_bs_x27_627_; lean_object* v_a_629_; lean_object* v_a_630_; 
v_v_623_ = lean_array_uget_borrowed(v_bs_619_, v_i_618_);
v_fst_624_ = lean_ctor_get(v_v_623_, 0);
lean_inc(v_fst_624_);
v_snd_625_ = lean_ctor_get(v_v_623_, 1);
lean_inc(v_snd_625_);
v___x_626_ = lean_unsigned_to_nat(0u);
v_bs_x27_627_ = lean_array_uset(v_bs_619_, v_i_618_, v___x_626_);
if (lean_obj_tag(v_snd_625_) == 0)
{
v_a_629_ = v_fst_624_;
v_a_630_ = v___y_620_;
goto v___jp_628_;
}
else
{
lean_object* v_val_635_; lean_object* v_doc_636_; lean_object* v_metaData_637_; lean_object* v___x_638_; 
v_val_635_ = lean_ctor_get(v_snd_625_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v_snd_625_, 1);
v_doc_636_ = lean_ctor_get(v_fst_624_, 0);
lean_inc(v_doc_636_);
v_metaData_637_ = lean_ctor_get(v_fst_624_, 1);
lean_inc(v_metaData_637_);
lean_dec(v_fst_624_);
v___x_638_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_636_, v_val_635_, v___y_620_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v_doc_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
v_a_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_638_, 2);
v_doc_641_ = lean_ctor_get(v_a_639_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_a_639_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_a_639_, 1);
lean_dec(v_unused_649_);
v___x_643_ = v_a_639_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_doc_641_);
lean_dec(v_a_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v_metaData_637_);
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_doc_641_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_metaData_637_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
v_a_629_ = v___x_646_;
v_a_630_ = v_a_640_;
goto v___jp_628_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_metaData_637_);
lean_dec_ref(v_bs_x27_627_);
v_a_650_ = lean_ctor_get(v___x_638_, 0);
v_a_651_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_638_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_inc(v_a_650_);
lean_dec(v___x_638_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_650_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
v___jp_628_:
{
size_t v___x_631_; size_t v___x_632_; lean_object* v___x_633_; 
v___x_631_ = ((size_t)1ULL);
v___x_632_ = lean_usize_add(v_i_618_, v___x_631_);
v___x_633_ = lean_array_uset(v_bs_x27_627_, v_i_618_, v_a_629_);
v_i_618_ = v___x_632_;
v_bs_619_ = v___x_633_;
v___y_620_ = v_a_630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg___boxed(lean_object* v_sz_659_, lean_object* v_i_660_, lean_object* v_bs_661_, lean_object* v___y_662_){
_start:
{
size_t v_sz_boxed_663_; size_t v_i_boxed_664_; lean_object* v_res_665_; 
v_sz_boxed_663_ = lean_unbox_usize(v_sz_659_);
lean_dec(v_sz_659_);
v_i_boxed_664_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_res_665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_boxed_663_, v_i_boxed_664_, v_bs_661_, v___y_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace(lean_object* v_stx_666_, lean_object* v_fmtLeading_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_stx_666_);
if (lean_obj_tag(v___x_670_) == 1)
{
lean_object* v_val_671_; lean_object* v___x_672_; 
v_val_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_Syntax_getLeading_x3f(v_val_671_);
if (lean_obj_tag(v___x_672_) == 1)
{
lean_object* v_val_673_; lean_object* v___x_674_; 
v_val_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v___x_672_, 1);
lean_inc_ref(v_a_668_);
v___x_674_ = lean_apply_4(v_fmtLeading_667_, v_val_671_, v_val_673_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v_a_676_; size_t v_sz_677_; size_t v___x_678_; lean_object* v___x_679_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
v_a_676_ = lean_ctor_get(v___x_674_, 1);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_674_, 2);
v_sz_677_ = lean_array_size(v_a_675_);
v___x_678_ = ((size_t)0ULL);
v___x_679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_677_, v___x_678_, v_a_675_, v_a_676_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_689_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_a_681_ = lean_ctor_get(v___x_679_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_689_ == 0)
{
v___x_683_ = v___x_679_;
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_689_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = l_Lean_Fmt_TaggedDoc_join(v_a_680_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_685_);
v___x_687_ = v___x_683_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_a_681_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v_a_690_; lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_690_ = lean_ctor_get(v___x_679_, 0);
v_a_691_ = lean_ctor_get(v___x_679_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_679_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_inc(v_a_690_);
lean_dec(v___x_679_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_690_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_a_699_ = lean_ctor_get(v___x_674_, 0);
v_a_700_ = lean_ctor_get(v___x_674_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_674_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_inc(v_a_699_);
lean_dec(v___x_674_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_699_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v___x_672_);
lean_dec(v_val_671_);
lean_dec_ref(v_fmtLeading_667_);
v___x_708_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_a_669_);
return v___x_709_;
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v___x_670_);
lean_dec_ref(v_fmtLeading_667_);
v___x_710_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_a_669_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace___boxed(lean_object* v_stx_712_, lean_object* v_fmtLeading_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_712_, v_fmtLeading_713_, v_a_714_, v_a_715_);
lean_dec_ref(v_a_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(size_t v_sz_717_, size_t v_i_718_, lean_object* v_bs_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_717_, v_i_718_, v_bs_719_, v___y_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___boxed(lean_object* v_sz_723_, lean_object* v_i_724_, lean_object* v_bs_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
size_t v_sz_boxed_728_; size_t v_i_boxed_729_; lean_object* v_res_730_; 
v_sz_boxed_728_ = lean_unbox_usize(v_sz_723_);
lean_dec(v_sz_723_);
v_i_boxed_729_ = lean_unbox_usize(v_i_724_);
lean_dec(v_i_724_);
v_res_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(v_sz_boxed_728_, v_i_boxed_729_, v_bs_725_, v___y_726_, v___y_727_);
lean_dec_ref(v___y_726_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace(lean_object* v_stx_731_, lean_object* v_fmtTrailing_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v_stx_731_);
if (lean_obj_tag(v___x_735_) == 1)
{
lean_object* v_val_736_; lean_object* v___x_737_; 
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_Syntax_getTrailing_x3f(v_val_736_);
if (lean_obj_tag(v___x_737_) == 1)
{
lean_object* v_val_738_; lean_object* v___x_739_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___x_737_, 1);
lean_inc_ref(v_a_733_);
v___x_739_ = lean_apply_4(v_fmtTrailing_732_, v_val_736_, v_val_738_, v_a_733_, v_a_734_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_a_741_; size_t v_sz_742_; size_t v___x_743_; lean_object* v___x_744_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
v_a_741_ = lean_ctor_get(v___x_739_, 1);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_739_, 2);
v_sz_742_ = lean_array_size(v_a_740_);
v___x_743_ = ((size_t)0ULL);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_742_, v___x_743_, v_a_740_, v_a_741_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_a_746_ = lean_ctor_get(v___x_744_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_754_ == 0)
{
v___x_748_ = v___x_744_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_Lean_Fmt_TaggedDoc_join(v_a_745_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_a_746_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
lean_object* v_a_755_; lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
v_a_755_ = lean_ctor_get(v___x_744_, 0);
v_a_756_ = lean_ctor_get(v___x_744_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_744_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_inc(v_a_755_);
lean_dec(v___x_744_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_755_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_764_ = lean_ctor_get(v___x_739_, 0);
v_a_765_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_739_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_inc(v_a_764_);
lean_dec(v___x_739_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_764_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec(v___x_737_);
lean_dec(v_val_736_);
lean_dec_ref(v_fmtTrailing_732_);
v___x_773_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v_a_734_);
return v___x_774_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v___x_735_);
lean_dec_ref(v_fmtTrailing_732_);
v___x_775_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v_a_734_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace___boxed(lean_object* v_stx_777_, lean_object* v_fmtTrailing_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_777_, v_fmtTrailing_778_, v_a_779_, v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(lean_object* v_env_782_, lean_object* v_opts_783_, lean_object* v_kind_784_){
_start:
{
uint8_t v___x_785_; lean_object* v___x_786_; 
v___x_785_ = 1;
v___x_786_ = l_Lean_Environment_evalConst___redArg(v_env_782_, v_opts_783_, v_kind_784_, v___x_785_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___x_787_; 
lean_dec_ref_known(v___x_786_, 1);
v___x_787_ = lean_box(0);
return v___x_787_;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
v_a_788_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_786_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1___boxed(lean_object* v_env_796_, lean_object* v_opts_797_, lean_object* v_kind_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(v_env_796_, v_opts_797_, v_kind_798_);
lean_dec(v_kind_798_);
lean_dec_ref(v_opts_797_);
lean_dec_ref(v_env_796_);
return v_res_799_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_box(0);
v___x_801_ = lean_unsigned_to_nat(16u);
v___x_802_ = lean_mk_array(v___x_801_, v___x_800_);
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(lean_object* v_env_817_, lean_object* v_opts_818_, lean_object* v_kind_819_){
_start:
{
uint8_t v___x_820_; lean_object* v___y_822_; lean_object* v___y_823_; uint8_t v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; lean_object* v___y_840_; uint8_t v___y_841_; lean_object* v___x_889_; 
v___x_820_ = 0;
lean_inc(v_kind_819_);
lean_inc_ref(v_env_817_);
v___x_889_ = l_Lean_Environment_find_x3f(v_env_817_, v_kind_819_, v___x_820_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_890_; 
lean_dec(v_kind_819_);
lean_dec_ref(v_env_817_);
v___x_890_ = lean_box(0);
return v___x_890_;
}
else
{
lean_object* v_val_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_val_891_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_891_);
lean_dec_ref_known(v___x_889_, 1);
v___x_892_ = l_Lean_ConstantInfo_type(v_val_891_);
lean_dec(v_val_891_);
v___x_893_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_894_ = l_Lean_Expr_isConstOf(v___x_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_896_ = l_Lean_Expr_isConstOf(v___x_892_, v___x_895_);
lean_dec_ref(v___x_892_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec(v_kind_819_);
lean_dec_ref(v_env_817_);
v___x_897_ = lean_box(0);
return v___x_897_;
}
else
{
goto v___jp_854_;
}
}
else
{
lean_dec_ref(v___x_892_);
goto v___jp_854_;
}
}
v___jp_821_:
{
lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_add(v___y_823_, v___x_827_);
lean_dec(v___y_823_);
v___x_829_ = lean_nat_dec_eq(v___x_828_, v___y_825_);
lean_dec(v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v___y_826_);
lean_dec(v___y_825_);
lean_dec(v___y_822_);
v___x_830_ = lean_box(0);
return v___x_830_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = lean_nat_dec_eq(v___y_825_, v___y_822_);
lean_dec(v___y_822_);
lean_dec(v___y_825_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v___y_826_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_834_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_834_, 0, v___y_826_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*2, v___y_824_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*2 + 1, v___x_820_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
v___jp_836_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_inc(v___y_837_);
lean_inc(v___y_840_);
lean_inc(v___y_838_);
v___x_842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_842_, 0, v___y_838_);
lean_ctor_set(v___x_842_, 1, v___y_840_);
lean_ctor_set(v___x_842_, 2, v___y_837_);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
if (v___y_841_ == 0)
{
uint8_t v___x_844_; 
v___x_844_ = lean_nat_dec_eq(v___y_838_, v___y_837_);
if (v___x_844_ == 0)
{
v___y_822_ = v___y_837_;
v___y_823_ = v___y_838_;
v___y_824_ = v___y_839_;
v___y_825_ = v___y_840_;
v___y_826_ = v___x_843_;
goto v___jp_821_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_nat_add(v___y_837_, v___x_845_);
v___x_847_ = lean_nat_dec_eq(v___y_840_, v___x_846_);
lean_dec(v___x_846_);
if (v___x_847_ == 0)
{
v___y_822_ = v___y_837_;
v___y_823_ = v___y_838_;
v___y_824_ = v___y_839_;
v___y_825_ = v___y_840_;
v___y_826_ = v___x_843_;
goto v___jp_821_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v___y_840_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
v___x_848_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_849_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_849_, 0, v___x_843_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*2, v___x_820_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*2 + 1, v___x_820_);
v___x_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v___y_840_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
v___x_851_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_852_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_852_, 0, v___x_843_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*2, v___x_820_);
lean_ctor_set_uint8(v___x_852_, sizeof(void*)*2 + 1, v___x_820_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
return v___x_853_;
}
}
v___jp_854_:
{
uint8_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = 1;
v___x_856_ = l_Lean_Environment_evalConst___redArg(v_env_817_, v_opts_818_, v_kind_819_, v___x_855_);
lean_dec(v_kind_819_);
lean_dec_ref(v_env_817_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_857_; 
lean_dec_ref_known(v___x_856_, 1);
v___x_857_ = lean_box(0);
return v___x_857_;
}
else
{
lean_object* v_a_858_; 
v_a_858_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_856_, 1);
if (lean_obj_tag(v_a_858_) == 4)
{
lean_object* v_p_859_; 
v_p_859_ = lean_ctor_get(v_a_858_, 3);
lean_inc_ref(v_p_859_);
if (lean_obj_tag(v_p_859_) == 2)
{
lean_object* v_name_860_; 
v_name_860_ = lean_ctor_get(v_p_859_, 0);
lean_inc(v_name_860_);
if (lean_obj_tag(v_name_860_) == 1)
{
lean_object* v_pre_861_; 
v_pre_861_ = lean_ctor_get(v_name_860_, 0);
if (lean_obj_tag(v_pre_861_) == 0)
{
lean_object* v_prec_862_; lean_object* v_lhsPrec_863_; lean_object* v_p_u2081_864_; lean_object* v_p_u2082_865_; lean_object* v_str_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_prec_862_ = lean_ctor_get(v_a_858_, 1);
lean_inc(v_prec_862_);
v_lhsPrec_863_ = lean_ctor_get(v_a_858_, 2);
lean_inc(v_lhsPrec_863_);
lean_dec_ref_known(v_a_858_, 4);
v_p_u2081_864_ = lean_ctor_get(v_p_859_, 1);
lean_inc_ref(v_p_u2081_864_);
v_p_u2082_865_ = lean_ctor_get(v_p_859_, 2);
lean_inc_ref(v_p_u2082_865_);
lean_dec_ref_known(v_p_859_, 3);
v_str_866_ = lean_ctor_get(v_name_860_, 1);
lean_inc_ref(v_str_866_);
lean_dec_ref_known(v_name_860_, 2);
v___x_867_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_868_ = lean_string_dec_eq(v_str_866_, v___x_867_);
lean_dec_ref(v_str_866_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec_ref(v_p_u2082_865_);
lean_dec_ref(v_p_u2081_864_);
lean_dec(v_lhsPrec_863_);
lean_dec(v_prec_862_);
v___x_869_ = lean_box(0);
return v___x_869_;
}
else
{
if (lean_obj_tag(v_p_u2081_864_) == 5)
{
lean_dec_ref_known(v_p_u2081_864_, 1);
if (lean_obj_tag(v_p_u2082_865_) == 7)
{
lean_object* v_catName_870_; 
v_catName_870_ = lean_ctor_get(v_p_u2082_865_, 0);
lean_inc(v_catName_870_);
if (lean_obj_tag(v_catName_870_) == 1)
{
lean_object* v_pre_871_; 
v_pre_871_ = lean_ctor_get(v_catName_870_, 0);
if (lean_obj_tag(v_pre_871_) == 0)
{
lean_object* v_rbp_872_; lean_object* v_str_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_rbp_872_ = lean_ctor_get(v_p_u2082_865_, 1);
lean_inc(v_rbp_872_);
lean_dec_ref_known(v_p_u2082_865_, 2);
v_str_873_ = lean_ctor_get(v_catName_870_, 1);
lean_inc_ref(v_str_873_);
lean_dec_ref_known(v_catName_870_, 2);
v___x_874_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_875_ = lean_string_dec_eq(v_str_873_, v___x_874_);
lean_dec_ref(v_str_873_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec(v_rbp_872_);
lean_dec(v_lhsPrec_863_);
lean_dec(v_prec_862_);
v___x_876_ = lean_box(0);
return v___x_876_;
}
else
{
uint8_t v___x_877_; 
v___x_877_ = lean_nat_dec_eq(v_prec_862_, v_lhsPrec_863_);
if (v___x_877_ == 0)
{
v___y_837_ = v_rbp_872_;
v___y_838_ = v_prec_862_;
v___y_839_ = v___x_875_;
v___y_840_ = v_lhsPrec_863_;
v___y_841_ = v___x_820_;
goto v___jp_836_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_nat_add(v_lhsPrec_863_, v___x_878_);
v___x_880_ = lean_nat_dec_eq(v___x_879_, v_rbp_872_);
lean_dec(v___x_879_);
v___y_837_ = v_rbp_872_;
v___y_838_ = v_prec_862_;
v___y_839_ = v___x_875_;
v___y_840_ = v_lhsPrec_863_;
v___y_841_ = v___x_880_;
goto v___jp_836_;
}
}
}
else
{
lean_object* v___x_881_; 
lean_dec_ref_known(v_catName_870_, 2);
lean_dec_ref_known(v_p_u2082_865_, 2);
lean_dec(v_lhsPrec_863_);
lean_dec(v_prec_862_);
v___x_881_ = lean_box(0);
return v___x_881_;
}
}
else
{
lean_object* v___x_882_; 
lean_dec_ref_known(v_p_u2082_865_, 2);
lean_dec(v_catName_870_);
lean_dec(v_lhsPrec_863_);
lean_dec(v_prec_862_);
v___x_882_ = lean_box(0);
return v___x_882_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec_ref(v_p_u2082_865_);
lean_dec(v_lhsPrec_863_);
lean_dec(v_prec_862_);
v___x_883_ = lean_box(0);
return v___x_883_;
}
}
else
{
lean_object* v___x_884_; 
lean_dec_ref(v_p_u2082_865_);
lean_dec_ref(v_p_u2081_864_);
lean_dec(v_lhsPrec_863_);
lean_dec(v_prec_862_);
v___x_884_ = lean_box(0);
return v___x_884_;
}
}
}
else
{
lean_object* v___x_885_; 
lean_dec_ref_known(v_name_860_, 2);
lean_dec_ref_known(v_p_859_, 3);
lean_dec_ref_known(v_a_858_, 4);
v___x_885_ = lean_box(0);
return v___x_885_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v_name_860_);
lean_dec_ref_known(v_p_859_, 3);
lean_dec_ref_known(v_a_858_, 4);
v___x_886_ = lean_box(0);
return v___x_886_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec_ref(v_p_859_);
lean_dec_ref_known(v_a_858_, 4);
v___x_887_ = lean_box(0);
return v___x_887_;
}
}
else
{
lean_object* v___x_888_; 
lean_dec(v_a_858_);
v___x_888_ = lean_box(0);
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___boxed(lean_object* v_env_898_, lean_object* v_opts_899_, lean_object* v_kind_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_898_, v_opts_899_, v_kind_900_);
lean_dec_ref(v_opts_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(lean_object* v_env_902_, lean_object* v_opts_903_, lean_object* v_kind_904_){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = l_Lean_Fmt_infixFmtAttribute;
lean_inc_ref(v_env_902_);
v___x_906_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_905_, v_env_902_, v_kind_904_);
v___x_907_ = l_List_head_x3f___redArg(v___x_906_);
lean_dec(v___x_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_908_; 
v___x_908_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_902_, v_opts_903_, v_kind_904_);
return v___x_908_;
}
else
{
lean_dec(v_kind_904_);
lean_dec_ref(v_env_902_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f___boxed(lean_object* v_env_909_, lean_object* v_opts_910_, lean_object* v_kind_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_909_, v_opts_910_, v_kind_911_);
lean_dec_ref(v_opts_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(lean_object* v_env_913_, lean_object* v_opts_914_, lean_object* v_kind_915_){
_start:
{
uint8_t v___x_916_; lean_object* v___x_917_; 
v___x_916_ = 1;
v___x_917_ = l_Lean_Environment_evalConst___redArg(v_env_913_, v_opts_914_, v_kind_915_, v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; 
lean_dec_ref_known(v___x_917_, 1);
v___x_918_ = lean_box(0);
return v___x_918_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_a_919_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_917_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1___boxed(lean_object* v_env_927_, lean_object* v_opts_928_, lean_object* v_kind_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(v_env_927_, v_opts_928_, v_kind_929_);
lean_dec(v_kind_929_);
lean_dec_ref(v_opts_928_);
lean_dec_ref(v_env_927_);
return v_res_930_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(lean_object* v_env_931_, lean_object* v_opts_932_, lean_object* v_kind_933_){
_start:
{
uint8_t v___x_934_; lean_object* v___x_935_; 
v___x_934_ = 0;
lean_inc(v_kind_933_);
lean_inc_ref(v_env_931_);
v___x_935_ = l_Lean_Environment_find_x3f(v_env_931_, v_kind_933_, v___x_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_dec(v_kind_933_);
lean_dec_ref(v_env_931_);
return v___x_934_;
}
else
{
lean_object* v_val_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_val_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_935_, 1);
v___x_937_ = l_Lean_ConstantInfo_type(v_val_936_);
lean_dec(v_val_936_);
v___x_938_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_939_ = l_Lean_Expr_isConstOf(v___x_937_, v___x_938_);
lean_dec_ref(v___x_937_);
if (v___x_939_ == 0)
{
lean_dec(v_kind_933_);
lean_dec_ref(v_env_931_);
return v___x_939_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Environment_evalConst___redArg(v_env_931_, v_opts_932_, v_kind_933_, v___x_939_);
lean_dec(v_kind_933_);
lean_dec_ref(v_env_931_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_dec_ref_known(v___x_940_, 1);
return v___x_934_;
}
else
{
lean_object* v_a_941_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
if (lean_obj_tag(v_a_941_) == 3)
{
lean_object* v_p_942_; 
v_p_942_ = lean_ctor_get(v_a_941_, 2);
lean_inc_ref(v_p_942_);
if (lean_obj_tag(v_p_942_) == 2)
{
lean_object* v_name_943_; 
v_name_943_ = lean_ctor_get(v_p_942_, 0);
lean_inc(v_name_943_);
if (lean_obj_tag(v_name_943_) == 1)
{
lean_object* v_pre_944_; 
v_pre_944_ = lean_ctor_get(v_name_943_, 0);
if (lean_obj_tag(v_pre_944_) == 0)
{
lean_object* v_prec_945_; lean_object* v_p_u2081_946_; lean_object* v_p_u2082_947_; lean_object* v_str_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_prec_945_ = lean_ctor_get(v_a_941_, 1);
lean_inc(v_prec_945_);
lean_dec_ref_known(v_a_941_, 3);
v_p_u2081_946_ = lean_ctor_get(v_p_942_, 1);
lean_inc_ref(v_p_u2081_946_);
v_p_u2082_947_ = lean_ctor_get(v_p_942_, 2);
lean_inc_ref(v_p_u2082_947_);
lean_dec_ref_known(v_p_942_, 3);
v_str_948_ = lean_ctor_get(v_name_943_, 1);
lean_inc_ref(v_str_948_);
lean_dec_ref_known(v_name_943_, 2);
v___x_949_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_950_ = lean_string_dec_eq(v_str_948_, v___x_949_);
lean_dec_ref(v_str_948_);
if (v___x_950_ == 0)
{
lean_dec_ref(v_p_u2082_947_);
lean_dec_ref(v_p_u2081_946_);
lean_dec(v_prec_945_);
return v___x_950_;
}
else
{
if (lean_obj_tag(v_p_u2081_946_) == 5)
{
lean_dec_ref_known(v_p_u2081_946_, 1);
if (lean_obj_tag(v_p_u2082_947_) == 7)
{
lean_object* v_catName_951_; 
v_catName_951_ = lean_ctor_get(v_p_u2082_947_, 0);
lean_inc(v_catName_951_);
if (lean_obj_tag(v_catName_951_) == 1)
{
lean_object* v_pre_952_; 
v_pre_952_ = lean_ctor_get(v_catName_951_, 0);
if (lean_obj_tag(v_pre_952_) == 0)
{
lean_object* v_rbp_953_; lean_object* v_str_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_rbp_953_ = lean_ctor_get(v_p_u2082_947_, 1);
lean_inc(v_rbp_953_);
lean_dec_ref_known(v_p_u2082_947_, 2);
v_str_954_ = lean_ctor_get(v_catName_951_, 1);
lean_inc_ref(v_str_954_);
lean_dec_ref_known(v_catName_951_, 2);
v___x_955_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_956_ = lean_string_dec_eq(v_str_954_, v___x_955_);
lean_dec_ref(v_str_954_);
if (v___x_956_ == 0)
{
lean_dec(v_rbp_953_);
lean_dec(v_prec_945_);
return v___x_956_;
}
else
{
uint8_t v___x_957_; 
v___x_957_ = lean_nat_dec_eq(v_prec_945_, v_rbp_953_);
lean_dec(v_rbp_953_);
lean_dec(v_prec_945_);
return v___x_957_;
}
}
else
{
lean_dec_ref_known(v_catName_951_, 2);
lean_dec_ref_known(v_p_u2082_947_, 2);
lean_dec(v_prec_945_);
return v___x_934_;
}
}
else
{
lean_dec(v_catName_951_);
lean_dec_ref_known(v_p_u2082_947_, 2);
lean_dec(v_prec_945_);
return v___x_934_;
}
}
else
{
lean_dec_ref(v_p_u2082_947_);
lean_dec(v_prec_945_);
return v___x_934_;
}
}
else
{
lean_dec_ref(v_p_u2082_947_);
lean_dec_ref(v_p_u2081_946_);
lean_dec(v_prec_945_);
return v___x_934_;
}
}
}
else
{
lean_dec_ref_known(v_name_943_, 2);
lean_dec_ref_known(v_p_942_, 3);
lean_dec_ref_known(v_a_941_, 3);
return v___x_934_;
}
}
else
{
lean_dec_ref_known(v_p_942_, 3);
lean_dec(v_name_943_);
lean_dec_ref_known(v_a_941_, 3);
return v___x_934_;
}
}
else
{
lean_dec_ref(v_p_942_);
lean_dec_ref_known(v_a_941_, 3);
return v___x_934_;
}
}
else
{
lean_dec(v_a_941_);
return v___x_934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter___boxed(lean_object* v_env_958_, lean_object* v_opts_959_, lean_object* v_kind_960_){
_start:
{
uint8_t v_res_961_; lean_object* v_r_962_; 
v_res_961_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_958_, v_opts_959_, v_kind_960_);
lean_dec_ref(v_opts_959_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(lean_object* v_env_963_, lean_object* v_opts_964_, lean_object* v_kind_965_){
_start:
{
uint8_t v___x_966_; lean_object* v___x_967_; 
v___x_966_ = 1;
v___x_967_ = l_Lean_Environment_evalConst___redArg(v_env_963_, v_opts_964_, v_kind_965_, v___x_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_968_; 
lean_dec_ref_known(v___x_967_, 1);
v___x_968_ = lean_box(0);
return v___x_968_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_969_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_967_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_967_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1___boxed(lean_object* v_env_977_, lean_object* v_opts_978_, lean_object* v_kind_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(v_env_977_, v_opts_978_, v_kind_979_);
lean_dec(v_kind_979_);
lean_dec_ref(v_opts_978_);
lean_dec_ref(v_env_977_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(lean_object* v_env_981_, lean_object* v_opts_982_, lean_object* v_kind_983_){
_start:
{
uint8_t v___x_984_; lean_object* v___x_985_; 
v___x_984_ = 0;
lean_inc(v_kind_983_);
lean_inc_ref(v_env_981_);
v___x_985_ = l_Lean_Environment_find_x3f(v_env_981_, v_kind_983_, v___x_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_dec(v_kind_983_);
lean_dec_ref(v_env_981_);
return v___x_984_;
}
else
{
lean_object* v_val_986_; lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_val_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_val_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = l_Lean_ConstantInfo_type(v_val_986_);
lean_dec(v_val_986_);
v___x_988_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_989_ = l_Lean_Expr_isConstOf(v___x_987_, v___x_988_);
lean_dec_ref(v___x_987_);
if (v___x_989_ == 0)
{
lean_dec(v_kind_983_);
lean_dec_ref(v_env_981_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Environment_evalConst___redArg(v_env_981_, v_opts_982_, v_kind_983_, v___x_989_);
lean_dec(v_kind_983_);
lean_dec_ref(v_env_981_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_dec_ref_known(v___x_990_, 1);
return v___x_984_;
}
else
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
if (lean_obj_tag(v_a_991_) == 4)
{
lean_object* v_p_992_; 
v_p_992_ = lean_ctor_get(v_a_991_, 3);
if (lean_obj_tag(v_p_992_) == 5)
{
lean_object* v_prec_993_; lean_object* v_lhsPrec_994_; uint8_t v___x_995_; 
v_prec_993_ = lean_ctor_get(v_a_991_, 1);
lean_inc(v_prec_993_);
v_lhsPrec_994_ = lean_ctor_get(v_a_991_, 2);
lean_inc(v_lhsPrec_994_);
lean_dec_ref_known(v_a_991_, 4);
v___x_995_ = lean_nat_dec_eq(v_prec_993_, v_lhsPrec_994_);
lean_dec(v_lhsPrec_994_);
lean_dec(v_prec_993_);
return v___x_995_;
}
else
{
lean_dec_ref_known(v_a_991_, 4);
return v___x_984_;
}
}
else
{
lean_dec(v_a_991_);
return v___x_984_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter___boxed(lean_object* v_env_996_, lean_object* v_opts_997_, lean_object* v_kind_998_){
_start:
{
uint8_t v_res_999_; lean_object* v_r_1000_; 
v_res_999_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_996_, v_opts_997_, v_kind_998_);
lean_dec_ref(v_opts_997_);
v_r_1000_ = lean_box(v_res_999_);
return v_r_1000_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(lean_object* v_a_1127_, lean_object* v_as_1128_, size_t v_i_1129_, size_t v_stop_1130_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_usize_dec_eq(v_i_1129_, v_stop_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_array_uget_borrowed(v_as_1128_, v_i_1129_);
v___x_1133_ = lean_name_eq(v_a_1127_, v___x_1132_);
if (v___x_1133_ == 0)
{
size_t v___x_1134_; size_t v___x_1135_; 
v___x_1134_ = ((size_t)1ULL);
v___x_1135_ = lean_usize_add(v_i_1129_, v___x_1134_);
v_i_1129_ = v___x_1135_;
goto _start;
}
else
{
return v___x_1133_;
}
}
else
{
uint8_t v___x_1137_; 
v___x_1137_ = 0;
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0___boxed(lean_object* v_a_1138_, lean_object* v_as_1139_, lean_object* v_i_1140_, lean_object* v_stop_1141_){
_start:
{
size_t v_i_boxed_1142_; size_t v_stop_boxed_1143_; uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_i_boxed_1142_ = lean_unbox_usize(v_i_1140_);
lean_dec(v_i_1140_);
v_stop_boxed_1143_ = lean_unbox_usize(v_stop_1141_);
lean_dec(v_stop_1141_);
v_res_1144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1138_, v_as_1139_, v_i_boxed_1142_, v_stop_boxed_1143_);
lean_dec_ref(v_as_1139_);
lean_dec(v_a_1138_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(lean_object* v_as_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_array_get_size(v_as_1146_);
v___x_1150_ = lean_nat_dec_lt(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
return v___x_1150_;
}
else
{
size_t v___x_1151_; size_t v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = lean_usize_of_nat(v___x_1149_);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1147_, v_as_1146_, v___x_1151_, v___x_1152_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0___boxed(lean_object* v_as_1154_, lean_object* v_a_1155_){
_start:
{
uint8_t v_res_1156_; lean_object* v_r_1157_; 
v_res_1156_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v_as_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_as_1154_);
v_r_1157_ = lean_box(v_res_1156_);
return v_r_1157_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(lean_object* v_x_1163_){
_start:
{
switch(lean_obj_tag(v_x_1163_))
{
case 5:
{
uint8_t v___x_1164_; 
v___x_1164_ = 1;
return v___x_1164_;
}
case 6:
{
uint8_t v___x_1165_; 
v___x_1165_ = 1;
return v___x_1165_;
}
case 12:
{
uint8_t v___x_1166_; 
v___x_1166_ = 1;
return v___x_1166_;
}
case 0:
{
lean_object* v_name_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_name_1167_ = lean_ctor_get(v_x_1163_, 0);
v___x_1168_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases));
v___x_1169_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1168_, v_name_1167_);
return v___x_1169_;
}
case 1:
{
lean_object* v_name_1170_; lean_object* v_p_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_name_1170_ = lean_ctor_get(v_x_1163_, 0);
v_p_1171_ = lean_ctor_get(v_x_1163_, 1);
v___x_1172_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases));
v___x_1173_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1172_, v_name_1170_);
if (v___x_1173_ == 0)
{
return v___x_1173_;
}
else
{
v_x_1163_ = v_p_1171_;
goto _start;
}
}
case 2:
{
lean_object* v_name_1175_; lean_object* v_p_u2081_1176_; lean_object* v_p_u2082_1177_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_name_1175_ = lean_ctor_get(v_x_1163_, 0);
v_p_u2081_1176_ = lean_ctor_get(v_x_1163_, 1);
v_p_u2082_1177_ = lean_ctor_get(v_x_1163_, 2);
v___x_1181_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0));
v___x_1182_ = lean_name_eq(v_name_1175_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2));
v___x_1184_ = lean_name_eq(v_name_1175_, v___x_1183_);
if (v___x_1184_ == 0)
{
return v___x_1184_;
}
else
{
goto v___jp_1178_;
}
}
else
{
goto v___jp_1178_;
}
v___jp_1178_:
{
uint8_t v___x_1179_; 
v___x_1179_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_p_u2081_1176_);
if (v___x_1179_ == 0)
{
return v___x_1179_;
}
else
{
v_x_1163_ = v_p_u2082_1177_;
goto _start;
}
}
}
case 3:
{
lean_object* v_p_1185_; 
v_p_1185_ = lean_ctor_get(v_x_1163_, 2);
v_x_1163_ = v_p_1185_;
goto _start;
}
case 9:
{
lean_object* v_p_1187_; 
v_p_1187_ = lean_ctor_get(v_x_1163_, 2);
v_x_1163_ = v_p_1187_;
goto _start;
}
default: 
{
uint8_t v___x_1189_; 
v___x_1189_ = 0;
return v___x_1189_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___boxed(lean_object* v_x_1190_){
_start:
{
uint8_t v_res_1191_; lean_object* v_r_1192_; 
v_res_1191_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_x_1190_);
lean_dec_ref(v_x_1190_);
v_r_1192_ = lean_box(v_res_1191_);
return v_r_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(lean_object* v_env_1193_, lean_object* v_opts_1194_, lean_object* v_kind_1195_){
_start:
{
uint8_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = 1;
v___x_1197_ = l_Lean_Environment_evalConst___redArg(v_env_1193_, v_opts_1194_, v_kind_1195_, v___x_1196_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref_known(v___x_1197_, 1);
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v_a_1199_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1197_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1___boxed(lean_object* v_env_1207_, lean_object* v_opts_1208_, lean_object* v_kind_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(v_env_1207_, v_opts_1208_, v_kind_1209_);
lean_dec(v_kind_1209_);
lean_dec_ref(v_opts_1208_);
lean_dec_ref(v_env_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(lean_object* v_env_1211_, lean_object* v_opts_1212_, lean_object* v_kind_1213_){
_start:
{
uint8_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = 0;
lean_inc(v_kind_1213_);
lean_inc_ref(v_env_1211_);
v___x_1215_ = l_Lean_Environment_find_x3f(v_env_1211_, v_kind_1213_, v___x_1214_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_dec(v_kind_1213_);
lean_dec_ref(v_env_1211_);
return v___x_1214_;
}
else
{
lean_object* v_val_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v_val_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_val_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1217_ = l_Lean_ConstantInfo_type(v_val_1216_);
lean_dec(v_val_1216_);
v___x_1218_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_1219_ = l_Lean_Expr_isConstOf(v___x_1217_, v___x_1218_);
lean_dec_ref(v___x_1217_);
if (v___x_1219_ == 0)
{
lean_dec(v_kind_1213_);
lean_dec_ref(v_env_1211_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Environment_evalConst___redArg(v_env_1211_, v_opts_1212_, v_kind_1213_, v___x_1219_);
lean_dec(v_kind_1213_);
lean_dec_ref(v_env_1211_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_dec_ref_known(v___x_1220_, 1);
return v___x_1214_;
}
else
{
lean_object* v_a_1221_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
if (lean_obj_tag(v_a_1221_) == 4)
{
lean_dec_ref_known(v_a_1221_, 4);
return v___x_1214_;
}
else
{
uint8_t v___x_1222_; 
v___x_1222_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_a_1221_);
lean_dec(v_a_1221_);
return v___x_1222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter___boxed(lean_object* v_env_1223_, lean_object* v_opts_1224_, lean_object* v_kind_1225_){
_start:
{
uint8_t v_res_1226_; lean_object* v_r_1227_; 
v_res_1226_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_1223_, v_opts_1224_, v_kind_1225_);
lean_dec_ref(v_opts_1224_);
v_r_1227_ = lean_box(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f(lean_object* v_env_1228_, lean_object* v_kind_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1231_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1230_, v_env_1228_, v_kind_1229_);
v___x_1232_ = l_List_head_x3f___redArg(v___x_1231_);
lean_dec(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f___boxed(lean_object* v_env_1233_, lean_object* v_kind_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Fmt_getConditionalFormatter_x3f(v_env_1233_, v_kind_1234_);
lean_dec(v_kind_1234_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f(lean_object* v_env_1236_, lean_object* v_kind_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_1239_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1238_, v_env_1236_, v_kind_1237_);
v___x_1240_ = l_List_head_x3f___redArg(v___x_1239_);
lean_dec(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f___boxed(lean_object* v_env_1241_, lean_object* v_kind_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1241_, v_kind_1242_);
lean_dec(v_kind_1242_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(lean_object* v_msg_1258_){
_start:
{
lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___f_1259_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0));
v___f_1260_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1));
v___f_1261_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2));
v___f_1262_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3));
v___f_1263_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4));
v___f_1264_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5));
v___f_1265_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6));
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___f_1259_);
lean_ctor_set(v___x_1266_, 1, v___f_1260_);
v___x_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___f_1261_);
lean_ctor_set(v___x_1267_, 2, v___f_1262_);
lean_ctor_set(v___x_1267_, 3, v___f_1263_);
lean_ctor_set(v___x_1267_, 4, v___f_1264_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v___f_1265_);
v___x_1269_ = ((lean_object*)(l_Lean_Fmt_instInhabitedQuantifierChain_default));
v___x_1270_ = l_instInhabitedOfMonad___redArg(v___x_1268_, v___x_1269_);
v___x_1271_ = lean_panic_fn_borrowed(v___x_1270_, v_msg_1258_);
lean_dec(v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(lean_object* v_env_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_snd_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1337_; 
v_snd_1274_ = lean_ctor_get(v_a_1273_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_a_1273_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_a_1273_, 0);
lean_dec(v_unused_1338_);
v___x_1276_ = v_a_1273_;
v_isShared_1277_ = v_isSharedCheck_1337_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_snd_1274_);
lean_dec(v_a_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1337_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_snd_1278_; lean_object* v_fst_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1336_; 
v_snd_1278_ = lean_ctor_get(v_snd_1274_, 1);
v_fst_1279_ = lean_ctor_get(v_snd_1274_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_snd_1274_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1281_ = v_snd_1274_;
v_isShared_1282_ = v_isSharedCheck_1336_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1278_);
lean_inc(v_fst_1279_);
lean_dec(v_snd_1274_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1336_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
if (lean_obj_tag(v_fst_1279_) == 1)
{
lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1318_; 
v_fst_1283_ = lean_ctor_get(v_snd_1278_, 0);
v_snd_1284_ = lean_ctor_get(v_snd_1278_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_snd_1278_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1286_ = v_snd_1278_;
v_isShared_1287_ = v_isSharedCheck_1318_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_snd_1284_);
lean_inc(v_fst_1283_);
lean_dec(v_snd_1278_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1318_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_val_1288_; lean_object* v___x_1289_; 
v_val_1288_ = lean_ctor_get(v_fst_1279_, 0);
lean_inc(v_val_1288_);
lean_inc(v_fst_1283_);
v___x_1289_ = lean_apply_1(v_val_1288_, v_fst_1283_);
if (lean_obj_tag(v___x_1289_) == 1)
{
lean_object* v_val_1290_; lean_object* v_toQuantifierHeadComponents_1291_; lean_object* v_body_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
lean_dec_ref_known(v_fst_1279_, 1);
lean_dec(v_fst_1283_);
v_val_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v_toQuantifierHeadComponents_1291_ = lean_ctor_get(v_val_1290_, 0);
lean_inc_ref(v_toQuantifierHeadComponents_1291_);
v_body_1292_ = lean_ctor_get(v_val_1290_, 1);
lean_inc_n(v_body_1292_, 2);
lean_dec(v_val_1290_);
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_array_push(v_snd_1284_, v_toQuantifierHeadComponents_1291_);
v___x_1295_ = l_Lean_Syntax_getKind(v_body_1292_);
lean_inc_ref(v_env_1272_);
v___x_1296_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1272_, v___x_1295_);
lean_dec(v___x_1295_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v___x_1294_);
lean_ctor_set(v___x_1286_, 0, v_body_1292_);
v___x_1298_ = v___x_1286_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_body_1292_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___x_1294_);
v___x_1298_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1300_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1298_);
lean_ctor_set(v___x_1281_, 0, v___x_1296_);
v___x_1300_ = v___x_1281_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1302_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1300_);
lean_ctor_set(v___x_1276_, 0, v___x_1293_);
v___x_1302_ = v___x_1276_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
v_a_1273_ = v___x_1302_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec(v___x_1289_);
lean_dec_ref(v_env_1272_);
lean_inc(v_fst_1283_);
lean_inc(v_snd_1284_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_snd_1284_);
lean_ctor_set(v___x_1307_, 1, v_fst_1283_);
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
if (v_isShared_1287_ == 0)
{
v___x_1310_ = v___x_1286_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_fst_1283_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_snd_1284_);
v___x_1310_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1310_);
v___x_1312_ = v___x_1281_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1314_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1312_);
lean_ctor_set(v___x_1276_, 0, v___x_1308_);
v___x_1314_ = v___x_1276_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_env_1272_);
v_fst_1319_ = lean_ctor_get(v_snd_1278_, 0);
v_snd_1320_ = lean_ctor_get(v_snd_1278_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_snd_1278_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1322_ = v_snd_1278_;
v_isShared_1323_ = v_isSharedCheck_1335_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_snd_1320_);
lean_inc(v_fst_1319_);
lean_dec(v_snd_1278_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1335_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_inc(v_fst_1319_);
lean_inc(v_snd_1320_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_snd_1320_);
lean_ctor_set(v___x_1324_, 1, v_fst_1319_);
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
if (v_isShared_1323_ == 0)
{
v___x_1327_ = v___x_1322_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_fst_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_snd_1320_);
v___x_1327_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1327_);
v___x_1329_ = v___x_1281_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_fst_1279_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1329_);
lean_ctor_set(v___x_1276_, 0, v___x_1325_);
v___x_1331_ = v___x_1276_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
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
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2));
v___x_1344_ = lean_unsigned_to_nat(2u);
v___x_1345_ = lean_unsigned_to_nat(246u);
v___x_1346_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1));
v___x_1347_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_1348_ = l_mkPanicMessageWithDecl(v___x_1347_, v___x_1346_, v___x_1345_, v___x_1344_, v___x_1343_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(lean_object* v_env_1349_, lean_object* v_deconstructQuantifier_x3f_1350_, lean_object* v_stx_1351_){
_start:
{
lean_object* v_deconstructQuantifier_x3f_1352_; lean_object* v_quantifiers_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_fst_1359_; 
v_deconstructQuantifier_x3f_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_deconstructQuantifier_x3f_1352_, 0, v_deconstructQuantifier_x3f_1350_);
v_quantifiers_1353_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0));
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_stx_1351_);
lean_ctor_set(v___x_1355_, 1, v_quantifiers_1353_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_deconstructQuantifier_x3f_1352_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1354_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1349_, v___x_1357_);
v_fst_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_fst_1359_);
lean_dec_ref(v___x_1358_);
if (lean_obj_tag(v_fst_1359_) == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3);
v___x_1361_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(v___x_1360_);
return v___x_1361_;
}
else
{
lean_object* v_val_1362_; 
v_val_1362_ = lean_ctor_get(v_fst_1359_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v_fst_1359_, 1);
return v_val_1362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0(lean_object* v_env_1363_, lean_object* v_inst_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1363_, v_a_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(lean_object* v_x_1367_, lean_object* v_x_1368_){
_start:
{
if (lean_obj_tag(v_x_1367_) == 0)
{
if (lean_obj_tag(v_x_1368_) == 0)
{
uint8_t v___x_1369_; 
v___x_1369_ = 1;
return v___x_1369_;
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = 0;
return v___x_1370_;
}
}
else
{
if (lean_obj_tag(v_x_1368_) == 0)
{
uint8_t v___x_1371_; 
v___x_1371_ = 0;
return v___x_1371_;
}
else
{
lean_object* v_val_1372_; lean_object* v_val_1373_; uint8_t v___x_1374_; 
v_val_1372_ = lean_ctor_get(v_x_1367_, 0);
v_val_1373_ = lean_ctor_get(v_x_1368_, 0);
v___x_1374_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_1372_, v_val_1373_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1___boxed(lean_object* v_x_1375_, lean_object* v_x_1376_){
_start:
{
uint8_t v_res_1377_; lean_object* v_r_1378_; 
v_res_1377_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_x_1375_, v_x_1376_);
lean_dec(v_x_1376_);
lean_dec(v_x_1375_);
v_r_1378_ = lean_box(v_res_1377_);
return v_r_1378_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(lean_object* v_a_1379_, lean_object* v_x_1380_){
_start:
{
if (lean_obj_tag(v_x_1380_) == 0)
{
uint8_t v___x_1381_; 
v___x_1381_ = 0;
return v___x_1381_;
}
else
{
lean_object* v_key_1382_; lean_object* v_tail_1383_; uint8_t v___x_1384_; 
v_key_1382_ = lean_ctor_get(v_x_1380_, 0);
v_tail_1383_ = lean_ctor_get(v_x_1380_, 2);
v___x_1384_ = lean_name_eq(v_key_1382_, v_a_1379_);
if (v___x_1384_ == 0)
{
v_x_1380_ = v_tail_1383_;
goto _start;
}
else
{
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg___boxed(lean_object* v_a_1386_, lean_object* v_x_1387_){
_start:
{
uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_res_1388_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1386_, v_x_1387_);
lean_dec(v_x_1387_);
lean_dec(v_a_1386_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(lean_object* v_m_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_buckets_1392_; lean_object* v___x_1393_; uint64_t v___y_1395_; 
v_buckets_1392_ = lean_ctor_get(v_m_1390_, 1);
v___x_1393_ = lean_array_get_size(v_buckets_1392_);
if (lean_obj_tag(v_a_1391_) == 0)
{
uint64_t v___x_1409_; 
v___x_1409_ = 1723ULL;
v___y_1395_ = v___x_1409_;
goto v___jp_1394_;
}
else
{
uint64_t v_hash_1410_; 
v_hash_1410_ = lean_ctor_get_uint64(v_a_1391_, sizeof(void*)*2);
v___y_1395_ = v_hash_1410_;
goto v___jp_1394_;
}
v___jp_1394_:
{
uint64_t v___x_1396_; uint64_t v___x_1397_; uint64_t v_fold_1398_; uint64_t v___x_1399_; uint64_t v___x_1400_; uint64_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; size_t v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1396_ = 32ULL;
v___x_1397_ = lean_uint64_shift_right(v___y_1395_, v___x_1396_);
v_fold_1398_ = lean_uint64_xor(v___y_1395_, v___x_1397_);
v___x_1399_ = 16ULL;
v___x_1400_ = lean_uint64_shift_right(v_fold_1398_, v___x_1399_);
v___x_1401_ = lean_uint64_xor(v_fold_1398_, v___x_1400_);
v___x_1402_ = lean_uint64_to_usize(v___x_1401_);
v___x_1403_ = lean_usize_of_nat(v___x_1393_);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = lean_usize_sub(v___x_1403_, v___x_1404_);
v___x_1406_ = lean_usize_land(v___x_1402_, v___x_1405_);
v___x_1407_ = lean_array_uget_borrowed(v_buckets_1392_, v___x_1406_);
v___x_1408_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1391_, v___x_1407_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg___boxed(lean_object* v_m_1411_, lean_object* v_a_1412_){
_start:
{
uint8_t v_res_1413_; lean_object* v_r_1414_; 
v_res_1413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_m_1411_);
v_r_1414_ = lean_box(v_res_1413_);
return v_r_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(lean_object* v_env_1415_, lean_object* v_opts_1416_, lean_object* v_op_1417_, lean_object* v_stx_1418_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = l_Lean_Syntax_getNumArgs(v_stx_1418_);
v___x_1436_ = lean_unsigned_to_nat(3u);
v___x_1437_ = lean_nat_dec_eq(v___x_1435_, v___x_1436_);
lean_dec(v___x_1435_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v_env_1415_);
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_mk_empty_array_with_capacity(v___x_1438_);
v___x_1440_ = lean_array_push(v___x_1439_, v_stx_1418_);
return v___x_1440_;
}
else
{
lean_object* v_precs_x3f_1441_; lean_object* v_extendedChainKinds_1442_; lean_object* v___x_1443_; 
v_precs_x3f_1441_ = lean_ctor_get(v_op_1417_, 0);
v_extendedChainKinds_1442_ = lean_ctor_get(v_op_1417_, 1);
lean_inc(v_stx_1418_);
v___x_1443_ = l_Lean_Syntax_getKind(v_stx_1418_);
if (lean_obj_tag(v_precs_x3f_1441_) == 0)
{
goto v___jp_1444_;
}
else
{
lean_object* v_op_x27_x3f_1449_; 
lean_inc(v___x_1443_);
lean_inc_ref(v_env_1415_);
v_op_x27_x3f_1449_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_1415_, v_opts_1416_, v___x_1443_);
if (lean_obj_tag(v_op_x27_x3f_1449_) == 0)
{
goto v___jp_1444_;
}
else
{
lean_object* v_val_1450_; lean_object* v_precs_x3f_1451_; uint8_t v___x_1452_; 
v_val_1450_ = lean_ctor_get(v_op_x27_x3f_1449_, 0);
lean_inc(v_val_1450_);
lean_dec_ref_known(v_op_x27_x3f_1449_, 1);
v_precs_x3f_1451_ = lean_ctor_get(v_val_1450_, 0);
lean_inc(v_precs_x3f_1451_);
lean_dec(v_val_1450_);
v___x_1452_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_precs_x3f_1451_, v_precs_x3f_1441_);
lean_dec(v_precs_x3f_1451_);
if (v___x_1452_ == 0)
{
goto v___jp_1444_;
}
else
{
lean_dec(v___x_1443_);
goto v___jp_1419_;
}
}
}
v___jp_1444_:
{
uint8_t v___x_1445_; 
v___x_1445_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_extendedChainKinds_1442_, v___x_1443_);
lean_dec(v___x_1443_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec_ref(v_env_1415_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_mk_empty_array_with_capacity(v___x_1446_);
v___x_1448_ = lean_array_push(v___x_1447_, v_stx_1418_);
return v___x_1448_;
}
else
{
goto v___jp_1419_;
}
}
}
v___jp_1419_:
{
lean_object* v___x_1420_; lean_object* v_op_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_unsigned_to_nat(1u);
v_op_1421_ = l_Lean_Syntax_getArg(v_stx_1418_, v___x_1420_);
v___x_1422_ = l_Lean_Syntax_isAtom(v_op_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec(v_op_1421_);
lean_dec_ref(v_env_1415_);
v___x_1423_ = lean_mk_empty_array_with_capacity(v___x_1420_);
v___x_1424_ = lean_array_push(v___x_1423_, v_stx_1418_);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; lean_object* v_left_1426_; lean_object* v___x_1427_; lean_object* v_right_1428_; lean_object* v_leftChain_1429_; lean_object* v_rightChain_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v_left_1426_ = l_Lean_Syntax_getArg(v_stx_1418_, v___x_1425_);
v___x_1427_ = lean_unsigned_to_nat(2u);
v_right_1428_ = l_Lean_Syntax_getArg(v_stx_1418_, v___x_1427_);
lean_dec(v_stx_1418_);
lean_inc_ref(v_env_1415_);
v_leftChain_1429_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1415_, v_opts_1416_, v_op_1417_, v_left_1426_);
v_rightChain_1430_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1415_, v_opts_1416_, v_op_1417_, v_right_1428_);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1420_);
v___x_1432_ = lean_array_push(v___x_1431_, v_op_1421_);
v___x_1433_ = l_Array_append___redArg(v_leftChain_1429_, v___x_1432_);
lean_dec_ref(v___x_1432_);
v___x_1434_ = l_Array_append___redArg(v___x_1433_, v_rightChain_1430_);
lean_dec_ref(v_rightChain_1430_);
return v___x_1434_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain___boxed(lean_object* v_env_1453_, lean_object* v_opts_1454_, lean_object* v_op_1455_, lean_object* v_stx_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1453_, v_opts_1454_, v_op_1455_, v_stx_1456_);
lean_dec_ref(v_op_1455_);
lean_dec_ref(v_opts_1454_);
return v_res_1457_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(lean_object* v_00_u03b2_1458_, lean_object* v_m_1459_, lean_object* v_a_1460_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1459_, v_a_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_m_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_res_1465_; lean_object* v_r_1466_; 
v_res_1465_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(v_00_u03b2_1462_, v_m_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_m_1463_);
v_r_1466_ = lean_box(v_res_1465_);
return v_r_1466_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(lean_object* v_00_u03b2_1467_, lean_object* v_a_1468_, lean_object* v_x_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1468_, v_x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1471_, lean_object* v_a_1472_, lean_object* v_x_1473_){
_start:
{
uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_res_1474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(v_00_u03b2_1471_, v_a_1472_, v_x_1473_);
lean_dec(v_x_1473_);
lean_dec(v_a_1472_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v_a_1479_, lean_object* v_b_1480_){
_start:
{
lean_object* v_it_1482_; lean_object* v_startInclusive_1483_; lean_object* v_endExclusive_1484_; 
if (lean_obj_tag(v_a_1479_) == 0)
{
lean_object* v_currPos_1490_; lean_object* v_searcher_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1597_; 
v_currPos_1490_ = lean_ctor_get(v_a_1479_, 0);
v_searcher_1491_ = lean_ctor_get(v_a_1479_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_a_1479_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1493_ = v_a_1479_;
v_isShared_1494_ = v_isSharedCheck_1597_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_searcher_1491_);
lean_inc(v_currPos_1490_);
lean_dec(v_a_1479_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1597_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v_it_1496_; lean_object* v_it_1502_; lean_object* v_startPos_1503_; lean_object* v_endPos_1504_; 
switch(lean_obj_tag(v_searcher_1491_))
{
case 0:
{
lean_object* v_pos_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1529_; 
lean_del_object(v___x_1493_);
v_pos_1517_ = lean_ctor_get(v_searcher_1491_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_searcher_1491_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1519_ = v_searcher_1491_;
v_isShared_1520_ = v_isSharedCheck_1529_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_pos_1517_);
lean_dec(v_searcher_1491_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1529_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_startInclusive_1521_; lean_object* v_endExclusive_1522_; lean_object* v___x_1523_; uint8_t v_decide_1524_; 
v_startInclusive_1521_ = lean_ctor_get(v___x_1477_, 1);
v_endExclusive_1522_ = lean_ctor_get(v___x_1477_, 2);
v___x_1523_ = lean_nat_sub(v_endExclusive_1522_, v_startInclusive_1521_);
v_decide_1524_ = lean_nat_dec_eq(v_pos_1517_, v___x_1523_);
lean_dec(v___x_1523_);
if (v_decide_1524_ == 0)
{
lean_object* v___x_1526_; 
lean_inc(v_pos_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
v___x_1526_ = v___x_1519_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_pos_1517_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_inc(v_pos_1517_);
v_it_1502_ = v___x_1526_;
v_startPos_1503_ = v_pos_1517_;
v_endPos_1504_ = v_pos_1517_;
goto v___jp_1501_;
}
}
else
{
lean_object* v___x_1528_; 
lean_del_object(v___x_1519_);
v___x_1528_ = lean_box(3);
lean_inc(v_pos_1517_);
v_it_1502_ = v___x_1528_;
v_startPos_1503_ = v_pos_1517_;
v_endPos_1504_ = v_pos_1517_;
goto v___jp_1501_;
}
}
}
case 1:
{
lean_object* v_pos_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_pos_1530_ = lean_ctor_get(v_searcher_1491_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_searcher_1491_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1532_ = v_searcher_1491_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_pos_1530_);
lean_dec(v_searcher_1491_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = lean_string_utf8_next_fast(v___x_1476_, v_pos_1530_);
lean_dec(v_pos_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
v_it_1496_ = v___x_1536_;
goto v___jp_1495_;
}
}
}
case 2:
{
lean_object* v_needle_1539_; lean_object* v_table_1540_; lean_object* v_stackPos_1541_; lean_object* v_needlePos_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1596_; 
v_needle_1539_ = lean_ctor_get(v_searcher_1491_, 0);
v_table_1540_ = lean_ctor_get(v_searcher_1491_, 1);
v_stackPos_1541_ = lean_ctor_get(v_searcher_1491_, 2);
v_needlePos_1542_ = lean_ctor_get(v_searcher_1491_, 3);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_searcher_1491_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1544_ = v_searcher_1491_;
v_isShared_1545_ = v_isSharedCheck_1596_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_needlePos_1542_);
lean_inc(v_stackPos_1541_);
lean_inc(v_table_1540_);
lean_inc(v_needle_1539_);
lean_dec(v_searcher_1491_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1596_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_str_1546_; lean_object* v_startInclusive_1547_; lean_object* v_endExclusive_1548_; lean_object* v_basePos_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_str_1546_ = lean_ctor_get(v_needle_1539_, 0);
v_startInclusive_1547_ = lean_ctor_get(v_needle_1539_, 1);
v_endExclusive_1548_ = lean_ctor_get(v_needle_1539_, 2);
v_basePos_1549_ = lean_nat_sub(v_stackPos_1541_, v_needlePos_1542_);
v___x_1550_ = lean_nat_sub(v_endExclusive_1548_, v_startInclusive_1547_);
v___x_1551_ = lean_nat_add(v_basePos_1549_, v___x_1550_);
v___x_1552_ = lean_nat_dec_le(v___x_1551_, v___x_1478_);
lean_dec(v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
lean_dec(v___x_1550_);
lean_del_object(v___x_1544_);
lean_dec(v_needlePos_1542_);
lean_dec(v_stackPos_1541_);
lean_dec_ref(v_table_1540_);
lean_dec_ref(v_needle_1539_);
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_nat_add(v_basePos_1549_, v___x_1553_);
lean_dec(v_basePos_1549_);
v___x_1555_ = lean_nat_dec_le(v___x_1554_, v___x_1478_);
lean_dec(v___x_1554_);
if (v___x_1555_ == 0)
{
lean_del_object(v___x_1493_);
goto v___jp_1515_;
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_box(3);
v_it_1496_ = v___x_1556_;
goto v___jp_1495_;
}
}
else
{
uint8_t v_stackByte_1557_; lean_object* v___x_1558_; uint8_t v_patByte_1559_; uint8_t v___x_1560_; 
lean_dec(v_basePos_1549_);
lean_inc(v_stackPos_1541_);
v_stackByte_1557_ = lean_string_get_byte_fast(v___x_1476_, v_stackPos_1541_);
v___x_1558_ = lean_nat_add(v_startInclusive_1547_, v_needlePos_1542_);
v_patByte_1559_ = lean_string_get_byte_fast(v_str_1546_, v___x_1558_);
v___x_1560_ = lean_uint8_dec_eq(v_stackByte_1557_, v_patByte_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; uint8_t v_decide_1562_; 
lean_dec(v___x_1550_);
v___x_1561_ = lean_unsigned_to_nat(0u);
v_decide_1562_ = lean_nat_dec_eq(v_needlePos_1542_, v___x_1561_);
if (v_decide_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_newNeedlePos_1565_; uint8_t v___x_1566_; 
v___x_1563_ = lean_unsigned_to_nat(1u);
v___x_1564_ = lean_nat_sub(v_needlePos_1542_, v___x_1563_);
lean_dec(v_needlePos_1542_);
v_newNeedlePos_1565_ = lean_array_fget_borrowed(v_table_1540_, v___x_1564_);
lean_dec(v___x_1564_);
v___x_1566_ = lean_nat_dec_eq(v_newNeedlePos_1565_, v___x_1561_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1568_; 
lean_inc(v_newNeedlePos_1565_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 3, v_newNeedlePos_1565_);
v___x_1568_ = v___x_1544_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_needle_1539_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_table_1540_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_stackPos_1541_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_newNeedlePos_1565_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
v_it_1496_ = v___x_1568_;
goto v___jp_1495_;
}
}
else
{
lean_object* v_nextStackPos_1570_; lean_object* v___x_1572_; 
v_nextStackPos_1570_ = l_String_Slice_posGE___redArg(v___x_1477_, v_stackPos_1541_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 3, v___x_1561_);
lean_ctor_set(v___x_1544_, 2, v_nextStackPos_1570_);
v___x_1572_ = v___x_1544_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_needle_1539_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_table_1540_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_nextStackPos_1570_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v___x_1561_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
v_it_1496_ = v___x_1572_;
goto v___jp_1495_;
}
}
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v_nextStackPos_1576_; lean_object* v___x_1578_; 
lean_dec(v_needlePos_1542_);
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = lean_nat_add(v_stackPos_1541_, v___x_1574_);
lean_dec(v_stackPos_1541_);
v_nextStackPos_1576_ = l_String_Slice_posGE___redArg(v___x_1477_, v___x_1575_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 3, v___x_1561_);
lean_ctor_set(v___x_1544_, 2, v_nextStackPos_1576_);
v___x_1578_ = v___x_1544_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_needle_1539_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_table_1540_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_nextStackPos_1576_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v___x_1561_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v_it_1496_ = v___x_1578_;
goto v___jp_1495_;
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v_nextStackPos_1581_; lean_object* v_nextNeedlePos_1582_; uint8_t v_decide_1583_; 
lean_del_object(v___x_1493_);
v___x_1580_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1581_ = lean_nat_add(v_stackPos_1541_, v___x_1580_);
lean_dec(v_stackPos_1541_);
v_nextNeedlePos_1582_ = lean_nat_add(v_needlePos_1542_, v___x_1580_);
lean_dec(v_needlePos_1542_);
v_decide_1583_ = lean_nat_dec_eq(v_nextNeedlePos_1582_, v___x_1550_);
lean_dec(v___x_1550_);
if (v_decide_1583_ == 0)
{
lean_object* v___x_1585_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 3, v_nextNeedlePos_1582_);
lean_ctor_set(v___x_1544_, 2, v_nextStackPos_1581_);
v___x_1585_ = v___x_1544_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_needle_1539_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_table_1540_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_nextStackPos_1581_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_nextNeedlePos_1582_);
v___x_1585_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_currPos_1490_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v_a_1479_ = v___x_1586_;
goto _start;
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1589_ = lean_nat_sub(v_nextStackPos_1581_, v_nextNeedlePos_1582_);
lean_dec(v_nextNeedlePos_1582_);
v___x_1590_ = l_String_Slice_pos_x21(v___x_1477_, v___x_1589_);
lean_dec(v___x_1589_);
v___x_1591_ = l_String_Slice_pos_x21(v___x_1477_, v_nextStackPos_1581_);
v___x_1592_ = lean_unsigned_to_nat(0u);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 3, v___x_1592_);
lean_ctor_set(v___x_1544_, 2, v_nextStackPos_1581_);
v___x_1594_ = v___x_1544_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_needle_1539_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_table_1540_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_nextStackPos_1581_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v_it_1502_ = v___x_1594_;
v_startPos_1503_ = v___x_1590_;
v_endPos_1504_ = v___x_1591_;
goto v___jp_1501_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_1493_);
goto v___jp_1515_;
}
}
v___jp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v_it_1496_);
v___x_1498_ = v___x_1493_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_currPos_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_it_1496_);
v___x_1498_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
v_a_1479_ = v___x_1498_;
goto _start;
}
}
v___jp_1501_:
{
lean_object* v_slice_1505_; lean_object* v_startInclusive_1506_; lean_object* v_endExclusive_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_slice_1505_ = l_String_Slice_subslice_x21(v___x_1477_, v_currPos_1490_, v_startPos_1503_);
v_startInclusive_1506_ = lean_ctor_get(v_slice_1505_, 0);
v_endExclusive_1507_ = lean_ctor_get(v_slice_1505_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_slice_1505_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v_slice_1505_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_endExclusive_1507_);
lean_inc(v_startInclusive_1506_);
lean_dec(v_slice_1505_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_nextIt_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 1, v_it_1502_);
lean_ctor_set(v___x_1509_, 0, v_endPos_1504_);
v_nextIt_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_endPos_1504_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_it_1502_);
v_nextIt_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
v_it_1482_ = v_nextIt_1512_;
v_startInclusive_1483_ = v_startInclusive_1506_;
v_endExclusive_1484_ = v_endExclusive_1507_;
goto v___jp_1481_;
}
}
}
v___jp_1515_:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_box(1);
lean_inc(v___x_1478_);
v_it_1482_ = v___x_1516_;
v_startInclusive_1483_ = v_currPos_1490_;
v_endExclusive_1484_ = v___x_1478_;
goto v___jp_1481_;
}
}
}
else
{
lean_dec(v___x_1478_);
lean_dec_ref(v___x_1476_);
return v_b_1480_;
}
v___jp_1481_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_inc_ref(v___x_1476_);
v___x_1485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1476_);
lean_ctor_set(v___x_1485_, 1, v_startInclusive_1483_);
lean_ctor_set(v___x_1485_, 2, v_endExclusive_1484_);
v___x_1486_ = l_String_Slice_toString(v___x_1485_);
lean_dec_ref_known(v___x_1485_, 3);
v___x_1487_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_1486_);
v___x_1488_ = lean_array_push(v_b_1480_, v___x_1487_);
v_a_1479_ = v_it_1482_;
v_b_1480_ = v___x_1488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg___boxed(lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v___x_1600_, lean_object* v_a_1601_, lean_object* v_b_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1598_, v___x_1599_, v___x_1600_, v_a_1601_, v_b_1602_);
lean_dec_ref(v___x_1599_);
return v_res_1603_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtRawAsInSource___closed__3(void){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource(uint8_t v_isFallback_1610_, lean_object* v_stx_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
uint8_t v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = 0;
v___x_1615_ = l_Lean_Syntax_getPos_x3f(v_stx_1611_, v___x_1614_);
if (lean_obj_tag(v___x_1615_) == 1)
{
lean_object* v_val_1616_; lean_object* v___x_1617_; 
v_val_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1611_, v___x_1614_);
if (lean_obj_tag(v___x_1617_) == 1)
{
lean_object* v_text_1618_; lean_object* v_val_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1669_; 
v_text_1618_ = lean_ctor_get(v_a_1612_, 1);
v_val_1619_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1621_ = v___x_1617_;
v_isShared_1622_ = v_isSharedCheck_1669_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_val_1619_);
lean_dec(v___x_1617_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1669_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_source_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v_source_1623_ = lean_ctor_get(v_text_1618_, 0);
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = lean_string_utf8_byte_size(v_source_1623_);
lean_inc_ref(v_source_1623_);
v___x_1626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1626_, 0, v_source_1623_);
lean_ctor_set(v___x_1626_, 1, v___x_1624_);
lean_ctor_set(v___x_1626_, 2, v___x_1625_);
v___x_1627_ = l_String_Slice_pos_x3f(v___x_1626_, v_val_1616_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1626_, 3);
lean_dec(v_val_1619_);
v___x_1628_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1629_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1630_, 0, v_stx_1611_);
lean_ctor_set(v___x_1630_, 1, v___x_1628_);
lean_ctor_set(v___x_1630_, 2, v___x_1629_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 2);
lean_ctor_set(v___x_1621_, 0, v___x_1630_);
v___x_1632_ = v___x_1621_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v_a_1613_);
return v___x_1633_;
}
}
else
{
lean_object* v_val_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1668_; 
lean_del_object(v___x_1621_);
v_val_1635_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1637_ = v___x_1627_;
v_isShared_1638_ = v_isSharedCheck_1668_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_val_1635_);
lean_dec(v___x_1627_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1668_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_String_Slice_pos_x3f(v___x_1626_, v_val_1619_);
lean_dec_ref_known(v___x_1626_, 3);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_dec(v_val_1635_);
v___x_1640_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1641_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1642_, 0, v_stx_1611_);
lean_ctor_set(v___x_1642_, 1, v___x_1640_);
lean_ctor_set(v___x_1642_, 2, v___x_1641_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 2);
lean_ctor_set(v___x_1637_, 0, v___x_1642_);
v___x_1644_ = v___x_1637_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_a_1613_);
return v___x_1645_;
}
}
else
{
lean_object* v_val_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
lean_del_object(v___x_1637_);
v_val_1647_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1648_ = lean_string_utf8_extract_fast(v_source_1623_, v_val_1635_, v_val_1647_);
lean_dec(v_val_1647_);
lean_dec(v_val_1635_);
v___x_1649_ = lean_string_utf8_byte_size(v___x_1648_);
lean_inc_ref(v___x_1648_);
v___x_1650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1624_);
lean_ctor_set(v___x_1650_, 2, v___x_1649_);
v___x_1651_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1652_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1653_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1648_, v___x_1650_, v___x_1649_, v___x_1651_, v___x_1652_);
lean_dec_ref_known(v___x_1650_, 3);
v___x_1654_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1655_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1654_, v___x_1653_);
v___x_1656_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1614_, v___x_1655_);
v___x_1657_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___x_1656_, v_stx_1611_, v_a_1613_);
lean_dec(v_stx_1611_);
if (lean_obj_tag(v___x_1657_) == 0)
{
if (v_isFallback_1610_ == 0)
{
return v___x_1657_;
}
else
{
lean_object* v_a_1658_; lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1667_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_a_1659_ = lean_ctor_get(v___x_1657_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1661_ = v___x_1657_;
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1667_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_1658_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1663_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_a_1659_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
return v___x_1657_;
}
}
}
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v___x_1617_);
lean_dec(v_val_1616_);
v___x_1670_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1671_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1670_, v_stx_1611_, v_a_1613_);
lean_dec(v_stx_1611_);
return v___x_1671_;
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v___x_1615_);
v___x_1672_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1673_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1672_, v_stx_1611_, v_a_1613_);
lean_dec(v_stx_1611_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource___boxed(lean_object* v_isFallback_1674_, lean_object* v_stx_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
uint8_t v_isFallback_boxed_1678_; lean_object* v_res_1679_; 
v_isFallback_boxed_1678_ = lean_unbox(v_isFallback_1674_);
v_res_1679_ = l_Lean_Fmt_fmtRawAsInSource(v_isFallback_boxed_1678_, v_stx_1675_, v_a_1676_, v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(lean_object* v___x_1680_, lean_object* v___x_1681_, lean_object* v___x_1682_, lean_object* v_inst_1683_, lean_object* v_R_1684_, lean_object* v_a_1685_, lean_object* v_b_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1680_, v___x_1681_, v___x_1682_, v_a_1685_, v_b_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___boxed(lean_object* v___x_1688_, lean_object* v___x_1689_, lean_object* v___x_1690_, lean_object* v_inst_1691_, lean_object* v_R_1692_, lean_object* v_a_1693_, lean_object* v_b_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(v___x_1688_, v___x_1689_, v___x_1690_, v_inst_1691_, v_R_1692_, v_a_1693_, v_b_1694_);
lean_dec_ref(v___x_1689_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(lean_object* v_token_1696_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_lines_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_string_utf8_byte_size(v_token_1696_);
lean_inc_ref(v_token_1696_);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v_token_1696_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
lean_ctor_set(v___x_1699_, 2, v___x_1698_);
v___x_1700_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1701_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_lines_1702_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_token_1696_, v___x_1699_, v___x_1698_, v___x_1700_, v___x_1701_);
lean_dec_ref_known(v___x_1699_, 3);
v___x_1703_ = lean_array_get_size(v_lines_1702_);
v___x_1704_ = lean_unsigned_to_nat(1u);
v___x_1705_ = lean_nat_dec_eq(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1707_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1706_, v_lines_1702_);
v___x_1708_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1705_, v___x_1707_);
return v___x_1708_;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_array_get(v___x_1709_, v_lines_1702_, v___x_1697_);
lean_dec_ref(v_lines_1702_);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_bs_1713_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_lt(v_i_1712_, v_sz_1711_);
if (v___x_1714_ == 0)
{
return v_bs_1713_;
}
else
{
lean_object* v_v_1715_; lean_object* v___x_1716_; lean_object* v_bs_x27_1717_; lean_object* v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v_v_1715_ = lean_array_uget(v_bs_1713_, v_i_1712_);
v___x_1716_ = lean_unsigned_to_nat(0u);
v_bs_x27_1717_ = lean_array_uset(v_bs_1713_, v_i_1712_, v___x_1716_);
v___x_1718_ = l_Lean_Fmt_Doc_text___override___redArg(v_v_1715_);
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1712_, v___x_1719_);
v___x_1721_ = lean_array_uset(v_bs_x27_1717_, v_i_1712_, v___x_1718_);
v_i_1712_ = v___x_1720_;
v_bs_1713_ = v___x_1721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2___boxed(lean_object* v_sz_1723_, lean_object* v_i_1724_, lean_object* v_bs_1725_){
_start:
{
size_t v_sz_boxed_1726_; size_t v_i_boxed_1727_; lean_object* v_res_1728_; 
v_sz_boxed_1726_ = lean_unbox_usize(v_sz_1723_);
lean_dec(v_sz_1723_);
v_i_boxed_1727_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_res_1728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_boxed_1726_, v_i_boxed_1727_, v_bs_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(lean_object* v_ctx_1729_, size_t v_sz_1730_, size_t v_i_1731_, lean_object* v_bs_1732_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_lt(v_i_1731_, v_sz_1730_);
if (v___x_1733_ == 0)
{
lean_dec_ref(v_ctx_1729_);
return v_bs_1732_;
}
else
{
lean_object* v_v_1734_; lean_object* v_str_1735_; lean_object* v_startPos_1736_; lean_object* v_stopPos_1737_; lean_object* v_anchorColumnPos_1738_; lean_object* v___x_1739_; lean_object* v_bs_x27_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v_v_1734_ = lean_array_uget_borrowed(v_bs_1732_, v_i_1731_);
v_str_1735_ = lean_ctor_get(v_v_1734_, 0);
lean_inc_ref(v_str_1735_);
v_startPos_1736_ = lean_ctor_get(v_v_1734_, 1);
lean_inc(v_startPos_1736_);
v_stopPos_1737_ = lean_ctor_get(v_v_1734_, 2);
lean_inc(v_stopPos_1737_);
v_anchorColumnPos_1738_ = lean_ctor_get(v_ctx_1729_, 0);
v___x_1739_ = lean_unsigned_to_nat(0u);
v_bs_x27_1740_ = lean_array_uset(v_bs_1732_, v_i_1731_, v___x_1739_);
v___x_1741_ = lean_string_utf8_extract(v_str_1735_, v_startPos_1736_, v_stopPos_1737_);
lean_dec(v_stopPos_1737_);
lean_dec(v_startPos_1736_);
lean_dec_ref(v_str_1735_);
lean_inc(v_anchorColumnPos_1738_);
v___x_1742_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(v___x_1741_, v_anchorColumnPos_1738_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1731_, v___x_1743_);
v___x_1745_ = lean_array_uset(v_bs_x27_1740_, v_i_1731_, v___x_1742_);
v_i_1731_ = v___x_1744_;
v_bs_1732_ = v___x_1745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1___boxed(lean_object* v_ctx_1747_, lean_object* v_sz_1748_, lean_object* v_i_1749_, lean_object* v_bs_1750_){
_start:
{
size_t v_sz_boxed_1751_; size_t v_i_boxed_1752_; lean_object* v_res_1753_; 
v_sz_boxed_1751_ = lean_unbox_usize(v_sz_1748_);
lean_dec(v_sz_1748_);
v_i_boxed_1752_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1747_, v_sz_boxed_1751_, v_i_boxed_1752_, v_bs_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(lean_object* v_a_1754_, lean_object* v_b_1755_){
_start:
{
lean_object* v_array_1756_; lean_object* v_start_1757_; lean_object* v_stop_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1771_; 
v_array_1756_ = lean_ctor_get(v_a_1754_, 0);
v_start_1757_ = lean_ctor_get(v_a_1754_, 1);
v_stop_1758_ = lean_ctor_get(v_a_1754_, 2);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_a_1754_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1760_ = v_a_1754_;
v_isShared_1761_ = v_isSharedCheck_1771_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_stop_1758_);
lean_inc(v_start_1757_);
lean_inc(v_array_1756_);
lean_dec(v_a_1754_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1771_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_nat_dec_lt(v_start_1757_, v_stop_1758_);
if (v___x_1762_ == 0)
{
lean_del_object(v___x_1760_);
lean_dec(v_stop_1758_);
lean_dec(v_start_1757_);
lean_dec_ref(v_array_1756_);
return v_b_1755_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_add(v_start_1757_, v___x_1763_);
lean_inc_ref(v_array_1756_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v___x_1764_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_array_1756_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_stop_1758_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_array_fget(v_array_1756_, v_start_1757_);
lean_dec(v_start_1757_);
lean_dec_ref(v_array_1756_);
v___x_1768_ = lean_array_push(v_b_1755_, v___x_1767_);
v_a_1754_ = v___x_1766_;
v_b_1755_ = v___x_1768_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(lean_object* v_ctx_1776_, lean_object* v_trailing_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_lastTokenTailPos_1779_; lean_object* v_startPos_1780_; uint8_t v___x_1781_; 
v_lastTokenTailPos_1779_ = lean_ctor_get(v_ctx_1776_, 2);
v_startPos_1780_ = lean_ctor_get(v_trailing_1777_, 1);
v___x_1781_ = lean_nat_dec_le(v_lastTokenTailPos_1779_, v_startPos_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v_lines_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_str_1788_; lean_object* v_startPos_1789_; lean_object* v_stopPos_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; size_t v_sz_1799_; size_t v___x_1800_; lean_object* v___x_1801_; lean_object* v_newLines_1802_; size_t v_sz_1803_; lean_object* v_formatted_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1782_ = l_instInhabitedRaw__1;
v___x_1783_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_trailing_1777_);
v___x_1784_ = l_Substring_Raw_splitOn(v_trailing_1777_, v___x_1783_);
v_lines_1785_ = lean_array_mk(v___x_1784_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_array_get_borrowed(v___x_1782_, v_lines_1785_, v___x_1786_);
v_str_1788_ = lean_ctor_get(v___x_1787_, 0);
v_startPos_1789_ = lean_ctor_get(v___x_1787_, 1);
v_stopPos_1790_ = lean_ctor_get(v___x_1787_, 2);
v___x_1791_ = lean_string_utf8_extract(v_str_1788_, v_startPos_1789_, v_stopPos_1790_);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_mk_empty_array_with_capacity(v___x_1792_);
lean_inc_ref(v___x_1793_);
v___x_1794_ = lean_array_push(v___x_1793_, v___x_1791_);
v___x_1795_ = lean_array_get_size(v_lines_1785_);
v___x_1796_ = l_Array_toSubarray___redArg(v_lines_1785_, v___x_1792_, v___x_1795_);
v___x_1797_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0));
v___x_1798_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v___x_1796_, v___x_1797_);
v_sz_1799_ = lean_array_size(v___x_1798_);
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1776_, v_sz_1799_, v___x_1800_, v___x_1798_);
v_newLines_1802_ = l_Array_append___redArg(v___x_1794_, v___x_1801_);
lean_dec_ref(v___x_1801_);
v_sz_1803_ = lean_array_size(v_newLines_1802_);
v_formatted_1804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1803_, v___x_1800_, v_newLines_1802_);
v___x_1805_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1806_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1805_, v_formatted_1804_);
v___x_1807_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1806_);
v___x_1808_ = l_Lean_Syntax_Range_ofSubstring(v_trailing_1777_);
lean_dec_ref(v_trailing_1777_);
v___x_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1807_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_array_push(v___x_1793_, v___x_1810_);
v___x_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v_a_1778_);
return v___x_1812_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec_ref(v_trailing_1777_);
lean_dec_ref(v_ctx_1776_);
v___x_1813_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v_a_1778_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(lean_object* v_ctx_1815_, lean_object* v___trailingTk_1816_, lean_object* v_trailing_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(v_ctx_1815_, v_trailing_1817_, v_a_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed(lean_object* v_ctx_1821_, lean_object* v___trailingTk_1822_, lean_object* v_trailing_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(v_ctx_1821_, v___trailingTk_1822_, v_trailing_1823_, v_a_1824_, v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v___trailingTk_1822_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0(lean_object* v_inst_1827_, lean_object* v_R_1828_, lean_object* v_a_1829_, lean_object* v_b_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v_a_1829_, v_b_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(lean_object* v_ctx_1832_, lean_object* v_leading_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_stopPos_1835_; lean_object* v_firstTokenPos_1836_; uint8_t v___x_1837_; 
v_stopPos_1835_ = lean_ctor_get(v_leading_1833_, 2);
v_firstTokenPos_1836_ = lean_ctor_get(v_ctx_1832_, 1);
v___x_1837_ = lean_nat_dec_le(v_stopPos_1835_, v_firstTokenPos_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v_lines_1840_; size_t v_sz_1841_; size_t v___x_1842_; lean_object* v_newLines_1843_; size_t v_sz_1844_; lean_object* v_formatted_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1838_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_leading_1833_);
v___x_1839_ = l_Substring_Raw_splitOn(v_leading_1833_, v___x_1838_);
v_lines_1840_ = lean_array_mk(v___x_1839_);
v_sz_1841_ = lean_array_size(v_lines_1840_);
v___x_1842_ = ((size_t)0ULL);
v_newLines_1843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1832_, v_sz_1841_, v___x_1842_, v_lines_1840_);
v_sz_1844_ = lean_array_size(v_newLines_1843_);
v_formatted_1845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1844_, v___x_1842_, v_newLines_1843_);
v___x_1846_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1847_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1846_, v_formatted_1845_);
v___x_1848_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1847_);
v___x_1849_ = l_Lean_Syntax_Range_ofSubstring(v_leading_1833_);
lean_dec_ref(v_leading_1833_);
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1848_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_mk_empty_array_with_capacity(v___x_1852_);
v___x_1854_ = lean_array_push(v___x_1853_, v___x_1851_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v_a_1834_);
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec_ref(v_leading_1833_);
lean_dec_ref(v_ctx_1832_);
v___x_1856_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v_a_1834_);
return v___x_1857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(lean_object* v_ctx_1858_, lean_object* v___leadingTk_1859_, lean_object* v_leading_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(v_ctx_1858_, v_leading_1860_, v_a_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed(lean_object* v_ctx_1864_, lean_object* v___leadingTk_1865_, lean_object* v_leading_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(v_ctx_1864_, v___leadingTk_1865_, v_leading_1866_, v_a_1867_, v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v___leadingTk_1865_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(lean_object* v_stx_1870_, lean_object* v_token_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_inc_ref(v_a_1872_);
v___x_1875_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed), 5, 1);
lean_closure_set(v___x_1875_, 0, v_a_1872_);
lean_inc(v_stx_1870_);
v___x_1876_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_1870_, v___x_1875_, v_a_1873_, v_a_1874_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v_a_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
v_a_1878_ = lean_ctor_get(v___x_1876_, 1);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1876_, 2);
lean_inc_ref(v_a_1872_);
v___x_1879_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed), 5, 1);
lean_closure_set(v___x_1879_, 0, v_a_1872_);
lean_inc(v_stx_1870_);
v___x_1880_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_1870_, v___x_1879_, v_a_1873_, v_a_1878_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v_a_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
v_a_1882_ = lean_ctor_get(v___x_1880_, 1);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1880_, 2);
v___x_1883_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(v_token_1871_);
v___x_1884_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_1883_, v_stx_1870_, v_a_1882_);
lean_dec(v_stx_1870_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1927_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
v_a_1886_ = lean_ctor_get(v___x_1884_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1888_ = v___x_1884_;
v_isShared_1889_ = v_isSharedCheck_1927_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_inc(v_a_1885_);
lean_dec(v___x_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1927_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___y_1891_; uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1877_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1885_);
if (v___x_1918_ == 0)
{
lean_object* v_doc_1919_; lean_object* v_doc_1920_; uint8_t v___x_1921_; 
v_doc_1919_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_doc_1919_);
lean_dec(v_a_1877_);
v_doc_1920_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_doc_1920_);
lean_dec(v_a_1885_);
v___x_1921_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1919_);
if (v___x_1921_ == 0)
{
uint8_t v___x_1922_; 
v___x_1922_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1920_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1919_, v_doc_1920_);
v___x_1924_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1923_);
v___y_1891_ = v___x_1924_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1925_; 
lean_dec(v_doc_1920_);
v___x_1925_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1919_);
v___y_1891_ = v___x_1925_;
goto v___jp_1890_;
}
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_doc_1919_);
v___x_1926_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1920_);
v___y_1891_ = v___x_1926_;
goto v___jp_1890_;
}
}
else
{
lean_dec(v_a_1885_);
v___y_1891_ = v_a_1877_;
goto v___jp_1890_;
}
}
else
{
lean_dec(v_a_1877_);
v___y_1891_ = v_a_1885_;
goto v___jp_1890_;
}
v___jp_1890_:
{
uint8_t v___x_1892_; 
v___x_1892_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1891_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1881_);
if (v___x_1893_ == 0)
{
lean_object* v_doc_1894_; lean_object* v_doc_1895_; uint8_t v___x_1896_; 
v_doc_1894_ = lean_ctor_get(v___y_1891_, 0);
lean_inc(v_doc_1894_);
lean_dec_ref(v___y_1891_);
v_doc_1895_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_doc_1895_);
lean_dec(v_a_1881_);
v___x_1896_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1894_);
if (v___x_1896_ == 0)
{
uint8_t v___x_1897_; 
v___x_1897_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1895_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1898_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1894_, v_doc_1895_);
v___x_1899_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1898_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1899_);
v___x_1901_ = v___x_1888_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_a_1886_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
lean_dec(v_doc_1895_);
v___x_1903_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1894_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1903_);
v___x_1905_ = v___x_1888_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_a_1886_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
return v___x_1905_;
}
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_dec(v_doc_1894_);
v___x_1907_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1895_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1907_);
v___x_1909_ = v___x_1888_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_a_1886_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec(v_a_1881_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___y_1891_);
v___x_1912_ = v___x_1888_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___y_1891_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_a_1886_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v___x_1915_; 
lean_dec_ref(v___y_1891_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v_a_1881_);
v___x_1915_ = v___x_1888_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1881_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1886_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
else
{
lean_dec(v_a_1881_);
lean_dec(v_a_1877_);
return v___x_1884_;
}
}
else
{
lean_dec(v_a_1877_);
lean_dec_ref(v_token_1871_);
lean_dec(v_stx_1870_);
return v___x_1880_;
}
}
else
{
lean_dec_ref(v_token_1871_);
lean_dec(v_stx_1870_);
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___boxed(lean_object* v_stx_1928_, lean_object* v_token_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1928_, v_token_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec_ref(v_a_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object* v_stx_1937_, uint8_t v_isRoot_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
switch(lean_obj_tag(v_stx_1937_))
{
case 0:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v_a_1941_);
return v___x_1943_;
}
case 1:
{
lean_object* v_kind_1944_; lean_object* v_args_1945_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_kind_1944_ = lean_ctor_get(v_stx_1937_, 1);
v_args_1945_ = lean_ctor_get(v_stx_1937_, 2);
v___x_1993_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_1994_ = lean_name_eq(v_kind_1944_, v___x_1993_);
if (v___x_1994_ == 0)
{
v___y_1947_ = v_a_1939_;
v___y_1948_ = v_a_1940_;
v___y_1949_ = v_a_1941_;
goto v___jp_1946_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_array_get_size(v_args_1945_);
v___x_1997_ = lean_nat_dec_lt(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
v___y_1947_ = v_a_1939_;
v___y_1948_ = v_a_1940_;
v___y_1949_ = v_a_1941_;
goto v___jp_1946_;
}
else
{
lean_object* v___x_1998_; 
lean_inc_ref(v_args_1945_);
lean_dec_ref_known(v_stx_1937_, 3);
v___x_1998_ = lean_array_fget(v_args_1945_, v___x_1995_);
lean_dec_ref(v_args_1945_);
v_stx_1937_ = v___x_1998_;
goto _start;
}
}
v___jp_1946_:
{
size_t v_sz_1950_; size_t v___x_1951_; lean_object* v___x_1952_; 
v_sz_1950_ = lean_array_size(v_args_1945_);
v___x_1951_ = ((size_t)0ULL);
lean_inc_ref(v_args_1945_);
v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_1950_, v___x_1951_, v_args_1945_, v___y_1947_, v___y_1948_, v___y_1949_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1983_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_a_1954_ = lean_ctor_get(v___x_1952_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1956_ = v___x_1952_;
v_isShared_1957_ = v_isSharedCheck_1983_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1983_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_Lean_Fmt_TaggedDoc_join(v_a_1953_);
if (v_isRoot_1938_ == 0)
{
lean_object* v_doc_1959_; lean_object* v_metaData_1960_; lean_object* v___x_1961_; 
lean_del_object(v___x_1956_);
v_doc_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_doc_1959_);
v_metaData_1960_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_metaData_1960_);
lean_dec_ref(v___x_1958_);
v___x_1961_ = l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(v_doc_1959_, v_stx_1937_, v_a_1954_);
lean_dec_ref_known(v_stx_1937_, 3);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1979_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_a_1963_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1979_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1979_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_doc_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1977_; 
v_doc_1967_ = lean_ctor_get(v_a_1962_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_a_1962_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_a_1962_, 1);
lean_dec(v_unused_1978_);
v___x_1969_ = v_a_1962_;
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_doc_1967_);
lean_dec(v_a_1962_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v_metaData_1960_);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_doc_1967_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_metaData_1960_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1972_);
v___x_1974_ = v___x_1965_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_a_1963_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
else
{
lean_dec(v_metaData_1960_);
return v___x_1961_;
}
}
else
{
lean_object* v___x_1981_; 
lean_dec_ref_known(v_stx_1937_, 3);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1958_);
v___x_1981_ = v___x_1956_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_a_1954_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref_known(v_stx_1937_, 3);
v_a_1984_ = lean_ctor_get(v___x_1952_, 0);
v_a_1985_ = lean_ctor_get(v___x_1952_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1952_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_inc(v_a_1984_);
lean_dec(v___x_1952_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1984_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
case 2:
{
lean_object* v_val_2000_; lean_object* v___x_2001_; 
v_val_2000_ = lean_ctor_get(v_stx_1937_, 1);
lean_inc_ref(v_val_2000_);
v___x_2001_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1937_, v_val_2000_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_2001_;
}
default: 
{
lean_object* v_rawVal_2002_; lean_object* v_str_2003_; lean_object* v_startPos_2004_; lean_object* v_stopPos_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_rawVal_2002_ = lean_ctor_get(v_stx_1937_, 1);
v_str_2003_ = lean_ctor_get(v_rawVal_2002_, 0);
v_startPos_2004_ = lean_ctor_get(v_rawVal_2002_, 1);
v_stopPos_2005_ = lean_ctor_get(v_rawVal_2002_, 2);
v___x_2006_ = lean_string_utf8_extract(v_str_2003_, v_startPos_2004_, v_stopPos_2005_);
v___x_2007_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1937_, v___x_2006_, v_a_1939_, v_a_1940_, v_a_1941_);
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_bs_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_bs_2010_);
lean_ctor_set(v___x_2015_, 1, v___y_2013_);
return v___x_2015_;
}
else
{
lean_object* v_v_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; 
v_v_2016_ = lean_array_uget_borrowed(v_bs_2010_, v_i_2009_);
v___x_2017_ = 0;
lean_inc(v_v_2016_);
v___x_2018_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_v_2016_, v___x_2017_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v_bs_x27_2022_; size_t v___x_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
v_a_2020_ = lean_ctor_get(v___x_2018_, 1);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2018_, 2);
v___x_2021_ = lean_unsigned_to_nat(0u);
v_bs_x27_2022_ = lean_array_uset(v_bs_2010_, v_i_2009_, v___x_2021_);
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2009_, v___x_2023_);
v___x_2025_ = lean_array_uset(v_bs_x27_2022_, v_i_2009_, v_a_2019_);
v_i_2009_ = v___x_2024_;
v_bs_2010_ = v___x_2025_;
v___y_2013_ = v_a_2020_;
goto _start;
}
else
{
lean_object* v_a_2027_; lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v_bs_2010_);
v_a_2027_ = lean_ctor_get(v___x_2018_, 0);
v_a_2028_ = lean_ctor_get(v___x_2018_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2018_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_inc(v_a_2027_);
lean_dec(v___x_2018_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2027_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object* v_sz_2036_, lean_object* v_i_2037_, lean_object* v_bs_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
size_t v_sz_boxed_2042_; size_t v_i_boxed_2043_; lean_object* v_res_2044_; 
v_sz_boxed_2042_ = lean_unbox_usize(v_sz_2036_);
lean_dec(v_sz_2036_);
v_i_boxed_2043_ = lean_unbox_usize(v_i_2037_);
lean_dec(v_i_2037_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_boxed_2042_, v_i_boxed_2043_, v_bs_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v___y_2039_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object* v_stx_2045_, lean_object* v_isRoot_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
uint8_t v_isRoot_boxed_2050_; lean_object* v_res_2051_; 
v_isRoot_boxed_2050_ = lean_unbox(v_isRoot_2046_);
v_res_2051_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2045_, v_isRoot_boxed_2050_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec_ref(v_a_2047_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object* v_stx_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
uint8_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = 0;
v___x_2056_ = l_Lean_Syntax_getPos_x3f(v_stx_2052_, v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 1)
{
lean_object* v_val_2057_; lean_object* v___x_2058_; 
v_val_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_val_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2052_, v___x_2055_);
if (lean_obj_tag(v___x_2058_) == 1)
{
lean_object* v_val_2059_; lean_object* v___x_2060_; 
v_val_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_val_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = l_Lean_Fmt_getLineInfos(v_val_2057_, v_val_2059_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2073_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_a_2062_ = lean_ctor_get(v___x_2060_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2064_ = v___x_2060_;
v_isShared_2065_ = v_isSharedCheck_2073_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2073_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_array_get_size(v_a_2061_);
lean_dec(v_a_2061_);
v___x_2068_ = lean_nat_dec_lt(v___x_2066_, v___x_2067_);
v___x_2069_ = lean_box(v___x_2068_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2069_);
v___x_2071_ = v___x_2064_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_a_2062_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2074_ = lean_ctor_get(v___x_2060_, 0);
v_a_2075_ = lean_ctor_get(v___x_2060_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2060_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_inc(v_a_2074_);
lean_dec(v___x_2060_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2074_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec(v___x_2058_);
lean_dec(v_val_2057_);
v___x_2083_ = lean_box(v___x_2055_);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v_a_2054_);
return v___x_2084_;
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec(v___x_2056_);
v___x_2085_ = lean_box(v___x_2055_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v_a_2054_);
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object* v_stx_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_2087_, v_a_2088_, v_a_2089_);
lean_dec_ref(v_a_2088_);
lean_dec(v_stx_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object* v_msg_2091_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = lean_panic_fn_borrowed(v___x_2092_, v_msg_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object* v_x2_2094_, lean_object* v_as_2095_, size_t v_i_2096_, size_t v_stop_2097_){
_start:
{
uint8_t v___x_2098_; 
v___x_2098_ = lean_usize_dec_eq(v_i_2096_, v_stop_2097_);
if (v___x_2098_ == 0)
{
lean_object* v_startPos_2099_; lean_object* v___x_2100_; lean_object* v_start_2101_; uint8_t v___x_2102_; 
v_startPos_2099_ = lean_ctor_get(v_x2_2094_, 4);
v___x_2100_ = lean_array_uget_borrowed(v_as_2095_, v_i_2096_);
v_start_2101_ = lean_ctor_get(v___x_2100_, 0);
v___x_2102_ = lean_nat_dec_le(v_startPos_2099_, v_start_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; 
v___x_2103_ = 1;
return v___x_2103_;
}
else
{
size_t v___x_2104_; size_t v___x_2105_; 
v___x_2104_ = ((size_t)1ULL);
v___x_2105_ = lean_usize_add(v_i_2096_, v___x_2104_);
v_i_2096_ = v___x_2105_;
goto _start;
}
}
else
{
uint8_t v___x_2107_; 
v___x_2107_ = 0;
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object* v_x2_2108_, lean_object* v_as_2109_, lean_object* v_i_2110_, lean_object* v_stop_2111_){
_start:
{
size_t v_i_boxed_2112_; size_t v_stop_boxed_2113_; uint8_t v_res_2114_; lean_object* v_r_2115_; 
v_i_boxed_2112_ = lean_unbox_usize(v_i_2110_);
lean_dec(v_i_2110_);
v_stop_boxed_2113_ = lean_unbox_usize(v_stop_2111_);
lean_dec(v_stop_2111_);
v_res_2114_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v_x2_2108_, v_as_2109_, v_i_boxed_2112_, v_stop_boxed_2113_);
lean_dec_ref(v_as_2109_);
lean_dec_ref(v_x2_2108_);
v_r_2115_ = lean_box(v_res_2114_);
return v_r_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object* v_as_2116_, size_t v_i_2117_, size_t v_stop_2118_, lean_object* v_b_2119_){
_start:
{
lean_object* v___y_2121_; uint8_t v___x_2125_; 
v___x_2125_ = lean_usize_dec_eq(v_i_2117_, v_stop_2118_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v_length_2127_; lean_object* v_indentation_2128_; lean_object* v_tokenRanges_2129_; lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2126_ = lean_array_uget_borrowed(v_as_2116_, v_i_2117_);
v_length_2127_ = lean_ctor_get(v___x_2126_, 0);
v_indentation_2128_ = lean_ctor_get(v___x_2126_, 1);
v_tokenRanges_2129_ = lean_ctor_get(v___x_2126_, 3);
v___x_2133_ = lean_unsigned_to_nat(0u);
v___x_2134_ = lean_array_get_size(v_tokenRanges_2129_);
v___x_2135_ = lean_nat_dec_lt(v___x_2133_, v___x_2134_);
if (v___x_2135_ == 0)
{
goto v___jp_2130_;
}
else
{
if (v___x_2135_ == 0)
{
goto v___jp_2130_;
}
else
{
size_t v___x_2136_; size_t v___x_2137_; uint8_t v___x_2138_; 
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = lean_usize_of_nat(v___x_2134_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v___x_2126_, v_tokenRanges_2129_, v___x_2136_, v___x_2137_);
if (v___x_2138_ == 0)
{
goto v___jp_2130_;
}
else
{
v___y_2121_ = v_b_2119_;
goto v___jp_2120_;
}
}
}
v___jp_2130_:
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_nat_dec_lt(v_indentation_2128_, v_length_2127_);
if (v___x_2131_ == 0)
{
v___y_2121_ = v_b_2119_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2132_; 
lean_inc(v___x_2126_);
v___x_2132_ = lean_array_push(v_b_2119_, v___x_2126_);
v___y_2121_ = v___x_2132_;
goto v___jp_2120_;
}
}
}
else
{
return v_b_2119_;
}
v___jp_2120_:
{
size_t v___x_2122_; size_t v___x_2123_; 
v___x_2122_ = ((size_t)1ULL);
v___x_2123_ = lean_usize_add(v_i_2117_, v___x_2122_);
v_i_2117_ = v___x_2123_;
v_b_2119_ = v___y_2121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object* v_as_2139_, lean_object* v_i_2140_, lean_object* v_stop_2141_, lean_object* v_b_2142_){
_start:
{
size_t v_i_boxed_2143_; size_t v_stop_boxed_2144_; lean_object* v_res_2145_; 
v_i_boxed_2143_ = lean_unbox_usize(v_i_2140_);
lean_dec(v_i_2140_);
v_stop_boxed_2144_ = lean_unbox_usize(v_stop_2141_);
lean_dec(v_stop_2141_);
v_res_2145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v_as_2139_, v_i_boxed_2143_, v_stop_boxed_2144_, v_b_2142_);
lean_dec_ref(v_as_2139_);
return v_res_2145_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object* v___x_2146_, lean_object* v___x_2147_, lean_object* v___x_2148_, lean_object* v_as_2149_, size_t v_i_2150_, size_t v_stop_2151_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_eq(v_i_2150_, v_stop_2151_);
if (v___x_2152_ == 0)
{
uint8_t v___x_2153_; uint8_t v___y_2155_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2153_ = 1;
v___x_2159_ = lean_array_uget_borrowed(v_as_2149_, v_i_2150_);
v___x_2160_ = lean_nat_dec_le(v___x_2146_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_unsigned_to_nat(1u);
v___x_2162_ = lean_nat_dec_lt(v___x_2161_, v___x_2147_);
v___y_2155_ = v___x_2162_;
goto v___jp_2154_;
}
else
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_nat_dec_le(v___x_2146_, v___x_2148_);
v___y_2155_ = v___x_2163_;
goto v___jp_2154_;
}
v___jp_2154_:
{
if (v___y_2155_ == 0)
{
size_t v___x_2156_; size_t v___x_2157_; 
v___x_2156_ = ((size_t)1ULL);
v___x_2157_ = lean_usize_add(v_i_2150_, v___x_2156_);
v_i_2150_ = v___x_2157_;
goto _start;
}
else
{
return v___x_2153_;
}
}
}
else
{
uint8_t v___x_2164_; 
v___x_2164_ = 0;
return v___x_2164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object* v___x_2165_, lean_object* v___x_2166_, lean_object* v___x_2167_, lean_object* v_as_2168_, lean_object* v_i_2169_, lean_object* v_stop_2170_){
_start:
{
size_t v_i_boxed_2171_; size_t v_stop_boxed_2172_; uint8_t v_res_2173_; lean_object* v_r_2174_; 
v_i_boxed_2171_ = lean_unbox_usize(v_i_2169_);
lean_dec(v_i_2169_);
v_stop_boxed_2172_ = lean_unbox_usize(v_stop_2170_);
lean_dec(v_stop_2170_);
v_res_2173_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2165_, v___x_2166_, v___x_2167_, v_as_2168_, v_i_boxed_2171_, v_stop_boxed_2172_);
lean_dec_ref(v_as_2168_);
lean_dec(v___x_2167_);
lean_dec(v___x_2166_);
lean_dec(v___x_2165_);
v_r_2174_ = lean_box(v_res_2173_);
return v_r_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t v_sz_2175_, size_t v_i_2176_, lean_object* v_bs_2177_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_usize_dec_lt(v_i_2176_, v_sz_2175_);
if (v___x_2178_ == 0)
{
return v_bs_2177_;
}
else
{
lean_object* v_v_2179_; lean_object* v_indentation_2180_; lean_object* v___x_2181_; lean_object* v_bs_x27_2182_; size_t v___x_2183_; size_t v___x_2184_; lean_object* v___x_2185_; 
v_v_2179_ = lean_array_uget_borrowed(v_bs_2177_, v_i_2176_);
v_indentation_2180_ = lean_ctor_get(v_v_2179_, 1);
lean_inc(v_indentation_2180_);
v___x_2181_ = lean_unsigned_to_nat(0u);
v_bs_x27_2182_ = lean_array_uset(v_bs_2177_, v_i_2176_, v___x_2181_);
v___x_2183_ = ((size_t)1ULL);
v___x_2184_ = lean_usize_add(v_i_2176_, v___x_2183_);
v___x_2185_ = lean_array_uset(v_bs_x27_2182_, v_i_2176_, v_indentation_2180_);
v_i_2176_ = v___x_2184_;
v_bs_2177_ = v___x_2185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object* v_sz_2187_, lean_object* v_i_2188_, lean_object* v_bs_2189_){
_start:
{
size_t v_sz_boxed_2190_; size_t v_i_boxed_2191_; lean_object* v_res_2192_; 
v_sz_boxed_2190_ = lean_unbox_usize(v_sz_2187_);
lean_dec(v_sz_2187_);
v_i_boxed_2191_ = lean_unbox_usize(v_i_2188_);
lean_dec(v_i_2188_);
v_res_2192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_boxed_2190_, v_i_boxed_2191_, v_bs_2189_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object* v_as_2193_, size_t v_i_2194_, size_t v_stop_2195_, lean_object* v_b_2196_){
_start:
{
lean_object* v___y_2198_; uint8_t v___x_2202_; 
v___x_2202_ = lean_usize_dec_eq(v_i_2194_, v_stop_2195_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = lean_array_uget_borrowed(v_as_2193_, v_i_2194_);
v___x_2204_ = lean_nat_dec_le(v_b_2196_, v___x_2203_);
if (v___x_2204_ == 0)
{
v___y_2198_ = v___x_2203_;
goto v___jp_2197_;
}
else
{
v___y_2198_ = v_b_2196_;
goto v___jp_2197_;
}
}
else
{
lean_inc(v_b_2196_);
return v_b_2196_;
}
v___jp_2197_:
{
size_t v___x_2199_; size_t v___x_2200_; 
v___x_2199_ = ((size_t)1ULL);
v___x_2200_ = lean_usize_add(v_i_2194_, v___x_2199_);
v_i_2194_ = v___x_2200_;
v_b_2196_ = v___y_2198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object* v_as_2205_, lean_object* v_i_2206_, lean_object* v_stop_2207_, lean_object* v_b_2208_){
_start:
{
size_t v_i_boxed_2209_; size_t v_stop_boxed_2210_; lean_object* v_res_2211_; 
v_i_boxed_2209_ = lean_unbox_usize(v_i_2206_);
lean_dec(v_i_2206_);
v_stop_boxed_2210_ = lean_unbox_usize(v_stop_2207_);
lean_dec(v_stop_2207_);
v_res_2211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_as_2205_, v_i_boxed_2209_, v_stop_boxed_2210_, v_b_2208_);
lean_dec(v_b_2208_);
lean_dec_ref(v_as_2205_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object* v_arr_2212_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_array_fget_borrowed(v_arr_2212_, v___x_2213_);
v___x_2215_ = lean_unsigned_to_nat(1u);
v___x_2216_ = lean_array_get_size(v_arr_2212_);
v___x_2217_ = lean_nat_dec_lt(v___x_2215_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_inc(v___x_2214_);
return v___x_2214_;
}
else
{
size_t v___x_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_of_nat(v___x_2216_);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_arr_2212_, v___x_2218_, v___x_2219_, v___x_2214_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object* v_arr_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2221_);
lean_dec_ref(v_arr_2221_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object* v_arr_2223_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2224_ = lean_array_get_size(v_arr_2223_);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_nat_dec_eq(v___x_2224_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2223_);
v___x_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_box(0);
return v___x_2229_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object* v_arr_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v_arr_2230_);
lean_dec_ref(v_arr_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t v_isFallback_2232_, lean_object* v_stx_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_rawDoc_2237_; lean_object* v___y_2238_; uint8_t v___y_2243_; lean_object* v_rawDoc_2244_; lean_object* v___y_2245_; lean_object* v___y_2262_; lean_object* v___y_2263_; uint8_t v___y_2264_; lean_object* v___y_2267_; lean_object* v___y_2268_; uint8_t v___y_2269_; uint8_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = 0;
v___x_2274_ = l_Lean_Syntax_getPos_x3f(v_stx_2233_, v___x_2273_);
if (lean_obj_tag(v___x_2274_) == 1)
{
lean_object* v_val_2275_; lean_object* v___x_2276_; 
v_val_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_val_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v___x_2276_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2233_, v___x_2273_);
if (lean_obj_tag(v___x_2276_) == 1)
{
lean_object* v_val_2277_; lean_object* v___x_2278_; 
v_val_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc_n(v_val_2277_, 2);
lean_dec_ref_known(v___x_2276_, 1);
lean_inc(v_val_2275_);
v___x_2278_ = l_Lean_Fmt_getLineInfos(v_val_2275_, v_val_2277_, v_a_2234_, v_a_2235_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_indentation_2284_; lean_object* v_line_2285_; lean_object* v_startPos_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; size_t v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2307_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_n(v_a_2279_, 2);
v_a_2280_ = lean_ctor_get(v___x_2278_, 1);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2278_, 2);
v___x_2281_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = lean_array_get_borrowed(v___x_2281_, v_a_2279_, v___x_2282_);
v_indentation_2284_ = lean_ctor_get(v___x_2283_, 1);
lean_inc(v_indentation_2284_);
v_line_2285_ = lean_ctor_get(v___x_2283_, 2);
v_startPos_2286_ = lean_ctor_get(v___x_2283_, 4);
v___x_2287_ = lean_nat_sub(v_val_2275_, v_startPos_2286_);
v___x_2288_ = l_String_Pos_Raw_offsetOfPosAux(v_line_2285_, v___x_2287_, v___x_2282_, v___x_2282_);
lean_dec(v___x_2287_);
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_array_get_size(v_a_2279_);
v___x_2319_ = l_Array_toSubarray___redArg(v_a_2279_, v___x_2289_, v___x_2318_);
v___x_2320_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_2321_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_2319_, v___x_2320_);
v___x_2322_ = lean_array_get_size(v___x_2321_);
v___x_2323_ = lean_nat_dec_lt(v___x_2282_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_dec_ref(v___x_2321_);
v___y_2307_ = v___x_2320_;
goto v___jp_2306_;
}
else
{
size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = lean_usize_of_nat(v___x_2322_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2321_, v___x_2324_, v___x_2325_, v___x_2320_);
lean_dec_ref(v___x_2321_);
v___y_2307_ = v___x_2326_;
goto v___jp_2306_;
}
v___jp_2290_:
{
uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = 1;
v___x_2295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2295_, 0, v___y_2293_);
lean_ctor_set(v___x_2295_, 1, v_val_2275_);
lean_ctor_set(v___x_2295_, 2, v_val_2277_);
lean_inc(v_stx_2233_);
v___x_2296_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2233_, v___x_2294_, v___x_2295_, v_a_2234_, v_a_2280_);
lean_dec_ref_known(v___x_2295_, 3);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v_a_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
v_a_2298_ = lean_ctor_get(v___x_2296_, 1);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2296_, 2);
v___x_2299_ = lean_array_get_size(v_a_2279_);
lean_dec(v_a_2279_);
v___x_2300_ = lean_nat_dec_lt(v___x_2289_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_dec_ref(v___y_2292_);
lean_dec(v___x_2288_);
lean_dec(v_indentation_2284_);
v___y_2262_ = v_a_2298_;
v___y_2263_ = v_a_2297_;
v___y_2264_ = v___x_2300_;
goto v___jp_2261_;
}
else
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_nat_dec_le(v___x_2288_, v_indentation_2284_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = lean_array_get_size(v___y_2292_);
v___x_2303_ = lean_nat_dec_lt(v___x_2282_, v___x_2302_);
if (v___x_2303_ == 0)
{
lean_dec_ref(v___y_2292_);
lean_dec(v___x_2288_);
lean_dec(v_indentation_2284_);
v___y_2267_ = v_a_2298_;
v___y_2268_ = v_a_2297_;
v___y_2269_ = v___x_2300_;
goto v___jp_2266_;
}
else
{
if (v___x_2303_ == 0)
{
lean_dec_ref(v___y_2292_);
lean_dec(v___x_2288_);
lean_dec(v_indentation_2284_);
v___y_2267_ = v_a_2298_;
v___y_2268_ = v_a_2297_;
v___y_2269_ = v___x_2300_;
goto v___jp_2266_;
}
else
{
size_t v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = lean_usize_of_nat(v___x_2302_);
v___x_2305_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2288_, v___x_2299_, v_indentation_2284_, v___y_2292_, v___y_2291_, v___x_2304_);
lean_dec_ref(v___y_2292_);
lean_dec(v_indentation_2284_);
lean_dec(v___x_2288_);
if (v___x_2305_ == 0)
{
v___y_2267_ = v_a_2298_;
v___y_2268_ = v_a_2297_;
v___y_2269_ = v___x_2300_;
goto v___jp_2266_;
}
else
{
v___y_2262_ = v_a_2298_;
v___y_2263_ = v_a_2297_;
v___y_2264_ = v___x_2300_;
goto v___jp_2261_;
}
}
}
}
else
{
lean_dec_ref(v___y_2292_);
lean_dec(v___x_2288_);
lean_dec(v_indentation_2284_);
v___y_2267_ = v_a_2298_;
v___y_2268_ = v_a_2297_;
v___y_2269_ = v___x_2300_;
goto v___jp_2266_;
}
}
}
else
{
lean_dec_ref(v___y_2292_);
lean_dec(v___x_2288_);
lean_dec(v_indentation_2284_);
lean_dec(v_a_2279_);
lean_dec(v_stx_2233_);
return v___x_2296_;
}
}
v___jp_2306_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; size_t v_sz_2310_; size_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2289_);
lean_inc(v___x_2288_);
v___x_2309_ = lean_array_push(v___x_2308_, v___x_2288_);
v_sz_2310_ = lean_array_size(v___y_2307_);
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_2310_, v___x_2311_, v___y_2307_);
v___x_2313_ = l_Array_append___redArg(v___x_2309_, v___x_2312_);
v___x_2314_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v___x_2313_);
lean_dec_ref(v___x_2313_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_2316_ = l_panic___at___00Lean_Fmt_fmtRaw_spec__4(v___x_2315_);
v___y_2291_ = v___x_2311_;
v___y_2292_ = v___x_2312_;
v___y_2293_ = v___x_2316_;
goto v___jp_2290_;
}
else
{
lean_object* v_val_2317_; 
v_val_2317_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_val_2317_);
lean_dec_ref_known(v___x_2314_, 1);
v___y_2291_ = v___x_2311_;
v___y_2292_ = v___x_2312_;
v___y_2293_ = v_val_2317_;
goto v___jp_2290_;
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_val_2277_);
lean_dec(v_val_2275_);
lean_dec(v_stx_2233_);
v_a_2327_ = lean_ctor_get(v___x_2278_, 0);
v_a_2328_ = lean_ctor_get(v___x_2278_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2278_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_inc(v_a_2327_);
lean_dec(v___x_2278_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2327_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec(v___x_2276_);
lean_dec(v_val_2275_);
v___x_2336_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2337_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2336_, v_stx_2233_, v_a_2235_);
lean_dec(v_stx_2233_);
return v___x_2337_;
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_dec(v___x_2274_);
v___x_2338_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2339_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2338_, v_stx_2233_, v_a_2235_);
lean_dec(v_stx_2233_);
return v___x_2339_;
}
v___jp_2236_:
{
if (v_isFallback_2232_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_rawDoc_2237_);
lean_ctor_set(v___x_2239_, 1, v___y_2238_);
return v___x_2239_;
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_rawDoc_2237_);
v___x_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2240_);
lean_ctor_set(v___x_2241_, 1, v___y_2238_);
return v___x_2241_;
}
}
v___jp_2242_:
{
lean_object* v_doc_2246_; lean_object* v_metaData_2247_; lean_object* v___x_2248_; 
v_doc_2246_ = lean_ctor_get(v_rawDoc_2244_, 0);
lean_inc(v_doc_2246_);
v_metaData_2247_ = lean_ctor_get(v_rawDoc_2244_, 1);
lean_inc(v_metaData_2247_);
lean_dec_ref(v_rawDoc_2244_);
v___x_2248_ = l_Lean_Fmt_TaggedDoc_taggedRaw___redArg(v_doc_2246_, v_stx_2233_, v___y_2245_);
lean_dec(v_stx_2233_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v_a_2250_; lean_object* v_doc_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
v_a_2250_ = lean_ctor_get(v___x_2248_, 1);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2248_, 2);
v_doc_2251_ = lean_ctor_get(v_a_2249_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_a_2249_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; 
v_unused_2260_ = lean_ctor_get(v_a_2249_, 1);
lean_dec(v_unused_2260_);
v___x_2253_ = v_a_2249_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_doc_2251_);
lean_dec(v_a_2249_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v_metaData_2247_);
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_doc_2251_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_metaData_2247_);
v___x_2256_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
if (v___y_2243_ == 0)
{
v_rawDoc_2237_ = v___x_2256_;
v___y_2238_ = v_a_2250_;
goto v___jp_2236_;
}
else
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Fmt_TaggedDoc_markMultiLineRaw(v___x_2256_);
v_rawDoc_2237_ = v___x_2257_;
v___y_2238_ = v_a_2250_;
goto v___jp_2236_;
}
}
}
}
else
{
lean_dec(v_metaData_2247_);
return v___x_2248_;
}
}
v___jp_2261_:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2263_);
v___y_2243_ = v___y_2264_;
v_rawDoc_2244_ = v___x_2265_;
v___y_2245_ = v___y_2262_;
goto v___jp_2242_;
}
v___jp_2266_:
{
lean_object* v_doc_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_doc_2270_ = lean_ctor_get(v___y_2268_, 0);
lean_inc(v_doc_2270_);
lean_dec_ref(v___y_2268_);
v___x_2271_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_2270_);
v___x_2272_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2271_);
v___y_2243_ = v___y_2269_;
v_rawDoc_2244_ = v___x_2272_;
v___y_2245_ = v___y_2267_;
goto v___jp_2242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object* v_isFallback_2340_, lean_object* v_stx_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
uint8_t v_isFallback_boxed_2344_; lean_object* v_res_2345_; 
v_isFallback_boxed_2344_ = lean_unbox(v_isFallback_2340_);
v_res_2345_ = l_Lean_Fmt_fmtRaw(v_isFallback_boxed_2344_, v_stx_2341_, v_a_2342_, v_a_2343_);
lean_dec_ref(v_a_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object* v_arr_2346_, lean_object* v_h_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object* v_arr_2349_, lean_object* v_h_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(v_arr_2349_, v_h_2350_);
lean_dec_ref(v_arr_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object* v_a_2352_, lean_object* v_____r_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_a_2352_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v___y_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object* v_a_2358_, lean_object* v_____r_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2358_, v_____r_2359_, v___y_2360_, v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object* v_a_2363_, lean_object* v_b_2364_, lean_object* v_x_2365_){
_start:
{
if (lean_obj_tag(v_x_2365_) == 0)
{
lean_dec(v_b_2364_);
lean_dec_ref(v_a_2363_);
return v_x_2365_;
}
else
{
lean_object* v_key_2366_; lean_object* v_value_2367_; lean_object* v_tail_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2380_; 
v_key_2366_ = lean_ctor_get(v_x_2365_, 0);
v_value_2367_ = lean_ctor_get(v_x_2365_, 1);
v_tail_2368_ = lean_ctor_get(v_x_2365_, 2);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_x_2365_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2370_ = v_x_2365_;
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_tail_2368_);
lean_inc(v_value_2367_);
lean_inc(v_key_2366_);
lean_dec(v_x_2365_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2380_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
uint8_t v___x_2372_; 
v___x_2372_ = l_Lean_Syntax_instBEqRange_beq(v_key_2366_, v_a_2363_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2373_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2363_, v_b_2364_, v_tail_2368_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 2, v___x_2373_);
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_key_2366_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_value_2367_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
else
{
lean_object* v___x_2378_; 
lean_dec(v_value_2367_);
lean_dec(v_key_2366_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v_b_2364_);
lean_ctor_set(v___x_2370_, 0, v_a_2363_);
v___x_2378_ = v___x_2370_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2363_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_b_2364_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_tail_2368_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
if (lean_obj_tag(v_x_2382_) == 0)
{
return v_x_2381_;
}
else
{
lean_object* v_key_2383_; lean_object* v_value_2384_; lean_object* v_tail_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2408_; 
v_key_2383_ = lean_ctor_get(v_x_2382_, 0);
v_value_2384_ = lean_ctor_get(v_x_2382_, 1);
v_tail_2385_ = lean_ctor_get(v_x_2382_, 2);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_x_2382_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2387_ = v_x_2382_;
v_isShared_2388_ = v_isSharedCheck_2408_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_tail_2385_);
lean_inc(v_value_2384_);
lean_inc(v_key_2383_);
lean_dec(v_x_2382_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2408_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; uint64_t v___x_2390_; uint64_t v___x_2391_; uint64_t v___x_2392_; uint64_t v_fold_2393_; uint64_t v___x_2394_; uint64_t v___x_2395_; uint64_t v___x_2396_; size_t v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; size_t v___x_2400_; size_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2389_ = lean_array_get_size(v_x_2381_);
v___x_2390_ = l_Lean_Syntax_instHashableRange_hash(v_key_2383_);
v___x_2391_ = 32ULL;
v___x_2392_ = lean_uint64_shift_right(v___x_2390_, v___x_2391_);
v_fold_2393_ = lean_uint64_xor(v___x_2390_, v___x_2392_);
v___x_2394_ = 16ULL;
v___x_2395_ = lean_uint64_shift_right(v_fold_2393_, v___x_2394_);
v___x_2396_ = lean_uint64_xor(v_fold_2393_, v___x_2395_);
v___x_2397_ = lean_uint64_to_usize(v___x_2396_);
v___x_2398_ = lean_usize_of_nat(v___x_2389_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = lean_usize_sub(v___x_2398_, v___x_2399_);
v___x_2401_ = lean_usize_land(v___x_2397_, v___x_2400_);
v___x_2402_ = lean_array_uget_borrowed(v_x_2381_, v___x_2401_);
lean_inc(v___x_2402_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 2, v___x_2402_);
v___x_2404_ = v___x_2387_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_key_2383_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_value_2384_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_array_uset(v_x_2381_, v___x_2401_, v___x_2404_);
v_x_2381_ = v___x_2405_;
v_x_2382_ = v_tail_2385_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2409_, lean_object* v_source_2410_, lean_object* v_target_2411_){
_start:
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = lean_array_get_size(v_source_2410_);
v___x_2413_ = lean_nat_dec_lt(v_i_2409_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_dec_ref(v_source_2410_);
lean_dec(v_i_2409_);
return v_target_2411_;
}
else
{
lean_object* v_es_2414_; lean_object* v___x_2415_; lean_object* v_source_2416_; lean_object* v_target_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_es_2414_ = lean_array_fget(v_source_2410_, v_i_2409_);
v___x_2415_ = lean_box(0);
v_source_2416_ = lean_array_fset(v_source_2410_, v_i_2409_, v___x_2415_);
v_target_2417_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2411_, v_es_2414_);
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_nat_add(v_i_2409_, v___x_2418_);
lean_dec(v_i_2409_);
v_i_2409_ = v___x_2419_;
v_source_2410_ = v_source_2416_;
v_target_2411_ = v_target_2417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object* v_data_2421_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v_nbuckets_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2422_ = lean_array_get_size(v_data_2421_);
v___x_2423_ = lean_unsigned_to_nat(2u);
v_nbuckets_2424_ = lean_nat_mul(v___x_2422_, v___x_2423_);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_box(0);
v___x_2427_ = lean_mk_array(v_nbuckets_2424_, v___x_2426_);
v___x_2428_ = lean_array_propagate_mark(v_data_2421_, v___x_2427_);
v___x_2429_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v___x_2425_, v_data_2421_, v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object* v_a_2430_, lean_object* v_x_2431_){
_start:
{
if (lean_obj_tag(v_x_2431_) == 0)
{
uint8_t v___x_2432_; 
v___x_2432_ = 0;
return v___x_2432_;
}
else
{
lean_object* v_key_2433_; lean_object* v_tail_2434_; uint8_t v___x_2435_; 
v_key_2433_ = lean_ctor_get(v_x_2431_, 0);
v_tail_2434_ = lean_ctor_get(v_x_2431_, 2);
v___x_2435_ = l_Lean_Syntax_instBEqRange_beq(v_key_2433_, v_a_2430_);
if (v___x_2435_ == 0)
{
v_x_2431_ = v_tail_2434_;
goto _start;
}
else
{
return v___x_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object* v_a_2437_, lean_object* v_x_2438_){
_start:
{
uint8_t v_res_2439_; lean_object* v_r_2440_; 
v_res_2439_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2437_, v_x_2438_);
lean_dec(v_x_2438_);
lean_dec_ref(v_a_2437_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object* v_m_2441_, lean_object* v_a_2442_, lean_object* v_b_2443_){
_start:
{
lean_object* v_size_2444_; lean_object* v_buckets_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2488_; 
v_size_2444_ = lean_ctor_get(v_m_2441_, 0);
v_buckets_2445_ = lean_ctor_get(v_m_2441_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_m_2441_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2447_ = v_m_2441_;
v_isShared_2448_ = v_isSharedCheck_2488_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_buckets_2445_);
lean_inc(v_size_2444_);
lean_dec(v_m_2441_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2488_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; uint64_t v___x_2450_; uint64_t v___x_2451_; uint64_t v___x_2452_; uint64_t v_fold_2453_; uint64_t v___x_2454_; uint64_t v___x_2455_; uint64_t v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; size_t v___x_2461_; lean_object* v_bkt_2462_; uint8_t v___x_2463_; 
v___x_2449_ = lean_array_get_size(v_buckets_2445_);
v___x_2450_ = l_Lean_Syntax_instHashableRange_hash(v_a_2442_);
v___x_2451_ = 32ULL;
v___x_2452_ = lean_uint64_shift_right(v___x_2450_, v___x_2451_);
v_fold_2453_ = lean_uint64_xor(v___x_2450_, v___x_2452_);
v___x_2454_ = 16ULL;
v___x_2455_ = lean_uint64_shift_right(v_fold_2453_, v___x_2454_);
v___x_2456_ = lean_uint64_xor(v_fold_2453_, v___x_2455_);
v___x_2457_ = lean_uint64_to_usize(v___x_2456_);
v___x_2458_ = lean_usize_of_nat(v___x_2449_);
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_sub(v___x_2458_, v___x_2459_);
v___x_2461_ = lean_usize_land(v___x_2457_, v___x_2460_);
v_bkt_2462_ = lean_array_uget_borrowed(v_buckets_2445_, v___x_2461_);
v___x_2463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2442_, v_bkt_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v_size_x27_2465_; lean_object* v___x_2466_; lean_object* v_buckets_x27_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2464_ = lean_unsigned_to_nat(1u);
v_size_x27_2465_ = lean_nat_add(v_size_2444_, v___x_2464_);
lean_dec(v_size_2444_);
lean_inc(v_bkt_2462_);
v___x_2466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2466_, 0, v_a_2442_);
lean_ctor_set(v___x_2466_, 1, v_b_2443_);
lean_ctor_set(v___x_2466_, 2, v_bkt_2462_);
v_buckets_x27_2467_ = lean_array_uset(v_buckets_2445_, v___x_2461_, v___x_2466_);
v___x_2468_ = lean_unsigned_to_nat(4u);
v___x_2469_ = lean_nat_mul(v_size_x27_2465_, v___x_2468_);
v___x_2470_ = lean_unsigned_to_nat(3u);
v___x_2471_ = lean_nat_div(v___x_2469_, v___x_2470_);
lean_dec(v___x_2469_);
v___x_2472_ = lean_array_get_size(v_buckets_x27_2467_);
v___x_2473_ = lean_nat_dec_le(v___x_2471_, v___x_2472_);
lean_dec(v___x_2471_);
if (v___x_2473_ == 0)
{
lean_object* v_val_2474_; lean_object* v___x_2476_; 
v_val_2474_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_buckets_x27_2467_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v_val_2474_);
lean_ctor_set(v___x_2447_, 0, v_size_x27_2465_);
v___x_2476_ = v___x_2447_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_size_x27_2465_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_val_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
else
{
lean_object* v___x_2479_; 
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v_buckets_x27_2467_);
lean_ctor_set(v___x_2447_, 0, v_size_x27_2465_);
v___x_2479_ = v___x_2447_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_size_x27_2465_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_buckets_x27_2467_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_object* v___x_2481_; lean_object* v_buckets_x27_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
lean_inc(v_bkt_2462_);
v___x_2481_ = lean_box(0);
v_buckets_x27_2482_ = lean_array_uset(v_buckets_2445_, v___x_2461_, v___x_2481_);
v___x_2483_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2442_, v_b_2443_, v_bkt_2462_);
v___x_2484_ = lean_array_uset(v_buckets_x27_2482_, v___x_2461_, v___x_2483_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v___x_2484_);
v___x_2486_ = v___x_2447_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_size_2444_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object* v_f_2489_, lean_object* v_formatterName_2490_, lean_object* v_stx_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___y_2495_; lean_object* v_a_2507_; lean_object* v_a_2508_; lean_object* v___x_2544_; 
lean_inc_ref(v_a_2492_);
lean_inc(v_stx_2491_);
v___x_2544_ = lean_apply_3(v_f_2489_, v_stx_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v_a_2546_; lean_object* v___x_2547_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
v_a_2546_ = lean_ctor_get(v___x_2544_, 1);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2544_, 2);
v___x_2547_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_a_2545_, v_stx_2491_, v_a_2546_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_stx_2491_);
lean_dec(v_formatterName_2490_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 1);
v_a_2549_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2551_ = v___x_2547_;
v_isShared_2552_ = v_isSharedCheck_2573_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2548_);
lean_inc(v_a_2549_);
lean_dec(v___x_2547_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2573_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_toBacktrackableState_2553_; lean_object* v_shareCommonState_2554_; lean_object* v_freshTagId_2555_; lean_object* v_missingFormatters_2556_; lean_object* v_partialFormatters_2557_; lean_object* v_missingChoiceResolutions_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2572_; 
v_toBacktrackableState_2553_ = lean_ctor_get(v_a_2548_, 0);
v_shareCommonState_2554_ = lean_ctor_get(v_a_2548_, 1);
v_freshTagId_2555_ = lean_ctor_get(v_a_2548_, 2);
v_missingFormatters_2556_ = lean_ctor_get(v_a_2548_, 3);
v_partialFormatters_2557_ = lean_ctor_get(v_a_2548_, 4);
v_missingChoiceResolutions_2558_ = lean_ctor_get(v_a_2548_, 5);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_a_2548_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2560_ = v_a_2548_;
v_isShared_2561_ = v_isSharedCheck_2572_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_missingChoiceResolutions_2558_);
lean_inc(v_partialFormatters_2557_);
lean_inc(v_missingFormatters_2556_);
lean_inc(v_freshTagId_2555_);
lean_inc(v_shareCommonState_2554_);
lean_inc(v_toBacktrackableState_2553_);
lean_dec(v_a_2548_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2572_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v___x_2567_; 
v___x_2562_ = l_Lean_ShareCommon_objectFactory;
v___x_2563_ = lean_state_sharecommon(v___x_2562_, v_shareCommonState_2554_, v_a_2549_);
v_fst_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_fst_2564_);
v_snd_2565_ = lean_ctor_get(v___x_2563_, 1);
lean_inc(v_snd_2565_);
lean_dec_ref(v___x_2563_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 1, v_snd_2565_);
v___x_2567_ = v___x_2560_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_toBacktrackableState_2553_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_snd_2565_);
lean_ctor_set(v_reuseFailAlloc_2571_, 2, v_freshTagId_2555_);
lean_ctor_set(v_reuseFailAlloc_2571_, 3, v_missingFormatters_2556_);
lean_ctor_set(v_reuseFailAlloc_2571_, 4, v_partialFormatters_2557_);
lean_ctor_set(v_reuseFailAlloc_2571_, 5, v_missingChoiceResolutions_2558_);
v___x_2567_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2569_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 1, v___x_2567_);
lean_ctor_set(v___x_2551_, 0, v_fst_2564_);
v___x_2569_ = v___x_2551_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_fst_2564_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v_a_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2574_);
v_a_2575_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2547_, 2);
v_a_2507_ = v_a_2574_;
v_a_2508_ = v_a_2575_;
goto v___jp_2506_;
}
}
else
{
lean_object* v_a_2576_; lean_object* v_a_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2576_);
v_a_2577_ = lean_ctor_get(v___x_2544_, 1);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2544_, 2);
v_a_2507_ = v_a_2576_;
v_a_2508_ = v_a_2577_;
goto v___jp_2506_;
}
v___jp_2494_:
{
lean_object* v_a_2496_; lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2505_; 
v_a_2496_ = lean_ctor_get(v___y_2495_, 0);
v_a_2497_ = lean_ctor_get(v___y_2495_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___y_2495_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2499_ = v___y_2495_;
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_inc(v_a_2496_);
lean_dec(v___y_2495_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2505_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_a_2501_; lean_object* v___x_2503_; 
v_a_2501_ = lean_ctor_get(v_a_2496_, 0);
lean_inc(v_a_2501_);
lean_dec(v_a_2496_);
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v_a_2501_);
v___x_2503_ = v___x_2499_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2501_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_a_2497_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
v___jp_2506_:
{
if (lean_obj_tag(v_a_2507_) == 0)
{
uint8_t v_err_2509_; 
v_err_2509_ = lean_ctor_get_uint8(v_a_2507_, 0);
if (v_err_2509_ == 0)
{
uint8_t v___x_2510_; lean_object* v___x_2511_; 
lean_dec_ref_known(v_a_2507_, 0);
v___x_2510_ = 1;
lean_inc(v_stx_2491_);
v___x_2511_ = l_Lean_Fmt_fmtRaw(v___x_2510_, v_stx_2491_, v_a_2492_, v_a_2508_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2541_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_a_2513_ = lean_ctor_get(v___x_2511_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2515_ = v___x_2511_;
v_isShared_2516_ = v_isSharedCheck_2541_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2541_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
uint8_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = 0;
v___x_2518_ = l_Lean_Syntax_getRange_x3f(v_stx_2491_, v___x_2517_);
if (lean_obj_tag(v___x_2518_) == 1)
{
lean_object* v_val_2519_; lean_object* v_toBacktrackableState_2520_; lean_object* v_shareCommonState_2521_; lean_object* v_freshTagId_2522_; lean_object* v_missingFormatters_2523_; lean_object* v_partialFormatters_2524_; lean_object* v_missingChoiceResolutions_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2538_; 
v_val_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_val_2519_);
lean_dec_ref_known(v___x_2518_, 1);
v_toBacktrackableState_2520_ = lean_ctor_get(v_a_2513_, 0);
v_shareCommonState_2521_ = lean_ctor_get(v_a_2513_, 1);
v_freshTagId_2522_ = lean_ctor_get(v_a_2513_, 2);
v_missingFormatters_2523_ = lean_ctor_get(v_a_2513_, 3);
v_partialFormatters_2524_ = lean_ctor_get(v_a_2513_, 4);
v_missingChoiceResolutions_2525_ = lean_ctor_get(v_a_2513_, 5);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_a_2513_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2527_ = v_a_2513_;
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_missingChoiceResolutions_2525_);
lean_inc(v_partialFormatters_2524_);
lean_inc(v_missingFormatters_2523_);
lean_inc(v_freshTagId_2522_);
lean_inc(v_shareCommonState_2521_);
lean_inc(v_toBacktrackableState_2520_);
lean_dec(v_a_2513_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2529_ = lean_box(0);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 1, v_formatterName_2490_);
lean_ctor_set(v___x_2515_, 0, v_stx_2491_);
v___x_2531_ = v___x_2515_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_stx_2491_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_formatterName_2490_);
v___x_2531_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_partialFormatters_2524_, v_val_2519_, v___x_2531_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 4, v___x_2532_);
v___x_2534_ = v___x_2527_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_toBacktrackableState_2520_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_shareCommonState_2521_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_freshTagId_2522_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_missingFormatters_2523_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v___x_2532_);
lean_ctor_set(v_reuseFailAlloc_2536_, 5, v_missingChoiceResolutions_2525_);
v___x_2534_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2512_, v___x_2529_, v_a_2492_, v___x_2534_);
v___y_2495_ = v___x_2535_;
goto v___jp_2494_;
}
}
}
}
else
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v___x_2518_);
lean_del_object(v___x_2515_);
lean_dec(v_stx_2491_);
lean_dec(v_formatterName_2490_);
v___x_2539_ = lean_box(0);
v___x_2540_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2512_, v___x_2539_, v_a_2492_, v_a_2513_);
v___y_2495_ = v___x_2540_;
goto v___jp_2494_;
}
}
}
else
{
lean_dec(v_stx_2491_);
lean_dec(v_formatterName_2490_);
return v___x_2511_;
}
}
else
{
lean_object* v___x_2542_; 
lean_dec(v_stx_2491_);
lean_dec(v_formatterName_2490_);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_a_2507_);
lean_ctor_set(v___x_2542_, 1, v_a_2508_);
return v___x_2542_;
}
}
else
{
lean_object* v___x_2543_; 
lean_dec(v_stx_2491_);
lean_dec(v_formatterName_2490_);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v_a_2507_);
lean_ctor_set(v___x_2543_, 1, v_a_2508_);
return v___x_2543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object* v_f_2578_, lean_object* v_formatterName_2579_, lean_object* v_stx_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_Fmt_fmtWith(v_f_2578_, v_formatterName_2579_, v_stx_2580_, v_a_2581_, v_a_2582_);
lean_dec_ref(v_a_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object* v_00_u03b2_2584_, lean_object* v_m_2585_, lean_object* v_a_2586_, lean_object* v_b_2587_){
_start:
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_m_2585_, v_a_2586_, v_b_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object* v_00_u03b2_2589_, lean_object* v_a_2590_, lean_object* v_x_2591_){
_start:
{
uint8_t v___x_2592_; 
v___x_2592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2590_, v_x_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2593_, lean_object* v_a_2594_, lean_object* v_x_2595_){
_start:
{
uint8_t v_res_2596_; lean_object* v_r_2597_; 
v_res_2596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(v_00_u03b2_2593_, v_a_2594_, v_x_2595_);
lean_dec(v_x_2595_);
lean_dec_ref(v_a_2594_);
v_r_2597_ = lean_box(v_res_2596_);
return v_r_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object* v_00_u03b2_2598_, lean_object* v_data_2599_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_data_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object* v_00_u03b2_2601_, lean_object* v_a_2602_, lean_object* v_b_2603_, lean_object* v_x_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2602_, v_b_2603_, v_x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2606_, lean_object* v_i_2607_, lean_object* v_source_2608_, lean_object* v_target_2609_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v_i_2607_, v_source_2608_, v_target_2609_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2611_, lean_object* v_x_2612_, lean_object* v_x_2613_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2612_, v_x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object* v_a_2618_, lean_object* v_kind_2619_, lean_object* v_as_2620_, size_t v_sz_2621_, size_t v_i_2622_, lean_object* v_b_2623_){
_start:
{
uint8_t v___x_2624_; 
v___x_2624_ = lean_usize_dec_lt(v_i_2622_, v_sz_2621_);
if (v___x_2624_ == 0)
{
lean_dec(v_kind_2619_);
lean_inc_ref(v_b_2623_);
return v_b_2623_;
}
else
{
lean_object* v_a_2625_; lean_object* v_provider_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2642_; 
v_a_2625_ = lean_array_uget(v_as_2620_, v_i_2622_);
v_provider_2626_ = lean_ctor_get(v_a_2625_, 1);
v_isSharedCheck_2642_ = !lean_is_exclusive(v_a_2625_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v_a_2625_, 0);
lean_dec(v_unused_2643_);
v___x_2628_ = v_a_2625_;
v_isShared_2629_ = v_isSharedCheck_2642_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_provider_2626_);
lean_dec(v_a_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2642_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_env_2630_; lean_object* v_opts_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_env_2630_ = lean_ctor_get(v_a_2618_, 0);
v_opts_2631_ = lean_ctor_get(v_a_2618_, 3);
v___x_2632_ = lean_box(0);
lean_inc(v_kind_2619_);
lean_inc_ref(v_opts_2631_);
lean_inc_ref(v_env_2630_);
v___x_2633_ = lean_apply_3(v_provider_2626_, v_env_2630_, v_opts_2631_, v_kind_2619_);
if (lean_obj_tag(v___x_2633_) == 1)
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
lean_dec(v_kind_2619_);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 1, v___x_2632_);
lean_ctor_set(v___x_2628_, 0, v___x_2634_);
v___x_2636_ = v___x_2628_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2632_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v___x_2638_; size_t v___x_2639_; size_t v___x_2640_; 
lean_dec(v___x_2633_);
lean_del_object(v___x_2628_);
v___x_2638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v___x_2639_ = ((size_t)1ULL);
v___x_2640_ = lean_usize_add(v_i_2622_, v___x_2639_);
v_i_2622_ = v___x_2640_;
v_b_2623_ = v___x_2638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object* v_a_2644_, lean_object* v_kind_2645_, lean_object* v_as_2646_, lean_object* v_sz_2647_, lean_object* v_i_2648_, lean_object* v_b_2649_){
_start:
{
size_t v_sz_boxed_2650_; size_t v_i_boxed_2651_; lean_object* v_res_2652_; 
v_sz_boxed_2650_ = lean_unbox_usize(v_sz_2647_);
lean_dec(v_sz_2647_);
v_i_boxed_2651_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_res_2652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2644_, v_kind_2645_, v_as_2646_, v_sz_boxed_2650_, v_i_boxed_2651_, v_b_2649_);
lean_dec_ref(v_b_2649_);
lean_dec_ref(v_as_2646_);
lean_dec_ref(v_a_2644_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object* v_kind_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_env_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; size_t v_sz_2660_; size_t v___x_2661_; lean_object* v___x_2662_; lean_object* v_fst_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2674_; 
v_env_2656_ = lean_ctor_get(v_a_2654_, 0);
lean_inc_ref(v_env_2656_);
v___x_2657_ = l_Lean_Fmt_getFmtProviders(v_env_2656_);
v___x_2658_ = lean_box(0);
v___x_2659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v_sz_2660_ = lean_array_size(v___x_2657_);
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2654_, v_kind_2653_, v___x_2657_, v_sz_2660_, v___x_2661_, v___x_2659_);
lean_dec_ref(v___x_2657_);
v_fst_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; 
v_unused_2675_ = lean_ctor_get(v___x_2662_, 1);
lean_dec(v_unused_2675_);
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_fst_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
if (lean_obj_tag(v_fst_2663_) == 0)
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v_a_2655_);
lean_ctor_set(v___x_2665_, 0, v___x_2658_);
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_a_2655_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2672_; 
v_val_2670_ = lean_ctor_get(v_fst_2663_, 0);
lean_inc(v_val_2670_);
lean_dec_ref_known(v_fst_2663_, 1);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 1, v_a_2655_);
lean_ctor_set(v___x_2665_, 0, v_val_2670_);
v___x_2672_ = v___x_2665_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_val_2670_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_a_2655_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object* v_kind_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2676_, v_a_2677_, v_a_2678_);
lean_dec_ref(v_a_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object* v_stx_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
switch(lean_obj_tag(v_stx_2680_))
{
case 0:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v_a_2682_);
return v___x_2684_;
}
case 1:
{
lean_object* v_kind_2685_; lean_object* v___x_2686_; lean_object* v_a_2687_; 
lean_inc_ref(v_stx_2680_);
v_kind_2685_ = l_Lean_Syntax_getKind(v_stx_2680_);
lean_inc(v_kind_2685_);
v___x_2686_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2685_, v_a_2681_, v_a_2682_);
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
if (lean_obj_tag(v_a_2687_) == 1)
{
lean_object* v_val_2688_; lean_object* v_a_2689_; lean_object* v_fst_2690_; lean_object* v_snd_2691_; lean_object* v___x_2692_; 
lean_dec(v_kind_2685_);
v_val_2688_ = lean_ctor_get(v_a_2687_, 0);
lean_inc(v_val_2688_);
v_a_2689_ = lean_ctor_get(v___x_2686_, 1);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2686_);
v_fst_2690_ = lean_ctor_get(v_val_2688_, 0);
lean_inc(v_fst_2690_);
v_snd_2691_ = lean_ctor_get(v_val_2688_, 1);
lean_inc(v_snd_2691_);
lean_dec(v_val_2688_);
v___x_2692_ = l_Lean_Fmt_fmtWith(v_snd_2691_, v_fst_2690_, v_stx_2680_, v_a_2681_, v_a_2689_);
return v___x_2692_;
}
else
{
lean_object* v_a_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; 
v_a_2693_ = lean_ctor_get(v___x_2686_, 1);
lean_inc(v_a_2693_);
lean_dec_ref(v___x_2686_);
v___x_2694_ = 1;
lean_inc_ref(v_stx_2680_);
v___x_2695_ = l_Lean_Fmt_fmtRaw(v___x_2694_, v_stx_2680_, v_a_2681_, v_a_2693_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v_a_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
v_a_2697_ = lean_ctor_get(v___x_2695_, 1);
lean_inc(v_a_2697_);
v___x_2698_ = 0;
v___x_2699_ = l_Lean_Syntax_getRange_x3f(v_stx_2680_, v___x_2698_);
lean_dec_ref_known(v_stx_2680_, 3);
if (lean_obj_tag(v___x_2699_) == 1)
{
lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2721_; 
lean_inc(v_a_2696_);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; lean_object* v_unused_2723_; 
v_unused_2722_ = lean_ctor_get(v___x_2695_, 1);
lean_dec(v_unused_2722_);
v_unused_2723_ = lean_ctor_get(v___x_2695_, 0);
lean_dec(v_unused_2723_);
v___x_2701_ = v___x_2695_;
v_isShared_2702_ = v_isSharedCheck_2721_;
goto v_resetjp_2700_;
}
else
{
lean_dec(v___x_2695_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2721_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v_val_2703_; lean_object* v_toBacktrackableState_2704_; lean_object* v_shareCommonState_2705_; lean_object* v_freshTagId_2706_; lean_object* v_missingFormatters_2707_; lean_object* v_partialFormatters_2708_; lean_object* v_missingChoiceResolutions_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2720_; 
v_val_2703_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_val_2703_);
lean_dec_ref_known(v___x_2699_, 1);
v_toBacktrackableState_2704_ = lean_ctor_get(v_a_2697_, 0);
v_shareCommonState_2705_ = lean_ctor_get(v_a_2697_, 1);
v_freshTagId_2706_ = lean_ctor_get(v_a_2697_, 2);
v_missingFormatters_2707_ = lean_ctor_get(v_a_2697_, 3);
v_partialFormatters_2708_ = lean_ctor_get(v_a_2697_, 4);
v_missingChoiceResolutions_2709_ = lean_ctor_get(v_a_2697_, 5);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_a_2697_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2711_ = v_a_2697_;
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_missingChoiceResolutions_2709_);
lean_inc(v_partialFormatters_2708_);
lean_inc(v_missingFormatters_2707_);
lean_inc(v_freshTagId_2706_);
lean_inc(v_shareCommonState_2705_);
lean_inc(v_toBacktrackableState_2704_);
lean_dec(v_a_2697_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2720_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingFormatters_2707_, v_val_2703_, v_kind_2685_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 3, v___x_2713_);
v___x_2715_ = v___x_2711_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_toBacktrackableState_2704_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_shareCommonState_2705_);
lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_freshTagId_2706_);
lean_ctor_set(v_reuseFailAlloc_2719_, 3, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2719_, 4, v_partialFormatters_2708_);
lean_ctor_set(v_reuseFailAlloc_2719_, 5, v_missingChoiceResolutions_2709_);
v___x_2715_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2717_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2715_);
v___x_2717_ = v___x_2701_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2696_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
}
else
{
lean_dec(v___x_2699_);
lean_dec(v_a_2697_);
lean_dec(v_kind_2685_);
return v___x_2695_;
}
}
else
{
lean_dec(v_kind_2685_);
lean_dec_ref_known(v_stx_2680_, 3);
return v___x_2695_;
}
}
}
case 2:
{
lean_object* v_val_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_val_2724_ = lean_ctor_get(v_stx_2680_, 1);
lean_inc_ref(v_val_2724_);
v___x_2725_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(v_val_2724_);
v___x_2726_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_2725_, v_stx_2680_, v_a_2682_);
lean_dec_ref_known(v_stx_2680_, 2);
return v___x_2726_;
}
default: 
{
lean_object* v_rawVal_2727_; lean_object* v_str_2728_; lean_object* v_startPos_2729_; lean_object* v_stopPos_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v_rawVal_2727_ = lean_ctor_get(v_stx_2680_, 1);
v_str_2728_ = lean_ctor_get(v_rawVal_2727_, 0);
v_startPos_2729_ = lean_ctor_get(v_rawVal_2727_, 1);
v_stopPos_2730_ = lean_ctor_get(v_rawVal_2727_, 2);
v___x_2731_ = lean_string_utf8_extract(v_str_2728_, v_startPos_2729_, v_stopPos_2730_);
v___x_2732_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_tokenDoc(v___x_2731_);
v___x_2733_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_2732_, v_stx_2680_, v_a_2682_);
lean_dec_ref_known(v_stx_2680_, 4);
return v___x_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object* v_stx_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Fmt_fmt(v_stx_2734_, v_a_2735_, v_a_2736_);
lean_dec_ref(v_a_2735_);
return v_res_2737_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(lean_object* v_x_2738_){
_start:
{
lean_object* v_aPtr_2739_; lean_object* v_bPtr_2740_; size_t v_ptr_2741_; size_t v_ptr_2742_; uint64_t v___x_2743_; uint64_t v___x_2744_; uint64_t v___x_2745_; uint64_t v___x_2746_; uint64_t v___x_2747_; 
v_aPtr_2739_ = lean_ctor_get(v_x_2738_, 0);
v_bPtr_2740_ = lean_ctor_get(v_x_2738_, 1);
v_ptr_2741_ = lean_ctor_get_usize(v_aPtr_2739_, 1);
v_ptr_2742_ = lean_ctor_get_usize(v_bPtr_2740_, 1);
v___x_2743_ = 0ULL;
v___x_2744_ = lean_usize_to_uint64(v_ptr_2741_);
v___x_2745_ = lean_uint64_mix_hash(v___x_2743_, v___x_2744_);
v___x_2746_ = lean_usize_to_uint64(v_ptr_2742_);
v___x_2747_ = lean_uint64_mix_hash(v___x_2745_, v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8___boxed(lean_object* v_x_2748_){
_start:
{
uint64_t v_res_2749_; lean_object* v_r_2750_; 
v_res_2749_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_x_2748_);
lean_dec_ref(v_x_2748_);
v_r_2750_ = lean_box_uint64(v_res_2749_);
return v_r_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16___redArg(lean_object* v_x_2751_, lean_object* v_x_2752_){
_start:
{
if (lean_obj_tag(v_x_2752_) == 0)
{
return v_x_2751_;
}
else
{
lean_object* v_key_2753_; lean_object* v_value_2754_; lean_object* v_tail_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2778_; 
v_key_2753_ = lean_ctor_get(v_x_2752_, 0);
v_value_2754_ = lean_ctor_get(v_x_2752_, 1);
v_tail_2755_ = lean_ctor_get(v_x_2752_, 2);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_x_2752_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2757_ = v_x_2752_;
v_isShared_2758_ = v_isSharedCheck_2778_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_tail_2755_);
lean_inc(v_value_2754_);
lean_inc(v_key_2753_);
lean_dec(v_x_2752_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2778_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; uint64_t v___x_2760_; uint64_t v___x_2761_; uint64_t v___x_2762_; uint64_t v_fold_2763_; uint64_t v___x_2764_; uint64_t v___x_2765_; uint64_t v___x_2766_; size_t v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; size_t v___x_2770_; size_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2759_ = lean_array_get_size(v_x_2751_);
v___x_2760_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_key_2753_);
v___x_2761_ = 32ULL;
v___x_2762_ = lean_uint64_shift_right(v___x_2760_, v___x_2761_);
v_fold_2763_ = lean_uint64_xor(v___x_2760_, v___x_2762_);
v___x_2764_ = 16ULL;
v___x_2765_ = lean_uint64_shift_right(v_fold_2763_, v___x_2764_);
v___x_2766_ = lean_uint64_xor(v_fold_2763_, v___x_2765_);
v___x_2767_ = lean_uint64_to_usize(v___x_2766_);
v___x_2768_ = lean_usize_of_nat(v___x_2759_);
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_sub(v___x_2768_, v___x_2769_);
v___x_2771_ = lean_usize_land(v___x_2767_, v___x_2770_);
v___x_2772_ = lean_array_uget_borrowed(v_x_2751_, v___x_2771_);
lean_inc(v___x_2772_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 2, v___x_2772_);
v___x_2774_ = v___x_2757_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_key_2753_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_value_2754_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_array_uset(v_x_2751_, v___x_2771_, v___x_2774_);
v_x_2751_ = v___x_2775_;
v_x_2752_ = v_tail_2755_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15___redArg(lean_object* v_i_2779_, lean_object* v_source_2780_, lean_object* v_target_2781_){
_start:
{
lean_object* v___x_2782_; uint8_t v___x_2783_; 
v___x_2782_ = lean_array_get_size(v_source_2780_);
v___x_2783_ = lean_nat_dec_lt(v_i_2779_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_dec_ref(v_source_2780_);
lean_dec(v_i_2779_);
return v_target_2781_;
}
else
{
lean_object* v_es_2784_; lean_object* v___x_2785_; lean_object* v_source_2786_; lean_object* v_target_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_es_2784_ = lean_array_fget(v_source_2780_, v_i_2779_);
v___x_2785_ = lean_box(0);
v_source_2786_ = lean_array_fset(v_source_2780_, v_i_2779_, v___x_2785_);
v_target_2787_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16___redArg(v_target_2781_, v_es_2784_);
v___x_2788_ = lean_unsigned_to_nat(1u);
v___x_2789_ = lean_nat_add(v_i_2779_, v___x_2788_);
lean_dec(v_i_2779_);
v_i_2779_ = v___x_2789_;
v_source_2780_ = v_source_2786_;
v_target_2781_ = v_target_2787_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13___redArg(lean_object* v_data_2791_){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v_nbuckets_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2792_ = lean_array_get_size(v_data_2791_);
v___x_2793_ = lean_unsigned_to_nat(2u);
v_nbuckets_2794_ = lean_nat_mul(v___x_2792_, v___x_2793_);
v___x_2795_ = lean_unsigned_to_nat(0u);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_mk_array(v_nbuckets_2794_, v___x_2796_);
v___x_2798_ = lean_array_propagate_mark(v_data_2791_, v___x_2797_);
v___x_2799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15___redArg(v___x_2795_, v_data_2791_, v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(lean_object* v_x_2800_, lean_object* v_x_2801_){
_start:
{
lean_object* v_aPtr_2802_; lean_object* v_aPtr_2803_; lean_object* v_bPtr_2804_; lean_object* v_bPtr_2805_; size_t v_ptr_2806_; size_t v_ptr_2807_; uint8_t v___x_2808_; 
v_aPtr_2802_ = lean_ctor_get(v_x_2800_, 0);
v_aPtr_2803_ = lean_ctor_get(v_x_2801_, 0);
v_bPtr_2804_ = lean_ctor_get(v_x_2800_, 1);
v_bPtr_2805_ = lean_ctor_get(v_x_2801_, 1);
v_ptr_2806_ = lean_ctor_get_usize(v_aPtr_2802_, 1);
v_ptr_2807_ = lean_ctor_get_usize(v_aPtr_2803_, 1);
v___x_2808_ = lean_usize_dec_eq(v_ptr_2806_, v_ptr_2807_);
if (v___x_2808_ == 0)
{
return v___x_2808_;
}
else
{
size_t v_ptr_2809_; size_t v_ptr_2810_; uint8_t v___x_2811_; 
v_ptr_2809_ = lean_ctor_get_usize(v_bPtr_2804_, 1);
v_ptr_2810_ = lean_ctor_get_usize(v_bPtr_2805_, 1);
v___x_2811_ = lean_usize_dec_eq(v_ptr_2809_, v_ptr_2810_);
return v___x_2811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10___boxed(lean_object* v_x_2812_, lean_object* v_x_2813_){
_start:
{
uint8_t v_res_2814_; lean_object* v_r_2815_; 
v_res_2814_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_x_2812_, v_x_2813_);
lean_dec_ref(v_x_2813_);
lean_dec_ref(v_x_2812_);
v_r_2815_ = lean_box(v_res_2814_);
return v_r_2815_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_a_2816_, lean_object* v_x_2817_){
_start:
{
if (lean_obj_tag(v_x_2817_) == 0)
{
uint8_t v___x_2818_; 
v___x_2818_ = 0;
return v___x_2818_;
}
else
{
lean_object* v_key_2819_; lean_object* v_tail_2820_; uint8_t v___x_2821_; 
v_key_2819_ = lean_ctor_get(v_x_2817_, 0);
v_tail_2820_ = lean_ctor_get(v_x_2817_, 2);
v___x_2821_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_key_2819_, v_a_2816_);
if (v___x_2821_ == 0)
{
v_x_2817_ = v_tail_2820_;
goto _start;
}
else
{
return v___x_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg___boxed(lean_object* v_a_2823_, lean_object* v_x_2824_){
_start:
{
uint8_t v_res_2825_; lean_object* v_r_2826_; 
v_res_2825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(v_a_2823_, v_x_2824_);
lean_dec(v_x_2824_);
lean_dec_ref(v_a_2823_);
v_r_2826_ = lean_box(v_res_2825_);
return v_r_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(lean_object* v_a_2827_, lean_object* v_b_2828_, lean_object* v_x_2829_){
_start:
{
if (lean_obj_tag(v_x_2829_) == 0)
{
lean_dec(v_b_2828_);
lean_dec_ref(v_a_2827_);
return v_x_2829_;
}
else
{
lean_object* v_key_2830_; lean_object* v_value_2831_; lean_object* v_tail_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2844_; 
v_key_2830_ = lean_ctor_get(v_x_2829_, 0);
v_value_2831_ = lean_ctor_get(v_x_2829_, 1);
v_tail_2832_ = lean_ctor_get(v_x_2829_, 2);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_x_2829_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2834_ = v_x_2829_;
v_isShared_2835_ = v_isSharedCheck_2844_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_tail_2832_);
lean_inc(v_value_2831_);
lean_inc(v_key_2830_);
lean_dec(v_x_2829_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2844_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
uint8_t v___x_2836_; 
v___x_2836_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_key_2830_, v_a_2827_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(v_a_2827_, v_b_2828_, v_tail_2832_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 2, v___x_2837_);
v___x_2839_ = v___x_2834_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_key_2830_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_value_2831_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
else
{
lean_object* v___x_2842_; 
lean_dec(v_value_2831_);
lean_dec(v_key_2830_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 1, v_b_2828_);
lean_ctor_set(v___x_2834_, 0, v_a_2827_);
v___x_2842_ = v___x_2834_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2827_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_b_2828_);
lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_tail_2832_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2845_, lean_object* v_a_2846_, lean_object* v_b_2847_){
_start:
{
lean_object* v_size_2848_; lean_object* v_buckets_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2892_; 
v_size_2848_ = lean_ctor_get(v_m_2845_, 0);
v_buckets_2849_ = lean_ctor_get(v_m_2845_, 1);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_m_2845_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2851_ = v_m_2845_;
v_isShared_2852_ = v_isSharedCheck_2892_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_buckets_2849_);
lean_inc(v_size_2848_);
lean_dec(v_m_2845_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2892_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; uint64_t v___x_2854_; uint64_t v___x_2855_; uint64_t v___x_2856_; uint64_t v_fold_2857_; uint64_t v___x_2858_; uint64_t v___x_2859_; uint64_t v___x_2860_; size_t v___x_2861_; size_t v___x_2862_; size_t v___x_2863_; size_t v___x_2864_; size_t v___x_2865_; lean_object* v_bkt_2866_; uint8_t v___x_2867_; 
v___x_2853_ = lean_array_get_size(v_buckets_2849_);
v___x_2854_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_a_2846_);
v___x_2855_ = 32ULL;
v___x_2856_ = lean_uint64_shift_right(v___x_2854_, v___x_2855_);
v_fold_2857_ = lean_uint64_xor(v___x_2854_, v___x_2856_);
v___x_2858_ = 16ULL;
v___x_2859_ = lean_uint64_shift_right(v_fold_2857_, v___x_2858_);
v___x_2860_ = lean_uint64_xor(v_fold_2857_, v___x_2859_);
v___x_2861_ = lean_uint64_to_usize(v___x_2860_);
v___x_2862_ = lean_usize_of_nat(v___x_2853_);
v___x_2863_ = ((size_t)1ULL);
v___x_2864_ = lean_usize_sub(v___x_2862_, v___x_2863_);
v___x_2865_ = lean_usize_land(v___x_2861_, v___x_2864_);
v_bkt_2866_ = lean_array_uget_borrowed(v_buckets_2849_, v___x_2865_);
v___x_2867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(v_a_2846_, v_bkt_2866_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v_size_x27_2869_; lean_object* v___x_2870_; lean_object* v_buckets_x27_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2868_ = lean_unsigned_to_nat(1u);
v_size_x27_2869_ = lean_nat_add(v_size_2848_, v___x_2868_);
lean_dec(v_size_2848_);
lean_inc(v_bkt_2866_);
v___x_2870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2870_, 0, v_a_2846_);
lean_ctor_set(v___x_2870_, 1, v_b_2847_);
lean_ctor_set(v___x_2870_, 2, v_bkt_2866_);
v_buckets_x27_2871_ = lean_array_uset(v_buckets_2849_, v___x_2865_, v___x_2870_);
v___x_2872_ = lean_unsigned_to_nat(4u);
v___x_2873_ = lean_nat_mul(v_size_x27_2869_, v___x_2872_);
v___x_2874_ = lean_unsigned_to_nat(3u);
v___x_2875_ = lean_nat_div(v___x_2873_, v___x_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_array_get_size(v_buckets_x27_2871_);
v___x_2877_ = lean_nat_dec_le(v___x_2875_, v___x_2876_);
lean_dec(v___x_2875_);
if (v___x_2877_ == 0)
{
lean_object* v_val_2878_; lean_object* v___x_2880_; 
v_val_2878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13___redArg(v_buckets_x27_2871_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_val_2878_);
lean_ctor_set(v___x_2851_, 0, v_size_x27_2869_);
v___x_2880_ = v___x_2851_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_size_x27_2869_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_val_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
else
{
lean_object* v___x_2883_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v_buckets_x27_2871_);
lean_ctor_set(v___x_2851_, 0, v_size_x27_2869_);
v___x_2883_ = v___x_2851_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_size_x27_2869_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v_buckets_x27_2871_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
else
{
lean_object* v___x_2885_; lean_object* v_buckets_x27_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
lean_inc(v_bkt_2866_);
v___x_2885_ = lean_box(0);
v_buckets_x27_2886_ = lean_array_uset(v_buckets_2849_, v___x_2865_, v___x_2885_);
v___x_2887_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(v_a_2846_, v_b_2847_, v_bkt_2866_);
v___x_2888_ = lean_array_uset(v_buckets_x27_2886_, v___x_2865_, v___x_2887_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2888_);
v___x_2890_ = v___x_2851_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_size_2848_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(lean_object* v_a_2893_, lean_object* v_x_2894_){
_start:
{
if (lean_obj_tag(v_x_2894_) == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_box(0);
return v___x_2895_;
}
else
{
lean_object* v_key_2896_; lean_object* v_value_2897_; lean_object* v_tail_2898_; uint8_t v___x_2899_; 
v_key_2896_ = lean_ctor_get(v_x_2894_, 0);
v_value_2897_ = lean_ctor_get(v_x_2894_, 1);
v_tail_2898_ = lean_ctor_get(v_x_2894_, 2);
v___x_2899_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9_spec__10(v_key_2896_, v_a_2893_);
if (v___x_2899_ == 0)
{
v_x_2894_ = v_tail_2898_;
goto _start;
}
else
{
lean_object* v___x_2901_; 
lean_inc(v_value_2897_);
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_value_2897_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg___boxed(lean_object* v_a_2902_, lean_object* v_x_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(v_a_2902_, v_x_2903_);
lean_dec(v_x_2903_);
lean_dec_ref(v_a_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(lean_object* v_m_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_buckets_2907_; lean_object* v___x_2908_; uint64_t v___x_2909_; uint64_t v___x_2910_; uint64_t v___x_2911_; uint64_t v_fold_2912_; uint64_t v___x_2913_; uint64_t v___x_2914_; uint64_t v___x_2915_; size_t v___x_2916_; size_t v___x_2917_; size_t v___x_2918_; size_t v___x_2919_; size_t v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_buckets_2907_ = lean_ctor_get(v_m_2905_, 1);
v___x_2908_ = lean_array_get_size(v_buckets_2907_);
v___x_2909_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__8(v_a_2906_);
v___x_2910_ = 32ULL;
v___x_2911_ = lean_uint64_shift_right(v___x_2909_, v___x_2910_);
v_fold_2912_ = lean_uint64_xor(v___x_2909_, v___x_2911_);
v___x_2913_ = 16ULL;
v___x_2914_ = lean_uint64_shift_right(v_fold_2912_, v___x_2913_);
v___x_2915_ = lean_uint64_xor(v_fold_2912_, v___x_2914_);
v___x_2916_ = lean_uint64_to_usize(v___x_2915_);
v___x_2917_ = lean_usize_of_nat(v___x_2908_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_sub(v___x_2917_, v___x_2918_);
v___x_2920_ = lean_usize_land(v___x_2916_, v___x_2919_);
v___x_2921_ = lean_array_uget_borrowed(v_buckets_2907_, v___x_2920_);
v___x_2922_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(v_a_2906_, v___x_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(v_m_2923_, v_a_2924_);
lean_dec_ref(v_a_2924_);
lean_dec_ref(v_m_2923_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object* v_a_2926_, lean_object* v_b_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v___y_2930_; lean_object* v_da1_2935_; lean_object* v_da2_2936_; lean_object* v_db1_2937_; lean_object* v_db2_2938_; lean_object* v___y_2939_; lean_object* v_sa_2946_; lean_object* v_sb_2947_; lean_object* v___y_2948_; 
switch(lean_obj_tag(v_a_2926_))
{
case 0:
{
if (lean_obj_tag(v_b_2927_) == 0)
{
uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = 1;
v___x_2957_ = lean_box(v___x_2956_);
v___x_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v_a_2928_);
return v___x_2958_;
}
else
{
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 1:
{
if (lean_obj_tag(v_b_2927_) == 1)
{
lean_object* v_f_2959_; lean_object* v_f_2960_; 
v_f_2959_ = lean_ctor_get(v_a_2926_, 1);
lean_inc_ref(v_f_2959_);
lean_dec_ref_known(v_a_2926_, 2);
v_f_2960_ = lean_ctor_get(v_b_2927_, 1);
lean_inc_ref(v_f_2960_);
lean_dec_ref_known(v_b_2927_, 2);
v_sa_2946_ = v_f_2959_;
v_sb_2947_ = v_f_2960_;
v___y_2948_ = v_a_2928_;
goto v___jp_2945_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 2:
{
if (lean_obj_tag(v_b_2927_) == 2)
{
lean_object* v_s_2961_; lean_object* v_s_2962_; 
v_s_2961_ = lean_ctor_get(v_a_2926_, 1);
lean_inc_ref(v_s_2961_);
lean_dec_ref_known(v_a_2926_, 2);
v_s_2962_ = lean_ctor_get(v_b_2927_, 1);
lean_inc_ref(v_s_2962_);
lean_dec_ref_known(v_b_2927_, 2);
v_sa_2946_ = v_s_2961_;
v_sb_2947_ = v_s_2962_;
v___y_2948_ = v_a_2928_;
goto v___jp_2945_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 3:
{
if (lean_obj_tag(v_b_2927_) == 3)
{
lean_object* v_id_2963_; lean_object* v_d_2964_; lean_object* v_id_2965_; lean_object* v_d_2966_; uint8_t v___x_2967_; 
v_id_2963_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_id_2963_);
v_d_2964_ = lean_ctor_get(v_a_2926_, 2);
lean_inc(v_d_2964_);
lean_dec_ref_known(v_a_2926_, 3);
v_id_2965_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_id_2965_);
v_d_2966_ = lean_ctor_get(v_b_2927_, 2);
lean_inc(v_d_2966_);
lean_dec_ref_known(v_b_2927_, 3);
v___x_2967_ = lean_nat_dec_eq(v_id_2963_, v_id_2965_);
lean_dec(v_id_2965_);
lean_dec(v_id_2963_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec(v_d_2966_);
lean_dec(v_d_2964_);
v___x_2968_ = lean_box(v___x_2967_);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v_a_2928_);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; 
v___x_2970_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2964_, v_d_2966_, v_a_2928_);
return v___x_2970_;
}
}
else
{
lean_dec_ref_known(v_a_2926_, 3);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 4:
{
if (lean_obj_tag(v_b_2927_) == 4)
{
lean_object* v_d_2971_; lean_object* v_d_2972_; lean_object* v___x_2973_; 
v_d_2971_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_2971_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_2972_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_2972_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_2973_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2971_, v_d_2972_, v_a_2928_);
return v___x_2973_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 5:
{
if (lean_obj_tag(v_b_2927_) == 5)
{
lean_object* v_d_2974_; lean_object* v_d_2975_; lean_object* v___x_2976_; 
v_d_2974_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_2974_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_2975_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_2975_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_2976_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2974_, v_d_2975_, v_a_2928_);
return v___x_2976_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 6:
{
if (lean_obj_tag(v_b_2927_) == 6)
{
lean_object* v_n_2977_; uint8_t v_isCumulative_2978_; lean_object* v_d_2979_; lean_object* v_n_2980_; uint8_t v_isCumulative_2981_; lean_object* v_d_2982_; uint8_t v___x_2983_; 
v_n_2977_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_n_2977_);
v_isCumulative_2978_ = lean_ctor_get_uint8(v_a_2926_, sizeof(void*)*3 + 8);
v_d_2979_ = lean_ctor_get(v_a_2926_, 2);
lean_inc(v_d_2979_);
lean_dec_ref_known(v_a_2926_, 3);
v_n_2980_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_n_2980_);
v_isCumulative_2981_ = lean_ctor_get_uint8(v_b_2927_, sizeof(void*)*3 + 8);
v_d_2982_ = lean_ctor_get(v_b_2927_, 2);
lean_inc(v_d_2982_);
lean_dec_ref_known(v_b_2927_, 3);
v___x_2983_ = lean_nat_dec_eq(v_n_2977_, v_n_2980_);
lean_dec(v_n_2980_);
lean_dec(v_n_2977_);
if (v___x_2983_ == 0)
{
lean_dec(v_d_2982_);
lean_dec(v_d_2979_);
goto v___jp_2952_;
}
else
{
if (v_isCumulative_2981_ == 0)
{
if (v_isCumulative_2978_ == 0)
{
lean_object* v___x_2984_; 
v___x_2984_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2979_, v_d_2982_, v_a_2928_);
return v___x_2984_;
}
else
{
lean_dec(v_d_2982_);
lean_dec(v_d_2979_);
goto v___jp_2952_;
}
}
else
{
if (v_isCumulative_2978_ == 0)
{
lean_dec(v_d_2982_);
lean_dec(v_d_2979_);
goto v___jp_2952_;
}
else
{
lean_object* v___x_2985_; 
v___x_2985_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2979_, v_d_2982_, v_a_2928_);
return v___x_2985_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2926_, 3);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 7:
{
if (lean_obj_tag(v_b_2927_) == 7)
{
lean_object* v_d_2986_; lean_object* v_d_2987_; lean_object* v___x_2988_; 
v_d_2986_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_2986_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_2987_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_2987_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_2988_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2986_, v_d_2987_, v_a_2928_);
return v___x_2988_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 8:
{
if (lean_obj_tag(v_b_2927_) == 8)
{
uint8_t v_onlyNonCumulative_2989_; 
v_onlyNonCumulative_2989_ = lean_ctor_get_uint8(v_b_2927_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_2989_ == 0)
{
uint8_t v_onlyNonCumulative_2990_; 
v_onlyNonCumulative_2990_ = lean_ctor_get_uint8(v_a_2926_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_2990_ == 0)
{
lean_object* v_d_2991_; lean_object* v_d_2992_; lean_object* v___x_2993_; 
v_d_2991_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_2991_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_2992_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_2992_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_2993_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2991_, v_d_2992_, v_a_2928_);
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec_ref_known(v_b_2927_, 2);
lean_dec_ref_known(v_a_2926_, 2);
v___x_2994_ = lean_box(v_onlyNonCumulative_2989_);
v___x_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
lean_ctor_set(v___x_2995_, 1, v_a_2928_);
return v___x_2995_;
}
}
else
{
uint8_t v_onlyNonCumulative_2996_; 
v_onlyNonCumulative_2996_ = lean_ctor_get_uint8(v_a_2926_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec_ref_known(v_b_2927_, 2);
lean_dec_ref_known(v_a_2926_, 2);
v___x_2997_ = lean_box(v_onlyNonCumulative_2996_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v_a_2928_);
return v___x_2998_;
}
else
{
lean_object* v_d_2999_; lean_object* v_d_3000_; lean_object* v___x_3001_; 
v_d_2999_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_2999_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_3000_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_3000_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_3001_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_2999_, v_d_3000_, v_a_2928_);
return v___x_3001_;
}
}
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 9:
{
if (lean_obj_tag(v_b_2927_) == 9)
{
lean_object* v_d_3002_; lean_object* v_d_3003_; lean_object* v___x_3004_; 
v_d_3002_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_3002_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_3003_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_3003_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_3004_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3002_, v_d_3003_, v_a_2928_);
return v___x_3004_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 10:
{
if (lean_obj_tag(v_b_2927_) == 10)
{
lean_object* v_d_3005_; lean_object* v_d_3006_; lean_object* v___x_3007_; 
v_d_3005_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_3005_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_3006_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_3006_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_3007_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3005_, v_d_3006_, v_a_2928_);
return v___x_3007_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 11:
{
if (lean_obj_tag(v_b_2927_) == 11)
{
lean_object* v_d_3008_; lean_object* v_d_3009_; lean_object* v___x_3010_; 
v_d_3008_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_d_3008_);
lean_dec_ref_known(v_a_2926_, 2);
v_d_3009_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_d_3009_);
lean_dec_ref_known(v_b_2927_, 2);
v___x_3010_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3008_, v_d_3009_, v_a_2928_);
return v___x_3010_;
}
else
{
lean_dec_ref_known(v_a_2926_, 2);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 12:
{
if (lean_obj_tag(v_b_2927_) == 12)
{
lean_object* v_p_3011_; lean_object* v_p_3012_; lean_object* v_d_3013_; lean_object* v_d_3014_; lean_object* v_id_3015_; lean_object* v_id_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3026_; 
v_p_3011_ = lean_ctor_get(v_a_2926_, 1);
lean_inc_ref(v_p_3011_);
v_p_3012_ = lean_ctor_get(v_b_2927_, 1);
lean_inc_ref(v_p_3012_);
v_d_3013_ = lean_ctor_get(v_a_2926_, 2);
lean_inc(v_d_3013_);
lean_dec_ref_known(v_a_2926_, 3);
v_d_3014_ = lean_ctor_get(v_b_2927_, 2);
lean_inc(v_d_3014_);
lean_dec_ref_known(v_b_2927_, 3);
v_id_3015_ = lean_ctor_get(v_p_3011_, 1);
lean_inc(v_id_3015_);
lean_dec_ref(v_p_3011_);
v_id_3016_ = lean_ctor_get(v_p_3012_, 1);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_p_3012_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v_p_3012_, 0);
lean_dec(v_unused_3027_);
v___x_3018_ = v_p_3012_;
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_id_3016_);
lean_dec(v_p_3012_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3026_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_name_eq(v_id_3015_, v_id_3016_);
lean_dec(v_id_3016_);
lean_dec(v_id_3015_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_dec(v_d_3014_);
lean_dec(v_d_3013_);
v___x_3021_ = lean_box(v___x_3020_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 1, v_a_2928_);
lean_ctor_set(v___x_3018_, 0, v___x_3021_);
v___x_3023_ = v___x_3018_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_a_2928_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
else
{
lean_object* v___x_3025_; 
lean_del_object(v___x_3018_);
v___x_3025_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3013_, v_d_3014_, v_a_2928_);
return v___x_3025_;
}
}
}
else
{
lean_dec_ref_known(v_a_2926_, 3);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 13:
{
if (lean_obj_tag(v_b_2927_) == 13)
{
lean_object* v_cost_3028_; lean_object* v_d_3029_; lean_object* v_cost_3030_; lean_object* v_d_3031_; uint8_t v___x_3032_; 
v_cost_3028_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_cost_3028_);
v_d_3029_ = lean_ctor_get(v_a_2926_, 2);
lean_inc(v_d_3029_);
lean_dec_ref_known(v_a_2926_, 3);
v_cost_3030_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_cost_3030_);
v_d_3031_ = lean_ctor_get(v_b_2927_, 2);
lean_inc(v_d_3031_);
lean_dec_ref_known(v_b_2927_, 3);
v___x_3032_ = l_Lean_Fmt_instBEqDefaultCost_beq___redArg(v_cost_3028_, v_cost_3030_);
lean_dec(v_cost_3030_);
lean_dec(v_cost_3028_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_dec(v_d_3031_);
lean_dec(v_d_3029_);
v___x_3033_ = lean_box(v___x_3032_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v_a_2928_);
return v___x_3034_;
}
else
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3029_, v_d_3031_, v_a_2928_);
return v___x_3035_;
}
}
else
{
lean_dec_ref_known(v_a_2926_, 3);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
case 14:
{
if (lean_obj_tag(v_b_2927_) == 14)
{
lean_object* v_a_3036_; lean_object* v_b_3037_; lean_object* v_a_3038_; lean_object* v_b_3039_; 
v_a_3036_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_a_3036_);
v_b_3037_ = lean_ctor_get(v_a_2926_, 2);
lean_inc(v_b_3037_);
lean_dec_ref_known(v_a_2926_, 3);
v_a_3038_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_a_3038_);
v_b_3039_ = lean_ctor_get(v_b_2927_, 2);
lean_inc(v_b_3039_);
lean_dec_ref_known(v_b_2927_, 3);
v_da1_2935_ = v_a_3036_;
v_da2_2936_ = v_b_3037_;
v_db1_2937_ = v_a_3038_;
v_db2_2938_ = v_b_3039_;
v___y_2939_ = v_a_2928_;
goto v___jp_2934_;
}
else
{
lean_dec_ref_known(v_a_2926_, 3);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
default: 
{
if (lean_obj_tag(v_b_2927_) == 15)
{
lean_object* v_a_3040_; lean_object* v_b_3041_; lean_object* v_a_3042_; lean_object* v_b_3043_; 
v_a_3040_ = lean_ctor_get(v_a_2926_, 1);
lean_inc(v_a_3040_);
v_b_3041_ = lean_ctor_get(v_a_2926_, 2);
lean_inc(v_b_3041_);
lean_dec_ref_known(v_a_2926_, 3);
v_a_3042_ = lean_ctor_get(v_b_2927_, 1);
lean_inc(v_a_3042_);
v_b_3043_ = lean_ctor_get(v_b_2927_, 2);
lean_inc(v_b_3043_);
lean_dec_ref_known(v_b_2927_, 3);
v_da1_2935_ = v_a_3040_;
v_da2_2936_ = v_b_3041_;
v_db1_2937_ = v_a_3042_;
v_db2_2938_ = v_b_3043_;
v___y_2939_ = v_a_2928_;
goto v___jp_2934_;
}
else
{
lean_dec_ref_known(v_a_2926_, 3);
lean_dec(v_b_2927_);
v___y_2930_ = v_a_2928_;
goto v___jp_2929_;
}
}
}
v___jp_2929_:
{
uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = 0;
v___x_2932_ = lean_box(v___x_2931_);
v___x_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v___y_2930_);
return v___x_2933_;
}
v___jp_2934_:
{
lean_object* v___x_2940_; lean_object* v_fst_2941_; uint8_t v___x_2942_; 
v___x_2940_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da1_2935_, v_db1_2937_, v___y_2939_);
v_fst_2941_ = lean_ctor_get(v___x_2940_, 0);
v___x_2942_ = lean_unbox(v_fst_2941_);
if (v___x_2942_ == 0)
{
lean_dec(v_db2_2938_);
lean_dec(v_da2_2936_);
return v___x_2940_;
}
else
{
lean_object* v_snd_2943_; lean_object* v___x_2944_; 
v_snd_2943_ = lean_ctor_get(v___x_2940_, 1);
lean_inc(v_snd_2943_);
lean_dec_ref(v___x_2940_);
v___x_2944_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da2_2936_, v_db2_2938_, v_snd_2943_);
return v___x_2944_;
}
}
v___jp_2945_:
{
uint8_t v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = lean_string_dec_eq(v_sa_2946_, v_sb_2947_);
lean_dec_ref(v_sb_2947_);
lean_dec_ref(v_sa_2946_);
v___x_2950_ = lean_box(v___x_2949_);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v___y_2948_);
return v___x_2951_;
}
v___jp_2952_:
{
uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = 0;
v___x_2954_ = lean_box(v___x_2953_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
lean_ctor_set(v___x_2955_, 1, v_a_2928_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object* v_a_3044_, lean_object* v_b_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_cacheKey_3049_; lean_object* v___x_3050_; 
lean_inc(v_a_3044_);
v___x_3047_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3044_);
lean_inc(v_b_3045_);
v___x_3048_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3045_);
v_cacheKey_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3049_, 0, v___x_3047_);
lean_ctor_set(v_cacheKey_3049_, 1, v___x_3048_);
v___x_3050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(v_a_3046_, v_cacheKey_3049_);
if (lean_obj_tag(v___x_3050_) == 1)
{
lean_object* v_val_3051_; lean_object* v___x_3052_; 
lean_dec_ref_known(v_cacheKey_3049_, 2);
lean_dec(v_b_3045_);
lean_dec(v_a_3044_);
v_val_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_val_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v_val_3051_);
lean_ctor_set(v___x_3052_, 1, v_a_3046_);
return v___x_3052_;
}
else
{
lean_object* v___x_3053_; lean_object* v_fst_3054_; lean_object* v_snd_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___x_3050_);
v___x_3053_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(v_a_3044_, v_b_3045_, v_a_3046_);
v_fst_3054_ = lean_ctor_get(v___x_3053_, 0);
v_snd_3055_ = lean_ctor_get(v___x_3053_, 1);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3057_ = v___x_3053_;
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_snd_3055_);
lean_inc(v_fst_3054_);
lean_dec(v___x_3053_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
lean_inc(v_fst_3054_);
v___x_3059_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3___redArg(v_snd_3055_, v_cacheKey_3049_, v_fst_3054_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 1, v___x_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_fst_3054_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_unsigned_to_nat(16u);
v___x_3066_ = lean_mk_array(v___x_3065_, v___x_3064_);
return v___x_3066_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0);
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
lean_ctor_set(v___x_3069_, 1, v___x_3067_);
return v___x_3069_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object* v_a_3070_, lean_object* v_b_3071_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_fst_3074_; uint8_t v___x_3075_; 
v___x_3072_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1);
v___x_3073_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_a_3070_, v_b_3071_, v___x_3072_);
v_fst_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_fst_3074_);
lean_dec_ref(v___x_3073_);
v___x_3075_ = lean_unbox(v_fst_3074_);
lean_dec(v_fst_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object* v_a_3076_, lean_object* v_b_3077_){
_start:
{
uint8_t v_res_3078_; lean_object* v_r_3079_; 
v_res_3078_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_a_3076_, v_b_3077_);
v_r_3079_ = lean_box(v_res_3078_);
return v_r_3079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__3(lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
if (lean_obj_tag(v_x_3081_) == 0)
{
return v_x_3080_;
}
else
{
lean_object* v_key_3082_; lean_object* v_value_3083_; lean_object* v_tail_3084_; lean_object* v___x_3085_; 
v_key_3082_ = lean_ctor_get(v_x_3081_, 0);
lean_inc(v_key_3082_);
v_value_3083_ = lean_ctor_get(v_x_3081_, 1);
lean_inc(v_value_3083_);
v_tail_3084_ = lean_ctor_get(v_x_3081_, 2);
lean_inc(v_tail_3084_);
lean_dec_ref_known(v_x_3081_, 3);
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_x_3080_, v_key_3082_, v_value_3083_);
v_x_3080_ = v___x_3085_;
v_x_3081_ = v_tail_3084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4(lean_object* v_as_3087_, size_t v_i_3088_, size_t v_stop_3089_, lean_object* v_b_3090_){
_start:
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_usize_dec_eq(v_i_3088_, v_stop_3089_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; size_t v___x_3094_; size_t v___x_3095_; 
v___x_3092_ = lean_array_uget_borrowed(v_as_3087_, v_i_3088_);
lean_inc(v___x_3092_);
v___x_3093_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__3(v_b_3090_, v___x_3092_);
v___x_3094_ = ((size_t)1ULL);
v___x_3095_ = lean_usize_add(v_i_3088_, v___x_3094_);
v_i_3088_ = v___x_3095_;
v_b_3090_ = v___x_3093_;
goto _start;
}
else
{
return v_b_3090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4___boxed(lean_object* v_as_3097_, lean_object* v_i_3098_, lean_object* v_stop_3099_, lean_object* v_b_3100_){
_start:
{
size_t v_i_boxed_3101_; size_t v_stop_boxed_3102_; lean_object* v_res_3103_; 
v_i_boxed_3101_ = lean_unbox_usize(v_i_3098_);
lean_dec(v_i_3098_);
v_stop_boxed_3102_ = lean_unbox_usize(v_stop_3099_);
lean_dec(v_stop_3099_);
v_res_3103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4(v_as_3097_, v_i_boxed_3101_, v_stop_boxed_3102_, v_b_3100_);
lean_dec_ref(v_as_3097_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object* v_x_3104_, lean_object* v_x_3105_){
_start:
{
if (lean_obj_tag(v_x_3105_) == 0)
{
return v_x_3104_;
}
else
{
lean_object* v_key_3106_; lean_object* v_value_3107_; lean_object* v_tail_3108_; lean_object* v___x_3109_; 
v_key_3106_ = lean_ctor_get(v_x_3105_, 0);
lean_inc(v_key_3106_);
v_value_3107_ = lean_ctor_get(v_x_3105_, 1);
lean_inc(v_value_3107_);
v_tail_3108_ = lean_ctor_get(v_x_3105_, 2);
lean_inc(v_tail_3108_);
lean_dec_ref_known(v_x_3105_, 3);
v___x_3109_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_x_3104_, v_key_3106_, v_value_3107_);
v_x_3104_ = v___x_3109_;
v_x_3105_ = v_tail_3108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object* v_as_3111_, size_t v_i_3112_, size_t v_stop_3113_, lean_object* v_b_3114_){
_start:
{
uint8_t v___x_3115_; 
v___x_3115_ = lean_usize_dec_eq(v_i_3112_, v_stop_3113_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; size_t v___x_3118_; size_t v___x_3119_; 
v___x_3116_ = lean_array_uget_borrowed(v_as_3111_, v_i_3112_);
lean_inc(v___x_3116_);
v___x_3117_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_b_3114_, v___x_3116_);
v___x_3118_ = ((size_t)1ULL);
v___x_3119_ = lean_usize_add(v_i_3112_, v___x_3118_);
v_i_3112_ = v___x_3119_;
v_b_3114_ = v___x_3117_;
goto _start;
}
else
{
return v_b_3114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___boxed(lean_object* v_as_3121_, lean_object* v_i_3122_, lean_object* v_stop_3123_, lean_object* v_b_3124_){
_start:
{
size_t v_i_boxed_3125_; size_t v_stop_boxed_3126_; lean_object* v_res_3127_; 
v_i_boxed_3125_ = lean_unbox_usize(v_i_3122_);
lean_dec(v_i_3122_);
v_stop_boxed_3126_ = lean_unbox_usize(v_stop_3123_);
lean_dec(v_stop_3123_);
v_res_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v_as_3121_, v_i_boxed_3125_, v_stop_boxed_3126_, v_b_3124_);
lean_dec_ref(v_as_3121_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5(lean_object* v_a_3128_, lean_object* v___x_3129_, lean_object* v_as_3130_, size_t v_sz_3131_, size_t v_i_3132_, lean_object* v_b_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_a_3137_; lean_object* v_a_3138_; uint8_t v___x_3142_; 
v___x_3142_ = lean_usize_dec_lt(v_i_3132_, v_sz_3131_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; 
lean_dec_ref(v_a_3128_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_b_3133_);
lean_ctor_set(v___x_3143_, 1, v___y_3135_);
return v___x_3143_;
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3145_; 
lean_dec_ref(v___y_3135_);
v_a_3144_ = lean_array_uget_borrowed(v_as_3130_, v_i_3132_);
lean_inc_ref(v_a_3128_);
lean_inc(v_a_3144_);
v___x_3145_ = l_Lean_Fmt_fmt(v_a_3144_, v___y_3134_, v_a_3128_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_snd_3146_; lean_object* v_snd_3147_; lean_object* v_a_3148_; lean_object* v_missingFormatters_3149_; lean_object* v_a_3150_; lean_object* v_fst_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3245_; 
v_snd_3146_ = lean_ctor_get(v_b_3133_, 1);
lean_inc(v_snd_3146_);
v_snd_3147_ = lean_ctor_get(v_snd_3146_, 1);
lean_inc(v_snd_3147_);
v_a_3148_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_a_3148_);
v_missingFormatters_3149_ = lean_ctor_get(v_a_3148_, 3);
lean_inc_ref(v_missingFormatters_3149_);
v_a_3150_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3145_, 2);
v_fst_3151_ = lean_ctor_get(v_b_3133_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_b_3133_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v_b_3133_, 1);
lean_dec(v_unused_3246_);
v___x_3153_ = v_b_3133_;
v_isShared_3154_ = v_isSharedCheck_3245_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_fst_3151_);
lean_dec(v_b_3133_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3245_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_fst_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3243_; 
v_fst_3155_ = lean_ctor_get(v_snd_3146_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_snd_3146_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v_snd_3146_, 1);
lean_dec(v_unused_3244_);
v___x_3157_ = v_snd_3146_;
v_isShared_3158_ = v_isSharedCheck_3243_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_fst_3155_);
lean_dec(v_snd_3146_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3243_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_fst_3159_; lean_object* v_snd_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3242_; 
v_fst_3159_ = lean_ctor_get(v_snd_3147_, 0);
v_snd_3160_ = lean_ctor_get(v_snd_3147_, 1);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_snd_3147_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3162_ = v_snd_3147_;
v_isShared_3163_ = v_isSharedCheck_3242_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snd_3160_);
lean_inc(v_fst_3159_);
lean_dec(v_snd_3147_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3242_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v_partialFormatters_3164_; lean_object* v_buckets_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3240_; 
v_partialFormatters_3164_ = lean_ctor_get(v_a_3148_, 4);
v_buckets_3165_ = lean_ctor_get(v_missingFormatters_3149_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_missingFormatters_3149_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v_missingFormatters_3149_, 0);
lean_dec(v_unused_3241_);
v___x_3167_ = v_missingFormatters_3149_;
v_isShared_3168_ = v_isSharedCheck_3240_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_buckets_3165_);
lean_dec(v_missingFormatters_3149_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3240_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; uint8_t v_areFormattedAlike_3170_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3228_; lean_object* v___x_3235_; uint8_t v___x_3236_; 
v___x_3169_ = lean_unsigned_to_nat(0u);
v_areFormattedAlike_3170_ = lean_nat_dec_eq(v___x_3129_, v___x_3169_);
v___x_3235_ = lean_array_get_size(v_buckets_3165_);
v___x_3236_ = lean_nat_dec_lt(v___x_3169_, v___x_3235_);
if (v___x_3236_ == 0)
{
lean_dec_ref(v_buckets_3165_);
v___y_3228_ = v_fst_3159_;
goto v___jp_3227_;
}
else
{
size_t v___x_3237_; size_t v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = ((size_t)0ULL);
v___x_3238_ = lean_usize_of_nat(v___x_3235_);
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__4(v_buckets_3165_, v___x_3237_, v___x_3238_, v_fst_3159_);
lean_dec_ref(v_buckets_3165_);
v___y_3228_ = v___x_3239_;
goto v___jp_3227_;
}
v___jp_3171_:
{
uint8_t v___x_3174_; 
lean_inc(v_a_3150_);
v___x_3174_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_a_3150_);
if (v___x_3174_ == 0)
{
if (lean_obj_tag(v_fst_3151_) == 1)
{
lean_object* v_val_3175_; lean_object* v_fst_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3202_; 
lean_del_object(v___x_3167_);
lean_del_object(v___x_3153_);
v_val_3175_ = lean_ctor_get(v_fst_3151_, 0);
lean_inc(v_val_3175_);
v_fst_3176_ = lean_ctor_get(v_val_3175_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_val_3175_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v_val_3175_, 1);
lean_dec(v_unused_3203_);
v___x_3178_ = v_val_3175_;
v_isShared_3179_ = v_isSharedCheck_3202_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_fst_3176_);
lean_dec(v_val_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3202_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v_doc_3180_; lean_object* v_doc_3181_; uint8_t v___x_3182_; 
v_doc_3180_ = lean_ctor_get(v_a_3150_, 0);
lean_inc(v_doc_3180_);
lean_dec(v_a_3150_);
v_doc_3181_ = lean_ctor_get(v_fst_3176_, 0);
lean_inc(v_doc_3181_);
lean_dec(v_fst_3176_);
v___x_3182_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_doc_3180_, v_doc_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3184_; 
lean_dec(v_fst_3155_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v___y_3173_);
lean_ctor_set(v___x_3178_, 0, v___y_3172_);
v___x_3184_ = v___x_3178_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___y_3172_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___y_3173_);
v___x_3184_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = lean_box(v___x_3174_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3184_);
lean_ctor_set(v___x_3162_, 0, v___x_3185_);
v___x_3187_ = v___x_3162_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3184_);
v___x_3187_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 1, v___x_3187_);
lean_ctor_set(v___x_3157_, 0, v_fst_3151_);
v___x_3189_ = v___x_3157_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_fst_3151_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
v_a_3137_ = v___x_3189_;
v_a_3138_ = v_a_3148_;
goto v___jp_3136_;
}
}
}
}
else
{
lean_object* v___x_3194_; 
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v___y_3173_);
lean_ctor_set(v___x_3178_, 0, v___y_3172_);
v___x_3194_ = v___x_3178_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___y_3172_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___y_3173_);
v___x_3194_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3196_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3194_);
lean_ctor_set(v___x_3162_, 0, v_fst_3155_);
v___x_3196_ = v___x_3162_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_fst_3155_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 1, v___x_3196_);
lean_ctor_set(v___x_3157_, 0, v_fst_3151_);
v___x_3198_ = v___x_3157_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_fst_3151_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
v_a_3137_ = v___x_3198_;
v_a_3138_ = v_a_3148_;
goto v___jp_3136_;
}
}
}
}
}
}
else
{
lean_object* v___x_3205_; 
lean_dec(v_fst_3151_);
lean_inc(v_a_3148_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v_a_3148_);
lean_ctor_set(v___x_3162_, 0, v_a_3150_);
v___x_3205_ = v___x_3162_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3150_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_a_3148_);
v___x_3205_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 1, v___y_3173_);
lean_ctor_set(v___x_3157_, 0, v___y_3172_);
v___x_3208_ = v___x_3157_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___y_3172_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___y_3173_);
v___x_3208_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3210_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v___x_3208_);
lean_ctor_set(v___x_3153_, 0, v_fst_3155_);
v___x_3210_ = v___x_3153_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_fst_3155_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3212_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___x_3210_);
lean_ctor_set(v___x_3167_, 0, v___x_3206_);
v___x_3212_ = v___x_3167_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
v_a_3137_ = v___x_3212_;
v_a_3138_ = v_a_3148_;
goto v___jp_3136_;
}
}
}
}
}
}
else
{
lean_object* v___x_3218_; 
lean_del_object(v___x_3167_);
lean_dec(v_fst_3155_);
lean_dec(v_a_3150_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___y_3173_);
lean_ctor_set(v___x_3162_, 0, v___y_3172_);
v___x_3218_ = v___x_3162_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___y_3172_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___y_3173_);
v___x_3218_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3219_ = lean_box(v_areFormattedAlike_3170_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 1, v___x_3218_);
lean_ctor_set(v___x_3157_, 0, v___x_3219_);
v___x_3221_ = v___x_3157_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_3218_);
v___x_3221_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3223_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v___x_3221_);
v___x_3223_ = v___x_3153_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_fst_3151_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
v_a_3137_ = v___x_3223_;
v_a_3138_ = v_a_3148_;
goto v___jp_3136_;
}
}
}
}
}
v___jp_3227_:
{
lean_object* v_buckets_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v_buckets_3229_ = lean_ctor_get(v_partialFormatters_3164_, 1);
v___x_3230_ = lean_array_get_size(v_buckets_3229_);
v___x_3231_ = lean_nat_dec_lt(v___x_3169_, v___x_3230_);
if (v___x_3231_ == 0)
{
v___y_3172_ = v___y_3228_;
v___y_3173_ = v_snd_3160_;
goto v___jp_3171_;
}
else
{
size_t v___x_3232_; size_t v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = ((size_t)0ULL);
v___x_3233_ = lean_usize_of_nat(v___x_3230_);
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v_buckets_3229_, v___x_3232_, v___x_3233_, v_snd_3160_);
v___y_3172_ = v___y_3228_;
v___y_3173_ = v___x_3234_;
goto v___jp_3171_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v_b_3133_);
lean_dec_ref(v_a_3128_);
v_a_3247_ = lean_ctor_get(v___x_3145_, 0);
v_a_3248_ = lean_ctor_get(v___x_3145_, 1);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3145_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_inc(v_a_3247_);
lean_dec(v___x_3145_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3247_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
v___jp_3136_:
{
size_t v___x_3139_; size_t v___x_3140_; 
v___x_3139_ = ((size_t)1ULL);
v___x_3140_ = lean_usize_add(v_i_3132_, v___x_3139_);
v_i_3132_ = v___x_3140_;
v_b_3133_ = v_a_3137_;
v___y_3135_ = v_a_3138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5___boxed(lean_object* v_a_3256_, lean_object* v___x_3257_, lean_object* v_as_3258_, lean_object* v_sz_3259_, lean_object* v_i_3260_, lean_object* v_b_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
size_t v_sz_boxed_3264_; size_t v_i_boxed_3265_; lean_object* v_res_3266_; 
v_sz_boxed_3264_ = lean_unbox_usize(v_sz_3259_);
lean_dec(v_sz_3259_);
v_i_boxed_3265_ = lean_unbox_usize(v_i_3260_);
lean_dec(v_i_3260_);
v_res_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5(v_a_3256_, v___x_3257_, v_as_3258_, v_sz_boxed_3264_, v_i_boxed_3265_, v_b_3261_, v___y_3262_, v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v_as_3258_);
lean_dec(v___x_3257_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6(size_t v_sz_3267_, size_t v_i_3268_, lean_object* v_bs_3269_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_lt(v_i_3268_, v_sz_3267_);
if (v___x_3270_ == 0)
{
return v_bs_3269_;
}
else
{
lean_object* v_v_3271_; lean_object* v___x_3272_; lean_object* v_bs_x27_3273_; lean_object* v___x_3274_; size_t v___x_3275_; size_t v___x_3276_; lean_object* v___x_3277_; 
v_v_3271_ = lean_array_uget(v_bs_3269_, v_i_3268_);
v___x_3272_ = lean_unsigned_to_nat(0u);
v_bs_x27_3273_ = lean_array_uset(v_bs_3269_, v_i_3268_, v___x_3272_);
v___x_3274_ = l_Lean_Syntax_getKind(v_v_3271_);
v___x_3275_ = ((size_t)1ULL);
v___x_3276_ = lean_usize_add(v_i_3268_, v___x_3275_);
v___x_3277_ = lean_array_uset(v_bs_x27_3273_, v_i_3268_, v___x_3274_);
v_i_3268_ = v___x_3276_;
v_bs_3269_ = v___x_3277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6___boxed(lean_object* v_sz_3279_, lean_object* v_i_3280_, lean_object* v_bs_3281_){
_start:
{
size_t v_sz_boxed_3282_; size_t v_i_boxed_3283_; lean_object* v_res_3284_; 
v_sz_boxed_3282_ = lean_unbox_usize(v_sz_3279_);
lean_dec(v_sz_3279_);
v_i_boxed_3283_ = lean_unbox_usize(v_i_3280_);
lean_dec(v_i_3280_);
v_res_3284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6(v_sz_boxed_3282_, v_i_boxed_3283_, v_bs_3281_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object* v_choiceStx_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v_areFormattedAlike_3290_; 
v___x_3288_ = l_Lean_Syntax_getNumArgs(v_choiceStx_3285_);
v___x_3289_ = lean_unsigned_to_nat(0u);
v_areFormattedAlike_3290_ = lean_nat_dec_eq(v___x_3288_, v___x_3289_);
if (v_areFormattedAlike_3290_ == 0)
{
lean_object* v_toBacktrackableState_3291_; lean_object* v_shareCommonState_3292_; lean_object* v_freshTagId_3293_; lean_object* v_missingFormatters_3294_; lean_object* v_partialFormatters_3295_; lean_object* v_missingChoiceResolutions_3296_; uint8_t v_areFormattedAlike_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; size_t v_sz_3304_; size_t v___x_3305_; lean_object* v___x_3306_; 
v_toBacktrackableState_3291_ = lean_ctor_get(v_a_3287_, 0);
lean_inc_ref(v_toBacktrackableState_3291_);
v_shareCommonState_3292_ = lean_ctor_get(v_a_3287_, 1);
lean_inc(v_shareCommonState_3292_);
v_freshTagId_3293_ = lean_ctor_get(v_a_3287_, 2);
lean_inc(v_freshTagId_3293_);
v_missingFormatters_3294_ = lean_ctor_get(v_a_3287_, 3);
v_partialFormatters_3295_ = lean_ctor_get(v_a_3287_, 4);
v_missingChoiceResolutions_3296_ = lean_ctor_get(v_a_3287_, 5);
lean_inc_ref(v_missingChoiceResolutions_3296_);
v_areFormattedAlike_3297_ = 1;
v___x_3298_ = lean_box(0);
v___x_3299_ = l_Lean_Syntax_getArgs(v_choiceStx_3285_);
lean_inc_ref(v_partialFormatters_3295_);
lean_inc_ref(v_missingFormatters_3294_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_missingFormatters_3294_);
lean_ctor_set(v___x_3300_, 1, v_partialFormatters_3295_);
v___x_3301_ = lean_box(v_areFormattedAlike_3297_);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v___x_3300_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3298_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v_sz_3304_ = lean_array_size(v___x_3299_);
v___x_3305_ = ((size_t)0ULL);
lean_inc_ref(v_a_3287_);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__5(v_a_3287_, v___x_3288_, v___x_3299_, v_sz_3304_, v___x_3305_, v___x_3303_, v_a_3286_, v_a_3287_);
lean_dec(v___x_3288_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3356_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v___x_3306_, 1);
lean_dec(v_unused_3357_);
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3356_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3356_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v_snd_3311_; lean_object* v_snd_3312_; lean_object* v_fst_3313_; lean_object* v_fst_3314_; lean_object* v_fst_3315_; lean_object* v_snd_3316_; lean_object* v___y_3318_; uint8_t v___x_3349_; 
v_snd_3311_ = lean_ctor_get(v_a_3307_, 1);
lean_inc(v_snd_3311_);
v_snd_3312_ = lean_ctor_get(v_snd_3311_, 1);
lean_inc(v_snd_3312_);
v_fst_3313_ = lean_ctor_get(v_a_3307_, 0);
lean_inc(v_fst_3313_);
lean_dec(v_a_3307_);
v_fst_3314_ = lean_ctor_get(v_snd_3311_, 0);
lean_inc(v_fst_3314_);
lean_dec(v_snd_3311_);
v_fst_3315_ = lean_ctor_get(v_snd_3312_, 0);
lean_inc(v_fst_3315_);
v_snd_3316_ = lean_ctor_get(v_snd_3312_, 1);
lean_inc(v_snd_3316_);
lean_dec(v_snd_3312_);
v___x_3349_ = lean_unbox(v_fst_3314_);
lean_dec(v_fst_3314_);
if (v___x_3349_ == 0)
{
lean_dec(v_fst_3313_);
lean_del_object(v___x_3309_);
v___y_3318_ = v_a_3286_;
goto v___jp_3317_;
}
else
{
if (lean_obj_tag(v_fst_3313_) == 1)
{
lean_object* v_val_3350_; lean_object* v_fst_3351_; lean_object* v_snd_3352_; lean_object* v___x_3354_; 
lean_dec(v_snd_3316_);
lean_dec(v_fst_3315_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_missingChoiceResolutions_3296_);
lean_dec(v_freshTagId_3293_);
lean_dec(v_shareCommonState_3292_);
lean_dec_ref(v_toBacktrackableState_3291_);
lean_dec(v_choiceStx_3285_);
v_val_3350_ = lean_ctor_get(v_fst_3313_, 0);
lean_inc(v_val_3350_);
lean_dec_ref_known(v_fst_3313_, 1);
v_fst_3351_ = lean_ctor_get(v_val_3350_, 0);
lean_inc(v_fst_3351_);
v_snd_3352_ = lean_ctor_get(v_val_3350_, 1);
lean_inc(v_snd_3352_);
lean_dec(v_val_3350_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 1, v_snd_3352_);
lean_ctor_set(v___x_3309_, 0, v_fst_3351_);
v___x_3354_ = v___x_3309_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_fst_3351_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_snd_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
else
{
lean_dec(v_fst_3313_);
lean_del_object(v___x_3309_);
v___y_3318_ = v_a_3286_;
goto v___jp_3317_;
}
}
v___jp_3317_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3319_, 0, v_toBacktrackableState_3291_);
lean_ctor_set(v___x_3319_, 1, v_shareCommonState_3292_);
lean_ctor_set(v___x_3319_, 2, v_freshTagId_3293_);
lean_ctor_set(v___x_3319_, 3, v_fst_3315_);
lean_ctor_set(v___x_3319_, 4, v_snd_3316_);
lean_ctor_set(v___x_3319_, 5, v_missingChoiceResolutions_3296_);
lean_inc(v_choiceStx_3285_);
v___x_3320_ = l_Lean_Fmt_fmtRaw(v_areFormattedAlike_3297_, v_choiceStx_3285_, v___y_3318_, v___x_3319_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v_a_3322_; lean_object* v___x_3323_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
v_a_3322_ = lean_ctor_get(v___x_3320_, 1);
lean_inc(v_a_3322_);
v___x_3323_ = l_Lean_Syntax_getRange_x3f(v_choiceStx_3285_, v_areFormattedAlike_3290_);
lean_dec(v_choiceStx_3285_);
if (lean_obj_tag(v___x_3323_) == 1)
{
lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3346_; 
lean_inc(v_a_3321_);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3346_ == 0)
{
lean_object* v_unused_3347_; lean_object* v_unused_3348_; 
v_unused_3347_ = lean_ctor_get(v___x_3320_, 1);
lean_dec(v_unused_3347_);
v_unused_3348_ = lean_ctor_get(v___x_3320_, 0);
lean_dec(v_unused_3348_);
v___x_3325_ = v___x_3320_;
v_isShared_3326_ = v_isSharedCheck_3346_;
goto v_resetjp_3324_;
}
else
{
lean_dec(v___x_3320_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3346_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v_val_3327_; lean_object* v_toBacktrackableState_3328_; lean_object* v_shareCommonState_3329_; lean_object* v_freshTagId_3330_; lean_object* v_missingFormatters_3331_; lean_object* v_partialFormatters_3332_; lean_object* v_missingChoiceResolutions_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3345_; 
v_val_3327_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_val_3327_);
lean_dec_ref_known(v___x_3323_, 1);
v_toBacktrackableState_3328_ = lean_ctor_get(v_a_3322_, 0);
v_shareCommonState_3329_ = lean_ctor_get(v_a_3322_, 1);
v_freshTagId_3330_ = lean_ctor_get(v_a_3322_, 2);
v_missingFormatters_3331_ = lean_ctor_get(v_a_3322_, 3);
v_partialFormatters_3332_ = lean_ctor_get(v_a_3322_, 4);
v_missingChoiceResolutions_3333_ = lean_ctor_get(v_a_3322_, 5);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_a_3322_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3335_ = v_a_3322_;
v_isShared_3336_ = v_isSharedCheck_3345_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_missingChoiceResolutions_3333_);
lean_inc(v_partialFormatters_3332_);
lean_inc(v_missingFormatters_3331_);
lean_inc(v_freshTagId_3330_);
lean_inc(v_shareCommonState_3329_);
lean_inc(v_toBacktrackableState_3328_);
lean_dec(v_a_3322_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3345_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__6(v_sz_3304_, v___x_3305_, v___x_3299_);
v___x_3338_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingChoiceResolutions_3333_, v_val_3327_, v___x_3337_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 5, v___x_3338_);
v___x_3340_ = v___x_3335_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_toBacktrackableState_3328_);
lean_ctor_set(v_reuseFailAlloc_3344_, 1, v_shareCommonState_3329_);
lean_ctor_set(v_reuseFailAlloc_3344_, 2, v_freshTagId_3330_);
lean_ctor_set(v_reuseFailAlloc_3344_, 3, v_missingFormatters_3331_);
lean_ctor_set(v_reuseFailAlloc_3344_, 4, v_partialFormatters_3332_);
lean_ctor_set(v_reuseFailAlloc_3344_, 5, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3342_; 
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 1, v___x_3340_);
v___x_3342_ = v___x_3325_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3321_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
else
{
lean_dec(v___x_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v___x_3299_);
return v___x_3320_;
}
}
else
{
lean_dec_ref(v___x_3299_);
lean_dec(v_choiceStx_3285_);
return v___x_3320_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_missingChoiceResolutions_3296_);
lean_dec(v_freshTagId_3293_);
lean_dec(v_shareCommonState_3292_);
lean_dec_ref(v_toBacktrackableState_3291_);
lean_dec(v_choiceStx_3285_);
v_a_3358_ = lean_ctor_get(v___x_3306_, 0);
v_a_3359_ = lean_ctor_get(v___x_3306_, 1);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3306_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_inc(v_a_3358_);
lean_dec(v___x_3306_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3358_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec(v___x_3288_);
v___x_3367_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3368_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_3367_, v_choiceStx_3285_, v_a_3287_);
lean_dec(v_choiceStx_3285_);
return v___x_3368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object* v_choiceStx_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(v_choiceStx_3369_, v_a_3370_, v_a_3371_);
lean_dec_ref(v_a_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3373_, lean_object* v_m_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___redArg(v_m_3374_, v_a_3375_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3377_, lean_object* v_m_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1(v_00_u03b2_3377_, v_m_3378_, v_a_3379_);
lean_dec_ref(v_a_3379_);
lean_dec_ref(v_m_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_3381_, lean_object* v_m_3382_, lean_object* v_a_3383_, lean_object* v_b_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3___redArg(v_m_3382_, v_a_3383_, v_b_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9(lean_object* v_00_u03b2_3386_, lean_object* v_a_3387_, lean_object* v_x_3388_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___redArg(v_a_3387_, v_x_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9___boxed(lean_object* v_00_u03b2_3390_, lean_object* v_a_3391_, lean_object* v_x_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__1_spec__9(v_00_u03b2_3390_, v_a_3391_, v_x_3392_);
lean_dec(v_x_3392_);
lean_dec_ref(v_a_3391_);
return v_res_3393_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b2_3394_, lean_object* v_a_3395_, lean_object* v_x_3396_){
_start:
{
uint8_t v___x_3397_; 
v___x_3397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___redArg(v_a_3395_, v_x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12___boxed(lean_object* v_00_u03b2_3398_, lean_object* v_a_3399_, lean_object* v_x_3400_){
_start:
{
uint8_t v_res_3401_; lean_object* v_r_3402_; 
v_res_3401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__12(v_00_u03b2_3398_, v_a_3399_, v_x_3400_);
lean_dec(v_x_3400_);
lean_dec_ref(v_a_3399_);
v_r_3402_ = lean_box(v_res_3401_);
return v_r_3402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13(lean_object* v_00_u03b2_3403_, lean_object* v_data_3404_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13___redArg(v_data_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14(lean_object* v_00_u03b2_3406_, lean_object* v_a_3407_, lean_object* v_b_3408_, lean_object* v_x_3409_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__14___redArg(v_a_3407_, v_b_3408_, v_x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15(lean_object* v_00_u03b2_3411_, lean_object* v_i_3412_, lean_object* v_source_3413_, lean_object* v_target_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15___redArg(v_i_3412_, v_source_3413_, v_target_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16(lean_object* v_00_u03b2_3416_, lean_object* v_x_3417_, lean_object* v_x_3418_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3_spec__13_spec__15_spec__16___redArg(v_x_3417_, v_x_3418_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(size_t v_sz_3420_, size_t v_i_3421_, lean_object* v_bs_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_usize_dec_lt(v_i_3421_, v_sz_3420_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v_bs_3422_);
lean_ctor_set(v___x_3426_, 1, v___y_3424_);
return v___x_3426_;
}
else
{
lean_object* v_v_3427_; lean_object* v___x_3428_; 
v_v_3427_ = lean_array_uget_borrowed(v_bs_3422_, v_i_3421_);
lean_inc(v_v_3427_);
v___x_3428_ = l_Lean_Fmt_fmt(v_v_3427_, v___y_3423_, v___y_3424_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v_a_3430_; lean_object* v___x_3431_; lean_object* v_bs_x27_3432_; size_t v___x_3433_; size_t v___x_3434_; lean_object* v___x_3435_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
v_a_3430_ = lean_ctor_get(v___x_3428_, 1);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3428_, 2);
v___x_3431_ = lean_unsigned_to_nat(0u);
v_bs_x27_3432_ = lean_array_uset(v_bs_3422_, v_i_3421_, v___x_3431_);
v___x_3433_ = ((size_t)1ULL);
v___x_3434_ = lean_usize_add(v_i_3421_, v___x_3433_);
v___x_3435_ = lean_array_uset(v_bs_x27_3432_, v_i_3421_, v_a_3429_);
v_i_3421_ = v___x_3434_;
v_bs_3422_ = v___x_3435_;
v___y_3424_ = v_a_3430_;
goto _start;
}
else
{
lean_object* v_a_3437_; lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_bs_3422_);
v_a_3437_ = lean_ctor_get(v___x_3428_, 0);
v_a_3438_ = lean_ctor_get(v___x_3428_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3428_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_inc(v_a_3437_);
lean_dec(v___x_3428_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3437_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1___boxed(lean_object* v_sz_3446_, lean_object* v_i_3447_, lean_object* v_bs_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
size_t v_sz_boxed_3451_; size_t v_i_boxed_3452_; lean_object* v_res_3453_; 
v_sz_boxed_3451_ = lean_unbox_usize(v_sz_3446_);
lean_dec(v_sz_3446_);
v_i_boxed_3452_ = lean_unbox_usize(v_i_3447_);
lean_dec(v_i_3447_);
v_res_3453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_boxed_3451_, v_i_boxed_3452_, v_bs_3448_, v___y_3449_, v___y_3450_);
lean_dec_ref(v___y_3449_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3454_, lean_object* v_x_3455_){
_start:
{
if (lean_obj_tag(v_x_3455_) == 0)
{
return v_x_3454_;
}
else
{
lean_object* v_key_3456_; lean_object* v_value_3457_; lean_object* v_tail_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3484_; 
v_key_3456_ = lean_ctor_get(v_x_3455_, 0);
v_value_3457_ = lean_ctor_get(v_x_3455_, 1);
v_tail_3458_ = lean_ctor_get(v_x_3455_, 2);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_x_3455_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3460_ = v_x_3455_;
v_isShared_3461_ = v_isSharedCheck_3484_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_tail_3458_);
lean_inc(v_value_3457_);
lean_inc(v_key_3456_);
lean_dec(v_x_3455_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3484_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; uint64_t v___y_3464_; 
v___x_3462_ = lean_array_get_size(v_x_3454_);
if (lean_obj_tag(v_key_3456_) == 0)
{
uint64_t v___x_3482_; 
v___x_3482_ = 1723ULL;
v___y_3464_ = v___x_3482_;
goto v___jp_3463_;
}
else
{
uint64_t v_hash_3483_; 
v_hash_3483_ = lean_ctor_get_uint64(v_key_3456_, sizeof(void*)*2);
v___y_3464_ = v_hash_3483_;
goto v___jp_3463_;
}
v___jp_3463_:
{
uint64_t v___x_3465_; uint64_t v___x_3466_; uint64_t v_fold_3467_; uint64_t v___x_3468_; uint64_t v___x_3469_; uint64_t v___x_3470_; size_t v___x_3471_; size_t v___x_3472_; size_t v___x_3473_; size_t v___x_3474_; size_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3465_ = 32ULL;
v___x_3466_ = lean_uint64_shift_right(v___y_3464_, v___x_3465_);
v_fold_3467_ = lean_uint64_xor(v___y_3464_, v___x_3466_);
v___x_3468_ = 16ULL;
v___x_3469_ = lean_uint64_shift_right(v_fold_3467_, v___x_3468_);
v___x_3470_ = lean_uint64_xor(v_fold_3467_, v___x_3469_);
v___x_3471_ = lean_uint64_to_usize(v___x_3470_);
v___x_3472_ = lean_usize_of_nat(v___x_3462_);
v___x_3473_ = ((size_t)1ULL);
v___x_3474_ = lean_usize_sub(v___x_3472_, v___x_3473_);
v___x_3475_ = lean_usize_land(v___x_3471_, v___x_3474_);
v___x_3476_ = lean_array_uget_borrowed(v_x_3454_, v___x_3475_);
lean_inc(v___x_3476_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 2, v___x_3476_);
v___x_3478_ = v___x_3460_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_key_3456_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_value_3457_);
lean_ctor_set(v_reuseFailAlloc_3481_, 2, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_array_uset(v_x_3454_, v___x_3475_, v___x_3478_);
v_x_3454_ = v___x_3479_;
v_x_3455_ = v_tail_3458_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(lean_object* v_i_3485_, lean_object* v_source_3486_, lean_object* v_target_3487_){
_start:
{
lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3488_ = lean_array_get_size(v_source_3486_);
v___x_3489_ = lean_nat_dec_lt(v_i_3485_, v___x_3488_);
if (v___x_3489_ == 0)
{
lean_dec_ref(v_source_3486_);
lean_dec(v_i_3485_);
return v_target_3487_;
}
else
{
lean_object* v_es_3490_; lean_object* v___x_3491_; lean_object* v_source_3492_; lean_object* v_target_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_es_3490_ = lean_array_fget(v_source_3486_, v_i_3485_);
v___x_3491_ = lean_box(0);
v_source_3492_ = lean_array_fset(v_source_3486_, v_i_3485_, v___x_3491_);
v_target_3493_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_target_3487_, v_es_3490_);
v___x_3494_ = lean_unsigned_to_nat(1u);
v___x_3495_ = lean_nat_add(v_i_3485_, v___x_3494_);
lean_dec(v_i_3485_);
v_i_3485_ = v___x_3495_;
v_source_3486_ = v_source_3492_;
v_target_3487_ = v_target_3493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(lean_object* v_data_3497_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v_nbuckets_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3498_ = lean_array_get_size(v_data_3497_);
v___x_3499_ = lean_unsigned_to_nat(2u);
v_nbuckets_3500_ = lean_nat_mul(v___x_3498_, v___x_3499_);
v___x_3501_ = lean_unsigned_to_nat(0u);
v___x_3502_ = lean_box(0);
v___x_3503_ = lean_mk_array(v_nbuckets_3500_, v___x_3502_);
v___x_3504_ = lean_array_propagate_mark(v_data_3497_, v___x_3503_);
v___x_3505_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v___x_3501_, v_data_3497_, v___x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(lean_object* v_m_3506_, lean_object* v_a_3507_, lean_object* v_b_3508_){
_start:
{
lean_object* v_size_3509_; lean_object* v_buckets_3510_; lean_object* v___x_3511_; uint64_t v___y_3513_; 
v_size_3509_ = lean_ctor_get(v_m_3506_, 0);
v_buckets_3510_ = lean_ctor_get(v_m_3506_, 1);
v___x_3511_ = lean_array_get_size(v_buckets_3510_);
if (lean_obj_tag(v_a_3507_) == 0)
{
uint64_t v___x_3550_; 
v___x_3550_ = 1723ULL;
v___y_3513_ = v___x_3550_;
goto v___jp_3512_;
}
else
{
uint64_t v_hash_3551_; 
v_hash_3551_ = lean_ctor_get_uint64(v_a_3507_, sizeof(void*)*2);
v___y_3513_ = v_hash_3551_;
goto v___jp_3512_;
}
v___jp_3512_:
{
uint64_t v___x_3514_; uint64_t v___x_3515_; uint64_t v_fold_3516_; uint64_t v___x_3517_; uint64_t v___x_3518_; uint64_t v___x_3519_; size_t v___x_3520_; size_t v___x_3521_; size_t v___x_3522_; size_t v___x_3523_; size_t v___x_3524_; lean_object* v_bkt_3525_; uint8_t v___x_3526_; 
v___x_3514_ = 32ULL;
v___x_3515_ = lean_uint64_shift_right(v___y_3513_, v___x_3514_);
v_fold_3516_ = lean_uint64_xor(v___y_3513_, v___x_3515_);
v___x_3517_ = 16ULL;
v___x_3518_ = lean_uint64_shift_right(v_fold_3516_, v___x_3517_);
v___x_3519_ = lean_uint64_xor(v_fold_3516_, v___x_3518_);
v___x_3520_ = lean_uint64_to_usize(v___x_3519_);
v___x_3521_ = lean_usize_of_nat(v___x_3511_);
v___x_3522_ = ((size_t)1ULL);
v___x_3523_ = lean_usize_sub(v___x_3521_, v___x_3522_);
v___x_3524_ = lean_usize_land(v___x_3520_, v___x_3523_);
v_bkt_3525_ = lean_array_uget_borrowed(v_buckets_3510_, v___x_3524_);
v___x_3526_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_3507_, v_bkt_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3547_; 
lean_inc_ref(v_buckets_3510_);
lean_inc(v_size_3509_);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_m_3506_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; lean_object* v_unused_3549_; 
v_unused_3548_ = lean_ctor_get(v_m_3506_, 1);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_m_3506_, 0);
lean_dec(v_unused_3549_);
v___x_3528_ = v_m_3506_;
v_isShared_3529_ = v_isSharedCheck_3547_;
goto v_resetjp_3527_;
}
else
{
lean_dec(v_m_3506_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3547_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v_size_x27_3531_; lean_object* v___x_3532_; lean_object* v_buckets_x27_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3530_ = lean_unsigned_to_nat(1u);
v_size_x27_3531_ = lean_nat_add(v_size_3509_, v___x_3530_);
lean_dec(v_size_3509_);
lean_inc(v_bkt_3525_);
v___x_3532_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3532_, 0, v_a_3507_);
lean_ctor_set(v___x_3532_, 1, v_b_3508_);
lean_ctor_set(v___x_3532_, 2, v_bkt_3525_);
v_buckets_x27_3533_ = lean_array_uset(v_buckets_3510_, v___x_3524_, v___x_3532_);
v___x_3534_ = lean_unsigned_to_nat(4u);
v___x_3535_ = lean_nat_mul(v_size_x27_3531_, v___x_3534_);
v___x_3536_ = lean_unsigned_to_nat(3u);
v___x_3537_ = lean_nat_div(v___x_3535_, v___x_3536_);
lean_dec(v___x_3535_);
v___x_3538_ = lean_array_get_size(v_buckets_x27_3533_);
v___x_3539_ = lean_nat_dec_le(v___x_3537_, v___x_3538_);
lean_dec(v___x_3537_);
if (v___x_3539_ == 0)
{
lean_object* v_val_3540_; lean_object* v___x_3542_; 
v_val_3540_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_buckets_x27_3533_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v_val_3540_);
lean_ctor_set(v___x_3528_, 0, v_size_x27_3531_);
v___x_3542_ = v___x_3528_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_size_x27_3531_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_val_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
else
{
lean_object* v___x_3545_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v_buckets_x27_3533_);
lean_ctor_set(v___x_3528_, 0, v_size_x27_3531_);
v___x_3545_ = v___x_3528_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_size_x27_3531_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_buckets_x27_3533_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_dec(v_b_3508_);
lean_dec(v_a_3507_);
return v_m_3506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object* v_op_3552_, lean_object* v_stx_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
uint8_t v_sparse_3556_; uint8_t v_separateFinalOperand_3557_; lean_object* v_precs_x3f_3558_; lean_object* v_extendedChainKinds_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3600_; 
v_sparse_3556_ = lean_ctor_get_uint8(v_op_3552_, sizeof(void*)*2);
v_separateFinalOperand_3557_ = lean_ctor_get_uint8(v_op_3552_, sizeof(void*)*2 + 1);
v_precs_x3f_3558_ = lean_ctor_get(v_op_3552_, 0);
v_extendedChainKinds_3559_ = lean_ctor_get(v_op_3552_, 1);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_op_3552_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3561_ = v_op_3552_;
v_isShared_3562_ = v_isSharedCheck_3600_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_extendedChainKinds_3559_);
lean_inc(v_precs_x3f_3558_);
lean_dec(v_op_3552_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3600_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_env_3563_; lean_object* v_opts_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v_env_3563_ = lean_ctor_get(v_a_3554_, 0);
v_opts_3564_ = lean_ctor_get(v_a_3554_, 3);
lean_inc(v_stx_3553_);
v___x_3565_ = l_Lean_Syntax_getKind(v_stx_3553_);
v___x_3566_ = lean_box(0);
v___x_3567_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_extendedChainKinds_3559_, v___x_3565_, v___x_3566_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 1, v___x_3567_);
v___x_3569_ = v___x_3561_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_precs_x3f_3558_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v___x_3567_);
lean_ctor_set_uint8(v_reuseFailAlloc_3599_, sizeof(void*)*2, v_sparse_3556_);
lean_ctor_set_uint8(v_reuseFailAlloc_3599_, sizeof(void*)*2 + 1, v_separateFinalOperand_3557_);
v___x_3569_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; size_t v_sz_3571_; size_t v___x_3572_; lean_object* v___x_3573_; 
lean_inc_ref(v_env_3563_);
v___x_3570_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_3563_, v_opts_3564_, v___x_3569_, v_stx_3553_);
lean_dec_ref(v___x_3569_);
v_sz_3571_ = lean_array_size(v___x_3570_);
v___x_3572_ = ((size_t)0ULL);
v___x_3573_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_3571_, v___x_3572_, v___x_3570_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_a_3574_; lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3589_; 
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
v_a_3575_ = lean_ctor_get(v___x_3573_, 1);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3577_ = v___x_3573_;
v_isShared_3578_ = v_isSharedCheck_3589_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_inc(v_a_3574_);
lean_dec(v___x_3573_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3589_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___y_3580_; uint8_t v___x_3585_; 
v___x_3585_ = 1;
if (v_sparse_3556_ == 0)
{
lean_object* v___x_3586_; 
v___x_3586_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3586_, 0, v___x_3585_);
lean_ctor_set_uint8(v___x_3586_, 1, v_sparse_3556_);
lean_ctor_set_uint8(v___x_3586_, 2, v___x_3585_);
lean_ctor_set_uint8(v___x_3586_, 3, v___x_3585_);
v___y_3580_ = v___x_3586_;
goto v___jp_3579_;
}
else
{
uint8_t v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = 0;
v___x_3588_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_3588_, 0, v___x_3585_);
lean_ctor_set_uint8(v___x_3588_, 1, v___x_3587_);
lean_ctor_set_uint8(v___x_3588_, 2, v___x_3585_);
lean_ctor_set_uint8(v___x_3588_, 3, v___x_3587_);
lean_ctor_set_uint8(v___x_3588_, 4, v_separateFinalOperand_3557_);
v___y_3580_ = v___x_3588_;
goto v___jp_3579_;
}
v___jp_3579_:
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = l_Lean_Fmt_Layouts_infixOperator(v_a_3574_, v___y_3580_);
lean_dec_ref(v___y_3580_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3581_);
v___x_3583_ = v___x_3577_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_a_3575_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
v_a_3590_ = lean_ctor_get(v___x_3573_, 0);
v_a_3591_ = lean_ctor_get(v___x_3573_, 1);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3573_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_inc(v_a_3590_);
lean_dec(v___x_3573_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3590_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object* v_op_3601_, lean_object* v_stx_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Fmt_fmtInfixOperator(v_op_3601_, v_stx_3602_, v_a_3603_, v_a_3604_);
lean_dec_ref(v_a_3603_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0(lean_object* v_00_u03b2_3606_, lean_object* v_m_3607_, lean_object* v_a_3608_, lean_object* v_b_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_m_3607_, v_a_3608_, v_b_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0(lean_object* v_00_u03b2_3611_, lean_object* v_data_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_data_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3614_, lean_object* v_i_3615_, lean_object* v_source_3616_, lean_object* v_target_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v_i_3615_, v_source_3616_, v_target_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3620_, v_x_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
if (lean_obj_tag(v_x_3623_) == 0)
{
if (lean_obj_tag(v_x_3624_) == 0)
{
uint8_t v___x_3625_; 
v___x_3625_ = 1;
return v___x_3625_;
}
else
{
uint8_t v___x_3626_; 
v___x_3626_ = 0;
return v___x_3626_;
}
}
else
{
if (lean_obj_tag(v_x_3624_) == 0)
{
uint8_t v___x_3627_; 
v___x_3627_ = 0;
return v___x_3627_;
}
else
{
lean_object* v_val_3628_; lean_object* v_val_3629_; uint8_t v___x_3630_; 
v_val_3628_ = lean_ctor_get(v_x_3623_, 0);
v_val_3629_ = lean_ctor_get(v_x_3624_, 0);
v___x_3630_ = lean_string_dec_eq(v_val_3628_, v_val_3629_);
return v___x_3630_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0___boxed(lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
uint8_t v_res_3633_; lean_object* v_r_3634_; 
v_res_3633_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v_x_3631_, v_x_3632_);
lean_dec(v_x_3632_);
lean_dec(v_x_3631_);
v_r_3634_ = lean_box(v_res_3633_);
return v_r_3634_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(lean_object* v_msg_3635_){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = l_String_instInhabitedSlice;
v___x_3637_ = lean_panic_fn_borrowed(v___x_3636_, v_msg_3635_);
return v___x_3637_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(lean_object* v_s_3638_, lean_object* v_a_3639_, uint8_t v_b_3640_){
_start:
{
lean_object* v_str_3641_; lean_object* v_startInclusive_3642_; lean_object* v_endExclusive_3643_; lean_object* v___x_3644_; uint8_t v_decide_3645_; 
v_str_3641_ = lean_ctor_get(v_s_3638_, 0);
v_startInclusive_3642_ = lean_ctor_get(v_s_3638_, 1);
v_endExclusive_3643_ = lean_ctor_get(v_s_3638_, 2);
v___x_3644_ = lean_nat_sub(v_endExclusive_3643_, v_startInclusive_3642_);
v_decide_3645_ = lean_nat_dec_eq(v_a_3639_, v___x_3644_);
lean_dec(v___x_3644_);
if (v_decide_3645_ == 0)
{
lean_object* v___x_3646_; uint32_t v___x_3647_; uint32_t v___x_3648_; uint8_t v___x_3649_; 
v___x_3646_ = lean_nat_add(v_startInclusive_3642_, v_a_3639_);
lean_dec(v_a_3639_);
v___x_3647_ = lean_string_utf8_get_fast(v_str_3641_, v___x_3646_);
v___x_3648_ = l_Lean_idEndEscape;
v___x_3649_ = lean_uint32_dec_eq(v___x_3647_, v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = lean_string_utf8_next_fast(v_str_3641_, v___x_3646_);
lean_dec(v___x_3646_);
v___x_3651_ = lean_nat_sub(v___x_3650_, v_startInclusive_3642_);
v_a_3639_ = v___x_3651_;
v_b_3640_ = v___x_3649_;
goto _start;
}
else
{
lean_dec(v___x_3646_);
return v___x_3649_;
}
}
else
{
lean_dec(v_a_3639_);
return v_b_3640_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg___boxed(lean_object* v_s_3653_, lean_object* v_a_3654_, lean_object* v_b_3655_){
_start:
{
uint8_t v_b_boxed_3656_; uint8_t v_res_3657_; lean_object* v_r_3658_; 
v_b_boxed_3656_ = lean_unbox(v_b_3655_);
v_res_3657_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3653_, v_a_3654_, v_b_boxed_3656_);
lean_dec_ref(v_s_3653_);
v_r_3658_ = lean_box(v_res_3657_);
return v_r_3658_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(lean_object* v_s_3659_){
_start:
{
lean_object* v_searcher_3660_; uint8_t v___x_3661_; uint8_t v___x_3662_; 
v_searcher_3660_ = lean_unsigned_to_nat(0u);
v___x_3661_ = 0;
v___x_3662_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3659_, v_searcher_3660_, v___x_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1___boxed(lean_object* v_s_3663_){
_start:
{
uint8_t v_res_3664_; lean_object* v_r_3665_; 
v_res_3664_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v_s_3663_);
lean_dec_ref(v_s_3663_);
v_r_3665_ = lean_box(v_res_3664_);
return v_r_3665_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(lean_object* v_s_3666_, lean_object* v_pos_3667_){
_start:
{
lean_object* v_str_3668_; lean_object* v_startInclusive_3669_; lean_object* v_endExclusive_3670_; lean_object* v___x_3671_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v_decide_3682_; 
v_str_3668_ = lean_ctor_get(v_s_3666_, 0);
v_startInclusive_3669_ = lean_ctor_get(v_s_3666_, 1);
v_endExclusive_3670_ = lean_ctor_get(v_s_3666_, 2);
v___x_3671_ = lean_nat_add(v_startInclusive_3669_, v_pos_3667_);
v___x_3680_ = lean_unsigned_to_nat(0u);
v___x_3681_ = lean_nat_sub(v_endExclusive_3670_, v___x_3671_);
v_decide_3682_ = lean_nat_dec_eq(v___x_3680_, v___x_3681_);
lean_dec(v___x_3681_);
if (v_decide_3682_ == 0)
{
uint32_t v___x_3683_; uint32_t v___x_3705_; uint8_t v___x_3706_; 
v___x_3683_ = lean_string_utf8_get_fast(v_str_3668_, v___x_3671_);
v___x_3705_ = 65;
v___x_3706_ = lean_uint32_dec_le(v___x_3705_, v___x_3683_);
if (v___x_3706_ == 0)
{
goto v___jp_3700_;
}
else
{
uint32_t v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = 90;
v___x_3708_ = lean_uint32_dec_le(v___x_3683_, v___x_3707_);
if (v___x_3708_ == 0)
{
goto v___jp_3700_;
}
else
{
goto v___jp_3672_;
}
}
v___jp_3684_:
{
uint32_t v___x_3685_; uint8_t v___x_3686_; 
v___x_3685_ = 95;
v___x_3686_ = lean_uint32_dec_eq(v___x_3683_, v___x_3685_);
if (v___x_3686_ == 0)
{
uint32_t v___x_3687_; uint8_t v___x_3688_; 
v___x_3687_ = 39;
v___x_3688_ = lean_uint32_dec_eq(v___x_3683_, v___x_3687_);
if (v___x_3688_ == 0)
{
uint32_t v___x_3689_; uint8_t v___x_3690_; 
v___x_3689_ = 33;
v___x_3690_ = lean_uint32_dec_eq(v___x_3683_, v___x_3689_);
if (v___x_3690_ == 0)
{
uint32_t v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = 63;
v___x_3692_ = lean_uint32_dec_eq(v___x_3683_, v___x_3691_);
if (v___x_3692_ == 0)
{
uint8_t v___x_3693_; 
v___x_3693_ = l_Lean_isLetterLike(v___x_3683_);
if (v___x_3693_ == 0)
{
uint8_t v___x_3694_; 
v___x_3694_ = l_Lean_isSubScriptAlnum(v___x_3683_);
if (v___x_3694_ == 0)
{
lean_dec(v___x_3671_);
return v_pos_3667_;
}
else
{
goto v___jp_3672_;
}
}
else
{
goto v___jp_3672_;
}
}
else
{
goto v___jp_3672_;
}
}
else
{
goto v___jp_3672_;
}
}
else
{
goto v___jp_3672_;
}
}
else
{
goto v___jp_3672_;
}
}
v___jp_3695_:
{
uint32_t v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = 48;
v___x_3697_ = lean_uint32_dec_le(v___x_3696_, v___x_3683_);
if (v___x_3697_ == 0)
{
goto v___jp_3684_;
}
else
{
uint32_t v___x_3698_; uint8_t v___x_3699_; 
v___x_3698_ = 57;
v___x_3699_ = lean_uint32_dec_le(v___x_3683_, v___x_3698_);
if (v___x_3699_ == 0)
{
goto v___jp_3684_;
}
else
{
goto v___jp_3672_;
}
}
}
v___jp_3700_:
{
uint32_t v___x_3701_; uint8_t v___x_3702_; 
v___x_3701_ = 97;
v___x_3702_ = lean_uint32_dec_le(v___x_3701_, v___x_3683_);
if (v___x_3702_ == 0)
{
goto v___jp_3695_;
}
else
{
uint32_t v___x_3703_; uint8_t v___x_3704_; 
v___x_3703_ = 122;
v___x_3704_ = lean_uint32_dec_le(v___x_3683_, v___x_3703_);
if (v___x_3704_ == 0)
{
goto v___jp_3695_;
}
else
{
goto v___jp_3672_;
}
}
}
}
else
{
lean_dec(v___x_3671_);
return v_pos_3667_;
}
v___jp_3672_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; uint8_t v___x_3678_; 
v___x_3673_ = lean_string_utf8_next_fast(v_str_3668_, v___x_3671_);
v___x_3674_ = lean_nat_sub(v___x_3673_, v___x_3671_);
lean_dec(v___x_3671_);
v___x_3675_ = lean_nat_add(v_pos_3667_, v___x_3674_);
lean_dec(v___x_3674_);
v___x_3676_ = lean_unsigned_to_nat(1u);
v___x_3677_ = lean_nat_add(v_pos_3667_, v___x_3676_);
v___x_3678_ = lean_nat_dec_le(v___x_3677_, v___x_3675_);
lean_dec(v___x_3677_);
if (v___x_3678_ == 0)
{
lean_dec(v___x_3675_);
return v_pos_3667_;
}
else
{
lean_dec(v_pos_3667_);
v_pos_3667_ = v___x_3675_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2___boxed(lean_object* v_s_3709_, lean_object* v_pos_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v_s_3709_, v_pos_3710_);
lean_dec_ref(v_s_3709_);
return v_res_3711_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__0(void){
_start:
{
uint32_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3712_ = l_Lean_idBeginEscape;
v___x_3713_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3714_ = lean_string_push(v___x_3713_, v___x_3712_);
return v___x_3714_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__1(void){
_start:
{
uint32_t v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = l_Lean_idEndEscape;
v___x_3716_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3717_ = lean_string_push(v___x_3716_, v___x_3715_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object* v_stx_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; uint8_t v___y_3725_; lean_object* v___x_3728_; lean_object* v___x_3729_; uint8_t v___x_3730_; 
v___x_3728_ = l_Lean_Syntax_getNumArgs(v_stx_3718_);
v___x_3729_ = lean_unsigned_to_nat(2u);
v___x_3730_ = lean_nat_dec_eq(v___x_3728_, v___x_3729_);
lean_dec(v___x_3728_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3731_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
lean_ctor_set(v___x_3732_, 1, v_a_3720_);
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = lean_unsigned_to_nat(0u);
v___x_3734_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3718_, v___x_3733_, v_a_3720_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v_a_3736_; lean_object* v___x_3737_; lean_object* v___y_3739_; lean_object* v___y_3774_; lean_object* v_startInclusive_3775_; lean_object* v_endExclusive_3776_; uint32_t v___y_3796_; uint32_t v___y_3801_; uint32_t v___y_3807_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
v_a_3736_ = lean_ctor_get(v___x_3734_, 1);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3734_, 2);
v___x_3737_ = l_Lean_Syntax_getAtomVal(v_a_3735_);
v___x_3823_ = lean_string_utf8_byte_size(v___x_3737_);
v___x_3824_ = lean_nat_dec_lt(v___x_3733_, v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3825_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3826_ = lean_string_append(v___x_3825_, v___x_3737_);
v___x_3827_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3828_ = lean_string_append(v___x_3826_, v___x_3827_);
v___x_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
v___y_3739_ = v___x_3829_;
goto v___jp_3738_;
}
else
{
uint8_t v_c_3830_; uint8_t v___x_3839_; uint8_t v___x_3840_; 
v_c_3830_ = lean_string_get_byte_fast(v___x_3737_, v___x_3733_);
v___x_3839_ = 97;
v___x_3840_ = lean_uint8_dec_le(v___x_3839_, v_c_3830_);
if (v___x_3840_ == 0)
{
goto v___jp_3834_;
}
else
{
uint8_t v___x_3841_; uint8_t v___x_3842_; 
v___x_3841_ = 122;
v___x_3842_ = lean_uint8_dec_le(v_c_3830_, v___x_3841_);
if (v___x_3842_ == 0)
{
goto v___jp_3834_;
}
else
{
goto v___jp_3819_;
}
}
v___jp_3831_:
{
uint8_t v___x_3832_; uint8_t v___x_3833_; 
v___x_3832_ = 95;
v___x_3833_ = lean_uint8_dec_eq(v_c_3830_, v___x_3832_);
if (v___x_3833_ == 0)
{
goto v___jp_3812_;
}
else
{
goto v___jp_3819_;
}
}
v___jp_3834_:
{
uint8_t v___x_3835_; uint8_t v___x_3836_; 
v___x_3835_ = 65;
v___x_3836_ = lean_uint8_dec_le(v___x_3835_, v_c_3830_);
if (v___x_3836_ == 0)
{
goto v___jp_3831_;
}
else
{
uint8_t v___x_3837_; uint8_t v___x_3838_; 
v___x_3837_ = 90;
v___x_3838_ = lean_uint8_dec_le(v_c_3830_, v___x_3837_);
if (v___x_3838_ == 0)
{
goto v___jp_3831_;
}
else
{
goto v___jp_3819_;
}
}
}
}
v___jp_3738_:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Fmt_fmt(v_a_3735_, v_a_3719_, v_a_3736_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v_a_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
v_a_3742_ = lean_ctor_get(v___x_3740_, 1);
lean_inc(v_a_3742_);
lean_dec_ref_known(v___x_3740_, 2);
v___x_3743_ = lean_unsigned_to_nat(1u);
v___x_3744_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3718_, v___x_3743_, v_a_3742_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v_a_3746_; lean_object* v___x_3747_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
v_a_3746_ = lean_ctor_get(v___x_3744_, 1);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3744_, 2);
v___x_3747_ = l_Lean_Fmt_fmt(v_a_3745_, v_a_3719_, v_a_3746_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v_a_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
v_a_3749_ = lean_ctor_get(v___x_3747_, 1);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3747_, 2);
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3737_);
v___x_3751_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3739_, v___x_3750_);
lean_dec_ref_known(v___x_3750_, 1);
lean_dec(v___y_3739_);
if (v___x_3751_ == 0)
{
uint8_t v___x_3752_; 
v___x_3752_ = 1;
v___y_3722_ = v_a_3749_;
v___y_3723_ = v_a_3748_;
v___y_3724_ = v_a_3741_;
v___y_3725_ = v___x_3752_;
goto v___jp_3721_;
}
else
{
uint8_t v___x_3753_; 
v___x_3753_ = 2;
v___y_3722_ = v_a_3749_;
v___y_3723_ = v_a_3748_;
v___y_3724_ = v_a_3741_;
v___y_3725_ = v___x_3753_;
goto v___jp_3721_;
}
}
else
{
lean_dec(v_a_3741_);
lean_dec(v___y_3739_);
lean_dec_ref(v___x_3737_);
return v___x_3747_;
}
}
else
{
lean_object* v_a_3754_; lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v_a_3741_);
lean_dec(v___y_3739_);
lean_dec_ref(v___x_3737_);
v_a_3754_ = lean_ctor_get(v___x_3744_, 0);
v_a_3755_ = lean_ctor_get(v___x_3744_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3744_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_inc(v_a_3754_);
lean_dec(v___x_3744_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3754_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
else
{
lean_dec(v___y_3739_);
lean_dec_ref(v___x_3737_);
return v___x_3740_;
}
}
v___jp_3763_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v___x_3764_ = lean_string_utf8_byte_size(v___x_3737_);
lean_inc_ref(v___x_3737_);
v___x_3765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3737_);
lean_ctor_set(v___x_3765_, 1, v___x_3733_);
lean_ctor_set(v___x_3765_, 2, v___x_3764_);
v___x_3766_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3765_);
lean_dec_ref_known(v___x_3765_, 3);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3767_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3768_ = lean_string_append(v___x_3767_, v___x_3737_);
v___x_3769_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
v___y_3739_ = v___x_3771_;
goto v___jp_3738_;
}
else
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_box(0);
v___y_3739_ = v___x_3772_;
goto v___jp_3738_;
}
}
v___jp_3773_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; uint8_t v_decide_3779_; 
v___x_3777_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3774_, v___x_3733_);
lean_dec_ref(v___y_3774_);
v___x_3778_ = lean_nat_sub(v_endExclusive_3776_, v_startInclusive_3775_);
lean_dec(v_startInclusive_3775_);
lean_dec(v_endExclusive_3776_);
v_decide_3779_ = lean_nat_dec_eq(v___x_3777_, v___x_3778_);
lean_dec(v___x_3778_);
lean_dec(v___x_3777_);
if (v_decide_3779_ == 0)
{
goto v___jp_3763_;
}
else
{
lean_object* v___x_3780_; 
lean_inc_ref(v___x_3737_);
v___x_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3737_);
v___y_3739_ = v___x_3780_;
goto v___jp_3738_;
}
}
v___jp_3781_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v_startInclusive_3784_; lean_object* v_endExclusive_3785_; 
v___x_3782_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3783_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3782_);
v_startInclusive_3784_ = lean_ctor_get(v___x_3783_, 1);
lean_inc(v_startInclusive_3784_);
v_endExclusive_3785_ = lean_ctor_get(v___x_3783_, 2);
lean_inc(v_endExclusive_3785_);
v___y_3774_ = v___x_3783_;
v_startInclusive_3775_ = v_startInclusive_3784_;
v_endExclusive_3776_ = v_endExclusive_3785_;
goto v___jp_3773_;
}
v___jp_3786_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; 
v___x_3787_ = lean_string_utf8_byte_size(v___x_3737_);
lean_inc_ref(v___x_3737_);
v___x_3788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3737_);
lean_ctor_set(v___x_3788_, 1, v___x_3733_);
lean_ctor_set(v___x_3788_, 2, v___x_3787_);
v___x_3789_ = lean_unsigned_to_nat(1u);
v___x_3790_ = l_Substring_Raw_nextn(v___x_3788_, v___x_3789_, v___x_3733_);
lean_dec_ref_known(v___x_3788_, 3);
v___x_3791_ = lean_string_is_valid_pos(v___x_3737_, v___x_3790_);
if (v___x_3791_ == 0)
{
lean_dec(v___x_3790_);
goto v___jp_3781_;
}
else
{
uint8_t v___x_3792_; 
v___x_3792_ = lean_string_is_valid_pos(v___x_3737_, v___x_3787_);
if (v___x_3792_ == 0)
{
lean_dec(v___x_3790_);
goto v___jp_3781_;
}
else
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_nat_dec_le(v___x_3790_, v___x_3787_);
if (v___x_3793_ == 0)
{
lean_dec(v___x_3790_);
goto v___jp_3781_;
}
else
{
lean_object* v___x_3794_; 
lean_inc(v___x_3790_);
lean_inc_ref(v___x_3737_);
v___x_3794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3737_);
lean_ctor_set(v___x_3794_, 1, v___x_3790_);
lean_ctor_set(v___x_3794_, 2, v___x_3787_);
v___y_3774_ = v___x_3794_;
v_startInclusive_3775_ = v___x_3790_;
v_endExclusive_3776_ = v___x_3787_;
goto v___jp_3773_;
}
}
}
}
v___jp_3795_:
{
uint32_t v___x_3797_; uint8_t v___x_3798_; 
v___x_3797_ = 95;
v___x_3798_ = lean_uint32_dec_eq(v___y_3796_, v___x_3797_);
if (v___x_3798_ == 0)
{
uint8_t v___x_3799_; 
v___x_3799_ = l_Lean_isLetterLike(v___y_3796_);
if (v___x_3799_ == 0)
{
goto v___jp_3763_;
}
else
{
goto v___jp_3786_;
}
}
else
{
goto v___jp_3786_;
}
}
v___jp_3800_:
{
uint32_t v___x_3802_; uint8_t v___x_3803_; 
v___x_3802_ = 97;
v___x_3803_ = lean_uint32_dec_le(v___x_3802_, v___y_3801_);
if (v___x_3803_ == 0)
{
v___y_3796_ = v___y_3801_;
goto v___jp_3795_;
}
else
{
uint32_t v___x_3804_; uint8_t v___x_3805_; 
v___x_3804_ = 122;
v___x_3805_ = lean_uint32_dec_le(v___y_3801_, v___x_3804_);
if (v___x_3805_ == 0)
{
v___y_3796_ = v___y_3801_;
goto v___jp_3795_;
}
else
{
goto v___jp_3786_;
}
}
}
v___jp_3806_:
{
uint32_t v___x_3808_; uint8_t v___x_3809_; 
v___x_3808_ = 65;
v___x_3809_ = lean_uint32_dec_le(v___x_3808_, v___y_3807_);
if (v___x_3809_ == 0)
{
v___y_3801_ = v___y_3807_;
goto v___jp_3800_;
}
else
{
uint32_t v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = 90;
v___x_3811_ = lean_uint32_dec_le(v___y_3807_, v___x_3810_);
if (v___x_3811_ == 0)
{
v___y_3801_ = v___y_3807_;
goto v___jp_3800_;
}
else
{
goto v___jp_3786_;
}
}
}
v___jp_3812_:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_string_utf8_byte_size(v___x_3737_);
lean_inc_ref(v___x_3737_);
v___x_3814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3737_);
lean_ctor_set(v___x_3814_, 1, v___x_3733_);
lean_ctor_set(v___x_3814_, 2, v___x_3813_);
v___x_3815_ = l_String_Slice_Pos_get_x3f(v___x_3814_, v___x_3733_);
lean_dec_ref_known(v___x_3814_, 3);
if (lean_obj_tag(v___x_3815_) == 0)
{
uint32_t v___x_3816_; 
v___x_3816_ = 65;
v___y_3807_ = v___x_3816_;
goto v___jp_3806_;
}
else
{
lean_object* v_val_3817_; uint32_t v___x_3818_; 
v_val_3817_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_val_3817_);
lean_dec_ref_known(v___x_3815_, 1);
v___x_3818_ = lean_unbox_uint32(v_val_3817_);
lean_dec(v_val_3817_);
v___y_3807_ = v___x_3818_;
goto v___jp_3806_;
}
}
v___jp_3819_:
{
lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3737_, v___x_3820_);
if (v___x_3821_ == 0)
{
goto v___jp_3812_;
}
else
{
lean_object* v___x_3822_; 
lean_inc_ref(v___x_3737_);
v___x_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3737_);
v___y_3739_ = v___x_3822_;
goto v___jp_3738_;
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
v_a_3843_ = lean_ctor_get(v___x_3734_, 0);
v_a_3844_ = lean_ctor_get(v___x_3734_, 1);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3734_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_inc(v_a_3843_);
lean_dec(v___x_3734_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3843_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
v___jp_3721_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_3724_, v___y_3723_, v___y_3725_);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v___y_3722_);
return v___x_3727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object* v_stx_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_Fmt_fmtPrefixOperator(v_stx_3852_, v_a_3853_, v_a_3854_);
lean_dec_ref(v_a_3853_);
lean_dec(v_stx_3852_);
return v_res_3855_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(lean_object* v_s_3856_, lean_object* v_inst_3857_, lean_object* v_R_3858_, lean_object* v_a_3859_, uint8_t v_b_3860_, lean_object* v_c_3861_){
_start:
{
uint8_t v___x_3862_; 
v___x_3862_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3856_, v_a_3859_, v_b_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___boxed(lean_object* v_s_3863_, lean_object* v_inst_3864_, lean_object* v_R_3865_, lean_object* v_a_3866_, lean_object* v_b_3867_, lean_object* v_c_3868_){
_start:
{
uint8_t v_b_boxed_3869_; uint8_t v_res_3870_; lean_object* v_r_3871_; 
v_b_boxed_3869_ = lean_unbox(v_b_3867_);
v_res_3870_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(v_s_3863_, v_inst_3864_, v_R_3865_, v_a_3866_, v_b_boxed_3869_, v_c_3868_);
lean_dec_ref(v_s_3863_);
v_r_3871_ = lean_box(v_res_3870_);
return v_r_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object* v_stx_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3875_ = l_Lean_Syntax_getNumArgs(v_stx_3872_);
v___x_3876_ = lean_unsigned_to_nat(2u);
v___x_3877_ = lean_nat_dec_eq(v___x_3875_, v___x_3876_);
lean_dec(v___x_3875_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
lean_ctor_set(v___x_3879_, 1, v_a_3874_);
return v___x_3879_;
}
else
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_unsigned_to_nat(0u);
v___x_3881_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3872_, v___x_3880_, v_a_3874_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v_a_3883_; lean_object* v___x_3884_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
v_a_3883_ = lean_ctor_get(v___x_3881_, 1);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3881_, 2);
v___x_3884_ = l_Lean_Fmt_fmt(v_a_3882_, v_a_3873_, v_a_3883_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3999_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
v_a_3886_ = lean_ctor_get(v___x_3884_, 1);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3888_ = v___x_3884_;
v_isShared_3889_ = v_isSharedCheck_3999_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_inc(v_a_3885_);
lean_dec(v___x_3884_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3999_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___y_3891_; lean_object* v___y_3892_; uint8_t v___y_3893_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3872_, v___x_3898_, v_a_3886_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v_a_3901_; lean_object* v___x_3902_; lean_object* v___y_3904_; lean_object* v___y_3923_; lean_object* v_startInclusive_3924_; lean_object* v_endExclusive_3925_; uint32_t v___y_3944_; uint32_t v___y_3949_; uint32_t v___y_3955_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
v_a_3901_ = lean_ctor_get(v___x_3899_, 1);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3899_, 2);
v___x_3902_ = l_Lean_Syntax_getAtomVal(v_a_3900_);
v___x_3970_ = lean_string_utf8_byte_size(v___x_3902_);
v___x_3971_ = lean_nat_dec_lt(v___x_3880_, v___x_3970_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3972_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3973_ = lean_string_append(v___x_3972_, v___x_3902_);
v___x_3974_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3975_ = lean_string_append(v___x_3973_, v___x_3974_);
v___x_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
v___y_3904_ = v___x_3976_;
goto v___jp_3903_;
}
else
{
uint8_t v_c_3977_; uint8_t v___x_3986_; uint8_t v___x_3987_; 
v_c_3977_ = lean_string_get_byte_fast(v___x_3902_, v___x_3880_);
v___x_3986_ = 97;
v___x_3987_ = lean_uint8_dec_le(v___x_3986_, v_c_3977_);
if (v___x_3987_ == 0)
{
goto v___jp_3981_;
}
else
{
uint8_t v___x_3988_; uint8_t v___x_3989_; 
v___x_3988_ = 122;
v___x_3989_ = lean_uint8_dec_le(v_c_3977_, v___x_3988_);
if (v___x_3989_ == 0)
{
goto v___jp_3981_;
}
else
{
goto v___jp_3967_;
}
}
v___jp_3978_:
{
uint8_t v___x_3979_; uint8_t v___x_3980_; 
v___x_3979_ = 95;
v___x_3980_ = lean_uint8_dec_eq(v_c_3977_, v___x_3979_);
if (v___x_3980_ == 0)
{
goto v___jp_3960_;
}
else
{
goto v___jp_3967_;
}
}
v___jp_3981_:
{
uint8_t v___x_3982_; uint8_t v___x_3983_; 
v___x_3982_ = 65;
v___x_3983_ = lean_uint8_dec_le(v___x_3982_, v_c_3977_);
if (v___x_3983_ == 0)
{
goto v___jp_3978_;
}
else
{
uint8_t v___x_3984_; uint8_t v___x_3985_; 
v___x_3984_ = 90;
v___x_3985_ = lean_uint8_dec_le(v_c_3977_, v___x_3984_);
if (v___x_3985_ == 0)
{
goto v___jp_3978_;
}
else
{
goto v___jp_3967_;
}
}
}
}
v___jp_3903_:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Fmt_fmt(v_a_3900_, v_a_3873_, v_a_3901_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v_a_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
v_a_3907_ = lean_ctor_get(v___x_3905_, 1);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3905_, 2);
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3902_);
v___x_3909_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3904_, v___x_3908_);
lean_dec_ref_known(v___x_3908_, 1);
lean_dec(v___y_3904_);
if (v___x_3909_ == 0)
{
uint8_t v___x_3910_; 
v___x_3910_ = 0;
v___y_3891_ = v_a_3906_;
v___y_3892_ = v_a_3907_;
v___y_3893_ = v___x_3910_;
goto v___jp_3890_;
}
else
{
uint8_t v___x_3911_; 
v___x_3911_ = 1;
v___y_3891_ = v_a_3906_;
v___y_3892_ = v_a_3907_;
v___y_3893_ = v___x_3911_;
goto v___jp_3890_;
}
}
else
{
lean_dec(v___y_3904_);
lean_dec_ref(v___x_3902_);
lean_del_object(v___x_3888_);
lean_dec(v_a_3885_);
return v___x_3905_;
}
}
v___jp_3912_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; 
v___x_3913_ = lean_string_utf8_byte_size(v___x_3902_);
lean_inc_ref(v___x_3902_);
v___x_3914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3902_);
lean_ctor_set(v___x_3914_, 1, v___x_3880_);
lean_ctor_set(v___x_3914_, 2, v___x_3913_);
v___x_3915_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3914_);
lean_dec_ref_known(v___x_3914_, 3);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3916_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3917_ = lean_string_append(v___x_3916_, v___x_3902_);
v___x_3918_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3919_ = lean_string_append(v___x_3917_, v___x_3918_);
v___x_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3919_);
v___y_3904_ = v___x_3920_;
goto v___jp_3903_;
}
else
{
lean_object* v___x_3921_; 
v___x_3921_ = lean_box(0);
v___y_3904_ = v___x_3921_;
goto v___jp_3903_;
}
}
v___jp_3922_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; uint8_t v_decide_3928_; 
v___x_3926_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3923_, v___x_3880_);
lean_dec_ref(v___y_3923_);
v___x_3927_ = lean_nat_sub(v_endExclusive_3925_, v_startInclusive_3924_);
lean_dec(v_startInclusive_3924_);
lean_dec(v_endExclusive_3925_);
v_decide_3928_ = lean_nat_dec_eq(v___x_3926_, v___x_3927_);
lean_dec(v___x_3927_);
lean_dec(v___x_3926_);
if (v_decide_3928_ == 0)
{
goto v___jp_3912_;
}
else
{
lean_object* v___x_3929_; 
lean_inc_ref(v___x_3902_);
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3902_);
v___y_3904_ = v___x_3929_;
goto v___jp_3903_;
}
}
v___jp_3930_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v_startInclusive_3933_; lean_object* v_endExclusive_3934_; 
v___x_3931_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3932_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3931_);
v_startInclusive_3933_ = lean_ctor_get(v___x_3932_, 1);
lean_inc(v_startInclusive_3933_);
v_endExclusive_3934_ = lean_ctor_get(v___x_3932_, 2);
lean_inc(v_endExclusive_3934_);
v___y_3923_ = v___x_3932_;
v_startInclusive_3924_ = v_startInclusive_3933_;
v_endExclusive_3925_ = v_endExclusive_3934_;
goto v___jp_3922_;
}
v___jp_3935_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3936_ = lean_string_utf8_byte_size(v___x_3902_);
lean_inc_ref(v___x_3902_);
v___x_3937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3902_);
lean_ctor_set(v___x_3937_, 1, v___x_3880_);
lean_ctor_set(v___x_3937_, 2, v___x_3936_);
v___x_3938_ = l_Substring_Raw_nextn(v___x_3937_, v___x_3898_, v___x_3880_);
lean_dec_ref_known(v___x_3937_, 3);
v___x_3939_ = lean_string_is_valid_pos(v___x_3902_, v___x_3938_);
if (v___x_3939_ == 0)
{
lean_dec(v___x_3938_);
goto v___jp_3930_;
}
else
{
uint8_t v___x_3940_; 
v___x_3940_ = lean_string_is_valid_pos(v___x_3902_, v___x_3936_);
if (v___x_3940_ == 0)
{
lean_dec(v___x_3938_);
goto v___jp_3930_;
}
else
{
uint8_t v___x_3941_; 
v___x_3941_ = lean_nat_dec_le(v___x_3938_, v___x_3936_);
if (v___x_3941_ == 0)
{
lean_dec(v___x_3938_);
goto v___jp_3930_;
}
else
{
lean_object* v___x_3942_; 
lean_inc(v___x_3938_);
lean_inc_ref(v___x_3902_);
v___x_3942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3902_);
lean_ctor_set(v___x_3942_, 1, v___x_3938_);
lean_ctor_set(v___x_3942_, 2, v___x_3936_);
v___y_3923_ = v___x_3942_;
v_startInclusive_3924_ = v___x_3938_;
v_endExclusive_3925_ = v___x_3936_;
goto v___jp_3922_;
}
}
}
}
v___jp_3943_:
{
uint32_t v___x_3945_; uint8_t v___x_3946_; 
v___x_3945_ = 95;
v___x_3946_ = lean_uint32_dec_eq(v___y_3944_, v___x_3945_);
if (v___x_3946_ == 0)
{
uint8_t v___x_3947_; 
v___x_3947_ = l_Lean_isLetterLike(v___y_3944_);
if (v___x_3947_ == 0)
{
goto v___jp_3912_;
}
else
{
goto v___jp_3935_;
}
}
else
{
goto v___jp_3935_;
}
}
v___jp_3948_:
{
uint32_t v___x_3950_; uint8_t v___x_3951_; 
v___x_3950_ = 97;
v___x_3951_ = lean_uint32_dec_le(v___x_3950_, v___y_3949_);
if (v___x_3951_ == 0)
{
v___y_3944_ = v___y_3949_;
goto v___jp_3943_;
}
else
{
uint32_t v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = 122;
v___x_3953_ = lean_uint32_dec_le(v___y_3949_, v___x_3952_);
if (v___x_3953_ == 0)
{
v___y_3944_ = v___y_3949_;
goto v___jp_3943_;
}
else
{
goto v___jp_3935_;
}
}
}
v___jp_3954_:
{
uint32_t v___x_3956_; uint8_t v___x_3957_; 
v___x_3956_ = 65;
v___x_3957_ = lean_uint32_dec_le(v___x_3956_, v___y_3955_);
if (v___x_3957_ == 0)
{
v___y_3949_ = v___y_3955_;
goto v___jp_3948_;
}
else
{
uint32_t v___x_3958_; uint8_t v___x_3959_; 
v___x_3958_ = 90;
v___x_3959_ = lean_uint32_dec_le(v___y_3955_, v___x_3958_);
if (v___x_3959_ == 0)
{
v___y_3949_ = v___y_3955_;
goto v___jp_3948_;
}
else
{
goto v___jp_3935_;
}
}
}
v___jp_3960_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = lean_string_utf8_byte_size(v___x_3902_);
lean_inc_ref(v___x_3902_);
v___x_3962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3902_);
lean_ctor_set(v___x_3962_, 1, v___x_3880_);
lean_ctor_set(v___x_3962_, 2, v___x_3961_);
v___x_3963_ = l_String_Slice_Pos_get_x3f(v___x_3962_, v___x_3880_);
lean_dec_ref_known(v___x_3962_, 3);
if (lean_obj_tag(v___x_3963_) == 0)
{
uint32_t v___x_3964_; 
v___x_3964_ = 65;
v___y_3955_ = v___x_3964_;
goto v___jp_3954_;
}
else
{
lean_object* v_val_3965_; uint32_t v___x_3966_; 
v_val_3965_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_val_3965_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3966_ = lean_unbox_uint32(v_val_3965_);
lean_dec(v_val_3965_);
v___y_3955_ = v___x_3966_;
goto v___jp_3954_;
}
}
v___jp_3967_:
{
uint8_t v___x_3968_; 
v___x_3968_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3902_, v___x_3898_);
if (v___x_3968_ == 0)
{
goto v___jp_3960_;
}
else
{
lean_object* v___x_3969_; 
lean_inc_ref(v___x_3902_);
v___x_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3902_);
v___y_3904_ = v___x_3969_;
goto v___jp_3903_;
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_del_object(v___x_3888_);
lean_dec(v_a_3885_);
v_a_3990_ = lean_ctor_get(v___x_3899_, 0);
v_a_3991_ = lean_ctor_get(v___x_3899_, 1);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3899_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_inc(v_a_3990_);
lean_dec(v___x_3899_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3990_);
lean_ctor_set(v_reuseFailAlloc_3997_, 1, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
v___jp_3890_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3894_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_3885_, v___y_3891_, v___y_3893_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 1, v___y_3892_);
lean_ctor_set(v___x_3888_, 0, v___x_3894_);
v___x_3896_ = v___x_3888_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v___y_3892_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
return v___x_3884_;
}
}
else
{
lean_object* v_a_4000_; lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4000_ = lean_ctor_get(v___x_3881_, 0);
v_a_4001_ = lean_ctor_get(v___x_3881_, 1);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3881_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_inc(v_a_4000_);
lean_dec(v___x_3881_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4000_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object* v_stx_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_Fmt_fmtPostfixOperator(v_stx_4009_, v_a_4010_, v_a_4011_);
lean_dec_ref(v_a_4010_);
lean_dec(v_stx_4009_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t v_sz_4013_, size_t v_i_4014_, lean_object* v_bs_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
uint8_t v___x_4018_; 
v___x_4018_ = lean_usize_dec_lt(v_i_4014_, v_sz_4013_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4019_, 0, v_bs_4015_);
lean_ctor_set(v___x_4019_, 1, v___y_4017_);
return v___x_4019_;
}
else
{
lean_object* v_v_4020_; lean_object* v_elseTk_4021_; lean_object* v_ifTk_4022_; lean_object* v_cond_4023_; lean_object* v_thenTk_4024_; lean_object* v_body_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4086_; 
v_v_4020_ = lean_array_uget(v_bs_4015_, v_i_4014_);
v_elseTk_4021_ = lean_ctor_get(v_v_4020_, 0);
v_ifTk_4022_ = lean_ctor_get(v_v_4020_, 1);
v_cond_4023_ = lean_ctor_get(v_v_4020_, 2);
v_thenTk_4024_ = lean_ctor_get(v_v_4020_, 3);
v_body_4025_ = lean_ctor_get(v_v_4020_, 4);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_v_4020_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4027_ = v_v_4020_;
v_isShared_4028_ = v_isSharedCheck_4086_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_body_4025_);
lean_inc(v_thenTk_4024_);
lean_inc(v_cond_4023_);
lean_inc(v_ifTk_4022_);
lean_inc(v_elseTk_4021_);
lean_dec(v_v_4020_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4086_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_Fmt_fmt(v_elseTk_4021_, v___y_4016_, v___y_4017_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v_a_4031_; lean_object* v___x_4032_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
v_a_4031_ = lean_ctor_get(v___x_4029_, 1);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4029_, 2);
v___x_4032_ = l_Lean_Fmt_fmt(v_ifTk_4022_, v___y_4016_, v_a_4031_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v_a_4034_; lean_object* v___x_4035_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
v_a_4034_ = lean_ctor_get(v___x_4032_, 1);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4032_, 2);
v___x_4035_ = l_Lean_Fmt_fmt(v_thenTk_4024_, v___y_4016_, v_a_4034_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_a_4037_; lean_object* v___x_4038_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
v_a_4037_ = lean_ctor_get(v___x_4035_, 1);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4035_, 2);
v___x_4038_ = l_Lean_Fmt_fmt(v_body_4025_, v___y_4016_, v_a_4037_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v_a_4040_; lean_object* v___x_4041_; lean_object* v_bs_x27_4042_; lean_object* v___x_4044_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
v_a_4040_ = lean_ctor_get(v___x_4038_, 1);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4038_, 2);
v___x_4041_ = lean_unsigned_to_nat(0u);
v_bs_x27_4042_ = lean_array_uset(v_bs_4015_, v_i_4014_, v___x_4041_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 4, v_a_4039_);
lean_ctor_set(v___x_4027_, 3, v_a_4036_);
lean_ctor_set(v___x_4027_, 1, v_a_4033_);
lean_ctor_set(v___x_4027_, 0, v_a_4030_);
v___x_4044_ = v___x_4027_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4030_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_a_4033_);
lean_ctor_set(v_reuseFailAlloc_4049_, 2, v_cond_4023_);
lean_ctor_set(v_reuseFailAlloc_4049_, 3, v_a_4036_);
lean_ctor_set(v_reuseFailAlloc_4049_, 4, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
size_t v___x_4045_; size_t v___x_4046_; lean_object* v___x_4047_; 
v___x_4045_ = ((size_t)1ULL);
v___x_4046_ = lean_usize_add(v_i_4014_, v___x_4045_);
v___x_4047_ = lean_array_uset(v_bs_x27_4042_, v_i_4014_, v___x_4044_);
v_i_4014_ = v___x_4046_;
v_bs_4015_ = v___x_4047_;
v___y_4017_ = v_a_4040_;
goto _start;
}
}
else
{
lean_object* v_a_4050_; lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_a_4036_);
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_del_object(v___x_4027_);
lean_dec_ref(v_cond_4023_);
lean_dec_ref(v_bs_4015_);
v_a_4050_ = lean_ctor_get(v___x_4038_, 0);
v_a_4051_ = lean_ctor_get(v___x_4038_, 1);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4038_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_inc(v_a_4050_);
lean_dec(v___x_4038_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4050_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_object* v_a_4059_; lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
lean_dec(v_a_4033_);
lean_dec(v_a_4030_);
lean_del_object(v___x_4027_);
lean_dec(v_body_4025_);
lean_dec_ref(v_cond_4023_);
lean_dec_ref(v_bs_4015_);
v_a_4059_ = lean_ctor_get(v___x_4035_, 0);
v_a_4060_ = lean_ctor_get(v___x_4035_, 1);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4035_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_inc(v_a_4059_);
lean_dec(v___x_4035_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4059_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
else
{
lean_object* v_a_4068_; lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v_a_4030_);
lean_del_object(v___x_4027_);
lean_dec(v_body_4025_);
lean_dec(v_thenTk_4024_);
lean_dec_ref(v_cond_4023_);
lean_dec_ref(v_bs_4015_);
v_a_4068_ = lean_ctor_get(v___x_4032_, 0);
v_a_4069_ = lean_ctor_get(v___x_4032_, 1);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4032_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_inc(v_a_4068_);
lean_dec(v___x_4032_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4068_);
lean_ctor_set(v_reuseFailAlloc_4075_, 1, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
else
{
lean_object* v_a_4077_; lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_del_object(v___x_4027_);
lean_dec(v_body_4025_);
lean_dec(v_thenTk_4024_);
lean_dec_ref(v_cond_4023_);
lean_dec(v_ifTk_4022_);
lean_dec_ref(v_bs_4015_);
v_a_4077_ = lean_ctor_get(v___x_4029_, 0);
v_a_4078_ = lean_ctor_get(v___x_4029_, 1);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4029_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_inc(v_a_4077_);
lean_dec(v___x_4029_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4077_);
lean_ctor_set(v_reuseFailAlloc_4084_, 1, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object* v_sz_4087_, lean_object* v_i_4088_, lean_object* v_bs_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
size_t v_sz_boxed_4092_; size_t v_i_boxed_4093_; lean_object* v_res_4094_; 
v_sz_boxed_4092_ = lean_unbox_usize(v_sz_4087_);
lean_dec(v_sz_4087_);
v_i_boxed_4093_ = lean_unbox_usize(v_i_4088_);
lean_dec(v_i_4088_);
v_res_4094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_boxed_4092_, v_i_boxed_4093_, v_bs_4089_, v___y_4090_, v___y_4091_);
lean_dec_ref(v___y_4090_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object* v_a_4095_, lean_object* v_x_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_a_4095_);
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
lean_ctor_set(v___x_4100_, 1, v___y_4098_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object* v_a_4101_, lean_object* v_x_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4101_, v_x_4102_, v___y_4103_, v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec_ref(v_x_4102_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object* v___x_4106_, lean_object* v_val_4107_, lean_object* v_elseIfs_4108_, lean_object* v_ifTk_4109_, lean_object* v_cond_4110_, lean_object* v_thenTk_4111_, lean_object* v_thenBody_4112_, lean_object* v_a_4113_, lean_object* v_____r_4114_, lean_object* v_elseBody_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
lean_inc(v_elseBody_4115_);
v___x_4118_ = l_Lean_Syntax_getKind(v_elseBody_4115_);
v___x_4119_ = l_Lean_Fmt_getConditionalFormatter_x3f(v___x_4106_, v___x_4118_);
lean_dec(v___x_4118_);
if (lean_obj_tag(v___x_4119_) == 1)
{
lean_object* v_val_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4180_; 
v_val_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4180_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_val_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4180_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4124_; 
lean_inc_ref(v___y_4116_);
v___x_4124_ = lean_apply_3(v_val_4120_, v_elseBody_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
if (lean_obj_tag(v_a_4125_) == 1)
{
lean_object* v_val_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4158_; 
lean_del_object(v___x_4122_);
lean_dec_ref(v_a_4113_);
v_val_4126_ = lean_ctor_get(v_a_4125_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v_a_4125_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4128_ = v_a_4125_;
v_isShared_4129_ = v_isSharedCheck_4158_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_val_4126_);
lean_dec(v_a_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4158_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4156_; 
v_a_4130_ = lean_ctor_get(v___x_4124_, 1);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v___x_4124_, 0);
lean_dec(v_unused_4157_);
v___x_4132_ = v___x_4124_;
v_isShared_4133_ = v_isSharedCheck_4156_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4124_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4156_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v_ifTk_4134_; lean_object* v_cond_4135_; lean_object* v_thenTk_4136_; lean_object* v_thenBody_4137_; lean_object* v_elseTk_x3f_4138_; lean_object* v_elseBody_x3f_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4154_; 
v_ifTk_4134_ = lean_ctor_get(v_val_4126_, 0);
v_cond_4135_ = lean_ctor_get(v_val_4126_, 1);
v_thenTk_4136_ = lean_ctor_get(v_val_4126_, 2);
v_thenBody_4137_ = lean_ctor_get(v_val_4126_, 3);
v_elseTk_x3f_4138_ = lean_ctor_get(v_val_4126_, 5);
v_elseBody_x3f_4139_ = lean_ctor_get(v_val_4126_, 6);
v_isSharedCheck_4154_ = !lean_is_exclusive(v_val_4126_);
if (v_isSharedCheck_4154_ == 0)
{
lean_object* v_unused_4155_; 
v_unused_4155_ = lean_ctor_get(v_val_4126_, 4);
lean_dec(v_unused_4155_);
v___x_4141_ = v_val_4126_;
v_isShared_4142_ = v_isSharedCheck_4154_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_elseBody_x3f_4139_);
lean_inc(v_elseTk_x3f_4138_);
lean_inc(v_thenBody_4137_);
lean_inc(v_thenTk_4136_);
lean_inc(v_cond_4135_);
lean_inc(v_ifTk_4134_);
lean_dec(v_val_4126_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4154_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4143_, 0, v_val_4107_);
lean_ctor_set(v___x_4143_, 1, v_ifTk_4134_);
lean_ctor_set(v___x_4143_, 2, v_cond_4135_);
lean_ctor_set(v___x_4143_, 3, v_thenTk_4136_);
lean_ctor_set(v___x_4143_, 4, v_thenBody_4137_);
v___x_4144_ = lean_array_push(v_elseIfs_4108_, v___x_4143_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 4, v___x_4144_);
lean_ctor_set(v___x_4141_, 3, v_thenBody_4112_);
lean_ctor_set(v___x_4141_, 2, v_thenTk_4111_);
lean_ctor_set(v___x_4141_, 1, v_cond_4110_);
lean_ctor_set(v___x_4141_, 0, v_ifTk_4109_);
v___x_4146_ = v___x_4141_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_ifTk_4109_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_cond_4110_);
lean_ctor_set(v_reuseFailAlloc_4153_, 2, v_thenTk_4111_);
lean_ctor_set(v_reuseFailAlloc_4153_, 3, v_thenBody_4112_);
lean_ctor_set(v_reuseFailAlloc_4153_, 4, v___x_4144_);
lean_ctor_set(v_reuseFailAlloc_4153_, 5, v_elseTk_x3f_4138_);
lean_ctor_set(v_reuseFailAlloc_4153_, 6, v_elseBody_x3f_4139_);
v___x_4146_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
lean_object* v___x_4148_; 
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4146_);
v___x_4148_ = v___x_4128_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
lean_object* v___x_4150_; 
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 0, v___x_4148_);
v___x_4150_ = v___x_4132_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_4148_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v_a_4130_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_a_4125_);
lean_dec(v_thenBody_4112_);
lean_dec(v_thenTk_4111_);
lean_dec_ref(v_cond_4110_);
lean_dec(v_ifTk_4109_);
lean_dec_ref(v_elseIfs_4108_);
lean_dec(v_val_4107_);
v_a_4159_ = lean_ctor_get(v___x_4124_, 1);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4169_ == 0)
{
lean_object* v_unused_4170_; 
v_unused_4170_ = lean_ctor_get(v___x_4124_, 0);
lean_dec(v_unused_4170_);
v___x_4161_ = v___x_4124_;
v_isShared_4162_ = v_isSharedCheck_4169_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4124_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4169_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4123_ == 0)
{
lean_ctor_set_tag(v___x_4122_, 0);
lean_ctor_set(v___x_4122_, 0, v_a_4113_);
v___x_4164_ = v___x_4122_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4113_);
v___x_4164_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4166_; 
if (v_isShared_4162_ == 0)
{
lean_ctor_set(v___x_4161_, 0, v___x_4164_);
v___x_4166_ = v___x_4161_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_a_4159_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
}
else
{
lean_object* v_a_4171_; lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_del_object(v___x_4122_);
lean_dec_ref(v_a_4113_);
lean_dec(v_thenBody_4112_);
lean_dec(v_thenTk_4111_);
lean_dec_ref(v_cond_4110_);
lean_dec(v_ifTk_4109_);
lean_dec_ref(v_elseIfs_4108_);
lean_dec(v_val_4107_);
v_a_4171_ = lean_ctor_get(v___x_4124_, 0);
v_a_4172_ = lean_ctor_get(v___x_4124_, 1);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4124_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_inc(v_a_4171_);
lean_dec(v___x_4124_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4171_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
else
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_dec(v___x_4119_);
lean_dec(v_elseBody_4115_);
lean_dec(v_thenBody_4112_);
lean_dec(v_thenTk_4111_);
lean_dec_ref(v_cond_4110_);
lean_dec(v_ifTk_4109_);
lean_dec_ref(v_elseIfs_4108_);
lean_dec(v_val_4107_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v_a_4113_);
v___x_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
lean_ctor_set(v___x_4182_, 1, v___y_4117_);
return v___x_4182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object* v___x_4183_, lean_object* v_val_4184_, lean_object* v_elseIfs_4185_, lean_object* v_ifTk_4186_, lean_object* v_cond_4187_, lean_object* v_thenTk_4188_, lean_object* v_thenBody_4189_, lean_object* v_a_4190_, lean_object* v_____r_4191_, lean_object* v_elseBody_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4183_, v_val_4184_, v_elseIfs_4185_, v_ifTk_4186_, v_cond_4187_, v_thenTk_4188_, v_thenBody_4189_, v_a_4190_, v_____r_4191_, v_elseBody_4192_, v___y_4193_, v___y_4194_);
lean_dec_ref(v___y_4193_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object* v___x_4210_, lean_object* v_a_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
lean_object* v___y_4215_; lean_object* v_elseTk_x3f_4239_; 
v_elseTk_x3f_4239_ = lean_ctor_get(v_a_4211_, 5);
if (lean_obj_tag(v_elseTk_x3f_4239_) == 1)
{
lean_object* v_elseBody_x3f_4240_; 
v_elseBody_x3f_4240_ = lean_ctor_get(v_a_4211_, 6);
if (lean_obj_tag(v_elseBody_x3f_4240_) == 1)
{
lean_object* v_ifTk_4241_; lean_object* v_cond_4242_; lean_object* v_thenTk_4243_; lean_object* v_thenBody_4244_; lean_object* v_elseIfs_4245_; lean_object* v_val_4246_; lean_object* v_val_4247_; lean_object* v___x_4248_; uint8_t v___x_4249_; 
v_ifTk_4241_ = lean_ctor_get(v_a_4211_, 0);
lean_inc(v_ifTk_4241_);
v_cond_4242_ = lean_ctor_get(v_a_4211_, 1);
lean_inc_ref(v_cond_4242_);
v_thenTk_4243_ = lean_ctor_get(v_a_4211_, 2);
lean_inc(v_thenTk_4243_);
v_thenBody_4244_ = lean_ctor_get(v_a_4211_, 3);
lean_inc(v_thenBody_4244_);
v_elseIfs_4245_ = lean_ctor_get(v_a_4211_, 4);
lean_inc_ref(v_elseIfs_4245_);
v_val_4246_ = lean_ctor_get(v_elseTk_x3f_4239_, 0);
lean_inc(v_val_4246_);
v_val_4247_ = lean_ctor_get(v_elseBody_x3f_4240_, 0);
v___x_4248_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3));
lean_inc(v_val_4247_);
v___x_4249_ = l_Lean_Syntax_isOfKind(v_val_4247_, v___x_4248_);
if (v___x_4249_ == 0)
{
lean_object* v___x_4250_; lean_object* v___x_4251_; 
lean_inc(v_val_4247_);
v___x_4250_ = lean_box(0);
lean_inc_ref(v___x_4210_);
v___x_4251_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4210_, v_val_4246_, v_elseIfs_4245_, v_ifTk_4241_, v_cond_4242_, v_thenTk_4243_, v_thenBody_4244_, v_a_4211_, v___x_4250_, v_val_4247_, v___y_4212_, v___y_4213_);
v___y_4215_ = v___x_4251_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = l_Lean_Syntax_getArg(v_val_4247_, v___x_4252_);
v___x_4254_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5));
lean_inc(v___x_4253_);
v___x_4255_ = l_Lean_Syntax_isOfKind(v___x_4253_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_inc(v_val_4247_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
lean_inc_ref(v___x_4210_);
v___x_4257_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4210_, v_val_4246_, v_elseIfs_4245_, v_ifTk_4241_, v_cond_4242_, v_thenTk_4243_, v_thenBody_4244_, v_a_4211_, v___x_4256_, v_val_4247_, v___y_4212_, v___y_4213_);
v___y_4215_ = v___x_4257_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; 
v___x_4258_ = l_Lean_Syntax_getArg(v___x_4253_, v___x_4252_);
lean_dec(v___x_4253_);
v___x_4259_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4258_);
v___x_4260_ = l_Lean_Syntax_matchesNull(v___x_4258_, v___x_4259_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_inc(v_val_4247_);
lean_dec(v___x_4258_);
v___x_4261_ = lean_box(0);
lean_inc_ref(v___x_4210_);
v___x_4262_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4210_, v_val_4246_, v_elseIfs_4245_, v_ifTk_4241_, v_cond_4242_, v_thenTk_4243_, v_thenBody_4244_, v_a_4211_, v___x_4261_, v_val_4247_, v___y_4212_, v___y_4213_);
v___y_4215_ = v___x_4262_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = l_Lean_Syntax_getArg(v___x_4258_, v___x_4252_);
lean_dec(v___x_4258_);
v___x_4264_ = lean_box(0);
lean_inc_ref(v___x_4210_);
v___x_4265_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4210_, v_val_4246_, v_elseIfs_4245_, v_ifTk_4241_, v_cond_4242_, v_thenTk_4243_, v_thenBody_4244_, v_a_4211_, v___x_4264_, v___x_4263_, v___y_4212_, v___y_4213_);
v___y_4215_ = v___x_4265_;
goto v___jp_4214_;
}
}
}
}
else
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_inc(v_elseBody_x3f_4240_);
lean_inc_ref(v_elseTk_x3f_4239_);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v_elseTk_x3f_4239_);
lean_ctor_set(v___x_4266_, 1, v_elseBody_x3f_4240_);
v___x_4267_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4211_, v___x_4266_, v___y_4212_, v___y_4213_);
lean_dec_ref_known(v___x_4266_, 2);
v___y_4215_ = v___x_4267_;
goto v___jp_4214_;
}
}
else
{
lean_object* v_elseBody_x3f_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v_elseBody_x3f_4268_ = lean_ctor_get(v_a_4211_, 6);
lean_inc(v_elseBody_x3f_4268_);
lean_inc(v_elseTk_x3f_4239_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v_elseTk_x3f_4239_);
lean_ctor_set(v___x_4269_, 1, v_elseBody_x3f_4268_);
v___x_4270_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4211_, v___x_4269_, v___y_4212_, v___y_4213_);
lean_dec_ref_known(v___x_4269_, 2);
v___y_4215_ = v___x_4270_;
goto v___jp_4214_;
}
v___jp_4214_:
{
if (lean_obj_tag(v___y_4215_) == 0)
{
lean_object* v_a_4216_; 
v_a_4216_ = lean_ctor_get(v___y_4215_, 0);
lean_inc(v_a_4216_);
if (lean_obj_tag(v_a_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4225_; 
lean_dec_ref(v___x_4210_);
v_a_4217_ = lean_ctor_get(v___y_4215_, 1);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___y_4215_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; 
v_unused_4226_ = lean_ctor_get(v___y_4215_, 0);
lean_dec(v_unused_4226_);
v___x_4219_ = v___y_4215_;
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___y_4215_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4225_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v_a_4221_; lean_object* v___x_4223_; 
v_a_4221_ = lean_ctor_get(v_a_4216_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v_a_4216_, 1);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v_a_4221_);
v___x_4223_ = v___x_4219_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4221_);
lean_ctor_set(v_reuseFailAlloc_4224_, 1, v_a_4217_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v_a_4228_; 
v_a_4227_ = lean_ctor_get(v___y_4215_, 1);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___y_4215_, 2);
v_a_4228_ = lean_ctor_get(v_a_4216_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v_a_4216_, 1);
v_a_4211_ = v_a_4228_;
v___y_4213_ = v_a_4227_;
goto _start;
}
}
else
{
lean_object* v_a_4230_; lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec_ref(v___x_4210_);
v_a_4230_ = lean_ctor_get(v___y_4215_, 0);
v_a_4231_ = lean_ctor_get(v___y_4215_, 1);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___y_4215_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___y_4215_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_inc(v_a_4230_);
lean_dec(v___y_4215_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4230_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object* v___x_4271_, lean_object* v_a_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4271_, v_a_4272_, v___y_4273_, v___y_4274_);
lean_dec_ref(v___y_4273_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object* v_initialFmt_4276_, lean_object* v_stx_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; uint8_t v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; uint8_t v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v_env_4307_; lean_object* v___x_4308_; 
v_env_4307_ = lean_ctor_get(v_a_4278_, 0);
lean_inc_ref(v_a_4278_);
lean_inc(v_stx_4277_);
v___x_4308_ = lean_apply_3(v_initialFmt_4276_, v_stx_4277_, v_a_4278_, v_a_4279_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
if (lean_obj_tag(v_a_4309_) == 1)
{
lean_object* v_a_4310_; lean_object* v_val_4311_; lean_object* v___x_4312_; 
v_a_4310_ = lean_ctor_get(v___x_4308_, 1);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4308_, 2);
v_val_4311_ = lean_ctor_get(v_a_4309_, 0);
lean_inc(v_val_4311_);
lean_dec_ref_known(v_a_4309_, 1);
v___x_4312_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_4277_, v_a_4278_, v_a_4310_);
lean_dec(v_stx_4277_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v_a_4314_; uint8_t v___y_4316_; uint8_t v___x_4366_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
v_a_4314_ = lean_ctor_get(v___x_4312_, 1);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4312_, 2);
v___x_4366_ = lean_unbox(v_a_4313_);
lean_dec(v_a_4313_);
if (v___x_4366_ == 0)
{
uint8_t v___x_4367_; 
v___x_4367_ = 1;
v___y_4316_ = v___x_4367_;
goto v___jp_4315_;
}
else
{
uint8_t v___x_4368_; 
v___x_4368_ = 0;
v___y_4316_ = v___x_4368_;
goto v___jp_4315_;
}
v___jp_4315_:
{
lean_object* v___x_4317_; 
lean_inc_ref(v_env_4307_);
v___x_4317_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v_env_4307_, v_val_4311_, v_a_4278_, v_a_4314_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v_a_4319_; lean_object* v_ifTk_4320_; lean_object* v_cond_4321_; lean_object* v_thenTk_4322_; lean_object* v_thenBody_4323_; lean_object* v_elseIfs_4324_; lean_object* v_elseTk_x3f_4325_; lean_object* v_elseBody_x3f_4326_; lean_object* v___x_4327_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
v_a_4319_ = lean_ctor_get(v___x_4317_, 1);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___x_4317_, 2);
v_ifTk_4320_ = lean_ctor_get(v_a_4318_, 0);
lean_inc(v_ifTk_4320_);
v_cond_4321_ = lean_ctor_get(v_a_4318_, 1);
lean_inc_ref(v_cond_4321_);
v_thenTk_4322_ = lean_ctor_get(v_a_4318_, 2);
lean_inc(v_thenTk_4322_);
v_thenBody_4323_ = lean_ctor_get(v_a_4318_, 3);
lean_inc(v_thenBody_4323_);
v_elseIfs_4324_ = lean_ctor_get(v_a_4318_, 4);
lean_inc_ref(v_elseIfs_4324_);
v_elseTk_x3f_4325_ = lean_ctor_get(v_a_4318_, 5);
lean_inc(v_elseTk_x3f_4325_);
v_elseBody_x3f_4326_ = lean_ctor_get(v_a_4318_, 6);
lean_inc(v_elseBody_x3f_4326_);
lean_dec(v_a_4318_);
v___x_4327_ = l_Lean_Fmt_fmt(v_ifTk_4320_, v_a_4278_, v_a_4319_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v_a_4329_; lean_object* v___x_4330_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
v_a_4329_ = lean_ctor_get(v___x_4327_, 1);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4327_, 2);
v___x_4330_ = l_Lean_Fmt_fmt(v_thenTk_4322_, v_a_4278_, v_a_4329_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v_a_4332_; lean_object* v___x_4333_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
v_a_4332_ = lean_ctor_get(v___x_4330_, 1);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4330_, 2);
v___x_4333_ = l_Lean_Fmt_fmt(v_thenBody_4323_, v_a_4278_, v_a_4332_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v_a_4335_; size_t v_sz_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
v_a_4335_ = lean_ctor_get(v___x_4333_, 1);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4333_, 2);
v_sz_4336_ = lean_array_size(v_elseIfs_4324_);
v___x_4337_ = ((size_t)0ULL);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_4336_, v___x_4337_, v_elseIfs_4324_, v_a_4278_, v_a_4335_);
if (lean_obj_tag(v___x_4338_) == 0)
{
if (lean_obj_tag(v_elseTk_x3f_4325_) == 0)
{
lean_object* v_a_4339_; lean_object* v_a_4340_; lean_object* v___x_4341_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4339_);
v_a_4340_ = lean_ctor_get(v___x_4338_, 1);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4338_, 2);
v___x_4341_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4293_ = v_elseBody_x3f_4326_;
v___y_4294_ = v_a_4339_;
v___y_4295_ = v_a_4328_;
v___y_4296_ = v_a_4334_;
v___y_4297_ = v_a_4340_;
v___y_4298_ = v_a_4331_;
v___y_4299_ = v___y_4316_;
v___y_4300_ = v_cond_4321_;
v___y_4301_ = v___x_4341_;
goto v___jp_4292_;
}
else
{
lean_object* v_a_4342_; lean_object* v_a_4343_; lean_object* v_val_4344_; lean_object* v___x_4345_; 
v_a_4342_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_a_4342_);
v_a_4343_ = lean_ctor_get(v___x_4338_, 1);
lean_inc(v_a_4343_);
lean_dec_ref_known(v___x_4338_, 2);
v_val_4344_ = lean_ctor_get(v_elseTk_x3f_4325_, 0);
lean_inc(v_val_4344_);
lean_dec_ref_known(v_elseTk_x3f_4325_, 1);
v___x_4345_ = l_Lean_Fmt_fmt(v_val_4344_, v_a_4278_, v_a_4343_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; lean_object* v_a_4347_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4346_);
v_a_4347_ = lean_ctor_get(v___x_4345_, 1);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4345_, 2);
v___y_4293_ = v_elseBody_x3f_4326_;
v___y_4294_ = v_a_4342_;
v___y_4295_ = v_a_4328_;
v___y_4296_ = v_a_4334_;
v___y_4297_ = v_a_4347_;
v___y_4298_ = v_a_4331_;
v___y_4299_ = v___y_4316_;
v___y_4300_ = v_cond_4321_;
v___y_4301_ = v_a_4346_;
goto v___jp_4292_;
}
else
{
lean_dec(v_a_4342_);
lean_dec(v_a_4334_);
lean_dec(v_a_4331_);
lean_dec(v_a_4328_);
lean_dec(v_elseBody_x3f_4326_);
lean_dec_ref(v_cond_4321_);
return v___x_4345_;
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec(v_a_4334_);
lean_dec(v_a_4331_);
lean_dec(v_a_4328_);
lean_dec(v_elseBody_x3f_4326_);
lean_dec(v_elseTk_x3f_4325_);
lean_dec_ref(v_cond_4321_);
v_a_4348_ = lean_ctor_get(v___x_4338_, 0);
v_a_4349_ = lean_ctor_get(v___x_4338_, 1);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4338_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_inc(v_a_4348_);
lean_dec(v___x_4338_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4348_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
else
{
lean_dec(v_a_4331_);
lean_dec(v_a_4328_);
lean_dec(v_elseBody_x3f_4326_);
lean_dec(v_elseTk_x3f_4325_);
lean_dec_ref(v_elseIfs_4324_);
lean_dec_ref(v_cond_4321_);
return v___x_4333_;
}
}
else
{
lean_dec(v_a_4328_);
lean_dec(v_elseBody_x3f_4326_);
lean_dec(v_elseTk_x3f_4325_);
lean_dec_ref(v_elseIfs_4324_);
lean_dec(v_thenBody_4323_);
lean_dec_ref(v_cond_4321_);
return v___x_4330_;
}
}
else
{
lean_dec(v_elseBody_x3f_4326_);
lean_dec(v_elseTk_x3f_4325_);
lean_dec_ref(v_elseIfs_4324_);
lean_dec(v_thenBody_4323_);
lean_dec(v_thenTk_4322_);
lean_dec_ref(v_cond_4321_);
return v___x_4327_;
}
}
else
{
lean_object* v_a_4357_; lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
v_a_4357_ = lean_ctor_get(v___x_4317_, 0);
v_a_4358_ = lean_ctor_get(v___x_4317_, 1);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4317_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_inc(v_a_4357_);
lean_dec(v___x_4317_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4357_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
else
{
lean_object* v_a_4369_; lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_dec(v_val_4311_);
v_a_4369_ = lean_ctor_get(v___x_4312_, 0);
v_a_4370_ = lean_ctor_get(v___x_4312_, 1);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4312_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_inc(v_a_4369_);
lean_dec(v___x_4312_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4369_);
lean_ctor_set(v_reuseFailAlloc_4376_, 1, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_a_4309_);
lean_dec(v_stx_4277_);
v_a_4378_ = lean_ctor_get(v___x_4308_, 1);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4386_ == 0)
{
lean_object* v_unused_4387_; 
v_unused_4387_ = lean_ctor_get(v___x_4308_, 0);
lean_dec(v_unused_4387_);
v___x_4380_ = v___x_4308_;
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4308_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4386_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4382_; lean_object* v___x_4384_; 
v___x_4382_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4381_ == 0)
{
lean_ctor_set_tag(v___x_4380_, 1);
lean_ctor_set(v___x_4380_, 0, v___x_4382_);
v___x_4384_ = v___x_4380_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4382_);
lean_ctor_set(v_reuseFailAlloc_4385_, 1, v_a_4378_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec(v_stx_4277_);
v_a_4388_ = lean_ctor_get(v___x_4308_, 0);
v_a_4389_ = lean_ctor_get(v___x_4308_, 1);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4308_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_inc(v_a_4388_);
lean_dec(v___x_4308_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4388_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
v___jp_4280_:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4290_ = l_Lean_Fmt_Layouts_conditional(v___y_4284_, v___y_4288_, v___y_4286_, v___y_4285_, v___y_4283_, v___y_4282_, v___y_4289_, v___y_4287_);
lean_dec_ref(v___y_4283_);
v___x_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
lean_ctor_set(v___x_4291_, 1, v___y_4281_);
return v___x_4291_;
}
v___jp_4292_:
{
if (lean_obj_tag(v___y_4293_) == 0)
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4281_ = v___y_4297_;
v___y_4282_ = v___y_4301_;
v___y_4283_ = v___y_4294_;
v___y_4284_ = v___y_4295_;
v___y_4285_ = v___y_4296_;
v___y_4286_ = v___y_4298_;
v___y_4287_ = v___y_4299_;
v___y_4288_ = v___y_4300_;
v___y_4289_ = v___x_4302_;
goto v___jp_4280_;
}
else
{
lean_object* v_val_4303_; lean_object* v___x_4304_; 
v_val_4303_ = lean_ctor_get(v___y_4293_, 0);
lean_inc(v_val_4303_);
lean_dec_ref_known(v___y_4293_, 1);
v___x_4304_ = l_Lean_Fmt_fmt(v_val_4303_, v_a_4278_, v___y_4297_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v_a_4306_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4305_);
v_a_4306_ = lean_ctor_get(v___x_4304_, 1);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4304_, 2);
v___y_4281_ = v_a_4306_;
v___y_4282_ = v___y_4301_;
v___y_4283_ = v___y_4294_;
v___y_4284_ = v___y_4295_;
v___y_4285_ = v___y_4296_;
v___y_4286_ = v___y_4298_;
v___y_4287_ = v___y_4299_;
v___y_4288_ = v___y_4300_;
v___y_4289_ = v_a_4305_;
goto v___jp_4280_;
}
else
{
lean_dec_ref(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec_ref(v___y_4294_);
return v___x_4304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object* v_initialFmt_4397_, lean_object* v_stx_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_Fmt_fmtConditional(v_initialFmt_4397_, v_stx_4398_, v_a_4399_, v_a_4400_);
lean_dec_ref(v_a_4399_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object* v___x_4402_, lean_object* v_inst_4403_, lean_object* v_a_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4402_, v_a_4404_, v___y_4405_, v___y_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object* v___x_4408_, lean_object* v_inst_4409_, lean_object* v_a_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(v___x_4408_, v_inst_4409_, v_a_4410_, v___y_4411_, v___y_4412_);
lean_dec_ref(v___y_4411_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t v_sz_4414_, size_t v_i_4415_, lean_object* v_bs_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_){
_start:
{
uint8_t v___x_4419_; 
v___x_4419_ = lean_usize_dec_lt(v_i_4415_, v_sz_4414_);
if (v___x_4419_ == 0)
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4420_, 0, v_bs_4416_);
lean_ctor_set(v___x_4420_, 1, v___y_4418_);
return v___x_4420_;
}
else
{
lean_object* v_v_4421_; size_t v_sz_4422_; size_t v___x_4423_; lean_object* v___x_4424_; 
v_v_4421_ = lean_array_uget_borrowed(v_bs_4416_, v_i_4415_);
v_sz_4422_ = lean_array_size(v_v_4421_);
v___x_4423_ = ((size_t)0ULL);
lean_inc(v_v_4421_);
v___x_4424_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_4422_, v___x_4423_, v_v_4421_, v___y_4417_, v___y_4418_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v_a_4426_; lean_object* v___x_4427_; lean_object* v_bs_x27_4428_; size_t v___x_4429_; size_t v___x_4430_; lean_object* v___x_4431_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
v_a_4426_ = lean_ctor_get(v___x_4424_, 1);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4424_, 2);
v___x_4427_ = lean_unsigned_to_nat(0u);
v_bs_x27_4428_ = lean_array_uset(v_bs_4416_, v_i_4415_, v___x_4427_);
v___x_4429_ = ((size_t)1ULL);
v___x_4430_ = lean_usize_add(v_i_4415_, v___x_4429_);
v___x_4431_ = lean_array_uset(v_bs_x27_4428_, v_i_4415_, v_a_4425_);
v_i_4415_ = v___x_4430_;
v_bs_4416_ = v___x_4431_;
v___y_4418_ = v_a_4426_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4416_);
return v___x_4424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object* v_sz_4433_, lean_object* v_i_4434_, lean_object* v_bs_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
size_t v_sz_boxed_4438_; size_t v_i_boxed_4439_; lean_object* v_res_4440_; 
v_sz_boxed_4438_ = lean_unbox_usize(v_sz_4433_);
lean_dec(v_sz_4433_);
v_i_boxed_4439_ = lean_unbox_usize(v_i_4434_);
lean_dec(v_i_4434_);
v_res_4440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_boxed_4438_, v_i_boxed_4439_, v_bs_4435_, v___y_4436_, v___y_4437_);
lean_dec_ref(v___y_4436_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(size_t v_sz_4441_, size_t v_i_4442_, lean_object* v_bs_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_){
_start:
{
uint8_t v___x_4446_; 
v___x_4446_ = lean_usize_dec_lt(v_i_4442_, v_sz_4441_);
if (v___x_4446_ == 0)
{
lean_object* v___x_4447_; 
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v_bs_4443_);
lean_ctor_set(v___x_4447_, 1, v___y_4445_);
return v___x_4447_;
}
else
{
lean_object* v_v_4448_; size_t v_sz_4449_; size_t v___x_4450_; lean_object* v___x_4451_; 
v_v_4448_ = lean_array_uget_borrowed(v_bs_4443_, v_i_4442_);
v_sz_4449_ = lean_array_size(v_v_4448_);
v___x_4450_ = ((size_t)0ULL);
lean_inc(v_v_4448_);
v___x_4451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_4449_, v___x_4450_, v_v_4448_, v___y_4444_, v___y_4445_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v_a_4453_; lean_object* v___x_4454_; lean_object* v_bs_x27_4455_; size_t v___x_4456_; size_t v___x_4457_; lean_object* v___x_4458_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
v_a_4453_ = lean_ctor_get(v___x_4451_, 1);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4451_, 2);
v___x_4454_ = lean_unsigned_to_nat(0u);
v_bs_x27_4455_ = lean_array_uset(v_bs_4443_, v_i_4442_, v___x_4454_);
v___x_4456_ = ((size_t)1ULL);
v___x_4457_ = lean_usize_add(v_i_4442_, v___x_4456_);
v___x_4458_ = lean_array_uset(v_bs_x27_4455_, v_i_4442_, v_a_4452_);
v_i_4442_ = v___x_4457_;
v_bs_4443_ = v___x_4458_;
v___y_4445_ = v_a_4453_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4443_);
return v___x_4451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1___boxed(lean_object* v_sz_4460_, lean_object* v_i_4461_, lean_object* v_bs_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
size_t v_sz_boxed_4465_; size_t v_i_boxed_4466_; lean_object* v_res_4467_; 
v_sz_boxed_4465_ = lean_unbox_usize(v_sz_4460_);
lean_dec(v_sz_4460_);
v_i_boxed_4466_ = lean_unbox_usize(v_i_4461_);
lean_dec(v_i_4461_);
v_res_4467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_boxed_4465_, v_i_boxed_4466_, v_bs_4462_, v___y_4463_, v___y_4464_);
lean_dec_ref(v___y_4463_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object* v_bgs_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
size_t v_sz_4471_; size_t v___x_4472_; lean_object* v___x_4473_; 
v_sz_4471_ = lean_array_size(v_bgs_4468_);
v___x_4472_ = ((size_t)0ULL);
v___x_4473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_4471_, v___x_4472_, v_bgs_4468_, v_a_4469_, v_a_4470_);
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object* v_bgs_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l_Lean_Fmt_fmtBinderGroups(v_bgs_4474_, v_a_4475_, v_a_4476_);
lean_dec_ref(v_a_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object* v_lhs_4478_, lean_object* v_rhs_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_Fmt_fmt(v_lhs_4478_, v_a_4480_, v_a_4481_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v_a_4484_; lean_object* v___x_4485_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
v_a_4484_ = lean_ctor_get(v___x_4482_, 1);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4482_, 2);
v___x_4485_ = l_Lean_Fmt_fmt(v_rhs_4479_, v_a_4480_, v_a_4484_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4501_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
v_a_4487_ = lean_ctor_get(v___x_4485_, 1);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4489_ = v___x_4485_;
v_isShared_4490_ = v_isSharedCheck_4501_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_inc(v_a_4486_);
lean_dec(v___x_4485_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4501_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4499_; 
v___x_4491_ = lean_unsigned_to_nat(2u);
v___x_4492_ = lean_mk_empty_array_with_capacity(v___x_4491_);
v___x_4493_ = lean_array_push(v___x_4492_, v_a_4483_);
v___x_4494_ = lean_array_push(v___x_4493_, v_a_4486_);
v___x_4495_ = 1;
v___x_4496_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4494_, v___x_4495_);
lean_dec_ref(v___x_4494_);
v___x_4497_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4496_);
if (v_isShared_4490_ == 0)
{
lean_ctor_set(v___x_4489_, 0, v___x_4497_);
v___x_4499_ = v___x_4489_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4497_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_a_4487_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
else
{
lean_dec(v_a_4483_);
return v___x_4485_;
}
}
else
{
lean_dec(v_rhs_4479_);
return v___x_4482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object* v_lhs_4502_, lean_object* v_rhs_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4502_, v_rhs_4503_, v_a_4504_, v_a_4505_);
lean_dec_ref(v_a_4504_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object* v_head_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_){
_start:
{
lean_object* v_quantifier_4510_; lean_object* v_binders_4511_; lean_object* v_typeAscriptionTk_x3f_4512_; lean_object* v_type_x3f_4513_; lean_object* v_commaTk_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4627_; 
v_quantifier_4510_ = lean_ctor_get(v_head_4507_, 0);
v_binders_4511_ = lean_ctor_get(v_head_4507_, 1);
v_typeAscriptionTk_x3f_4512_ = lean_ctor_get(v_head_4507_, 2);
v_type_x3f_4513_ = lean_ctor_get(v_head_4507_, 3);
v_commaTk_4514_ = lean_ctor_get(v_head_4507_, 4);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_head_4507_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4516_ = v_head_4507_;
v_isShared_4517_ = v_isSharedCheck_4627_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_commaTk_4514_);
lean_inc(v_type_x3f_4513_);
lean_inc(v_typeAscriptionTk_x3f_4512_);
lean_inc(v_binders_4511_);
lean_inc(v_quantifier_4510_);
lean_dec(v_head_4507_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4627_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4518_; 
v___x_4518_ = l_Lean_Fmt_fmt(v_quantifier_4510_, v_a_4508_, v_a_4509_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v_a_4520_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v_binderGroups_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
v_a_4520_ = lean_ctor_get(v___x_4518_, 1);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4518_, 2);
if (lean_obj_tag(v_binders_4511_) == 0)
{
lean_object* v_group_4586_; lean_object* v___x_4587_; 
v_group_4586_ = lean_ctor_get(v_binders_4511_, 0);
lean_inc_ref(v_group_4586_);
lean_dec_ref_known(v_binders_4511_, 1);
v___x_4587_ = l_Lean_Fmt_fmtBinderGroups(v_group_4586_, v_a_4508_, v_a_4520_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v_a_4589_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
v_a_4589_ = lean_ctor_get(v___x_4587_, 1);
lean_inc(v_a_4589_);
lean_dec_ref_known(v___x_4587_, 2);
v_binderGroups_4569_ = v_a_4588_;
v___y_4570_ = v_a_4508_;
v___y_4571_ = v_a_4589_;
goto v___jp_4568_;
}
else
{
lean_object* v_a_4590_; lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
lean_dec(v_a_4519_);
lean_del_object(v___x_4516_);
lean_dec(v_commaTk_4514_);
lean_dec(v_type_x3f_4513_);
lean_dec(v_typeAscriptionTk_x3f_4512_);
v_a_4590_ = lean_ctor_get(v___x_4587_, 0);
v_a_4591_ = lean_ctor_get(v___x_4587_, 1);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v___x_4587_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_inc(v_a_4590_);
lean_dec(v___x_4587_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4590_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
else
{
lean_object* v_lhs_4599_; lean_object* v_rhs_4600_; lean_object* v___x_4601_; 
v_lhs_4599_ = lean_ctor_get(v_binders_4511_, 0);
lean_inc(v_lhs_4599_);
v_rhs_4600_ = lean_ctor_get(v_binders_4511_, 1);
lean_inc(v_rhs_4600_);
lean_dec_ref_known(v_binders_4511_, 2);
v___x_4601_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4599_, v_rhs_4600_, v_a_4508_, v_a_4520_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v_a_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc(v_a_4602_);
v_a_4603_ = lean_ctor_get(v___x_4601_, 1);
lean_inc(v_a_4603_);
lean_dec_ref_known(v___x_4601_, 2);
v___x_4604_ = lean_unsigned_to_nat(1u);
v___x_4605_ = lean_mk_empty_array_with_capacity(v___x_4604_);
lean_inc_ref_n(v___x_4605_, 2);
v___x_4606_ = lean_array_push(v___x_4605_, v_a_4602_);
v___x_4607_ = lean_array_push(v___x_4605_, v___x_4606_);
v___x_4608_ = lean_array_push(v___x_4605_, v___x_4607_);
v_binderGroups_4569_ = v___x_4608_;
v___y_4570_ = v_a_4508_;
v___y_4571_ = v_a_4603_;
goto v___jp_4568_;
}
else
{
lean_object* v_a_4609_; lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
lean_dec(v_a_4519_);
lean_del_object(v___x_4516_);
lean_dec(v_commaTk_4514_);
lean_dec(v_type_x3f_4513_);
lean_dec(v_typeAscriptionTk_x3f_4512_);
v_a_4609_ = lean_ctor_get(v___x_4601_, 0);
v_a_4610_ = lean_ctor_get(v___x_4601_, 1);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4601_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_inc(v_a_4609_);
lean_dec(v___x_4601_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4609_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
}
v___jp_4521_:
{
lean_object* v___x_4527_; 
v___x_4527_ = l_Lean_Fmt_fmt(v_commaTk_4514_, v___y_4524_, v___y_4523_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4539_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_a_4529_ = lean_ctor_get(v___x_4527_, 1);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4539_ == 0)
{
v___x_4531_ = v___x_4527_;
v_isShared_4532_ = v_isSharedCheck_4539_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4539_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4517_ == 0)
{
lean_ctor_set(v___x_4516_, 4, v_a_4528_);
lean_ctor_set(v___x_4516_, 3, v___y_4526_);
lean_ctor_set(v___x_4516_, 2, v___y_4522_);
lean_ctor_set(v___x_4516_, 1, v___y_4525_);
lean_ctor_set(v___x_4516_, 0, v_a_4519_);
v___x_4534_ = v___x_4516_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4538_; 
v_reuseFailAlloc_4538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4538_, 0, v_a_4519_);
lean_ctor_set(v_reuseFailAlloc_4538_, 1, v___y_4525_);
lean_ctor_set(v_reuseFailAlloc_4538_, 2, v___y_4522_);
lean_ctor_set(v_reuseFailAlloc_4538_, 3, v___y_4526_);
lean_ctor_set(v_reuseFailAlloc_4538_, 4, v_a_4528_);
v___x_4534_ = v_reuseFailAlloc_4538_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4536_; 
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v___x_4534_);
v___x_4536_ = v___x_4531_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_a_4529_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_dec_ref(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec_ref(v___y_4522_);
lean_dec(v_a_4519_);
lean_del_object(v___x_4516_);
v_a_4540_ = lean_ctor_get(v___x_4527_, 0);
v_a_4541_ = lean_ctor_get(v___x_4527_, 1);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4527_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_inc(v_a_4540_);
lean_dec(v___x_4527_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4540_);
lean_ctor_set(v_reuseFailAlloc_4547_, 1, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
v___jp_4549_:
{
if (lean_obj_tag(v_type_x3f_4513_) == 0)
{
lean_object* v___x_4554_; 
v___x_4554_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4522_ = v___y_4553_;
v___y_4523_ = v___y_4550_;
v___y_4524_ = v___y_4551_;
v___y_4525_ = v___y_4552_;
v___y_4526_ = v___x_4554_;
goto v___jp_4521_;
}
else
{
lean_object* v_val_4555_; lean_object* v___x_4556_; 
v_val_4555_ = lean_ctor_get(v_type_x3f_4513_, 0);
lean_inc(v_val_4555_);
lean_dec_ref_known(v_type_x3f_4513_, 1);
v___x_4556_ = l_Lean_Fmt_fmt(v_val_4555_, v___y_4551_, v___y_4550_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v_a_4558_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
v_a_4558_ = lean_ctor_get(v___x_4556_, 1);
lean_inc(v_a_4558_);
lean_dec_ref_known(v___x_4556_, 2);
v___y_4522_ = v___y_4553_;
v___y_4523_ = v_a_4558_;
v___y_4524_ = v___y_4551_;
v___y_4525_ = v___y_4552_;
v___y_4526_ = v_a_4557_;
goto v___jp_4521_;
}
else
{
lean_object* v_a_4559_; lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
lean_dec_ref(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v_a_4519_);
lean_del_object(v___x_4516_);
lean_dec(v_commaTk_4514_);
v_a_4559_ = lean_ctor_get(v___x_4556_, 0);
v_a_4560_ = lean_ctor_get(v___x_4556_, 1);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4556_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_inc(v_a_4559_);
lean_dec(v___x_4556_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4559_);
lean_ctor_set(v_reuseFailAlloc_4566_, 1, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
}
v___jp_4568_:
{
if (lean_obj_tag(v_typeAscriptionTk_x3f_4512_) == 0)
{
lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4550_ = v___y_4571_;
v___y_4551_ = v___y_4570_;
v___y_4552_ = v_binderGroups_4569_;
v___y_4553_ = v___x_4572_;
goto v___jp_4549_;
}
else
{
lean_object* v_val_4573_; lean_object* v___x_4574_; 
v_val_4573_ = lean_ctor_get(v_typeAscriptionTk_x3f_4512_, 0);
lean_inc(v_val_4573_);
lean_dec_ref_known(v_typeAscriptionTk_x3f_4512_, 1);
v___x_4574_ = l_Lean_Fmt_fmt(v_val_4573_, v___y_4570_, v___y_4571_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v_a_4576_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
v_a_4576_ = lean_ctor_get(v___x_4574_, 1);
lean_inc(v_a_4576_);
lean_dec_ref_known(v___x_4574_, 2);
v___y_4550_ = v_a_4576_;
v___y_4551_ = v___y_4570_;
v___y_4552_ = v_binderGroups_4569_;
v___y_4553_ = v_a_4575_;
goto v___jp_4549_;
}
else
{
lean_object* v_a_4577_; lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
lean_dec_ref(v_binderGroups_4569_);
lean_dec(v_a_4519_);
lean_del_object(v___x_4516_);
lean_dec(v_commaTk_4514_);
lean_dec(v_type_x3f_4513_);
v_a_4577_ = lean_ctor_get(v___x_4574_, 0);
v_a_4578_ = lean_ctor_get(v___x_4574_, 1);
v_isSharedCheck_4585_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v___x_4574_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_inc(v_a_4577_);
lean_dec(v___x_4574_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4577_);
lean_ctor_set(v_reuseFailAlloc_4584_, 1, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_del_object(v___x_4516_);
lean_dec(v_commaTk_4514_);
lean_dec(v_type_x3f_4513_);
lean_dec(v_typeAscriptionTk_x3f_4512_);
lean_dec_ref(v_binders_4511_);
v_a_4618_ = lean_ctor_get(v___x_4518_, 0);
v_a_4619_ = lean_ctor_get(v___x_4518_, 1);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4518_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_inc(v_a_4618_);
lean_dec(v___x_4518_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4618_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object* v_head_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l_Lean_Fmt_fmtQuantifierHead(v_head_4628_, v_a_4629_, v_a_4630_);
lean_dec_ref(v_a_4629_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t v_sz_4632_, size_t v_i_4633_, lean_object* v_bs_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v___x_4637_; 
v___x_4637_ = lean_usize_dec_lt(v_i_4633_, v_sz_4632_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4638_, 0, v_bs_4634_);
lean_ctor_set(v___x_4638_, 1, v___y_4636_);
return v___x_4638_;
}
else
{
lean_object* v_v_4639_; lean_object* v___x_4640_; 
v_v_4639_ = lean_array_uget_borrowed(v_bs_4634_, v_i_4633_);
lean_inc(v_v_4639_);
v___x_4640_ = l_Lean_Fmt_fmtQuantifierHead(v_v_4639_, v___y_4635_, v___y_4636_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v_a_4642_; lean_object* v___x_4643_; lean_object* v_bs_x27_4644_; size_t v___x_4645_; size_t v___x_4646_; lean_object* v___x_4647_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
v_a_4642_ = lean_ctor_get(v___x_4640_, 1);
lean_inc(v_a_4642_);
lean_dec_ref_known(v___x_4640_, 2);
v___x_4643_ = lean_unsigned_to_nat(0u);
v_bs_x27_4644_ = lean_array_uset(v_bs_4634_, v_i_4633_, v___x_4643_);
v___x_4645_ = ((size_t)1ULL);
v___x_4646_ = lean_usize_add(v_i_4633_, v___x_4645_);
v___x_4647_ = lean_array_uset(v_bs_x27_4644_, v_i_4633_, v_a_4641_);
v_i_4633_ = v___x_4646_;
v_bs_4634_ = v___x_4647_;
v___y_4636_ = v_a_4642_;
goto _start;
}
else
{
lean_object* v_a_4649_; lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_dec_ref(v_bs_4634_);
v_a_4649_ = lean_ctor_get(v___x_4640_, 0);
v_a_4650_ = lean_ctor_get(v___x_4640_, 1);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4640_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_inc(v_a_4649_);
lean_dec(v___x_4640_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4649_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object* v_sz_4658_, lean_object* v_i_4659_, lean_object* v_bs_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
size_t v_sz_boxed_4663_; size_t v_i_boxed_4664_; lean_object* v_res_4665_; 
v_sz_boxed_4663_ = lean_unbox_usize(v_sz_4658_);
lean_dec(v_sz_4658_);
v_i_boxed_4664_ = lean_unbox_usize(v_i_4659_);
lean_dec(v_i_4659_);
v_res_4665_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_boxed_4663_, v_i_boxed_4664_, v_bs_4660_, v___y_4661_, v___y_4662_);
lean_dec_ref(v___y_4661_);
return v_res_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object* v_deconstructQuantifier_x3f_4666_, lean_object* v_stx_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v_env_4670_; lean_object* v___x_4671_; lean_object* v_quantifiers_4672_; lean_object* v_body_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4709_; 
v_env_4670_ = lean_ctor_get(v_a_4668_, 0);
lean_inc_ref(v_env_4670_);
v___x_4671_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(v_env_4670_, v_deconstructQuantifier_x3f_4666_, v_stx_4667_);
v_quantifiers_4672_ = lean_ctor_get(v___x_4671_, 0);
v_body_4673_ = lean_ctor_get(v___x_4671_, 1);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4675_ = v___x_4671_;
v_isShared_4676_ = v_isSharedCheck_4709_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_body_4673_);
lean_inc(v_quantifiers_4672_);
lean_dec(v___x_4671_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4709_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; uint8_t v___x_4679_; 
v___x_4677_ = lean_array_get_size(v_quantifiers_4672_);
v___x_4678_ = lean_unsigned_to_nat(0u);
v___x_4679_ = lean_nat_dec_eq(v___x_4677_, v___x_4678_);
if (v___x_4679_ == 0)
{
size_t v_sz_4680_; size_t v___x_4681_; lean_object* v___x_4682_; 
lean_del_object(v___x_4675_);
v_sz_4680_ = lean_array_size(v_quantifiers_4672_);
v___x_4681_ = ((size_t)0ULL);
v___x_4682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_4680_, v___x_4681_, v_quantifiers_4672_, v_a_4668_, v_a_4669_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v_a_4684_; lean_object* v___x_4685_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
v_a_4684_ = lean_ctor_get(v___x_4682_, 1);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4682_, 2);
v___x_4685_ = l_Lean_Fmt_fmt(v_body_4673_, v_a_4668_, v_a_4684_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4695_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
v_a_4687_ = lean_ctor_get(v___x_4685_, 1);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4689_ = v___x_4685_;
v_isShared_4690_ = v_isSharedCheck_4695_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_inc(v_a_4686_);
lean_dec(v___x_4685_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4695_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___x_4693_; 
v___x_4691_ = l_Lean_Fmt_Layouts_quantified(v_a_4683_, v_a_4686_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set(v___x_4689_, 0, v___x_4691_);
v___x_4693_ = v___x_4689_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v_a_4687_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
else
{
lean_dec(v_a_4683_);
return v___x_4685_;
}
}
else
{
lean_object* v_a_4696_; lean_object* v_a_4697_; lean_object* v___x_4699_; uint8_t v_isShared_4700_; uint8_t v_isSharedCheck_4704_; 
lean_dec(v_body_4673_);
v_a_4696_ = lean_ctor_get(v___x_4682_, 0);
v_a_4697_ = lean_ctor_get(v___x_4682_, 1);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4699_ = v___x_4682_;
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
else
{
lean_inc(v_a_4697_);
lean_inc(v_a_4696_);
lean_dec(v___x_4682_);
v___x_4699_ = lean_box(0);
v_isShared_4700_ = v_isSharedCheck_4704_;
goto v_resetjp_4698_;
}
v_resetjp_4698_:
{
lean_object* v___x_4702_; 
if (v_isShared_4700_ == 0)
{
v___x_4702_ = v___x_4699_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v_a_4696_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_a_4697_);
v___x_4702_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
return v___x_4702_;
}
}
}
}
else
{
lean_object* v___x_4705_; lean_object* v___x_4707_; 
lean_dec(v_body_4673_);
lean_dec_ref(v_quantifiers_4672_);
v___x_4705_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4676_ == 0)
{
lean_ctor_set_tag(v___x_4675_, 1);
lean_ctor_set(v___x_4675_, 1, v_a_4669_);
lean_ctor_set(v___x_4675_, 0, v___x_4705_);
v___x_4707_ = v___x_4675_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_a_4669_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object* v_deconstructQuantifier_x3f_4710_, lean_object* v_stx_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Lean_Fmt_fmtQuantifier(v_deconstructQuantifier_x3f_4710_, v_stx_4711_, v_a_4712_, v_a_4713_);
lean_dec_ref(v_a_4712_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
uint8_t v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = 0;
v___x_4719_ = l_Lean_Fmt_fmtRaw(v___x_4718_, v_a_4715_, v_a_4716_, v_a_4717_);
return v___x_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_){
_start:
{
lean_object* v_res_4723_; 
v_res_4723_ = l_Lean_Fmt_fmtAtomic(v_a_4720_, v_a_4721_, v_a_4722_);
lean_dec_ref(v_a_4721_);
return v_res_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f(lean_object* v_ctx_4724_, lean_object* v_choiceStx_4725_){
_start:
{
uint8_t v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = 0;
v___x_4727_ = l_Lean_Syntax_getRange_x3f(v_choiceStx_4725_, v___x_4726_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v___x_4728_; 
lean_dec_ref(v_ctx_4724_);
v___x_4728_ = lean_box(0);
return v___x_4728_;
}
else
{
lean_object* v_val_4729_; lean_object* v_resolveChoiceNode_4730_; lean_object* v___x_4731_; 
v_val_4729_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_val_4729_);
lean_dec_ref_known(v___x_4727_, 1);
v_resolveChoiceNode_4730_ = lean_ctor_get(v_ctx_4724_, 2);
lean_inc_ref(v_resolveChoiceNode_4730_);
lean_dec_ref(v_ctx_4724_);
v___x_4731_ = lean_apply_1(v_resolveChoiceNode_4730_, v_val_4729_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v___x_4732_; 
v___x_4732_ = lean_box(0);
return v___x_4732_;
}
else
{
lean_object* v_val_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4751_; 
v_val_4733_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4735_ = v___x_4731_;
v_isShared_4736_ = v_isSharedCheck_4751_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_val_4733_);
lean_dec(v___x_4731_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4751_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v_stx_4737_; lean_object* v_chosenAltIdx_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; uint8_t v___x_4741_; 
v_stx_4737_ = lean_ctor_get(v_val_4733_, 0);
lean_inc(v_stx_4737_);
v_chosenAltIdx_4738_ = lean_ctor_get(v_val_4733_, 1);
lean_inc(v_chosenAltIdx_4738_);
lean_dec(v_val_4733_);
v___x_4739_ = l_Lean_Syntax_getNumArgs(v_stx_4737_);
lean_dec(v_stx_4737_);
v___x_4740_ = l_Lean_Syntax_getNumArgs(v_choiceStx_4725_);
v___x_4741_ = lean_nat_dec_eq(v___x_4739_, v___x_4740_);
lean_dec(v___x_4740_);
lean_dec(v___x_4739_);
if (v___x_4741_ == 0)
{
lean_object* v___x_4742_; 
lean_dec(v_chosenAltIdx_4738_);
lean_del_object(v___x_4735_);
v___x_4742_ = lean_box(0);
return v___x_4742_;
}
else
{
lean_object* v___x_4743_; lean_object* v___x_4744_; uint8_t v___x_4745_; 
v___x_4743_ = l_Lean_Syntax_getArgs(v_choiceStx_4725_);
v___x_4744_ = lean_array_get_size(v___x_4743_);
v___x_4745_ = lean_nat_dec_lt(v_chosenAltIdx_4738_, v___x_4744_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; 
lean_dec_ref(v___x_4743_);
lean_dec(v_chosenAltIdx_4738_);
lean_del_object(v___x_4735_);
v___x_4746_ = lean_box(0);
return v___x_4746_;
}
else
{
lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4747_ = lean_array_fget(v___x_4743_, v_chosenAltIdx_4738_);
lean_dec(v_chosenAltIdx_4738_);
lean_dec_ref(v___x_4743_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v___x_4747_);
v___x_4749_ = v___x_4735_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f___boxed(lean_object* v_ctx_4752_, lean_object* v_choiceStx_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f(v_ctx_4752_, v_choiceStx_4753_);
lean_dec(v_choiceStx_4753_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_resolveChoiceNodes(lean_object* v_ctx_4755_, lean_object* v_x_4756_){
_start:
{
if (lean_obj_tag(v_x_4756_) == 1)
{
lean_object* v_info_4757_; lean_object* v_kind_4758_; lean_object* v_args_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; 
v_info_4757_ = lean_ctor_get(v_x_4756_, 0);
lean_inc(v_info_4757_);
v_kind_4758_ = lean_ctor_get(v_x_4756_, 1);
lean_inc(v_kind_4758_);
v_args_4759_ = lean_ctor_get(v_x_4756_, 2);
lean_inc_ref(v_args_4759_);
v___x_4760_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_4761_ = lean_name_eq(v_kind_4758_, v___x_4760_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4771_; 
v_isSharedCheck_4771_ = !lean_is_exclusive(v_x_4756_);
if (v_isSharedCheck_4771_ == 0)
{
lean_object* v_unused_4772_; lean_object* v_unused_4773_; lean_object* v_unused_4774_; 
v_unused_4772_ = lean_ctor_get(v_x_4756_, 2);
lean_dec(v_unused_4772_);
v_unused_4773_ = lean_ctor_get(v_x_4756_, 1);
lean_dec(v_unused_4773_);
v_unused_4774_ = lean_ctor_get(v_x_4756_, 0);
lean_dec(v_unused_4774_);
v___x_4763_ = v_x_4756_;
v_isShared_4764_ = v_isSharedCheck_4771_;
goto v_resetjp_4762_;
}
else
{
lean_dec(v_x_4756_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4771_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
size_t v_sz_4765_; size_t v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
v_sz_4765_ = lean_array_size(v_args_4759_);
v___x_4766_ = ((size_t)0ULL);
v___x_4767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(v_ctx_4755_, v_sz_4765_, v___x_4766_, v_args_4759_);
if (v_isShared_4764_ == 0)
{
lean_ctor_set(v___x_4763_, 2, v___x_4767_);
v___x_4769_ = v___x_4763_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_info_4757_);
lean_ctor_set(v_reuseFailAlloc_4770_, 1, v_kind_4758_);
lean_ctor_set(v_reuseFailAlloc_4770_, 2, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4787_; 
lean_inc_ref(v_ctx_4755_);
v___x_4775_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_resolveChoiceNodes_pickedAlternative_x3f(v_ctx_4755_, v_x_4756_);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_x_4756_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; lean_object* v_unused_4789_; lean_object* v_unused_4790_; 
v_unused_4788_ = lean_ctor_get(v_x_4756_, 2);
lean_dec(v_unused_4788_);
v_unused_4789_ = lean_ctor_get(v_x_4756_, 1);
lean_dec(v_unused_4789_);
v_unused_4790_ = lean_ctor_get(v_x_4756_, 0);
lean_dec(v_unused_4790_);
v___x_4777_ = v_x_4756_;
v_isShared_4778_ = v_isSharedCheck_4787_;
goto v_resetjp_4776_;
}
else
{
lean_dec(v_x_4756_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4787_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
if (lean_obj_tag(v___x_4775_) == 0)
{
size_t v_sz_4779_; size_t v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4783_; 
v_sz_4779_ = lean_array_size(v_args_4759_);
v___x_4780_ = ((size_t)0ULL);
v___x_4781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(v_ctx_4755_, v_sz_4779_, v___x_4780_, v_args_4759_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 2, v___x_4781_);
v___x_4783_ = v___x_4777_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_info_4757_);
lean_ctor_set(v_reuseFailAlloc_4784_, 1, v_kind_4758_);
lean_ctor_set(v_reuseFailAlloc_4784_, 2, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
else
{
lean_object* v_val_4785_; 
lean_del_object(v___x_4777_);
lean_dec_ref(v_args_4759_);
lean_dec(v_kind_4758_);
lean_dec(v_info_4757_);
v_val_4785_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_val_4785_);
lean_dec_ref_known(v___x_4775_, 1);
v_x_4756_ = v_val_4785_;
goto _start;
}
}
}
}
else
{
lean_dec_ref(v_ctx_4755_);
return v_x_4756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(lean_object* v_ctx_4791_, size_t v_sz_4792_, size_t v_i_4793_, lean_object* v_bs_4794_){
_start:
{
uint8_t v___x_4795_; 
v___x_4795_ = lean_usize_dec_lt(v_i_4793_, v_sz_4792_);
if (v___x_4795_ == 0)
{
lean_dec_ref(v_ctx_4791_);
return v_bs_4794_;
}
else
{
lean_object* v_v_4796_; lean_object* v___x_4797_; lean_object* v_bs_x27_4798_; lean_object* v___x_4799_; size_t v___x_4800_; size_t v___x_4801_; lean_object* v___x_4802_; 
v_v_4796_ = lean_array_uget(v_bs_4794_, v_i_4793_);
v___x_4797_ = lean_unsigned_to_nat(0u);
v_bs_x27_4798_ = lean_array_uset(v_bs_4794_, v_i_4793_, v___x_4797_);
lean_inc_ref(v_ctx_4791_);
v___x_4799_ = l_Lean_Fmt_resolveChoiceNodes(v_ctx_4791_, v_v_4796_);
v___x_4800_ = ((size_t)1ULL);
v___x_4801_ = lean_usize_add(v_i_4793_, v___x_4800_);
v___x_4802_ = lean_array_uset(v_bs_x27_4798_, v_i_4793_, v___x_4799_);
v_i_4793_ = v___x_4801_;
v_bs_4794_ = v___x_4802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0___boxed(lean_object* v_ctx_4804_, lean_object* v_sz_4805_, lean_object* v_i_4806_, lean_object* v_bs_4807_){
_start:
{
size_t v_sz_boxed_4808_; size_t v_i_boxed_4809_; lean_object* v_res_4810_; 
v_sz_boxed_4808_ = lean_unbox_usize(v_sz_4805_);
lean_dec(v_sz_4805_);
v_i_boxed_4809_ = lean_unbox_usize(v_i_4806_);
lean_dec(v_i_4806_);
v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_resolveChoiceNodes_spec__0(v_ctx_4804_, v_sz_boxed_4808_, v_i_boxed_4809_, v_bs_4807_);
return v_res_4810_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4817_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed), 3, 0);
v___x_4818_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2));
v___x_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
lean_ctor_set(v___x_4819_, 1, v___x_4817_);
return v___x_4819_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4820_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3);
v___x_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object* v_kind_4822_){
_start:
{
lean_object* v___x_4823_; uint8_t v___x_4824_; 
v___x_4823_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_4824_ = lean_name_eq(v_kind_4822_, v___x_4823_);
if (v___x_4824_ == 0)
{
lean_object* v___x_4825_; 
v___x_4825_ = lean_box(0);
return v___x_4825_;
}
else
{
lean_object* v___x_4826_; 
v___x_4826_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4);
return v___x_4826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object* v_kind_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4827_);
lean_dec(v_kind_4827_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object* v_x_4829_, lean_object* v_x_4830_, lean_object* v_kind_4831_){
_start:
{
lean_object* v___x_4832_; 
v___x_4832_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object* v_x_4833_, lean_object* v_x_4834_, lean_object* v_kind_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(v_x_4833_, v_x_4834_, v_kind_4835_);
lean_dec(v_kind_4835_);
lean_dec_ref(v_x_4834_);
lean_dec_ref(v_x_4833_);
return v_res_4836_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object* v_x_4842_){
_start:
{
if (lean_obj_tag(v_x_4842_) == 1)
{
lean_object* v_pre_4843_; lean_object* v_str_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; 
v_pre_4843_ = lean_ctor_get(v_x_4842_, 0);
v_str_4844_ = lean_ctor_get(v_x_4842_, 1);
v___x_4845_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0));
v___x_4846_ = lean_string_dec_eq(v_str_4844_, v___x_4845_);
if (v___x_4846_ == 0)
{
lean_object* v___x_4847_; uint8_t v___x_4848_; 
v___x_4847_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1));
v___x_4848_ = lean_string_dec_eq(v_str_4844_, v___x_4847_);
if (v___x_4848_ == 0)
{
lean_object* v___x_4849_; uint8_t v___x_4850_; 
v___x_4849_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2));
v___x_4850_ = lean_string_dec_eq(v_str_4844_, v___x_4849_);
if (v___x_4850_ == 0)
{
lean_object* v___x_4851_; uint8_t v___x_4852_; 
v___x_4851_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3));
v___x_4852_ = lean_string_dec_eq(v_str_4844_, v___x_4851_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; uint8_t v___x_4854_; 
v___x_4853_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4));
v___x_4854_ = lean_string_dec_eq(v_str_4844_, v___x_4853_);
if (v___x_4854_ == 0)
{
return v___x_4854_;
}
else
{
if (lean_obj_tag(v_pre_4843_) == 0)
{
return v___x_4854_;
}
else
{
return v___x_4852_;
}
}
}
else
{
return v___x_4852_;
}
}
else
{
return v___x_4850_;
}
}
else
{
return v___x_4848_;
}
}
else
{
return v___x_4846_;
}
}
else
{
uint8_t v___x_4855_; 
v___x_4855_ = 0;
return v___x_4855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object* v_x_4856_){
_start:
{
uint8_t v_res_4857_; lean_object* v_r_4858_; 
v_res_4857_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_x_4856_);
lean_dec(v_x_4856_);
v_r_4858_ = lean_box(v_res_4857_);
return v_r_4858_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2(void){
_start:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4864_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAtomic___boxed), 3, 0);
v___x_4865_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1));
v___x_4866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
lean_ctor_set(v___x_4866_, 1, v___x_4864_);
return v___x_4866_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2);
v___x_4868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object* v_kind_4869_){
_start:
{
uint8_t v___x_4870_; 
v___x_4870_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_kind_4869_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; 
v___x_4871_ = lean_box(0);
return v___x_4871_;
}
else
{
lean_object* v___x_4872_; 
v___x_4872_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object* v_kind_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4873_);
lean_dec(v_kind_4873_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object* v_x_4875_, lean_object* v_x_4876_, lean_object* v_kind_4877_){
_start:
{
lean_object* v___x_4878_; 
v___x_4878_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object* v_x_4879_, lean_object* v_x_4880_, lean_object* v_kind_4881_){
_start:
{
lean_object* v_res_4882_; 
v_res_4882_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(v_x_4879_, v_x_4880_, v_kind_4881_);
lean_dec(v_kind_4881_);
lean_dec_ref(v_x_4880_);
lean_dec_ref(v_x_4879_);
return v_res_4882_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4(void){
_start:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4893_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostfixOperator___boxed), 3, 0);
v___x_4894_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3));
v___x_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4894_);
lean_ctor_set(v___x_4895_, 1, v___x_4893_);
return v___x_4895_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5(void){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4);
v___x_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
return v___x_4897_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8(void){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4903_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrefixOperator___boxed), 3, 0);
v___x_4904_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7));
v___x_4905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
lean_ctor_set(v___x_4905_, 1, v___x_4903_);
return v___x_4905_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9(void){
_start:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; 
v___x_4906_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8);
v___x_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
return v___x_4907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object* v_env_4908_, lean_object* v_opts_4909_, lean_object* v_kind_4910_){
_start:
{
lean_object* v___x_4911_; 
lean_inc(v_kind_4910_);
lean_inc_ref(v_env_4908_);
v___x_4911_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_4908_, v_opts_4909_, v_kind_4910_);
if (lean_obj_tag(v___x_4911_) == 1)
{
lean_object* v_val_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4922_; 
lean_dec(v_kind_4910_);
lean_dec_ref(v_env_4908_);
v_val_4912_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4914_ = v___x_4911_;
v_isShared_4915_ = v_isSharedCheck_4922_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_val_4912_);
lean_dec(v___x_4911_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4922_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4916_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1));
v___x_4917_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInfixOperator___boxed), 4, 1);
lean_closure_set(v___x_4917_, 0, v_val_4912_);
v___x_4918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4916_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v___x_4918_);
v___x_4920_ = v___x_4914_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
else
{
uint8_t v___x_4923_; 
lean_dec(v___x_4911_);
lean_inc(v_kind_4910_);
lean_inc_ref(v_env_4908_);
v___x_4923_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_4908_, v_opts_4909_, v_kind_4910_);
if (v___x_4923_ == 0)
{
uint8_t v___x_4924_; 
v___x_4924_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_4908_, v_opts_4909_, v_kind_4910_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; 
v___x_4925_ = lean_box(0);
return v___x_4925_;
}
else
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5);
return v___x_4926_;
}
}
else
{
lean_object* v___x_4927_; 
lean_dec(v_kind_4910_);
lean_dec_ref(v_env_4908_);
v___x_4927_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9);
return v___x_4927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object* v_env_4928_, lean_object* v_opts_4929_, lean_object* v_kind_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(v_env_4928_, v_opts_4929_, v_kind_4930_);
lean_dec_ref(v_opts_4929_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object* v_env_4932_, lean_object* v_opts_4933_, lean_object* v_kind_4934_){
_start:
{
uint8_t v___x_4935_; 
v___x_4935_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_4932_, v_opts_4933_, v_kind_4934_);
if (v___x_4935_ == 0)
{
lean_object* v___x_4936_; 
v___x_4936_ = lean_box(0);
return v___x_4936_;
}
else
{
lean_object* v___x_4937_; 
v___x_4937_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object* v_env_4938_, lean_object* v_opts_4939_, lean_object* v_kind_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(v_env_4938_, v_opts_4939_, v_kind_4940_);
lean_dec_ref(v_opts_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(lean_object* v_x_4942_, lean_object* v_x_4943_){
_start:
{
if (lean_obj_tag(v_x_4942_) == 0)
{
if (lean_obj_tag(v_x_4943_) == 0)
{
uint8_t v___x_4944_; 
v___x_4944_ = 1;
return v___x_4944_;
}
else
{
uint8_t v___x_4945_; 
v___x_4945_ = 0;
return v___x_4945_;
}
}
else
{
if (lean_obj_tag(v_x_4943_) == 0)
{
uint8_t v___x_4946_; 
v___x_4946_ = 0;
return v___x_4946_;
}
else
{
lean_object* v_val_4947_; lean_object* v_val_4948_; uint8_t v___x_4949_; 
v_val_4947_ = lean_ctor_get(v_x_4942_, 0);
v_val_4948_ = lean_ctor_get(v_x_4943_, 0);
v___x_4949_ = lean_nat_dec_eq(v_val_4947_, v_val_4948_);
return v___x_4949_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0___boxed(lean_object* v_x_4950_, lean_object* v_x_4951_){
_start:
{
uint8_t v_res_4952_; lean_object* v_r_4953_; 
v_res_4952_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v_x_4950_, v_x_4951_);
lean_dec(v_x_4951_);
lean_dec(v_x_4950_);
v_r_4953_ = lean_box(v_res_4952_);
return v_r_4953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(lean_object* v_lineInfos_4954_, lean_object* v___f_4955_, lean_object* v___f_4956_, lean_object* v_pos_4957_){
_start:
{
lean_object* v___x_4958_; 
v___x_4958_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_4954_, v_pos_4957_, v___f_4955_, v___f_4956_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v___x_4959_; 
v___x_4959_ = lean_box(0);
return v___x_4959_;
}
else
{
lean_object* v_val_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4968_; 
v_val_4960_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4962_ = v___x_4958_;
v_isShared_4963_ = v_isSharedCheck_4968_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_val_4960_);
lean_dec(v___x_4958_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4968_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v_fst_4964_; lean_object* v___x_4966_; 
v_fst_4964_ = lean_ctor_get(v_val_4960_, 0);
lean_inc(v_fst_4964_);
lean_dec(v_val_4960_);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 0, v_fst_4964_);
v___x_4966_ = v___x_4962_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_fst_4964_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2___boxed(lean_object* v_lineInfos_4969_, lean_object* v___f_4970_, lean_object* v___f_4971_, lean_object* v_pos_4972_){
_start:
{
lean_object* v_res_4973_; 
v_res_4973_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4969_, v___f_4970_, v___f_4971_, v_pos_4972_);
lean_dec_ref(v_lineInfos_4969_);
return v_res_4973_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(lean_object* v_lineInfos_4974_, lean_object* v_a_4975_, lean_object* v_b_4976_){
_start:
{
lean_object* v___f_4977_; lean_object* v___f_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; uint8_t v___x_4981_; 
v___f_4977_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_4978_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_4979_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4974_, v___f_4977_, v___f_4978_, v_a_4975_);
v___x_4980_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4974_, v___f_4977_, v___f_4978_, v_b_4976_);
v___x_4981_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v___x_4979_, v___x_4980_);
lean_dec(v___x_4980_);
lean_dec(v___x_4979_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___boxed(lean_object* v_lineInfos_4982_, lean_object* v_a_4983_, lean_object* v_b_4984_){
_start:
{
uint8_t v_res_4985_; lean_object* v_r_4986_; 
v_res_4985_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4982_, v_a_4983_, v_b_4984_);
lean_dec_ref(v_lineInfos_4982_);
v_r_4986_ = lean_box(v_res_4985_);
return v_r_4986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(lean_object* v_val_4987_, uint8_t v_opOnLhsLine_4988_, lean_object* v_val_4989_, uint8_t v_opOnRhsLine_4990_, lean_object* v___x_4991_, lean_object* v___x_4992_, lean_object* v_as_4993_, size_t v_sz_4994_, size_t v_i_4995_, lean_object* v_b_4996_){
_start:
{
lean_object* v_a_4998_; uint8_t v___x_5002_; 
v___x_5002_ = lean_usize_dec_lt(v_i_4995_, v_sz_4994_);
if (v___x_5002_ == 0)
{
lean_dec_ref(v_val_4989_);
lean_dec_ref(v_val_4987_);
return v_b_4996_;
}
else
{
lean_object* v_a_5003_; uint8_t v_kind_5004_; uint8_t v_placement_5005_; lean_object* v_originalTokenRange_5006_; lean_object* v_originalWhitespaceRange_5007_; uint8_t v_originalWhitespaceKind_5008_; lean_object* v_content_5009_; uint8_t v_emptyLineBefore_5010_; uint8_t v___y_5017_; 
v_a_5003_ = lean_array_uget_borrowed(v_as_4993_, v_i_4995_);
v_kind_5004_ = lean_ctor_get_uint8(v_a_5003_, sizeof(void*)*3);
v_placement_5005_ = lean_ctor_get_uint8(v_a_5003_, sizeof(void*)*3 + 1);
v_originalTokenRange_5006_ = lean_ctor_get(v_a_5003_, 0);
v_originalWhitespaceRange_5007_ = lean_ctor_get(v_a_5003_, 1);
v_originalWhitespaceKind_5008_ = lean_ctor_get_uint8(v_a_5003_, sizeof(void*)*3 + 2);
v_content_5009_ = lean_ctor_get(v_a_5003_, 2);
v_emptyLineBefore_5010_ = lean_ctor_get_uint8(v_a_5003_, sizeof(void*)*3 + 3);
if (v_placement_5005_ == 0)
{
lean_object* v___x_5020_; uint8_t v___x_5021_; 
v___x_5020_ = lean_unsigned_to_nat(3u);
v___x_5021_ = lean_nat_dec_eq(v___x_4991_, v___x_5020_);
v___y_5017_ = v___x_5021_;
goto v___jp_5016_;
}
else
{
lean_object* v___x_5022_; uint8_t v___x_5023_; 
v___x_5022_ = lean_unsigned_to_nat(0u);
v___x_5023_ = lean_nat_dec_eq(v___x_4992_, v___x_5022_);
v___y_5017_ = v___x_5023_;
goto v___jp_5016_;
}
v___jp_5011_:
{
uint8_t v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v___x_5012_ = 1;
lean_inc_ref(v_content_5009_);
lean_inc_ref(v_originalWhitespaceRange_5007_);
lean_inc_ref(v_originalTokenRange_5006_);
v___x_5013_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5013_, 0, v_originalTokenRange_5006_);
lean_ctor_set(v___x_5013_, 1, v_originalWhitespaceRange_5007_);
lean_ctor_set(v___x_5013_, 2, v_content_5009_);
lean_ctor_set_uint8(v___x_5013_, sizeof(void*)*3, v_kind_5004_);
lean_ctor_set_uint8(v___x_5013_, sizeof(void*)*3 + 1, v___x_5012_);
lean_ctor_set_uint8(v___x_5013_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_5008_);
lean_ctor_set_uint8(v___x_5013_, sizeof(void*)*3 + 3, v_emptyLineBefore_5010_);
lean_inc_ref(v_val_4987_);
v___x_5014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5013_);
lean_ctor_set(v___x_5014_, 1, v_val_4987_);
v___x_5015_ = lean_array_push(v_b_4996_, v___x_5014_);
v_a_4998_ = v___x_5015_;
goto v___jp_4997_;
}
v___jp_5016_:
{
if (v___y_5017_ == 0)
{
goto v___jp_5011_;
}
else
{
if (v_opOnRhsLine_4990_ == 0)
{
if (v_opOnLhsLine_4988_ == 0)
{
goto v___jp_5011_;
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
lean_inc_ref(v_val_4989_);
lean_inc(v_a_5003_);
v___x_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5018_, 0, v_a_5003_);
lean_ctor_set(v___x_5018_, 1, v_val_4989_);
v___x_5019_ = lean_array_push(v_b_4996_, v___x_5018_);
v_a_4998_ = v___x_5019_;
goto v___jp_4997_;
}
}
else
{
v_a_4998_ = v_b_4996_;
goto v___jp_4997_;
}
}
}
}
v___jp_4997_:
{
size_t v___x_4999_; size_t v___x_5000_; 
v___x_4999_ = ((size_t)1ULL);
v___x_5000_ = lean_usize_add(v_i_4995_, v___x_4999_);
v_i_4995_ = v___x_5000_;
v_b_4996_ = v_a_4998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0___boxed(lean_object* v_val_5024_, lean_object* v_opOnLhsLine_5025_, lean_object* v_val_5026_, lean_object* v_opOnRhsLine_5027_, lean_object* v___x_5028_, lean_object* v___x_5029_, lean_object* v_as_5030_, lean_object* v_sz_5031_, lean_object* v_i_5032_, lean_object* v_b_5033_){
_start:
{
uint8_t v_opOnLhsLine_boxed_5034_; uint8_t v_opOnRhsLine_boxed_5035_; size_t v_sz_boxed_5036_; size_t v_i_boxed_5037_; lean_object* v_res_5038_; 
v_opOnLhsLine_boxed_5034_ = lean_unbox(v_opOnLhsLine_5025_);
v_opOnRhsLine_boxed_5035_ = lean_unbox(v_opOnRhsLine_5027_);
v_sz_boxed_5036_ = lean_unbox_usize(v_sz_5031_);
lean_dec(v_sz_5031_);
v_i_boxed_5037_ = lean_unbox_usize(v_i_5032_);
lean_dec(v_i_5032_);
v_res_5038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_5024_, v_opOnLhsLine_boxed_5034_, v_val_5026_, v_opOnRhsLine_boxed_5035_, v___x_5028_, v___x_5029_, v_as_5030_, v_sz_boxed_5036_, v_i_boxed_5037_, v_b_5033_);
lean_dec_ref(v_as_5030_);
lean_dec(v___x_5029_);
lean_dec(v___x_5028_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector(lean_object* v_ctx_5041_, lean_object* v_stx_5042_){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; uint8_t v___x_5047_; 
v___x_5045_ = l_Lean_Syntax_getNumArgs(v_stx_5042_);
v___x_5046_ = lean_unsigned_to_nat(3u);
v___x_5047_ = lean_nat_dec_eq(v___x_5045_, v___x_5046_);
if (v___x_5047_ == 0)
{
lean_object* v___x_5048_; 
lean_dec(v___x_5045_);
lean_dec(v_stx_5042_);
lean_dec_ref(v_ctx_5041_);
v___x_5048_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5048_;
}
else
{
lean_object* v___x_5049_; lean_object* v___x_5050_; uint8_t v___x_5051_; 
v___x_5049_ = lean_unsigned_to_nat(1u);
v___x_5050_ = l_Lean_Syntax_getArg(v_stx_5042_, v___x_5049_);
v___x_5051_ = l_Lean_Syntax_isAtom(v___x_5050_);
if (v___x_5051_ == 0)
{
lean_object* v___x_5052_; 
lean_dec(v___x_5050_);
lean_dec(v___x_5045_);
lean_dec(v_stx_5042_);
lean_dec_ref(v_ctx_5041_);
v___x_5052_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5052_;
}
else
{
lean_object* v_env_5053_; lean_object* v_opts_5054_; lean_object* v_lineInfos_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v_env_5053_ = lean_ctor_get(v_ctx_5041_, 0);
v_opts_5054_ = lean_ctor_get(v_ctx_5041_, 1);
v_lineInfos_5055_ = lean_ctor_get(v_ctx_5041_, 2);
lean_inc_ref(v_lineInfos_5055_);
v___x_5056_ = lean_unsigned_to_nat(0u);
v___x_5057_ = l_Lean_Syntax_getArg(v_stx_5042_, v___x_5056_);
v___x_5058_ = lean_unsigned_to_nat(2u);
v___x_5059_ = l_Lean_Syntax_getArg(v_stx_5042_, v___x_5058_);
v___x_5060_ = l_Lean_Syntax_getKind(v_stx_5042_);
lean_inc_ref(v_env_5053_);
v___x_5061_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_5053_, v_opts_5054_, v___x_5060_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v___x_5062_; 
lean_dec(v___x_5059_);
lean_dec(v___x_5057_);
lean_dec_ref(v_lineInfos_5055_);
lean_dec(v___x_5050_);
lean_dec(v___x_5045_);
lean_dec_ref(v_ctx_5041_);
v___x_5062_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5062_;
}
else
{
lean_object* v_comments_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
lean_dec_ref_known(v___x_5061_, 1);
v_comments_5063_ = l_Lean_Fmt_CommentCollector_Context_trailingComments(v_ctx_5041_, v___x_5050_);
lean_dec_ref(v_ctx_5041_);
v___x_5064_ = lean_array_get_size(v_comments_5063_);
v___x_5065_ = lean_nat_dec_eq(v___x_5064_, v___x_5056_);
if (v___x_5065_ == 0)
{
lean_object* v___x_5066_; lean_object* v___x_5067_; 
v___x_5066_ = l_Lean_Syntax_getTailInfo(v___x_5057_);
lean_dec(v___x_5057_);
v___x_5067_ = l_Lean_SourceInfo_getRange_x3f(v___x_5065_, v___x_5066_);
lean_dec(v___x_5066_);
if (lean_obj_tag(v___x_5067_) == 1)
{
lean_object* v_val_5068_; lean_object* v___x_5069_; 
v_val_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_val_5068_);
lean_dec_ref_known(v___x_5067_, 1);
v___x_5069_ = l_Lean_Syntax_getRange_x3f(v___x_5050_, v___x_5065_);
lean_dec(v___x_5050_);
if (lean_obj_tag(v___x_5069_) == 1)
{
lean_object* v_val_5070_; lean_object* v___x_5071_; 
v_val_5070_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_val_5070_);
lean_dec_ref_known(v___x_5069_, 1);
v___x_5071_ = l_Lean_Syntax_getPos_x3f(v___x_5059_, v___x_5065_);
lean_dec(v___x_5059_);
if (lean_obj_tag(v___x_5071_) == 1)
{
lean_object* v_val_5072_; lean_object* v_stop_5073_; lean_object* v_start_5074_; lean_object* v_stop_5075_; uint8_t v_opOnLhsLine_5076_; uint8_t v_opOnRhsLine_5077_; lean_object* v_r_5078_; size_t v_sz_5079_; size_t v___x_5080_; lean_object* v___x_5081_; 
v_val_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc(v_val_5072_);
lean_dec_ref_known(v___x_5071_, 1);
v_stop_5073_ = lean_ctor_get(v_val_5068_, 1);
v_start_5074_ = lean_ctor_get(v_val_5070_, 0);
v_stop_5075_ = lean_ctor_get(v_val_5070_, 1);
lean_inc(v_start_5074_);
lean_inc(v_stop_5073_);
v_opOnLhsLine_5076_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_5055_, v_stop_5073_, v_start_5074_);
lean_inc(v_stop_5075_);
v_opOnRhsLine_5077_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_5055_, v_stop_5075_, v_val_5072_);
lean_dec_ref(v_lineInfos_5055_);
v_r_5078_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
v_sz_5079_ = lean_array_size(v_comments_5063_);
v___x_5080_ = ((size_t)0ULL);
v___x_5081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_5070_, v_opOnLhsLine_5076_, v_val_5068_, v_opOnRhsLine_5077_, v___x_5045_, v___x_5064_, v_comments_5063_, v_sz_5079_, v___x_5080_, v_r_5078_);
lean_dec_ref(v_comments_5063_);
lean_dec(v___x_5045_);
return v___x_5081_;
}
else
{
lean_dec(v___x_5071_);
lean_dec(v_val_5070_);
lean_dec(v_val_5068_);
lean_dec_ref(v_comments_5063_);
lean_dec_ref(v_lineInfos_5055_);
lean_dec(v___x_5045_);
goto v___jp_5043_;
}
}
else
{
lean_dec(v___x_5069_);
lean_dec(v_val_5068_);
lean_dec_ref(v_comments_5063_);
lean_dec(v___x_5059_);
lean_dec_ref(v_lineInfos_5055_);
lean_dec(v___x_5045_);
goto v___jp_5043_;
}
}
else
{
lean_dec(v___x_5067_);
lean_dec_ref(v_comments_5063_);
lean_dec(v___x_5059_);
lean_dec_ref(v_lineInfos_5055_);
lean_dec(v___x_5050_);
lean_dec(v___x_5045_);
goto v___jp_5043_;
}
}
else
{
lean_object* v___x_5082_; 
lean_dec_ref(v_comments_5063_);
lean_dec(v___x_5059_);
lean_dec(v___x_5057_);
lean_dec_ref(v_lineInfos_5055_);
lean_dec(v___x_5050_);
lean_dec(v___x_5045_);
v___x_5082_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5082_;
}
}
}
}
v___jp_5043_:
{
lean_object* v___x_5044_; 
v___x_5044_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v___x_5087_; 
lean_inc_ref(v___y_5085_);
v___x_5087_ = lean_apply_3(v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_){
_start:
{
lean_object* v_res_5092_; 
v_res_5092_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
lean_dec_ref(v___y_5090_);
return v_res_5092_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; 
v___f_5095_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5096_ = l_Lean_Fmt_fmtAttribute;
v___x_5097_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5097_, 0, lean_box(0));
lean_closure_set(v___x_5097_, 1, v___x_5096_);
lean_closure_set(v___x_5097_, 2, v___f_5095_);
return v___x_5097_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v___f_5098_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5099_ = l_Lean_Fmt_infixFmtAttribute;
v___x_5100_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5100_, 0, lean_box(0));
lean_closure_set(v___x_5100_, 1, v___x_5099_);
lean_closure_set(v___x_5100_, 2, v___f_5098_);
return v___x_5100_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5102_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5103_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_5104_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5104_, 0, lean_box(0));
lean_closure_set(v___x_5104_, 1, v___x_5103_);
lean_closure_set(v___x_5104_, 2, v___x_5102_);
return v___x_5104_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5106_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5107_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_5108_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5108_, 0, lean_box(0));
lean_closure_set(v___x_5108_, 1, v___x_5107_);
lean_closure_set(v___x_5108_, 2, v___x_5106_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5110_ = lean_unsigned_to_nat(1100u);
v___x_5111_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed), 3, 0);
v___x_5112_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5110_, v___x_5111_);
if (lean_obj_tag(v___x_5112_) == 0)
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
lean_dec_ref_known(v___x_5112_, 1);
v___x_5113_ = lean_unsigned_to_nat(1000u);
v___x_5114_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5115_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5113_, v___x_5114_);
if (lean_obj_tag(v___x_5115_) == 0)
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
lean_dec_ref_known(v___x_5115_, 1);
v___x_5116_ = lean_unsigned_to_nat(900u);
v___x_5117_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed), 3, 0);
v___x_5118_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5116_, v___x_5117_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; 
lean_dec_ref_known(v___x_5118_, 1);
v___x_5119_ = lean_unsigned_to_nat(800u);
v___x_5120_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5121_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5119_, v___x_5120_);
if (lean_obj_tag(v___x_5121_) == 0)
{
lean_object* v___x_5122_; lean_object* v___x_5123_; 
lean_dec_ref_known(v___x_5121_, 1);
v___x_5122_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5123_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5119_, v___x_5122_);
if (lean_obj_tag(v___x_5123_) == 0)
{
lean_object* v___x_5124_; lean_object* v___x_5125_; 
lean_dec_ref_known(v___x_5123_, 1);
v___x_5124_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5125_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5119_, v___x_5124_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
lean_dec_ref_known(v___x_5125_, 1);
v___x_5126_ = lean_unsigned_to_nat(600u);
v___x_5127_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed), 3, 0);
v___x_5128_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5126_, v___x_5127_);
if (lean_obj_tag(v___x_5128_) == 0)
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; 
lean_dec_ref_known(v___x_5128_, 1);
v___x_5129_ = lean_unsigned_to_nat(400u);
v___x_5130_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed), 3, 0);
v___x_5131_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5129_, v___x_5130_);
return v___x_5131_;
}
else
{
return v___x_5128_;
}
}
else
{
return v___x_5125_;
}
}
else
{
return v___x_5123_;
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
else
{
return v___x_5115_;
}
}
else
{
return v___x_5112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v_a_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_();
return v_res_5133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5135_ = lean_unsigned_to_nat(500u);
v___x_5136_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector), 2, 0);
v___x_5137_ = l_Lean_Fmt_addBuiltinCommentCollector(v___x_5135_, v___x_5136_);
return v___x_5137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2____boxed(lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_();
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object* v_stx_x3f_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5140_) == 1)
{
lean_object* v_val_5143_; lean_object* v___x_5144_; 
v_val_5143_ = lean_ctor_get(v_stx_x3f_5140_, 0);
lean_inc(v_val_5143_);
lean_dec_ref_known(v_stx_x3f_5140_, 1);
v___x_5144_ = l_Lean_Fmt_fmt(v_val_5143_, v_a_5141_, v_a_5142_);
return v___x_5144_;
}
else
{
lean_object* v___x_5145_; lean_object* v___x_5146_; 
lean_dec(v_stx_x3f_5140_);
v___x_5145_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5146_, 0, v___x_5145_);
lean_ctor_set(v___x_5146_, 1, v_a_5142_);
return v___x_5146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object* v_stx_x3f_5147_, lean_object* v_a_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Lean_Fmt_fmt_x3f(v_stx_x3f_5147_, v_a_5148_, v_a_5149_);
lean_dec_ref(v_a_5148_);
return v_res_5150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object* v_f_5151_, lean_object* v_formatterName_5152_, lean_object* v_stx_x3f_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5153_) == 1)
{
lean_object* v_val_5156_; lean_object* v___x_5157_; 
v_val_5156_ = lean_ctor_get(v_stx_x3f_5153_, 0);
lean_inc(v_val_5156_);
lean_dec_ref_known(v_stx_x3f_5153_, 1);
v___x_5157_ = l_Lean_Fmt_fmtWith(v_f_5151_, v_formatterName_5152_, v_val_5156_, v_a_5154_, v_a_5155_);
return v___x_5157_;
}
else
{
lean_object* v___x_5158_; lean_object* v___x_5159_; 
lean_dec(v_stx_x3f_5153_);
lean_dec(v_formatterName_5152_);
lean_dec_ref(v_f_5151_);
v___x_5158_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5158_);
lean_ctor_set(v___x_5159_, 1, v_a_5155_);
return v___x_5159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object* v_f_5160_, lean_object* v_formatterName_5161_, lean_object* v_stx_x3f_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l_Lean_Fmt_fmtWith_x3f(v_f_5160_, v_formatterName_5161_, v_stx_x3f_5162_, v_a_5163_, v_a_5164_);
lean_dec_ref(v_a_5163_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object* v_array_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
size_t v_sz_5169_; size_t v___x_5170_; lean_object* v___x_5171_; 
v_sz_5169_ = lean_array_size(v_array_5166_);
v___x_5170_ = ((size_t)0ULL);
v___x_5171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5169_, v___x_5170_, v_array_5166_, v_a_5167_, v_a_5168_);
return v___x_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object* v_array_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l_Lean_Fmt_fmtArray___redArg(v_array_5172_, v_a_5173_, v_a_5174_);
lean_dec_ref(v_a_5173_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object* v_ks_5176_, lean_object* v_array_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_){
_start:
{
lean_object* v___x_5180_; 
v___x_5180_ = l_Lean_Fmt_fmtArray___redArg(v_array_5177_, v_a_5178_, v_a_5179_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object* v_ks_5181_, lean_object* v_array_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_){
_start:
{
lean_object* v_res_5185_; 
v_res_5185_ = l_Lean_Fmt_fmtArray(v_ks_5181_, v_array_5182_, v_a_5183_, v_a_5184_);
lean_dec_ref(v_a_5183_);
lean_dec(v_ks_5181_);
return v_res_5185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object* v_f_5186_, lean_object* v_formatterName_5187_, size_t v_sz_5188_, size_t v_i_5189_, lean_object* v_bs_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
uint8_t v___x_5193_; 
v___x_5193_ = lean_usize_dec_lt(v_i_5189_, v_sz_5188_);
if (v___x_5193_ == 0)
{
lean_object* v___x_5194_; 
lean_dec(v_formatterName_5187_);
lean_dec_ref(v_f_5186_);
v___x_5194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5194_, 0, v_bs_5190_);
lean_ctor_set(v___x_5194_, 1, v___y_5192_);
return v___x_5194_;
}
else
{
lean_object* v_v_5195_; lean_object* v___x_5196_; 
v_v_5195_ = lean_array_uget_borrowed(v_bs_5190_, v_i_5189_);
lean_inc(v_v_5195_);
lean_inc(v_formatterName_5187_);
lean_inc_ref(v_f_5186_);
v___x_5196_ = l_Lean_Fmt_fmtWith(v_f_5186_, v_formatterName_5187_, v_v_5195_, v___y_5191_, v___y_5192_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_a_5197_; lean_object* v_a_5198_; lean_object* v___x_5199_; lean_object* v_bs_x27_5200_; size_t v___x_5201_; size_t v___x_5202_; lean_object* v___x_5203_; 
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
lean_inc(v_a_5197_);
v_a_5198_ = lean_ctor_get(v___x_5196_, 1);
lean_inc(v_a_5198_);
lean_dec_ref_known(v___x_5196_, 2);
v___x_5199_ = lean_unsigned_to_nat(0u);
v_bs_x27_5200_ = lean_array_uset(v_bs_5190_, v_i_5189_, v___x_5199_);
v___x_5201_ = ((size_t)1ULL);
v___x_5202_ = lean_usize_add(v_i_5189_, v___x_5201_);
v___x_5203_ = lean_array_uset(v_bs_x27_5200_, v_i_5189_, v_a_5197_);
v_i_5189_ = v___x_5202_;
v_bs_5190_ = v___x_5203_;
v___y_5192_ = v_a_5198_;
goto _start;
}
else
{
lean_object* v_a_5205_; lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
lean_dec_ref(v_bs_5190_);
lean_dec(v_formatterName_5187_);
lean_dec_ref(v_f_5186_);
v_a_5205_ = lean_ctor_get(v___x_5196_, 0);
v_a_5206_ = lean_ctor_get(v___x_5196_, 1);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5196_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_inc(v_a_5205_);
lean_dec(v___x_5196_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5205_);
lean_ctor_set(v_reuseFailAlloc_5212_, 1, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
return v___x_5211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object* v_f_5214_, lean_object* v_formatterName_5215_, lean_object* v_sz_5216_, lean_object* v_i_5217_, lean_object* v_bs_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_){
_start:
{
size_t v_sz_boxed_5221_; size_t v_i_boxed_5222_; lean_object* v_res_5223_; 
v_sz_boxed_5221_ = lean_unbox_usize(v_sz_5216_);
lean_dec(v_sz_5216_);
v_i_boxed_5222_ = lean_unbox_usize(v_i_5217_);
lean_dec(v_i_5217_);
v_res_5223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5214_, v_formatterName_5215_, v_sz_boxed_5221_, v_i_boxed_5222_, v_bs_5218_, v___y_5219_, v___y_5220_);
lean_dec_ref(v___y_5219_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object* v_f_5224_, lean_object* v_formatterName_5225_, lean_object* v_array_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_){
_start:
{
size_t v_sz_5229_; size_t v___x_5230_; lean_object* v___x_5231_; 
v_sz_5229_ = lean_array_size(v_array_5226_);
v___x_5230_ = ((size_t)0ULL);
v___x_5231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5224_, v_formatterName_5225_, v_sz_5229_, v___x_5230_, v_array_5226_, v_a_5227_, v_a_5228_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object* v_f_5232_, lean_object* v_formatterName_5233_, lean_object* v_array_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5232_, v_formatterName_5233_, v_array_5234_, v_a_5235_, v_a_5236_);
lean_dec_ref(v_a_5235_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object* v_ks_5238_, lean_object* v_f_5239_, lean_object* v_formatterName_5240_, lean_object* v_array_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5239_, v_formatterName_5240_, v_array_5241_, v_a_5242_, v_a_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object* v_ks_5245_, lean_object* v_f_5246_, lean_object* v_formatterName_5247_, lean_object* v_array_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_Fmt_fmtArrayWith(v_ks_5245_, v_f_5246_, v_formatterName_5247_, v_array_5248_, v_a_5249_, v_a_5250_);
lean_dec_ref(v_a_5249_);
lean_dec(v_ks_5245_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object* v_sepArray_5252_, lean_object* v_a_5253_, lean_object* v_a_5254_){
_start:
{
size_t v_sz_5255_; size_t v___x_5256_; lean_object* v___x_5257_; 
v_sz_5255_ = lean_array_size(v_sepArray_5252_);
v___x_5256_ = ((size_t)0ULL);
v___x_5257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5255_, v___x_5256_, v_sepArray_5252_, v_a_5253_, v_a_5254_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_object* v_a_5258_; lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
v_a_5258_ = lean_ctor_get(v___x_5257_, 0);
v_a_5259_ = lean_ctor_get(v___x_5257_, 1);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5257_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_inc(v_a_5258_);
lean_dec(v___x_5257_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5258_);
lean_ctor_set(v_reuseFailAlloc_5265_, 1, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v_a_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5275_; 
v_a_5267_ = lean_ctor_get(v___x_5257_, 0);
v_a_5268_ = lean_ctor_get(v___x_5257_, 1);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5270_ = v___x_5257_;
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_a_5268_);
lean_inc(v_a_5267_);
lean_dec(v___x_5257_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5275_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
lean_object* v___x_5273_; 
if (v_isShared_5271_ == 0)
{
v___x_5273_ = v___x_5270_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5267_);
lean_ctor_set(v_reuseFailAlloc_5274_, 1, v_a_5268_);
v___x_5273_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
return v___x_5273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object* v_sepArray_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_){
_start:
{
lean_object* v_res_5279_; 
v_res_5279_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5276_, v_a_5277_, v_a_5278_);
lean_dec_ref(v_a_5277_);
return v_res_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object* v_sep_5280_, lean_object* v_sepArray_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_){
_start:
{
lean_object* v___x_5284_; 
v___x_5284_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5281_, v_a_5282_, v_a_5283_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object* v_sep_5285_, lean_object* v_sepArray_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l_Lean_Fmt_fmtSepArray(v_sep_5285_, v_sepArray_5286_, v_a_5287_, v_a_5288_);
lean_dec_ref(v_a_5287_);
lean_dec_ref(v_sep_5285_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object* v_f_5290_, lean_object* v_formatterName_5291_, size_t v_sz_5292_, size_t v_i_5293_, lean_object* v_bs_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_){
_start:
{
uint8_t v___x_5297_; 
v___x_5297_ = lean_usize_dec_lt(v_i_5293_, v_sz_5292_);
if (v___x_5297_ == 0)
{
lean_object* v___x_5298_; 
lean_dec(v_formatterName_5291_);
lean_dec_ref(v_f_5290_);
v___x_5298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5298_, 0, v_bs_5294_);
lean_ctor_set(v___x_5298_, 1, v___y_5296_);
return v___x_5298_;
}
else
{
lean_object* v_v_5299_; lean_object* v___x_5300_; lean_object* v_bs_x27_5301_; lean_object* v___y_5303_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; uint8_t v___x_5322_; 
v_v_5299_ = lean_array_uget(v_bs_5294_, v_i_5293_);
v___x_5300_ = lean_unsigned_to_nat(0u);
v_bs_x27_5301_ = lean_array_uset(v_bs_5294_, v_i_5293_, v___x_5300_);
v___x_5319_ = lean_usize_to_nat(v_i_5293_);
v___x_5320_ = lean_unsigned_to_nat(2u);
v___x_5321_ = lean_nat_mod(v___x_5319_, v___x_5320_);
lean_dec(v___x_5319_);
v___x_5322_ = lean_nat_dec_eq(v___x_5321_, v___x_5300_);
lean_dec(v___x_5321_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; 
v___x_5323_ = l_Lean_Fmt_fmt(v_v_5299_, v___y_5295_, v___y_5296_);
v___y_5303_ = v___x_5323_;
goto v___jp_5302_;
}
else
{
lean_object* v___x_5324_; 
lean_inc(v_formatterName_5291_);
lean_inc_ref(v_f_5290_);
v___x_5324_ = l_Lean_Fmt_fmtWith(v_f_5290_, v_formatterName_5291_, v_v_5299_, v___y_5295_, v___y_5296_);
v___y_5303_ = v___x_5324_;
goto v___jp_5302_;
}
v___jp_5302_:
{
if (lean_obj_tag(v___y_5303_) == 0)
{
lean_object* v_a_5304_; lean_object* v_a_5305_; size_t v___x_5306_; size_t v___x_5307_; lean_object* v___x_5308_; 
v_a_5304_ = lean_ctor_get(v___y_5303_, 0);
lean_inc(v_a_5304_);
v_a_5305_ = lean_ctor_get(v___y_5303_, 1);
lean_inc(v_a_5305_);
lean_dec_ref_known(v___y_5303_, 2);
v___x_5306_ = ((size_t)1ULL);
v___x_5307_ = lean_usize_add(v_i_5293_, v___x_5306_);
v___x_5308_ = lean_array_uset(v_bs_x27_5301_, v_i_5293_, v_a_5304_);
v_i_5293_ = v___x_5307_;
v_bs_5294_ = v___x_5308_;
v___y_5296_ = v_a_5305_;
goto _start;
}
else
{
lean_object* v_a_5310_; lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5318_; 
lean_dec_ref(v_bs_x27_5301_);
lean_dec(v_formatterName_5291_);
lean_dec_ref(v_f_5290_);
v_a_5310_ = lean_ctor_get(v___y_5303_, 0);
v_a_5311_ = lean_ctor_get(v___y_5303_, 1);
v_isSharedCheck_5318_ = !lean_is_exclusive(v___y_5303_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5313_ = v___y_5303_;
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_inc(v_a_5310_);
lean_dec(v___y_5303_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5318_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
lean_object* v___x_5316_; 
if (v_isShared_5314_ == 0)
{
v___x_5316_ = v___x_5313_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v_a_5310_);
lean_ctor_set(v_reuseFailAlloc_5317_, 1, v_a_5311_);
v___x_5316_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
return v___x_5316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object* v_f_5325_, lean_object* v_formatterName_5326_, lean_object* v_sz_5327_, lean_object* v_i_5328_, lean_object* v_bs_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
size_t v_sz_boxed_5332_; size_t v_i_boxed_5333_; lean_object* v_res_5334_; 
v_sz_boxed_5332_ = lean_unbox_usize(v_sz_5327_);
lean_dec(v_sz_5327_);
v_i_boxed_5333_ = lean_unbox_usize(v_i_5328_);
lean_dec(v_i_5328_);
v_res_5334_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5325_, v_formatterName_5326_, v_sz_boxed_5332_, v_i_boxed_5333_, v_bs_5329_, v___y_5330_, v___y_5331_);
lean_dec_ref(v___y_5330_);
return v_res_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object* v_f_5335_, lean_object* v_formatterName_5336_, lean_object* v_sepArray_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_){
_start:
{
size_t v_sz_5340_; size_t v___x_5341_; lean_object* v___x_5342_; 
v_sz_5340_ = lean_array_size(v_sepArray_5337_);
v___x_5341_ = ((size_t)0ULL);
v___x_5342_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5335_, v_formatterName_5336_, v_sz_5340_, v___x_5341_, v_sepArray_5337_, v_a_5338_, v_a_5339_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
v_a_5344_ = lean_ctor_get(v___x_5342_, 1);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5342_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_inc(v_a_5343_);
lean_dec(v___x_5342_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5343_);
lean_ctor_set(v_reuseFailAlloc_5350_, 1, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5360_; 
v_a_5352_ = lean_ctor_get(v___x_5342_, 0);
v_a_5353_ = lean_ctor_get(v___x_5342_, 1);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5355_ = v___x_5342_;
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_inc(v_a_5352_);
lean_dec(v___x_5342_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5358_; 
if (v_isShared_5356_ == 0)
{
v___x_5358_ = v___x_5355_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5352_);
lean_ctor_set(v_reuseFailAlloc_5359_, 1, v_a_5353_);
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
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object* v_f_5361_, lean_object* v_formatterName_5362_, lean_object* v_sepArray_5363_, lean_object* v_a_5364_, lean_object* v_a_5365_){
_start:
{
lean_object* v_res_5366_; 
v_res_5366_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5361_, v_formatterName_5362_, v_sepArray_5363_, v_a_5364_, v_a_5365_);
lean_dec_ref(v_a_5364_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object* v_sep_5367_, lean_object* v_f_5368_, lean_object* v_formatterName_5369_, lean_object* v_sepArray_5370_, lean_object* v_a_5371_, lean_object* v_a_5372_){
_start:
{
lean_object* v___x_5373_; 
v___x_5373_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5368_, v_formatterName_5369_, v_sepArray_5370_, v_a_5371_, v_a_5372_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object* v_sep_5374_, lean_object* v_f_5375_, lean_object* v_formatterName_5376_, lean_object* v_sepArray_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_){
_start:
{
lean_object* v_res_5380_; 
v_res_5380_ = l_Lean_Fmt_fmtSepArrayWith(v_sep_5374_, v_f_5375_, v_formatterName_5376_, v_sepArray_5377_, v_a_5378_, v_a_5379_);
lean_dec_ref(v_a_5378_);
lean_dec_ref(v_sep_5374_);
return v_res_5380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object* v_f_5381_, lean_object* v_formatterName_5382_, lean_object* v_as_5383_, size_t v_sz_5384_, size_t v_i_5385_, lean_object* v_bs_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5381_, v_formatterName_5382_, v_sz_5384_, v_i_5385_, v_bs_5386_, v___y_5387_, v___y_5388_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object* v_f_5390_, lean_object* v_formatterName_5391_, lean_object* v_as_5392_, lean_object* v_sz_5393_, lean_object* v_i_5394_, lean_object* v_bs_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_){
_start:
{
size_t v_sz_boxed_5398_; size_t v_i_boxed_5399_; lean_object* v_res_5400_; 
v_sz_boxed_5398_ = lean_unbox_usize(v_sz_5393_);
lean_dec(v_sz_5393_);
v_i_boxed_5399_ = lean_unbox_usize(v_i_5394_);
lean_dec(v_i_5394_);
v_res_5400_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(v_f_5390_, v_formatterName_5391_, v_as_5392_, v_sz_boxed_5398_, v_i_boxed_5399_, v_bs_5395_, v___y_5396_, v___y_5397_);
lean_dec_ref(v___y_5396_);
lean_dec_ref(v_as_5392_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object* v_sepArray_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_){
_start:
{
size_t v_sz_5404_; size_t v___x_5405_; lean_object* v___x_5406_; 
v_sz_5404_ = lean_array_size(v_sepArray_5401_);
v___x_5405_ = ((size_t)0ULL);
v___x_5406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5404_, v___x_5405_, v_sepArray_5401_, v_a_5402_, v_a_5403_);
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
v_a_5408_ = lean_ctor_get(v___x_5406_, 1);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5406_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_inc(v_a_5407_);
lean_dec(v___x_5406_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5407_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5424_; 
v_a_5416_ = lean_ctor_get(v___x_5406_, 0);
v_a_5417_ = lean_ctor_get(v___x_5406_, 1);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5419_ = v___x_5406_;
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_inc(v_a_5416_);
lean_dec(v___x_5406_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5424_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5422_; 
if (v_isShared_5420_ == 0)
{
v___x_5422_ = v___x_5419_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_a_5416_);
lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_a_5417_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object* v_sepArray_5425_, lean_object* v_a_5426_, lean_object* v_a_5427_){
_start:
{
lean_object* v_res_5428_; 
v_res_5428_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5425_, v_a_5426_, v_a_5427_);
lean_dec_ref(v_a_5426_);
return v_res_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object* v_ks_5429_, lean_object* v_sep_5430_, lean_object* v_sepArray_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_){
_start:
{
lean_object* v___x_5434_; 
v___x_5434_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5431_, v_a_5432_, v_a_5433_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object* v_ks_5435_, lean_object* v_sep_5436_, lean_object* v_sepArray_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l_Lean_Fmt_fmtTSepArray(v_ks_5435_, v_sep_5436_, v_sepArray_5437_, v_a_5438_, v_a_5439_);
lean_dec_ref(v_a_5438_);
lean_dec_ref(v_sep_5436_);
lean_dec(v_ks_5435_);
return v_res_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object* v_f_5441_, lean_object* v_formatterName_5442_, lean_object* v_sepArray_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_){
_start:
{
size_t v_sz_5446_; size_t v___x_5447_; lean_object* v___x_5448_; 
v_sz_5446_ = lean_array_size(v_sepArray_5443_);
v___x_5447_ = ((size_t)0ULL);
v___x_5448_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5441_, v_formatterName_5442_, v_sz_5446_, v___x_5447_, v_sepArray_5443_, v_a_5444_, v_a_5445_);
if (lean_obj_tag(v___x_5448_) == 0)
{
lean_object* v_a_5449_; lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
v_a_5449_ = lean_ctor_get(v___x_5448_, 0);
v_a_5450_ = lean_ctor_get(v___x_5448_, 1);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5448_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5448_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_inc(v_a_5449_);
lean_dec(v___x_5448_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5449_);
lean_ctor_set(v_reuseFailAlloc_5456_, 1, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
else
{
lean_object* v_a_5458_; lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
v_a_5458_ = lean_ctor_get(v___x_5448_, 0);
v_a_5459_ = lean_ctor_get(v___x_5448_, 1);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5448_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5448_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_inc(v_a_5458_);
lean_dec(v___x_5448_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5464_; 
if (v_isShared_5462_ == 0)
{
v___x_5464_ = v___x_5461_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_a_5458_);
lean_ctor_set(v_reuseFailAlloc_5465_, 1, v_a_5459_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object* v_f_5467_, lean_object* v_formatterName_5468_, lean_object* v_sepArray_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5467_, v_formatterName_5468_, v_sepArray_5469_, v_a_5470_, v_a_5471_);
lean_dec_ref(v_a_5470_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object* v_ks_5473_, lean_object* v_sep_5474_, lean_object* v_f_5475_, lean_object* v_formatterName_5476_, lean_object* v_sepArray_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_){
_start:
{
lean_object* v___x_5480_; 
v___x_5480_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5475_, v_formatterName_5476_, v_sepArray_5477_, v_a_5478_, v_a_5479_);
return v___x_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object* v_ks_5481_, lean_object* v_sep_5482_, lean_object* v_f_5483_, lean_object* v_formatterName_5484_, lean_object* v_sepArray_5485_, lean_object* v_a_5486_, lean_object* v_a_5487_){
_start:
{
lean_object* v_res_5488_; 
v_res_5488_ = l_Lean_Fmt_fmtTSepArrayWith(v_ks_5481_, v_sep_5482_, v_f_5483_, v_formatterName_5484_, v_sepArray_5485_, v_a_5486_, v_a_5487_);
lean_dec_ref(v_a_5486_);
lean_dec_ref(v_sep_5482_);
lean_dec(v_ks_5481_);
return v_res_5488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(uint8_t v___x_5489_, lean_object* v___x_5490_, lean_object* v___x_5491_, lean_object* v___x_5492_, lean_object* v_a_5493_, lean_object* v_b_5494_){
_start:
{
lean_object* v___x_5495_; uint8_t v_decide_5496_; 
v___x_5495_ = lean_nat_sub(v___x_5490_, v___x_5491_);
v_decide_5496_ = lean_nat_dec_eq(v_a_5493_, v___x_5495_);
lean_dec(v___x_5495_);
if (v_decide_5496_ == 0)
{
uint32_t v___x_5497_; lean_object* v___x_5498_; uint32_t v___x_5499_; uint8_t v___x_5500_; 
v___x_5497_ = 10;
v___x_5498_ = lean_nat_add(v___x_5491_, v_a_5493_);
v___x_5499_ = lean_string_utf8_get_fast(v___x_5492_, v___x_5498_);
v___x_5500_ = lean_uint32_dec_eq(v___x_5499_, v___x_5497_);
if (v___x_5500_ == 0)
{
lean_object* v___x_5501_; lean_object* v___x_5502_; 
lean_dec(v_a_5493_);
v___x_5501_ = lean_string_utf8_next_fast(v___x_5492_, v___x_5498_);
lean_dec(v___x_5498_);
v___x_5502_ = lean_nat_sub(v___x_5501_, v___x_5491_);
v_a_5493_ = v___x_5502_;
goto _start;
}
else
{
lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; 
v___x_5504_ = lean_string_utf8_next_fast(v___x_5492_, v___x_5498_);
v___x_5505_ = lean_nat_sub(v___x_5504_, v___x_5498_);
lean_dec(v___x_5498_);
v___x_5506_ = lean_nat_add(v_a_5493_, v___x_5505_);
lean_dec(v___x_5505_);
lean_dec(v_a_5493_);
if (v___x_5489_ == 0)
{
v_a_5493_ = v___x_5506_;
goto _start;
}
else
{
lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5508_ = lean_unsigned_to_nat(1u);
v___x_5509_ = lean_nat_add(v_b_5494_, v___x_5508_);
lean_dec(v_b_5494_);
v_a_5493_ = v___x_5506_;
v_b_5494_ = v___x_5509_;
goto _start;
}
}
}
else
{
lean_dec(v_a_5493_);
return v_b_5494_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___x_5511_, lean_object* v___x_5512_, lean_object* v___x_5513_, lean_object* v___x_5514_, lean_object* v_a_5515_, lean_object* v_b_5516_){
_start:
{
uint8_t v___x_2013__boxed_5517_; lean_object* v_res_5518_; 
v___x_2013__boxed_5517_ = lean_unbox(v___x_5511_);
v_res_5518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_2013__boxed_5517_, v___x_5512_, v___x_5513_, v___x_5514_, v_a_5515_, v_b_5516_);
lean_dec_ref(v___x_5514_);
lean_dec(v___x_5513_);
lean_dec(v___x_5512_);
return v_res_5518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5521_, lean_object* v_minNewlines_5522_, lean_object* v_leadingTk_5523_, lean_object* v_leading_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v___y_5534_; lean_object* v___y_5545_; lean_object* v_str_5547_; lean_object* v_startPos_5548_; lean_object* v_stopPos_5549_; uint8_t v___x_5550_; 
v_str_5547_ = lean_ctor_get(v_leading_5524_, 0);
v_startPos_5548_ = lean_ctor_get(v_leading_5524_, 1);
v_stopPos_5549_ = lean_ctor_get(v_leading_5524_, 2);
v___x_5550_ = lean_string_is_valid_pos(v_str_5547_, v_startPos_5548_);
if (v___x_5550_ == 0)
{
lean_dec(v_minNewlines_5522_);
lean_dec(v_maxNewlines_5521_);
goto v___jp_5527_;
}
else
{
uint8_t v___x_5551_; 
v___x_5551_ = lean_string_is_valid_pos(v_str_5547_, v_stopPos_5549_);
if (v___x_5551_ == 0)
{
lean_dec(v_minNewlines_5522_);
lean_dec(v_maxNewlines_5521_);
goto v___jp_5527_;
}
else
{
uint8_t v___x_5552_; 
v___x_5552_ = lean_nat_dec_le(v_startPos_5548_, v_stopPos_5549_);
if (v___x_5552_ == 0)
{
lean_dec(v_minNewlines_5522_);
lean_dec(v_maxNewlines_5521_);
goto v___jp_5527_;
}
else
{
lean_object* v_searcher_5553_; lean_object* v_numNewlines_5554_; uint8_t v___x_5555_; 
lean_dec(v_leadingTk_5523_);
v_searcher_5553_ = lean_unsigned_to_nat(0u);
v_numNewlines_5554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5552_, v_stopPos_5549_, v_startPos_5548_, v_str_5547_, v_searcher_5553_, v_searcher_5553_);
v___x_5555_ = lean_nat_dec_le(v_numNewlines_5554_, v_minNewlines_5522_);
if (v___x_5555_ == 0)
{
lean_dec(v_minNewlines_5522_);
v___y_5545_ = v_numNewlines_5554_;
goto v___jp_5544_;
}
else
{
lean_dec(v_numNewlines_5554_);
v___y_5545_ = v_minNewlines_5522_;
goto v___jp_5544_;
}
}
}
}
v___jp_5527_:
{
lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5528_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5529_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5530_, 0, v_leadingTk_5523_);
lean_ctor_set(v___x_5530_, 1, v___x_5528_);
lean_ctor_set(v___x_5530_, 2, v___x_5529_);
v___x_5531_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5530_);
v___x_5532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5532_, 0, v___x_5531_);
lean_ctor_set(v___x_5532_, 1, v___y_5526_);
return v___x_5532_;
}
v___jp_5533_:
{
lean_object* v___x_5535_; lean_object* v_nls_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; 
v___x_5535_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5536_ = lean_mk_array(v___y_5534_, v___x_5535_);
v___x_5537_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5536_);
v___x_5538_ = lean_box(0);
v___x_5539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5537_);
lean_ctor_set(v___x_5539_, 1, v___x_5538_);
v___x_5540_ = lean_unsigned_to_nat(1u);
v___x_5541_ = lean_mk_empty_array_with_capacity(v___x_5540_);
v___x_5542_ = lean_array_push(v___x_5541_, v___x_5539_);
v___x_5543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5543_, 0, v___x_5542_);
lean_ctor_set(v___x_5543_, 1, v___y_5526_);
return v___x_5543_;
}
v___jp_5544_:
{
uint8_t v___x_5546_; 
v___x_5546_ = lean_nat_dec_le(v___y_5545_, v_maxNewlines_5521_);
if (v___x_5546_ == 0)
{
lean_dec(v___y_5545_);
v___y_5534_ = v_maxNewlines_5521_;
goto v___jp_5533_;
}
else
{
lean_dec(v_maxNewlines_5521_);
v___y_5534_ = v___y_5545_;
goto v___jp_5533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5556_, lean_object* v_minNewlines_5557_, lean_object* v_leadingTk_5558_, lean_object* v_leading_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_){
_start:
{
lean_object* v_res_5562_; 
v_res_5562_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(v_maxNewlines_5556_, v_minNewlines_5557_, v_leadingTk_5558_, v_leading_5559_, v___y_5560_, v___y_5561_);
lean_dec_ref(v___y_5560_);
lean_dec_ref(v_leading_5559_);
return v_res_5562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object* v_stx_5563_, lean_object* v_minNewlines_5564_, lean_object* v_maxNewlines_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_){
_start:
{
lean_object* v___f_5568_; lean_object* v___x_5569_; 
v___f_5568_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5568_, 0, v_maxNewlines_5565_);
lean_closure_set(v___f_5568_, 1, v_minNewlines_5564_);
v___x_5569_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_5563_, v___f_5568_, v_a_5566_, v_a_5567_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object* v_stx_5570_, lean_object* v_minNewlines_5571_, lean_object* v_maxNewlines_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_){
_start:
{
lean_object* v_res_5575_; 
v_res_5575_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines(v_stx_5570_, v_minNewlines_5571_, v_maxNewlines_5572_, v_a_5573_, v_a_5574_);
lean_dec_ref(v_a_5573_);
return v_res_5575_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(uint8_t v___x_5576_, lean_object* v___x_5577_, lean_object* v___x_5578_, lean_object* v___x_5579_, lean_object* v___x_5580_, lean_object* v_inst_5581_, lean_object* v_R_5582_, lean_object* v_a_5583_, lean_object* v_b_5584_, lean_object* v_c_5585_){
_start:
{
lean_object* v___x_5586_; 
v___x_5586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5576_, v___x_5577_, v___x_5578_, v___x_5580_, v_a_5583_, v_b_5584_);
return v___x_5586_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object* v___x_5587_, lean_object* v___x_5588_, lean_object* v___x_5589_, lean_object* v___x_5590_, lean_object* v___x_5591_, lean_object* v_inst_5592_, lean_object* v_R_5593_, lean_object* v_a_5594_, lean_object* v_b_5595_, lean_object* v_c_5596_){
_start:
{
uint8_t v___x_2122__boxed_5597_; lean_object* v_res_5598_; 
v___x_2122__boxed_5597_ = lean_unbox(v___x_5587_);
v_res_5598_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(v___x_2122__boxed_5597_, v___x_5588_, v___x_5589_, v___x_5590_, v___x_5591_, v_inst_5592_, v_R_5593_, v_a_5594_, v_b_5595_, v_c_5596_);
lean_dec_ref(v___x_5591_);
lean_dec_ref(v___x_5590_);
lean_dec(v___x_5589_);
lean_dec(v___x_5588_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5599_, lean_object* v_minNewlines_5600_, lean_object* v_trailingTk_5601_, lean_object* v_trailing_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
lean_object* v___y_5612_; lean_object* v___y_5623_; lean_object* v_str_5625_; lean_object* v_startPos_5626_; lean_object* v_stopPos_5627_; uint8_t v___x_5628_; 
v_str_5625_ = lean_ctor_get(v_trailing_5602_, 0);
v_startPos_5626_ = lean_ctor_get(v_trailing_5602_, 1);
v_stopPos_5627_ = lean_ctor_get(v_trailing_5602_, 2);
v___x_5628_ = lean_string_is_valid_pos(v_str_5625_, v_startPos_5626_);
if (v___x_5628_ == 0)
{
lean_dec(v_minNewlines_5600_);
lean_dec(v_maxNewlines_5599_);
goto v___jp_5605_;
}
else
{
uint8_t v___x_5629_; 
v___x_5629_ = lean_string_is_valid_pos(v_str_5625_, v_stopPos_5627_);
if (v___x_5629_ == 0)
{
lean_dec(v_minNewlines_5600_);
lean_dec(v_maxNewlines_5599_);
goto v___jp_5605_;
}
else
{
uint8_t v___x_5630_; 
v___x_5630_ = lean_nat_dec_le(v_startPos_5626_, v_stopPos_5627_);
if (v___x_5630_ == 0)
{
lean_dec(v_minNewlines_5600_);
lean_dec(v_maxNewlines_5599_);
goto v___jp_5605_;
}
else
{
lean_object* v_searcher_5631_; lean_object* v_numNewlines_5632_; uint8_t v___x_5633_; 
lean_dec(v_trailingTk_5601_);
v_searcher_5631_ = lean_unsigned_to_nat(0u);
v_numNewlines_5632_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5630_, v_stopPos_5627_, v_startPos_5626_, v_str_5625_, v_searcher_5631_, v_searcher_5631_);
v___x_5633_ = lean_nat_dec_le(v_numNewlines_5632_, v_minNewlines_5600_);
if (v___x_5633_ == 0)
{
lean_dec(v_minNewlines_5600_);
v___y_5623_ = v_numNewlines_5632_;
goto v___jp_5622_;
}
else
{
lean_dec(v_numNewlines_5632_);
v___y_5623_ = v_minNewlines_5600_;
goto v___jp_5622_;
}
}
}
}
v___jp_5605_:
{
lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; lean_object* v___x_5610_; 
v___x_5606_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5607_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5608_, 0, v_trailingTk_5601_);
lean_ctor_set(v___x_5608_, 1, v___x_5606_);
lean_ctor_set(v___x_5608_, 2, v___x_5607_);
v___x_5609_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5609_, 0, v___x_5608_);
v___x_5610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5609_);
lean_ctor_set(v___x_5610_, 1, v___y_5604_);
return v___x_5610_;
}
v___jp_5611_:
{
lean_object* v___x_5613_; lean_object* v_nls_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; 
v___x_5613_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5614_ = lean_mk_array(v___y_5612_, v___x_5613_);
v___x_5615_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5614_);
v___x_5616_ = lean_box(0);
v___x_5617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5615_);
lean_ctor_set(v___x_5617_, 1, v___x_5616_);
v___x_5618_ = lean_unsigned_to_nat(1u);
v___x_5619_ = lean_mk_empty_array_with_capacity(v___x_5618_);
v___x_5620_ = lean_array_push(v___x_5619_, v___x_5617_);
v___x_5621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5620_);
lean_ctor_set(v___x_5621_, 1, v___y_5604_);
return v___x_5621_;
}
v___jp_5622_:
{
uint8_t v___x_5624_; 
v___x_5624_ = lean_nat_dec_le(v___y_5623_, v_maxNewlines_5599_);
if (v___x_5624_ == 0)
{
lean_dec(v___y_5623_);
v___y_5612_ = v_maxNewlines_5599_;
goto v___jp_5611_;
}
else
{
lean_dec(v_maxNewlines_5599_);
v___y_5612_ = v___y_5623_;
goto v___jp_5611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5634_, lean_object* v_minNewlines_5635_, lean_object* v_trailingTk_5636_, lean_object* v_trailing_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(v_maxNewlines_5634_, v_minNewlines_5635_, v_trailingTk_5636_, v_trailing_5637_, v___y_5638_, v___y_5639_);
lean_dec_ref(v___y_5638_);
lean_dec_ref(v_trailing_5637_);
return v_res_5640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object* v_stx_5641_, lean_object* v_minNewlines_5642_, lean_object* v_maxNewlines_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_){
_start:
{
lean_object* v___f_5646_; lean_object* v___x_5647_; 
v___f_5646_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5646_, 0, v_maxNewlines_5643_);
lean_closure_set(v___f_5646_, 1, v_minNewlines_5642_);
v___x_5647_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_5641_, v___f_5646_, v_a_5644_, v_a_5645_);
return v___x_5647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object* v_stx_5648_, lean_object* v_minNewlines_5649_, lean_object* v_maxNewlines_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_){
_start:
{
lean_object* v_res_5653_; 
v_res_5653_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v_stx_5648_, v_minNewlines_5649_, v_maxNewlines_5650_, v_a_5651_, v_a_5652_);
lean_dec_ref(v_a_5651_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object* v_b_5654_, lean_object* v_a_5655_, lean_object* v_trailingDoc_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_){
_start:
{
lean_object* v___y_5660_; uint8_t v___x_5664_; 
v___x_5664_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_5655_);
if (v___x_5664_ == 0)
{
uint8_t v___x_5665_; 
v___x_5665_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_trailingDoc_5656_);
if (v___x_5665_ == 0)
{
lean_object* v_doc_5666_; lean_object* v_doc_5667_; uint8_t v___x_5668_; 
v_doc_5666_ = lean_ctor_get(v_a_5655_, 0);
lean_inc(v_doc_5666_);
lean_dec_ref(v_a_5655_);
v_doc_5667_ = lean_ctor_get(v_trailingDoc_5656_, 0);
lean_inc(v_doc_5667_);
lean_dec_ref(v_trailingDoc_5656_);
v___x_5668_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5666_);
if (v___x_5668_ == 0)
{
uint8_t v___x_5669_; 
v___x_5669_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5667_);
if (v___x_5669_ == 0)
{
lean_object* v___x_5670_; lean_object* v___x_5671_; 
v___x_5670_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_5666_, v_doc_5667_);
v___x_5671_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_5670_);
v___y_5660_ = v___x_5671_;
goto v___jp_5659_;
}
else
{
lean_object* v___x_5672_; 
lean_dec(v_doc_5667_);
v___x_5672_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5666_);
v___y_5660_ = v___x_5672_;
goto v___jp_5659_;
}
}
else
{
lean_object* v___x_5673_; 
lean_dec(v_doc_5666_);
v___x_5673_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5667_);
v___y_5660_ = v___x_5673_;
goto v___jp_5659_;
}
}
else
{
lean_dec_ref(v_trailingDoc_5656_);
v___y_5660_ = v_a_5655_;
goto v___jp_5659_;
}
}
else
{
lean_dec_ref(v_a_5655_);
v___y_5660_ = v_trailingDoc_5656_;
goto v___jp_5659_;
}
v___jp_5659_:
{
lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; 
v___x_5661_ = lean_array_push(v_b_5654_, v___y_5660_);
v___x_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
v___x_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
lean_ctor_set(v___x_5663_, 1, v___y_5658_);
return v___x_5663_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object* v_b_5674_, lean_object* v_a_5675_, lean_object* v_trailingDoc_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_){
_start:
{
lean_object* v_res_5679_; 
v_res_5679_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5674_, v_a_5675_, v_trailingDoc_5676_, v___y_5677_, v___y_5678_);
lean_dec_ref(v___y_5677_);
return v_res_5679_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object* v_upperBound_5680_, lean_object* v_stxs_5681_, lean_object* v___x_5682_, lean_object* v_a_5683_, lean_object* v_b_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_){
_start:
{
uint8_t v___x_5687_; 
v___x_5687_ = lean_nat_dec_lt(v_a_5683_, v_upperBound_5680_);
if (v___x_5687_ == 0)
{
lean_object* v___x_5688_; 
lean_dec(v_a_5683_);
v___x_5688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5688_, 0, v_b_5684_);
lean_ctor_set(v___x_5688_, 1, v___y_5686_);
return v___x_5688_;
}
else
{
lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5689_ = lean_array_fget_borrowed(v_stxs_5681_, v_a_5683_);
lean_inc(v___x_5689_);
v___x_5690_ = l_Lean_Fmt_fmt(v___x_5689_, v___y_5685_, v___y_5686_);
if (lean_obj_tag(v___x_5690_) == 0)
{
lean_object* v_a_5691_; lean_object* v_a_5692_; lean_object* v___x_5693_; lean_object* v___y_5695_; lean_object* v___x_5720_; uint8_t v___x_5721_; 
v_a_5691_ = lean_ctor_get(v___x_5690_, 0);
lean_inc(v_a_5691_);
v_a_5692_ = lean_ctor_get(v___x_5690_, 1);
lean_inc(v_a_5692_);
lean_dec_ref_known(v___x_5690_, 2);
v___x_5693_ = lean_unsigned_to_nat(1u);
v___x_5720_ = lean_nat_sub(v___x_5682_, v___x_5693_);
v___x_5721_ = lean_nat_dec_lt(v_a_5683_, v___x_5720_);
lean_dec(v___x_5720_);
if (v___x_5721_ == 0)
{
lean_object* v___x_5722_; lean_object* v___x_5723_; 
v___x_5722_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5684_, v_a_5691_, v___x_5722_, v___y_5685_, v_a_5692_);
v___y_5695_ = v___x_5723_;
goto v___jp_5694_;
}
else
{
lean_object* v___x_5724_; lean_object* v___x_5725_; 
v___x_5724_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5689_);
v___x_5725_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v___x_5689_, v___x_5693_, v___x_5724_, v___y_5685_, v_a_5692_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v_a_5726_; lean_object* v_a_5727_; lean_object* v___x_5728_; 
v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
lean_inc(v_a_5726_);
v_a_5727_ = lean_ctor_get(v___x_5725_, 1);
lean_inc(v_a_5727_);
lean_dec_ref_known(v___x_5725_, 2);
v___x_5728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5684_, v_a_5691_, v_a_5726_, v___y_5685_, v_a_5727_);
v___y_5695_ = v___x_5728_;
goto v___jp_5694_;
}
else
{
lean_object* v_a_5729_; lean_object* v_a_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5737_; 
lean_dec(v_a_5691_);
lean_dec_ref(v_b_5684_);
lean_dec(v_a_5683_);
v_a_5729_ = lean_ctor_get(v___x_5725_, 0);
v_a_5730_ = lean_ctor_get(v___x_5725_, 1);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5732_ = v___x_5725_;
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_a_5730_);
lean_inc(v_a_5729_);
lean_dec(v___x_5725_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5729_);
lean_ctor_set(v_reuseFailAlloc_5736_, 1, v_a_5730_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
}
v___jp_5694_:
{
if (lean_obj_tag(v___y_5695_) == 0)
{
lean_object* v_a_5696_; 
v_a_5696_ = lean_ctor_get(v___y_5695_, 0);
lean_inc(v_a_5696_);
if (lean_obj_tag(v_a_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5705_; 
lean_dec(v_a_5683_);
v_a_5697_ = lean_ctor_get(v___y_5695_, 1);
v_isSharedCheck_5705_ = !lean_is_exclusive(v___y_5695_);
if (v_isSharedCheck_5705_ == 0)
{
lean_object* v_unused_5706_; 
v_unused_5706_ = lean_ctor_get(v___y_5695_, 0);
lean_dec(v_unused_5706_);
v___x_5699_ = v___y_5695_;
v_isShared_5700_ = v_isSharedCheck_5705_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___y_5695_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5705_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v_a_5701_; lean_object* v___x_5703_; 
v_a_5701_ = lean_ctor_get(v_a_5696_, 0);
lean_inc(v_a_5701_);
lean_dec_ref_known(v_a_5696_, 1);
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 0, v_a_5701_);
v___x_5703_ = v___x_5699_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_a_5701_);
lean_ctor_set(v_reuseFailAlloc_5704_, 1, v_a_5697_);
v___x_5703_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
return v___x_5703_;
}
}
}
else
{
lean_object* v_a_5707_; lean_object* v_a_5708_; lean_object* v___x_5709_; 
v_a_5707_ = lean_ctor_get(v___y_5695_, 1);
lean_inc(v_a_5707_);
lean_dec_ref_known(v___y_5695_, 2);
v_a_5708_ = lean_ctor_get(v_a_5696_, 0);
lean_inc(v_a_5708_);
lean_dec_ref_known(v_a_5696_, 1);
v___x_5709_ = lean_nat_add(v_a_5683_, v___x_5693_);
lean_dec(v_a_5683_);
v_a_5683_ = v___x_5709_;
v_b_5684_ = v_a_5708_;
v___y_5686_ = v_a_5707_;
goto _start;
}
}
else
{
lean_object* v_a_5711_; lean_object* v_a_5712_; lean_object* v___x_5714_; uint8_t v_isShared_5715_; uint8_t v_isSharedCheck_5719_; 
lean_dec(v_a_5683_);
v_a_5711_ = lean_ctor_get(v___y_5695_, 0);
v_a_5712_ = lean_ctor_get(v___y_5695_, 1);
v_isSharedCheck_5719_ = !lean_is_exclusive(v___y_5695_);
if (v_isSharedCheck_5719_ == 0)
{
v___x_5714_ = v___y_5695_;
v_isShared_5715_ = v_isSharedCheck_5719_;
goto v_resetjp_5713_;
}
else
{
lean_inc(v_a_5712_);
lean_inc(v_a_5711_);
lean_dec(v___y_5695_);
v___x_5714_ = lean_box(0);
v_isShared_5715_ = v_isSharedCheck_5719_;
goto v_resetjp_5713_;
}
v_resetjp_5713_:
{
lean_object* v___x_5717_; 
if (v_isShared_5715_ == 0)
{
v___x_5717_ = v___x_5714_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_a_5711_);
lean_ctor_set(v_reuseFailAlloc_5718_, 1, v_a_5712_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
}
}
}
else
{
lean_object* v_a_5738_; lean_object* v_a_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5746_; 
lean_dec_ref(v_b_5684_);
lean_dec(v_a_5683_);
v_a_5738_ = lean_ctor_get(v___x_5690_, 0);
v_a_5739_ = lean_ctor_get(v___x_5690_, 1);
v_isSharedCheck_5746_ = !lean_is_exclusive(v___x_5690_);
if (v_isSharedCheck_5746_ == 0)
{
v___x_5741_ = v___x_5690_;
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_a_5739_);
lean_inc(v_a_5738_);
lean_dec(v___x_5690_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v___x_5744_; 
if (v_isShared_5742_ == 0)
{
v___x_5744_ = v___x_5741_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5738_);
lean_ctor_set(v_reuseFailAlloc_5745_, 1, v_a_5739_);
v___x_5744_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
return v___x_5744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object* v_upperBound_5747_, lean_object* v_stxs_5748_, lean_object* v___x_5749_, lean_object* v_a_5750_, lean_object* v_b_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_){
_start:
{
lean_object* v_res_5754_; 
v_res_5754_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5747_, v_stxs_5748_, v___x_5749_, v_a_5750_, v_b_5751_, v___y_5752_, v___y_5753_);
lean_dec_ref(v___y_5752_);
lean_dec(v___x_5749_);
lean_dec_ref(v_stxs_5748_);
lean_dec(v_upperBound_5747_);
return v_res_5754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object* v_stxs_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_){
_start:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; uint8_t v___x_5762_; 
v___x_5760_ = lean_array_get_size(v_stxs_5757_);
v___x_5761_ = lean_unsigned_to_nat(1u);
v___x_5762_ = lean_nat_dec_eq(v___x_5760_, v___x_5761_);
if (v___x_5762_ == 0)
{
lean_object* v___x_5763_; lean_object* v_acc_5764_; lean_object* v___x_5765_; 
v___x_5763_ = lean_unsigned_to_nat(0u);
v_acc_5764_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_5765_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v___x_5760_, v_stxs_5757_, v___x_5760_, v___x_5763_, v_acc_5764_, v_a_5758_, v_a_5759_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5766_; lean_object* v_a_5767_; lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5775_; 
v_a_5766_ = lean_ctor_get(v___x_5765_, 0);
v_a_5767_ = lean_ctor_get(v___x_5765_, 1);
v_isSharedCheck_5775_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5775_ == 0)
{
v___x_5769_ = v___x_5765_;
v_isShared_5770_ = v_isSharedCheck_5775_;
goto v_resetjp_5768_;
}
else
{
lean_inc(v_a_5767_);
lean_inc(v_a_5766_);
lean_dec(v___x_5765_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5775_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v___x_5771_; lean_object* v___x_5773_; 
v___x_5771_ = l_Lean_Fmt_TaggedDoc_join(v_a_5766_);
if (v_isShared_5770_ == 0)
{
lean_ctor_set(v___x_5769_, 0, v___x_5771_);
v___x_5773_ = v___x_5769_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v___x_5771_);
lean_ctor_set(v_reuseFailAlloc_5774_, 1, v_a_5767_);
v___x_5773_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
return v___x_5773_;
}
}
}
else
{
lean_object* v_a_5776_; lean_object* v_a_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5784_; 
v_a_5776_ = lean_ctor_get(v___x_5765_, 0);
v_a_5777_ = lean_ctor_get(v___x_5765_, 1);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5779_ = v___x_5765_;
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_a_5777_);
lean_inc(v_a_5776_);
lean_dec(v___x_5765_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5780_ == 0)
{
v___x_5782_ = v___x_5779_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5776_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v_a_5777_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
else
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; 
v___x_5785_ = lean_box(0);
v___x_5786_ = lean_unsigned_to_nat(0u);
v___x_5787_ = lean_array_get_borrowed(v___x_5785_, v_stxs_5757_, v___x_5786_);
lean_inc(v___x_5787_);
v___x_5788_ = l_Lean_Fmt_fmt(v___x_5787_, v_a_5758_, v_a_5759_);
return v___x_5788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object* v_stxs_5789_, lean_object* v_a_5790_, lean_object* v_a_5791_){
_start:
{
lean_object* v_res_5792_; 
v_res_5792_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(v_stxs_5789_, v_a_5790_, v_a_5791_);
lean_dec_ref(v_a_5790_);
lean_dec_ref(v_stxs_5789_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object* v_upperBound_5793_, lean_object* v_stxs_5794_, lean_object* v___x_5795_, lean_object* v_inst_5796_, lean_object* v_R_5797_, lean_object* v_a_5798_, lean_object* v_b_5799_, lean_object* v_c_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_){
_start:
{
lean_object* v___x_5803_; 
v___x_5803_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5793_, v_stxs_5794_, v___x_5795_, v_a_5798_, v_b_5799_, v___y_5801_, v___y_5802_);
return v___x_5803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object* v_upperBound_5804_, lean_object* v_stxs_5805_, lean_object* v___x_5806_, lean_object* v_inst_5807_, lean_object* v_R_5808_, lean_object* v_a_5809_, lean_object* v_b_5810_, lean_object* v_c_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(v_upperBound_5804_, v_stxs_5805_, v___x_5806_, v_inst_5807_, v_R_5808_, v_a_5809_, v_b_5810_, v_c_5811_, v___y_5812_, v___y_5813_);
lean_dec_ref(v___y_5812_);
lean_dec(v___x_5806_);
lean_dec_ref(v_stxs_5805_);
lean_dec(v_upperBound_5804_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object* v_comments_5815_, lean_object* v_out_5816_, lean_object* v_a_5817_){
_start:
{
lean_object* v___x_5818_; uint8_t v___x_5819_; 
v___x_5818_ = lean_array_get_size(v_comments_5815_);
v___x_5819_ = lean_nat_dec_lt(v_a_5817_, v___x_5818_);
if (v___x_5819_ == 0)
{
return v_a_5817_;
}
else
{
lean_object* v___x_5820_; lean_object* v_originalWhitespaceRange_5821_; lean_object* v_stop_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; uint8_t v___x_5825_; 
v___x_5820_ = lean_array_fget_borrowed(v_comments_5815_, v_a_5817_);
v_originalWhitespaceRange_5821_ = lean_ctor_get(v___x_5820_, 1);
v_stop_5822_ = lean_ctor_get(v_originalWhitespaceRange_5821_, 1);
v___x_5823_ = lean_unsigned_to_nat(1u);
v___x_5824_ = lean_nat_add(v_out_5816_, v___x_5823_);
v___x_5825_ = lean_nat_dec_le(v___x_5824_, v_stop_5822_);
lean_dec(v___x_5824_);
if (v___x_5825_ == 0)
{
lean_object* v___x_5826_; 
v___x_5826_ = lean_nat_add(v_a_5817_, v___x_5823_);
lean_dec(v_a_5817_);
v_a_5817_ = v___x_5826_;
goto _start;
}
else
{
return v_a_5817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object* v_comments_5828_, lean_object* v_out_5829_, lean_object* v_a_5830_){
_start:
{
lean_object* v_res_5831_; 
v_res_5831_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5828_, v_out_5829_, v_a_5830_);
lean_dec(v_out_5829_);
lean_dec_ref(v_comments_5828_);
return v_res_5831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_5832_, lean_object* v_x_5833_){
_start:
{
if (lean_obj_tag(v_x_5833_) == 0)
{
return v_x_5832_;
}
else
{
lean_object* v_key_5834_; lean_object* v_value_5835_; lean_object* v_tail_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5859_; 
v_key_5834_ = lean_ctor_get(v_x_5833_, 0);
v_value_5835_ = lean_ctor_get(v_x_5833_, 1);
v_tail_5836_ = lean_ctor_get(v_x_5833_, 2);
v_isSharedCheck_5859_ = !lean_is_exclusive(v_x_5833_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5838_ = v_x_5833_;
v_isShared_5839_ = v_isSharedCheck_5859_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_tail_5836_);
lean_inc(v_value_5835_);
lean_inc(v_key_5834_);
lean_dec(v_x_5833_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5859_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5840_; uint64_t v___x_5841_; uint64_t v___x_5842_; uint64_t v___x_5843_; uint64_t v_fold_5844_; uint64_t v___x_5845_; uint64_t v___x_5846_; uint64_t v___x_5847_; size_t v___x_5848_; size_t v___x_5849_; size_t v___x_5850_; size_t v___x_5851_; size_t v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5855_; 
v___x_5840_ = lean_array_get_size(v_x_5832_);
v___x_5841_ = lean_uint64_of_nat(v_key_5834_);
v___x_5842_ = 32ULL;
v___x_5843_ = lean_uint64_shift_right(v___x_5841_, v___x_5842_);
v_fold_5844_ = lean_uint64_xor(v___x_5841_, v___x_5843_);
v___x_5845_ = 16ULL;
v___x_5846_ = lean_uint64_shift_right(v_fold_5844_, v___x_5845_);
v___x_5847_ = lean_uint64_xor(v_fold_5844_, v___x_5846_);
v___x_5848_ = lean_uint64_to_usize(v___x_5847_);
v___x_5849_ = lean_usize_of_nat(v___x_5840_);
v___x_5850_ = ((size_t)1ULL);
v___x_5851_ = lean_usize_sub(v___x_5849_, v___x_5850_);
v___x_5852_ = lean_usize_land(v___x_5848_, v___x_5851_);
v___x_5853_ = lean_array_uget_borrowed(v_x_5832_, v___x_5852_);
lean_inc(v___x_5853_);
if (v_isShared_5839_ == 0)
{
lean_ctor_set(v___x_5838_, 2, v___x_5853_);
v___x_5855_ = v___x_5838_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_key_5834_);
lean_ctor_set(v_reuseFailAlloc_5858_, 1, v_value_5835_);
lean_ctor_set(v_reuseFailAlloc_5858_, 2, v___x_5853_);
v___x_5855_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
lean_object* v___x_5856_; 
v___x_5856_ = lean_array_uset(v_x_5832_, v___x_5852_, v___x_5855_);
v_x_5832_ = v___x_5856_;
v_x_5833_ = v_tail_5836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object* v_i_5860_, lean_object* v_source_5861_, lean_object* v_target_5862_){
_start:
{
lean_object* v___x_5863_; uint8_t v___x_5864_; 
v___x_5863_ = lean_array_get_size(v_source_5861_);
v___x_5864_ = lean_nat_dec_lt(v_i_5860_, v___x_5863_);
if (v___x_5864_ == 0)
{
lean_dec_ref(v_source_5861_);
lean_dec(v_i_5860_);
return v_target_5862_;
}
else
{
lean_object* v_es_5865_; lean_object* v___x_5866_; lean_object* v_source_5867_; lean_object* v_target_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v_es_5865_ = lean_array_fget(v_source_5861_, v_i_5860_);
v___x_5866_ = lean_box(0);
v_source_5867_ = lean_array_fset(v_source_5861_, v_i_5860_, v___x_5866_);
v_target_5868_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_target_5862_, v_es_5865_);
v___x_5869_ = lean_unsigned_to_nat(1u);
v___x_5870_ = lean_nat_add(v_i_5860_, v___x_5869_);
lean_dec(v_i_5860_);
v_i_5860_ = v___x_5870_;
v_source_5861_ = v_source_5867_;
v_target_5862_ = v_target_5868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object* v_data_5872_){
_start:
{
lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v_nbuckets_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; 
v___x_5873_ = lean_array_get_size(v_data_5872_);
v___x_5874_ = lean_unsigned_to_nat(2u);
v_nbuckets_5875_ = lean_nat_mul(v___x_5873_, v___x_5874_);
v___x_5876_ = lean_unsigned_to_nat(0u);
v___x_5877_ = lean_box(0);
v___x_5878_ = lean_mk_array(v_nbuckets_5875_, v___x_5877_);
v___x_5879_ = lean_array_propagate_mark(v_data_5872_, v___x_5878_);
v___x_5880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v___x_5876_, v_data_5872_, v___x_5879_);
return v___x_5880_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object* v_a_5881_, lean_object* v_x_5882_){
_start:
{
if (lean_obj_tag(v_x_5882_) == 0)
{
uint8_t v___x_5883_; 
v___x_5883_ = 0;
return v___x_5883_;
}
else
{
lean_object* v_key_5884_; lean_object* v_tail_5885_; uint8_t v___x_5886_; 
v_key_5884_ = lean_ctor_get(v_x_5882_, 0);
v_tail_5885_ = lean_ctor_get(v_x_5882_, 2);
v___x_5886_ = lean_nat_dec_eq(v_key_5884_, v_a_5881_);
if (v___x_5886_ == 0)
{
v_x_5882_ = v_tail_5885_;
goto _start;
}
else
{
return v___x_5886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object* v_a_5888_, lean_object* v_x_5889_){
_start:
{
uint8_t v_res_5890_; lean_object* v_r_5891_; 
v_res_5890_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5888_, v_x_5889_);
lean_dec(v_x_5889_);
lean_dec(v_a_5888_);
v_r_5891_ = lean_box(v_res_5890_);
return v_r_5891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object* v_x_5894_){
_start:
{
if (lean_obj_tag(v_x_5894_) == 0)
{
lean_object* v___x_5895_; 
v___x_5895_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0));
return v___x_5895_;
}
else
{
lean_object* v_val_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5905_; 
v_val_5896_ = lean_ctor_get(v_x_5894_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v_x_5894_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5898_ = v_x_5894_;
v_isShared_5899_ = v_isSharedCheck_5905_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_val_5896_);
lean_dec(v_x_5894_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5905_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5903_; 
v___x_5900_ = lean_unsigned_to_nat(1u);
v___x_5901_ = lean_nat_add(v_val_5896_, v___x_5900_);
lean_dec(v_val_5896_);
if (v_isShared_5899_ == 0)
{
lean_ctor_set(v___x_5898_, 0, v___x_5901_);
v___x_5903_ = v___x_5898_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v___x_5901_);
v___x_5903_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
return v___x_5903_;
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; 
v___x_5906_ = lean_box(0);
v___x_5907_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5906_);
return v___x_5907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object* v_a_5908_, lean_object* v_x_5909_){
_start:
{
if (lean_obj_tag(v_x_5909_) == 0)
{
lean_object* v___x_5910_; lean_object* v_val_5911_; lean_object* v___x_5912_; 
v___x_5910_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0);
v_val_5911_ = lean_ctor_get(v___x_5910_, 0);
lean_inc(v_val_5911_);
v___x_5912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5912_, 0, v_a_5908_);
lean_ctor_set(v___x_5912_, 1, v_val_5911_);
lean_ctor_set(v___x_5912_, 2, v_x_5909_);
return v___x_5912_;
}
else
{
lean_object* v_key_5913_; lean_object* v_value_5914_; lean_object* v_tail_5915_; lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5930_; 
v_key_5913_ = lean_ctor_get(v_x_5909_, 0);
v_value_5914_ = lean_ctor_get(v_x_5909_, 1);
v_tail_5915_ = lean_ctor_get(v_x_5909_, 2);
v_isSharedCheck_5930_ = !lean_is_exclusive(v_x_5909_);
if (v_isSharedCheck_5930_ == 0)
{
v___x_5917_ = v_x_5909_;
v_isShared_5918_ = v_isSharedCheck_5930_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_tail_5915_);
lean_inc(v_value_5914_);
lean_inc(v_key_5913_);
lean_dec(v_x_5909_);
v___x_5917_ = lean_box(0);
v_isShared_5918_ = v_isSharedCheck_5930_;
goto v_resetjp_5916_;
}
v_resetjp_5916_:
{
uint8_t v___x_5919_; 
v___x_5919_ = lean_nat_dec_eq(v_key_5913_, v_a_5908_);
if (v___x_5919_ == 0)
{
lean_object* v_tail_5920_; lean_object* v___x_5922_; 
v_tail_5920_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5908_, v_tail_5915_);
if (v_isShared_5918_ == 0)
{
lean_ctor_set(v___x_5917_, 2, v_tail_5920_);
v___x_5922_ = v___x_5917_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_key_5913_);
lean_ctor_set(v_reuseFailAlloc_5923_, 1, v_value_5914_);
lean_ctor_set(v_reuseFailAlloc_5923_, 2, v_tail_5920_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
else
{
lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v_val_5926_; lean_object* v___x_5928_; 
lean_dec(v_key_5913_);
v___x_5924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5924_, 0, v_value_5914_);
v___x_5925_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5924_);
v_val_5926_ = lean_ctor_get(v___x_5925_, 0);
lean_inc(v_val_5926_);
lean_dec(v___x_5925_);
if (v_isShared_5918_ == 0)
{
lean_ctor_set(v___x_5917_, 1, v_val_5926_);
lean_ctor_set(v___x_5917_, 0, v_a_5908_);
v___x_5928_ = v___x_5917_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v_a_5908_);
lean_ctor_set(v_reuseFailAlloc_5929_, 1, v_val_5926_);
lean_ctor_set(v_reuseFailAlloc_5929_, 2, v_tail_5915_);
v___x_5928_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
return v___x_5928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object* v_m_5931_, lean_object* v_a_5932_){
_start:
{
lean_object* v_size_5933_; lean_object* v_buckets_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5982_; 
v_size_5933_ = lean_ctor_get(v_m_5931_, 0);
v_buckets_5934_ = lean_ctor_get(v_m_5931_, 1);
v_isSharedCheck_5982_ = !lean_is_exclusive(v_m_5931_);
if (v_isSharedCheck_5982_ == 0)
{
v___x_5936_ = v_m_5931_;
v_isShared_5937_ = v_isSharedCheck_5982_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_buckets_5934_);
lean_inc(v_size_5933_);
lean_dec(v_m_5931_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5982_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
lean_object* v___x_5938_; uint64_t v___x_5939_; uint64_t v___x_5940_; uint64_t v___x_5941_; uint64_t v_fold_5942_; uint64_t v___x_5943_; uint64_t v___x_5944_; uint64_t v___x_5945_; size_t v___x_5946_; size_t v___x_5947_; size_t v___x_5948_; size_t v___x_5949_; size_t v___x_5950_; lean_object* v_bkt_5951_; uint8_t v___x_5952_; 
v___x_5938_ = lean_array_get_size(v_buckets_5934_);
v___x_5939_ = lean_uint64_of_nat(v_a_5932_);
v___x_5940_ = 32ULL;
v___x_5941_ = lean_uint64_shift_right(v___x_5939_, v___x_5940_);
v_fold_5942_ = lean_uint64_xor(v___x_5939_, v___x_5941_);
v___x_5943_ = 16ULL;
v___x_5944_ = lean_uint64_shift_right(v_fold_5942_, v___x_5943_);
v___x_5945_ = lean_uint64_xor(v_fold_5942_, v___x_5944_);
v___x_5946_ = lean_uint64_to_usize(v___x_5945_);
v___x_5947_ = lean_usize_of_nat(v___x_5938_);
v___x_5948_ = ((size_t)1ULL);
v___x_5949_ = lean_usize_sub(v___x_5947_, v___x_5948_);
v___x_5950_ = lean_usize_land(v___x_5946_, v___x_5949_);
v_bkt_5951_ = lean_array_uget_borrowed(v_buckets_5934_, v___x_5950_);
v___x_5952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5932_, v_bkt_5951_);
if (v___x_5952_ == 0)
{
lean_object* v___x_5953_; lean_object* v_size_x27_5954_; lean_object* v___x_5955_; lean_object* v_buckets_x27_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; uint8_t v___x_5962_; 
v___x_5953_ = lean_unsigned_to_nat(1u);
v_size_x27_5954_ = lean_nat_add(v_size_5933_, v___x_5953_);
lean_dec(v_size_5933_);
lean_inc(v_bkt_5951_);
v___x_5955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5955_, 0, v_a_5932_);
lean_ctor_set(v___x_5955_, 1, v___x_5953_);
lean_ctor_set(v___x_5955_, 2, v_bkt_5951_);
v_buckets_x27_5956_ = lean_array_uset(v_buckets_5934_, v___x_5950_, v___x_5955_);
v___x_5957_ = lean_unsigned_to_nat(4u);
v___x_5958_ = lean_nat_mul(v_size_x27_5954_, v___x_5957_);
v___x_5959_ = lean_unsigned_to_nat(3u);
v___x_5960_ = lean_nat_div(v___x_5958_, v___x_5959_);
lean_dec(v___x_5958_);
v___x_5961_ = lean_array_get_size(v_buckets_x27_5956_);
v___x_5962_ = lean_nat_dec_le(v___x_5960_, v___x_5961_);
lean_dec(v___x_5960_);
if (v___x_5962_ == 0)
{
lean_object* v_val_5963_; lean_object* v___x_5965_; 
v_val_5963_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_buckets_x27_5956_);
if (v_isShared_5937_ == 0)
{
lean_ctor_set(v___x_5936_, 1, v_val_5963_);
lean_ctor_set(v___x_5936_, 0, v_size_x27_5954_);
v___x_5965_ = v___x_5936_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v_size_x27_5954_);
lean_ctor_set(v_reuseFailAlloc_5966_, 1, v_val_5963_);
v___x_5965_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
return v___x_5965_;
}
}
else
{
lean_object* v___x_5968_; 
if (v_isShared_5937_ == 0)
{
lean_ctor_set(v___x_5936_, 1, v_buckets_x27_5956_);
lean_ctor_set(v___x_5936_, 0, v_size_x27_5954_);
v___x_5968_ = v___x_5936_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_size_x27_5954_);
lean_ctor_set(v_reuseFailAlloc_5969_, 1, v_buckets_x27_5956_);
v___x_5968_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
return v___x_5968_;
}
}
}
else
{
lean_object* v___x_5970_; lean_object* v_buckets_x27_5971_; lean_object* v_bkt_x27_5972_; lean_object* v___y_5974_; uint8_t v___x_5979_; 
lean_inc(v_bkt_5951_);
v___x_5970_ = lean_box(0);
v_buckets_x27_5971_ = lean_array_uset(v_buckets_5934_, v___x_5950_, v___x_5970_);
lean_inc(v_a_5932_);
v_bkt_x27_5972_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5932_, v_bkt_5951_);
v___x_5979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5932_, v_bkt_x27_5972_);
lean_dec(v_a_5932_);
if (v___x_5979_ == 0)
{
lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5980_ = lean_unsigned_to_nat(1u);
v___x_5981_ = lean_nat_sub(v_size_5933_, v___x_5980_);
lean_dec(v_size_5933_);
v___y_5974_ = v___x_5981_;
goto v___jp_5973_;
}
else
{
v___y_5974_ = v_size_5933_;
goto v___jp_5973_;
}
v___jp_5973_:
{
lean_object* v___x_5975_; lean_object* v___x_5977_; 
v___x_5975_ = lean_array_uset(v_buckets_x27_5971_, v___x_5950_, v_bkt_x27_5972_);
if (v_isShared_5937_ == 0)
{
lean_ctor_set(v___x_5936_, 1, v___x_5975_);
lean_ctor_set(v___x_5936_, 0, v___y_5974_);
v___x_5977_ = v___x_5936_;
goto v_reusejp_5976_;
}
else
{
lean_object* v_reuseFailAlloc_5978_; 
v_reuseFailAlloc_5978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5978_, 0, v___y_5974_);
lean_ctor_set(v_reuseFailAlloc_5978_, 1, v___x_5975_);
v___x_5977_ = v_reuseFailAlloc_5978_;
goto v_reusejp_5976_;
}
v_reusejp_5976_:
{
return v___x_5977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object* v_fst_5983_, lean_object* v___x_5984_, lean_object* v_____r_5985_){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; 
lean_inc(v___x_5984_);
v___x_5986_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(v_fst_5983_, v___x_5984_);
v___x_5987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set(v___x_5987_, 1, v___x_5984_);
v___x_5988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5988_, 0, v___x_5987_);
return v___x_5988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object* v_comments_5989_, lean_object* v_whitespace_5990_, lean_object* v_a_5991_, lean_object* v_b_5992_){
_start:
{
lean_object* v_str_5993_; lean_object* v_startInclusive_5994_; lean_object* v_endExclusive_5995_; lean_object* v___x_5996_; uint8_t v_decide_5997_; 
v_str_5993_ = lean_ctor_get(v_whitespace_5990_, 0);
v_startInclusive_5994_ = lean_ctor_get(v_whitespace_5990_, 1);
v_endExclusive_5995_ = lean_ctor_get(v_whitespace_5990_, 2);
v___x_5996_ = lean_nat_sub(v_endExclusive_5995_, v_startInclusive_5994_);
v_decide_5997_ = lean_nat_dec_eq(v_a_5991_, v___x_5996_);
lean_dec(v___x_5996_);
if (v_decide_5997_ == 0)
{
uint32_t v___x_5998_; lean_object* v___x_5999_; uint32_t v___x_6000_; uint8_t v___x_6001_; 
v___x_5998_ = 10;
v___x_5999_ = lean_nat_add(v_startInclusive_5994_, v_a_5991_);
v___x_6000_ = lean_string_utf8_get_fast(v_str_5993_, v___x_5999_);
v___x_6001_ = lean_uint32_dec_eq(v___x_6000_, v___x_5998_);
if (v___x_6001_ == 0)
{
lean_object* v___x_6002_; lean_object* v___x_6003_; 
lean_dec(v_a_5991_);
v___x_6002_ = lean_string_utf8_next_fast(v_str_5993_, v___x_5999_);
lean_dec(v___x_5999_);
v___x_6003_ = lean_nat_sub(v___x_6002_, v_startInclusive_5994_);
v_a_5991_ = v___x_6003_;
goto _start;
}
else
{
lean_object* v_fst_6005_; lean_object* v_snd_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6032_; 
v_fst_6005_ = lean_ctor_get(v_b_5992_, 0);
v_snd_6006_ = lean_ctor_get(v_b_5992_, 1);
v_isSharedCheck_6032_ = !lean_is_exclusive(v_b_5992_);
if (v_isSharedCheck_6032_ == 0)
{
v___x_6008_ = v_b_5992_;
v_isShared_6009_ = v_isSharedCheck_6032_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_snd_6006_);
lean_inc(v_fst_6005_);
lean_dec(v_b_5992_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6032_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v_val_6014_; lean_object* v___x_6018_; lean_object* v___x_6019_; uint8_t v___x_6020_; 
v___x_6010_ = lean_string_utf8_next_fast(v_str_5993_, v___x_5999_);
v___x_6011_ = lean_nat_sub(v___x_6010_, v___x_5999_);
v___x_6012_ = lean_nat_add(v_a_5991_, v___x_6011_);
lean_dec(v___x_6011_);
lean_dec(v_a_5991_);
v___x_6018_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5989_, v___x_5999_, v_snd_6006_);
v___x_6019_ = lean_array_get_size(v_comments_5989_);
v___x_6020_ = lean_nat_dec_lt(v___x_6018_, v___x_6019_);
if (v___x_6020_ == 0)
{
lean_object* v___x_6021_; lean_object* v___x_6022_; 
lean_del_object(v___x_6008_);
lean_dec(v___x_5999_);
v___x_6021_ = lean_box(0);
v___x_6022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_6005_, v___x_6018_, v___x_6021_);
v_val_6014_ = v___x_6022_;
goto v___jp_6013_;
}
else
{
lean_object* v___x_6023_; lean_object* v_originalWhitespaceRange_6024_; uint8_t v___x_6025_; 
v___x_6023_ = lean_array_fget_borrowed(v_comments_5989_, v___x_6018_);
v_originalWhitespaceRange_6024_ = lean_ctor_get(v___x_6023_, 1);
v___x_6025_ = l_Lean_Syntax_Range_contains(v_originalWhitespaceRange_6024_, v___x_5999_, v_decide_5997_);
lean_dec(v___x_5999_);
if (v___x_6025_ == 0)
{
lean_object* v___x_6026_; lean_object* v___x_6027_; 
lean_del_object(v___x_6008_);
v___x_6026_ = lean_box(0);
v___x_6027_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_6005_, v___x_6018_, v___x_6026_);
v_val_6014_ = v___x_6027_;
goto v___jp_6013_;
}
else
{
lean_object* v___x_6029_; 
if (v_isShared_6009_ == 0)
{
lean_ctor_set(v___x_6008_, 1, v___x_6018_);
v___x_6029_ = v___x_6008_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_fst_6005_);
lean_ctor_set(v_reuseFailAlloc_6031_, 1, v___x_6018_);
v___x_6029_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
v_a_5991_ = v___x_6012_;
v_b_5992_ = v___x_6029_;
goto _start;
}
}
}
v___jp_6013_:
{
if (lean_obj_tag(v_val_6014_) == 0)
{
lean_object* v_a_6015_; 
lean_dec(v___x_6012_);
v_a_6015_ = lean_ctor_get(v_val_6014_, 0);
lean_inc(v_a_6015_);
lean_dec_ref_known(v_val_6014_, 1);
return v_a_6015_;
}
else
{
lean_object* v_a_6016_; 
v_a_6016_ = lean_ctor_get(v_val_6014_, 0);
lean_inc(v_a_6016_);
lean_dec_ref_known(v_val_6014_, 1);
v_a_5991_ = v___x_6012_;
v_b_5992_ = v_a_6016_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_5991_);
return v_b_5992_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object* v_comments_6033_, lean_object* v_whitespace_6034_, lean_object* v_a_6035_, lean_object* v_b_6036_){
_start:
{
lean_object* v_res_6037_; 
v_res_6037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_6033_, v_whitespace_6034_, v_a_6035_, v_b_6036_);
lean_dec_ref(v_whitespace_6034_);
lean_dec_ref(v_comments_6033_);
return v_res_6037_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0(void){
_start:
{
lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6038_ = lean_box(0);
v___x_6039_ = lean_unsigned_to_nat(16u);
v___x_6040_ = lean_mk_array(v___x_6039_, v___x_6038_);
return v___x_6040_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1(void){
_start:
{
lean_object* v___x_6041_; lean_object* v_newlinePositions_6042_; lean_object* v_newlinesBeforeComment_6043_; 
v___x_6041_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0);
v_newlinePositions_6042_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_6043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_newlinesBeforeComment_6043_, 0, v_newlinePositions_6042_);
lean_ctor_set(v_newlinesBeforeComment_6043_, 1, v___x_6041_);
return v_newlinesBeforeComment_6043_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2(void){
_start:
{
lean_object* v_newlinePositions_6044_; lean_object* v_newlinesBeforeComment_6045_; lean_object* v___x_6046_; 
v_newlinePositions_6044_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_6045_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1);
v___x_6046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6046_, 0, v_newlinesBeforeComment_6045_);
lean_ctor_set(v___x_6046_, 1, v_newlinePositions_6044_);
return v___x_6046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object* v_comments_6047_, lean_object* v_whitespace_6048_){
_start:
{
lean_object* v_newlinePositions_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v_fst_6052_; 
v_newlinePositions_6049_ = lean_unsigned_to_nat(0u);
v___x_6050_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2);
v___x_6051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_6047_, v_whitespace_6048_, v_newlinePositions_6049_, v___x_6050_);
v_fst_6052_ = lean_ctor_get(v___x_6051_, 0);
lean_inc(v_fst_6052_);
lean_dec_ref(v___x_6051_);
return v_fst_6052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object* v_comments_6053_, lean_object* v_whitespace_6054_){
_start:
{
lean_object* v_res_6055_; 
v_res_6055_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v_comments_6053_, v_whitespace_6054_);
lean_dec_ref(v_whitespace_6054_);
lean_dec_ref(v_comments_6053_);
return v_res_6055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object* v_comments_6056_, lean_object* v_out_6057_, lean_object* v_inst_6058_, lean_object* v_a_6059_){
_start:
{
lean_object* v___x_6060_; 
v___x_6060_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_6056_, v_out_6057_, v_a_6059_);
return v___x_6060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object* v_comments_6061_, lean_object* v_out_6062_, lean_object* v_inst_6063_, lean_object* v_a_6064_){
_start:
{
lean_object* v_res_6065_; 
v_res_6065_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(v_comments_6061_, v_out_6062_, v_inst_6063_, v_a_6064_);
lean_dec(v_out_6062_);
lean_dec_ref(v_comments_6061_);
return v_res_6065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object* v_comments_6066_, lean_object* v_whitespace_6067_, lean_object* v_inst_6068_, lean_object* v_R_6069_, lean_object* v_a_6070_, lean_object* v_b_6071_, lean_object* v_c_6072_){
_start:
{
lean_object* v___x_6073_; 
v___x_6073_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_6066_, v_whitespace_6067_, v_a_6070_, v_b_6071_);
return v___x_6073_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object* v_comments_6074_, lean_object* v_whitespace_6075_, lean_object* v_inst_6076_, lean_object* v_R_6077_, lean_object* v_a_6078_, lean_object* v_b_6079_, lean_object* v_c_6080_){
_start:
{
lean_object* v_res_6081_; 
v_res_6081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(v_comments_6074_, v_whitespace_6075_, v_inst_6076_, v_R_6077_, v_a_6078_, v_b_6079_, v_c_6080_);
lean_dec_ref(v_whitespace_6075_);
lean_dec_ref(v_comments_6074_);
return v_res_6081_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object* v_00_u03b2_6082_, lean_object* v_a_6083_, lean_object* v_x_6084_){
_start:
{
uint8_t v___x_6085_; 
v___x_6085_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_6083_, v_x_6084_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6086_, lean_object* v_a_6087_, lean_object* v_x_6088_){
_start:
{
uint8_t v_res_6089_; lean_object* v_r_6090_; 
v_res_6089_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(v_00_u03b2_6086_, v_a_6087_, v_x_6088_);
lean_dec(v_x_6088_);
lean_dec(v_a_6087_);
v_r_6090_ = lean_box(v_res_6089_);
return v_r_6090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object* v_00_u03b2_6091_, lean_object* v_data_6092_){
_start:
{
lean_object* v___x_6093_; 
v___x_6093_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_data_6092_);
return v___x_6093_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_6094_, lean_object* v_i_6095_, lean_object* v_source_6096_, lean_object* v_target_6097_){
_start:
{
lean_object* v___x_6098_; 
v___x_6098_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v_i_6095_, v_source_6096_, v_target_6097_);
return v___x_6098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_6099_, lean_object* v_x_6100_, lean_object* v_x_6101_){
_start:
{
lean_object* v___x_6102_; 
v___x_6102_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_x_6100_, v_x_6101_);
return v___x_6102_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_6106_; 
v___x_6106_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0));
return v___x_6106_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___dummy_6107_){
_start:
{
lean_object* v_res_6108_; 
v_res_6108_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v_res_6108_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6109_; 
v___x_6109_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v___x_6109_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object* v_s_6110_){
_start:
{
lean_object* v___x_6111_; 
v___x_6111_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
return v___x_6111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object* v_s_6112_){
_start:
{
lean_object* v_res_6113_; 
v_res_6113_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(v_s_6112_);
lean_dec_ref(v_s_6112_);
return v_res_6113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t v_sz_6114_, size_t v_i_6115_, lean_object* v_bs_6116_){
_start:
{
uint8_t v___x_6117_; 
v___x_6117_ = lean_usize_dec_lt(v_i_6115_, v_sz_6114_);
if (v___x_6117_ == 0)
{
return v_bs_6116_;
}
else
{
lean_object* v_v_6118_; lean_object* v_rendered_6119_; lean_object* v___x_6120_; lean_object* v_bs_x27_6121_; size_t v___x_6122_; size_t v___x_6123_; lean_object* v___x_6124_; 
v_v_6118_ = lean_array_uget_borrowed(v_bs_6116_, v_i_6115_);
v_rendered_6119_ = lean_ctor_get(v_v_6118_, 0);
lean_inc_ref(v_rendered_6119_);
v___x_6120_ = lean_unsigned_to_nat(0u);
v_bs_x27_6121_ = lean_array_uset(v_bs_6116_, v_i_6115_, v___x_6120_);
v___x_6122_ = ((size_t)1ULL);
v___x_6123_ = lean_usize_add(v_i_6115_, v___x_6122_);
v___x_6124_ = lean_array_uset(v_bs_x27_6121_, v_i_6115_, v_rendered_6119_);
v_i_6115_ = v___x_6123_;
v_bs_6116_ = v___x_6124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object* v_sz_6126_, lean_object* v_i_6127_, lean_object* v_bs_6128_){
_start:
{
size_t v_sz_boxed_6129_; size_t v_i_boxed_6130_; lean_object* v_res_6131_; 
v_sz_boxed_6129_ = lean_unbox_usize(v_sz_6126_);
lean_dec(v_sz_6126_);
v_i_boxed_6130_ = lean_unbox_usize(v_i_6127_);
lean_dec(v_i_6127_);
v_res_6131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_boxed_6129_, v_i_boxed_6130_, v_bs_6128_);
return v_res_6131_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; 
v___x_6132_ = lean_box(0);
v___x_6133_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6133_);
lean_ctor_set(v___x_6134_, 1, v___x_6132_);
return v___x_6134_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object* v_upperBound_6135_, lean_object* v_next_6136_, lean_object* v_upperBound_6137_, lean_object* v_a_6138_, lean_object* v_b_6139_){
_start:
{
uint8_t v___x_6140_; 
v___x_6140_ = lean_nat_dec_lt(v_a_6138_, v_upperBound_6135_);
if (v___x_6140_ == 0)
{
lean_dec(v_a_6138_);
return v_b_6139_;
}
else
{
lean_object* v_fst_6141_; lean_object* v___x_6143_; uint8_t v_isShared_6144_; uint8_t v_isSharedCheck_6155_; 
v_fst_6141_ = lean_ctor_get(v_b_6139_, 0);
v_isSharedCheck_6155_ = !lean_is_exclusive(v_b_6139_);
if (v_isSharedCheck_6155_ == 0)
{
lean_object* v_unused_6156_; 
v_unused_6156_ = lean_ctor_get(v_b_6139_, 1);
lean_dec(v_unused_6156_);
v___x_6143_ = v_b_6139_;
v_isShared_6144_ = v_isSharedCheck_6155_;
goto v_resetjp_6142_;
}
else
{
lean_inc(v_fst_6141_);
lean_dec(v_b_6139_);
v___x_6143_ = lean_box(0);
v_isShared_6144_ = v_isSharedCheck_6155_;
goto v_resetjp_6142_;
}
v_resetjp_6142_:
{
uint8_t v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6150_; 
v___x_6145_ = lean_nat_dec_lt(v_next_6136_, v_upperBound_6137_);
v___x_6146_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6147_ = lean_array_push(v_fst_6141_, v___x_6146_);
v___x_6148_ = lean_box(v___x_6145_);
if (v_isShared_6144_ == 0)
{
lean_ctor_set(v___x_6143_, 1, v___x_6148_);
lean_ctor_set(v___x_6143_, 0, v___x_6147_);
v___x_6150_ = v___x_6143_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6154_; 
v_reuseFailAlloc_6154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6154_, 0, v___x_6147_);
lean_ctor_set(v_reuseFailAlloc_6154_, 1, v___x_6148_);
v___x_6150_ = v_reuseFailAlloc_6154_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
lean_object* v___x_6151_; lean_object* v___x_6152_; 
v___x_6151_ = lean_unsigned_to_nat(1u);
v___x_6152_ = lean_nat_add(v_a_6138_, v___x_6151_);
lean_dec(v_a_6138_);
v_a_6138_ = v___x_6152_;
v_b_6139_ = v___x_6150_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object* v_upperBound_6157_, lean_object* v_next_6158_, lean_object* v_upperBound_6159_, lean_object* v_a_6160_, lean_object* v_b_6161_){
_start:
{
lean_object* v_res_6162_; 
v_res_6162_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6157_, v_next_6158_, v_upperBound_6159_, v_a_6160_, v_b_6161_);
lean_dec(v_upperBound_6159_);
lean_dec(v_next_6158_);
lean_dec(v_upperBound_6157_);
return v_res_6162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(lean_object* v_originalWhitespaceRange_6163_, lean_object* v_fst_6164_, lean_object* v_____r_6165_, uint8_t v_insertedAnyNewlines_6166_, lean_object* v_d_6167_){
_start:
{
lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6168_, 0, v_originalWhitespaceRange_6163_);
v___x_6169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6169_, 0, v_d_6167_);
lean_ctor_set(v___x_6169_, 1, v___x_6168_);
v___x_6170_ = lean_array_push(v_fst_6164_, v___x_6169_);
v___x_6171_ = lean_box(v_insertedAnyNewlines_6166_);
v___x_6172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6172_, 0, v___x_6170_);
lean_ctor_set(v___x_6172_, 1, v___x_6171_);
v___x_6173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6172_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed(lean_object* v_originalWhitespaceRange_6174_, lean_object* v_fst_6175_, lean_object* v_____r_6176_, lean_object* v_insertedAnyNewlines_6177_, lean_object* v_d_6178_){
_start:
{
uint8_t v_insertedAnyNewlines_boxed_6179_; lean_object* v_res_6180_; 
v_insertedAnyNewlines_boxed_6179_ = lean_unbox(v_insertedAnyNewlines_6177_);
v_res_6180_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6174_, v_fst_6175_, v_____r_6176_, v_insertedAnyNewlines_boxed_6179_, v_d_6178_);
return v_res_6180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object* v_a_6181_, lean_object* v___x_6182_, lean_object* v___x_6183_, lean_object* v_a_6184_, lean_object* v_b_6185_){
_start:
{
lean_object* v_it_6187_; lean_object* v_startInclusive_6188_; lean_object* v_endExclusive_6189_; 
if (lean_obj_tag(v_a_6184_) == 0)
{
lean_object* v_currPos_6195_; lean_object* v_searcher_6196_; lean_object* v___x_6198_; uint8_t v_isShared_6199_; uint8_t v_isSharedCheck_6219_; 
v_currPos_6195_ = lean_ctor_get(v_a_6184_, 0);
v_searcher_6196_ = lean_ctor_get(v_a_6184_, 1);
v_isSharedCheck_6219_ = !lean_is_exclusive(v_a_6184_);
if (v_isSharedCheck_6219_ == 0)
{
v___x_6198_ = v_a_6184_;
v_isShared_6199_ = v_isSharedCheck_6219_;
goto v_resetjp_6197_;
}
else
{
lean_inc(v_searcher_6196_);
lean_inc(v_currPos_6195_);
lean_dec(v_a_6184_);
v___x_6198_ = lean_box(0);
v_isShared_6199_ = v_isSharedCheck_6219_;
goto v_resetjp_6197_;
}
v_resetjp_6197_:
{
uint8_t v_decide_6200_; 
v_decide_6200_ = lean_nat_dec_eq(v_searcher_6196_, v___x_6183_);
if (v_decide_6200_ == 0)
{
uint32_t v___x_6201_; uint32_t v___x_6202_; uint8_t v___x_6203_; 
v___x_6201_ = 10;
v___x_6202_ = lean_string_utf8_get_fast(v_a_6181_, v_searcher_6196_);
v___x_6203_ = lean_uint32_dec_eq(v___x_6202_, v___x_6201_);
if (v___x_6203_ == 0)
{
lean_object* v___x_6204_; lean_object* v___x_6206_; 
v___x_6204_ = lean_string_utf8_next_fast(v_a_6181_, v_searcher_6196_);
lean_dec(v_searcher_6196_);
if (v_isShared_6199_ == 0)
{
lean_ctor_set(v___x_6198_, 1, v___x_6204_);
v___x_6206_ = v___x_6198_;
goto v_reusejp_6205_;
}
else
{
lean_object* v_reuseFailAlloc_6208_; 
v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_currPos_6195_);
lean_ctor_set(v_reuseFailAlloc_6208_, 1, v___x_6204_);
v___x_6206_ = v_reuseFailAlloc_6208_;
goto v_reusejp_6205_;
}
v_reusejp_6205_:
{
v_a_6184_ = v___x_6206_;
goto _start;
}
}
else
{
lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v_slice_6212_; lean_object* v_nextIt_6214_; 
v___x_6209_ = lean_string_utf8_next_fast(v_a_6181_, v_searcher_6196_);
v___x_6210_ = lean_nat_sub(v___x_6209_, v_searcher_6196_);
v___x_6211_ = lean_nat_add(v_searcher_6196_, v___x_6210_);
lean_dec(v___x_6210_);
v_slice_6212_ = l_String_Slice_subslice_x21(v___x_6182_, v_currPos_6195_, v_searcher_6196_);
lean_inc(v___x_6211_);
if (v_isShared_6199_ == 0)
{
lean_ctor_set(v___x_6198_, 1, v___x_6211_);
lean_ctor_set(v___x_6198_, 0, v___x_6211_);
v_nextIt_6214_ = v___x_6198_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6217_; 
v_reuseFailAlloc_6217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6217_, 0, v___x_6211_);
lean_ctor_set(v_reuseFailAlloc_6217_, 1, v___x_6211_);
v_nextIt_6214_ = v_reuseFailAlloc_6217_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
lean_object* v_startInclusive_6215_; lean_object* v_endExclusive_6216_; 
v_startInclusive_6215_ = lean_ctor_get(v_slice_6212_, 0);
lean_inc(v_startInclusive_6215_);
v_endExclusive_6216_ = lean_ctor_get(v_slice_6212_, 1);
lean_inc(v_endExclusive_6216_);
lean_dec_ref(v_slice_6212_);
v_it_6187_ = v_nextIt_6214_;
v_startInclusive_6188_ = v_startInclusive_6215_;
v_endExclusive_6189_ = v_endExclusive_6216_;
goto v___jp_6186_;
}
}
}
else
{
lean_object* v___x_6218_; 
lean_del_object(v___x_6198_);
lean_dec(v_searcher_6196_);
v___x_6218_ = lean_box(1);
lean_inc(v___x_6183_);
v_it_6187_ = v___x_6218_;
v_startInclusive_6188_ = v_currPos_6195_;
v_endExclusive_6189_ = v___x_6183_;
goto v___jp_6186_;
}
}
}
else
{
lean_dec(v___x_6183_);
lean_dec_ref(v_a_6181_);
return v_b_6185_;
}
v___jp_6186_:
{
lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; 
lean_inc_ref(v_a_6181_);
v___x_6190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6190_, 0, v_a_6181_);
lean_ctor_set(v___x_6190_, 1, v_startInclusive_6188_);
lean_ctor_set(v___x_6190_, 2, v_endExclusive_6189_);
v___x_6191_ = l_String_Slice_toString(v___x_6190_);
lean_dec_ref_known(v___x_6190_, 3);
v___x_6192_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_6191_);
v___x_6193_ = lean_array_push(v_b_6185_, v___x_6192_);
v_a_6184_ = v_it_6187_;
v_b_6185_ = v___x_6193_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object* v_a_6220_, lean_object* v___x_6221_, lean_object* v___x_6222_, lean_object* v_a_6223_, lean_object* v_b_6224_){
_start:
{
lean_object* v_res_6225_; 
v_res_6225_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6220_, v___x_6221_, v___x_6222_, v_a_6223_, v_b_6224_);
lean_dec_ref(v___x_6221_);
return v_res_6225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(size_t v_sz_6226_, size_t v_i_6227_, lean_object* v_bs_6228_){
_start:
{
uint8_t v___x_6229_; 
v___x_6229_ = lean_usize_dec_lt(v_i_6227_, v_sz_6226_);
if (v___x_6229_ == 0)
{
return v_bs_6228_;
}
else
{
lean_object* v_v_6230_; lean_object* v___x_6231_; lean_object* v_bs_x27_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; size_t v___x_6241_; size_t v___x_6242_; lean_object* v___x_6243_; 
v_v_6230_ = lean_array_uget(v_bs_6228_, v_i_6227_);
v___x_6231_ = lean_unsigned_to_nat(0u);
v_bs_x27_6232_ = lean_array_uset(v_bs_6228_, v_i_6227_, v___x_6231_);
v___x_6233_ = lean_string_utf8_byte_size(v_v_6230_);
lean_inc(v_v_6230_);
v___x_6234_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6234_, 0, v_v_6230_);
lean_ctor_set(v___x_6234_, 1, v___x_6231_);
lean_ctor_set(v___x_6234_, 2, v___x_6233_);
v___x_6235_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
v___x_6236_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_6237_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_v_6230_, v___x_6234_, v___x_6233_, v___x_6235_, v___x_6236_);
lean_dec_ref_known(v___x_6234_, 3);
v___x_6238_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_6239_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_6238_, v___x_6237_);
v___x_6240_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6239_);
v___x_6241_ = ((size_t)1ULL);
v___x_6242_ = lean_usize_add(v_i_6227_, v___x_6241_);
v___x_6243_ = lean_array_uset(v_bs_x27_6232_, v_i_6227_, v___x_6240_);
v_i_6227_ = v___x_6242_;
v_bs_6228_ = v___x_6243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg___boxed(lean_object* v_sz_6245_, lean_object* v_i_6246_, lean_object* v_bs_6247_){
_start:
{
size_t v_sz_boxed_6248_; size_t v_i_boxed_6249_; lean_object* v_res_6250_; 
v_sz_boxed_6248_ = lean_unbox_usize(v_sz_6245_);
lean_dec(v_sz_6245_);
v_i_boxed_6249_ = lean_unbox_usize(v_i_6246_);
lean_dec(v_i_6246_);
v_res_6250_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_boxed_6248_, v_i_boxed_6249_, v_bs_6247_);
return v_res_6250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object* v_a_6251_, lean_object* v_x_6252_){
_start:
{
if (lean_obj_tag(v_x_6252_) == 0)
{
lean_object* v___x_6253_; 
v___x_6253_ = lean_box(0);
return v___x_6253_;
}
else
{
lean_object* v_key_6254_; lean_object* v_value_6255_; lean_object* v_tail_6256_; uint8_t v___x_6257_; 
v_key_6254_ = lean_ctor_get(v_x_6252_, 0);
v_value_6255_ = lean_ctor_get(v_x_6252_, 1);
v_tail_6256_ = lean_ctor_get(v_x_6252_, 2);
v___x_6257_ = lean_nat_dec_eq(v_key_6254_, v_a_6251_);
if (v___x_6257_ == 0)
{
v_x_6252_ = v_tail_6256_;
goto _start;
}
else
{
lean_object* v___x_6259_; 
lean_inc(v_value_6255_);
v___x_6259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6259_, 0, v_value_6255_);
return v___x_6259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object* v_a_6260_, lean_object* v_x_6261_){
_start:
{
lean_object* v_res_6262_; 
v_res_6262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6260_, v_x_6261_);
lean_dec(v_x_6261_);
lean_dec(v_a_6260_);
return v_res_6262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object* v_m_6263_, lean_object* v_a_6264_){
_start:
{
lean_object* v_buckets_6265_; lean_object* v___x_6266_; uint64_t v___x_6267_; uint64_t v___x_6268_; uint64_t v___x_6269_; uint64_t v_fold_6270_; uint64_t v___x_6271_; uint64_t v___x_6272_; uint64_t v___x_6273_; size_t v___x_6274_; size_t v___x_6275_; size_t v___x_6276_; size_t v___x_6277_; size_t v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; 
v_buckets_6265_ = lean_ctor_get(v_m_6263_, 1);
v___x_6266_ = lean_array_get_size(v_buckets_6265_);
v___x_6267_ = lean_uint64_of_nat(v_a_6264_);
v___x_6268_ = 32ULL;
v___x_6269_ = lean_uint64_shift_right(v___x_6267_, v___x_6268_);
v_fold_6270_ = lean_uint64_xor(v___x_6267_, v___x_6269_);
v___x_6271_ = 16ULL;
v___x_6272_ = lean_uint64_shift_right(v_fold_6270_, v___x_6271_);
v___x_6273_ = lean_uint64_xor(v_fold_6270_, v___x_6272_);
v___x_6274_ = lean_uint64_to_usize(v___x_6273_);
v___x_6275_ = lean_usize_of_nat(v___x_6266_);
v___x_6276_ = ((size_t)1ULL);
v___x_6277_ = lean_usize_sub(v___x_6275_, v___x_6276_);
v___x_6278_ = lean_usize_land(v___x_6274_, v___x_6277_);
v___x_6279_ = lean_array_uget_borrowed(v_buckets_6265_, v___x_6278_);
v___x_6280_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6264_, v___x_6279_);
return v___x_6280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object* v_m_6281_, lean_object* v_a_6282_){
_start:
{
lean_object* v_res_6283_; 
v_res_6283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6281_, v_a_6282_);
lean_dec(v_a_6282_);
lean_dec_ref(v_m_6281_);
return v_res_6283_;
}
}
static uint8_t _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_6284_; uint8_t v___x_6285_; 
v___x_6284_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6285_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6284_);
return v___x_6285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(lean_object* v_upperBound_6286_, lean_object* v_comments_6287_, lean_object* v_numNewlinesBeforeComments_6288_, lean_object* v_a_6289_, lean_object* v_b_6290_){
_start:
{
lean_object* v___y_6292_; uint8_t v___x_6298_; lean_object* v___y_6300_; lean_object* v___y_6301_; 
v___x_6298_ = lean_nat_dec_lt(v_a_6289_, v_upperBound_6286_);
if (v___x_6298_ == 0)
{
lean_dec(v_a_6289_);
return v_b_6290_;
}
else
{
lean_object* v_fst_6305_; lean_object* v_snd_6306_; lean_object* v___x_6308_; uint8_t v_isShared_6309_; uint8_t v_isSharedCheck_6372_; 
v_fst_6305_ = lean_ctor_get(v_b_6290_, 0);
v_snd_6306_ = lean_ctor_get(v_b_6290_, 1);
v_isSharedCheck_6372_ = !lean_is_exclusive(v_b_6290_);
if (v_isSharedCheck_6372_ == 0)
{
v___x_6308_ = v_b_6290_;
v_isShared_6309_ = v_isSharedCheck_6372_;
goto v_resetjp_6307_;
}
else
{
lean_inc(v_snd_6306_);
lean_inc(v_fst_6305_);
lean_dec(v_b_6290_);
v___x_6308_ = lean_box(0);
v_isShared_6309_ = v_isSharedCheck_6372_;
goto v_resetjp_6307_;
}
v_resetjp_6307_:
{
lean_object* v___x_6310_; lean_object* v___y_6312_; lean_object* v___y_6346_; lean_object* v___y_6347_; lean_object* v___y_6350_; uint8_t v___y_6353_; lean_object* v___y_6354_; uint8_t v___y_6358_; lean_object* v___y_6359_; uint8_t v___y_6363_; uint8_t v_insertedAnyNewlines_6366_; uint8_t v___x_6367_; 
v___x_6310_ = lean_unsigned_to_nat(0u);
v_insertedAnyNewlines_6366_ = 0;
v___x_6367_ = lean_nat_dec_eq(v_a_6289_, v___x_6310_);
if (v___x_6367_ == 0)
{
lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; uint8_t v_kind_6371_; 
v___x_6368_ = lean_unsigned_to_nat(1u);
v___x_6369_ = lean_nat_sub(v_a_6289_, v___x_6368_);
v___x_6370_ = lean_array_fget_borrowed(v_comments_6287_, v___x_6369_);
lean_dec(v___x_6369_);
v_kind_6371_ = lean_ctor_get_uint8(v___x_6370_, sizeof(void*)*3);
if (v_kind_6371_ == 1)
{
v___y_6363_ = v___x_6298_;
goto v___jp_6362_;
}
else
{
v___y_6363_ = v_insertedAnyNewlines_6366_;
goto v___jp_6362_;
}
}
else
{
v___y_6363_ = v_insertedAnyNewlines_6366_;
goto v___jp_6362_;
}
v___jp_6311_:
{
lean_object* v___x_6314_; 
if (v_isShared_6309_ == 0)
{
v___x_6314_ = v___x_6308_;
goto v_reusejp_6313_;
}
else
{
lean_object* v_reuseFailAlloc_6344_; 
v_reuseFailAlloc_6344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6344_, 0, v_fst_6305_);
lean_ctor_set(v_reuseFailAlloc_6344_, 1, v_snd_6306_);
v___x_6314_ = v_reuseFailAlloc_6344_;
goto v_reusejp_6313_;
}
v_reusejp_6313_:
{
lean_object* v___x_6315_; lean_object* v_fst_6316_; lean_object* v_snd_6317_; lean_object* v___x_6318_; lean_object* v___x_6319_; size_t v_sz_6320_; size_t v___x_6321_; lean_object* v___x_6322_; size_t v_sz_6323_; uint8_t v_kind_6324_; lean_object* v_originalWhitespaceRange_6325_; lean_object* v___x_6326_; lean_object* v___f_6327_; lean_object* v___x_6328_; lean_object* v___x_6329_; 
v___x_6315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v___y_6312_, v_a_6289_, v_upperBound_6286_, v___x_6310_, v___x_6314_);
lean_dec(v___y_6312_);
v_fst_6316_ = lean_ctor_get(v___x_6315_, 0);
lean_inc_n(v_fst_6316_, 2);
v_snd_6317_ = lean_ctor_get(v___x_6315_, 1);
lean_inc(v_snd_6317_);
lean_dec_ref(v___x_6315_);
v___x_6318_ = lean_array_fget_borrowed(v_comments_6287_, v_a_6289_);
lean_inc(v___x_6318_);
v___x_6319_ = l_Lean_Fmt_Comment_render(v___x_6318_);
v_sz_6320_ = lean_array_size(v___x_6319_);
v___x_6321_ = ((size_t)0ULL);
v___x_6322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_6320_, v___x_6321_, v___x_6319_);
v_sz_6323_ = lean_array_size(v___x_6322_);
v_kind_6324_ = lean_ctor_get_uint8(v___x_6318_, sizeof(void*)*3);
v_originalWhitespaceRange_6325_ = lean_ctor_get(v___x_6318_, 1);
v___x_6326_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6323_, v___x_6321_, v___x_6322_);
lean_inc_ref(v_originalWhitespaceRange_6325_);
v___f_6327_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_6327_, 0, v_originalWhitespaceRange_6325_);
lean_closure_set(v___f_6327_, 1, v_fst_6316_);
v___x_6328_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_6326_);
v___x_6329_ = l_Lean_Fmt_TaggedDoc_free(v___x_6328_);
if (v_kind_6324_ == 0)
{
lean_object* v___x_6330_; uint8_t v___x_6331_; 
lean_dec(v_snd_6317_);
lean_dec(v_fst_6316_);
v___x_6330_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6331_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6329_);
if (v___x_6331_ == 0)
{
uint8_t v___x_6332_; 
v___x_6332_ = lean_uint8_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0);
if (v___x_6332_ == 0)
{
lean_object* v_doc_6333_; lean_object* v_doc_6334_; uint8_t v___x_6335_; 
v_doc_6333_ = lean_ctor_get(v___x_6329_, 0);
lean_inc(v_doc_6333_);
lean_dec_ref(v___x_6329_);
v_doc_6334_ = lean_ctor_get(v___x_6330_, 0);
v___x_6335_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6333_);
if (v___x_6335_ == 0)
{
uint8_t v___x_6336_; 
v___x_6336_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6334_);
if (v___x_6336_ == 0)
{
lean_object* v___x_6337_; lean_object* v___x_6338_; 
lean_inc(v_doc_6334_);
v___x_6337_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_6333_, v_doc_6334_);
v___x_6338_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6337_);
v___y_6300_ = v___f_6327_;
v___y_6301_ = v___x_6338_;
goto v___jp_6299_;
}
else
{
lean_object* v___x_6339_; 
v___x_6339_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6333_);
v___y_6300_ = v___f_6327_;
v___y_6301_ = v___x_6339_;
goto v___jp_6299_;
}
}
else
{
lean_object* v___x_6340_; 
lean_dec(v_doc_6333_);
lean_inc(v_doc_6334_);
v___x_6340_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6334_);
v___y_6300_ = v___f_6327_;
v___y_6301_ = v___x_6340_;
goto v___jp_6299_;
}
}
else
{
v___y_6300_ = v___f_6327_;
v___y_6301_ = v___x_6329_;
goto v___jp_6299_;
}
}
else
{
lean_dec_ref(v___x_6329_);
v___y_6300_ = v___f_6327_;
v___y_6301_ = v___x_6330_;
goto v___jp_6299_;
}
}
else
{
lean_object* v___x_6341_; uint8_t v___x_6342_; lean_object* v___x_6343_; 
lean_dec_ref(v___f_6327_);
v___x_6341_ = lean_box(0);
v___x_6342_ = lean_unbox(v_snd_6317_);
lean_dec(v_snd_6317_);
lean_inc_ref(v_originalWhitespaceRange_6325_);
v___x_6343_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6325_, v_fst_6316_, v___x_6341_, v___x_6342_, v___x_6329_);
v___y_6292_ = v___x_6343_;
goto v___jp_6291_;
}
}
}
v___jp_6345_:
{
uint8_t v___x_6348_; 
v___x_6348_ = lean_nat_dec_le(v___y_6346_, v___y_6347_);
if (v___x_6348_ == 0)
{
lean_dec(v___y_6346_);
v___y_6312_ = v___y_6347_;
goto v___jp_6311_;
}
else
{
lean_dec(v___y_6347_);
v___y_6312_ = v___y_6346_;
goto v___jp_6311_;
}
}
v___jp_6349_:
{
lean_object* v___x_6351_; 
v___x_6351_ = lean_unsigned_to_nat(2u);
v___y_6346_ = v___y_6350_;
v___y_6347_ = v___x_6351_;
goto v___jp_6345_;
}
v___jp_6352_:
{
uint8_t v___x_6355_; 
v___x_6355_ = lean_nat_dec_eq(v_a_6289_, v___x_6310_);
if (v___x_6355_ == 0)
{
if (v___y_6353_ == 0)
{
lean_object* v___x_6356_; 
v___x_6356_ = lean_unsigned_to_nat(1u);
v___y_6346_ = v___y_6354_;
v___y_6347_ = v___x_6356_;
goto v___jp_6345_;
}
else
{
v___y_6350_ = v___y_6354_;
goto v___jp_6349_;
}
}
else
{
v___y_6350_ = v___y_6354_;
goto v___jp_6349_;
}
}
v___jp_6357_:
{
if (v___y_6358_ == 0)
{
v___y_6353_ = v___y_6358_;
v___y_6354_ = v___y_6359_;
goto v___jp_6352_;
}
else
{
lean_object* v___x_6360_; uint8_t v___x_6361_; 
v___x_6360_ = lean_unsigned_to_nat(1u);
v___x_6361_ = lean_nat_dec_le(v___y_6359_, v___x_6360_);
if (v___x_6361_ == 0)
{
v___y_6353_ = v___y_6358_;
v___y_6354_ = v___y_6359_;
goto v___jp_6352_;
}
else
{
lean_dec(v___y_6359_);
v___y_6353_ = v___y_6358_;
v___y_6354_ = v___x_6360_;
goto v___jp_6352_;
}
}
}
v___jp_6362_:
{
lean_object* v___x_6364_; 
v___x_6364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_numNewlinesBeforeComments_6288_, v_a_6289_);
if (lean_obj_tag(v___x_6364_) == 0)
{
v___y_6358_ = v___y_6363_;
v___y_6359_ = v___x_6310_;
goto v___jp_6357_;
}
else
{
lean_object* v_val_6365_; 
v_val_6365_ = lean_ctor_get(v___x_6364_, 0);
lean_inc(v_val_6365_);
lean_dec_ref_known(v___x_6364_, 1);
v___y_6358_ = v___y_6363_;
v___y_6359_ = v_val_6365_;
goto v___jp_6357_;
}
}
}
}
v___jp_6291_:
{
if (lean_obj_tag(v___y_6292_) == 0)
{
lean_object* v_a_6293_; 
lean_dec(v_a_6289_);
v_a_6293_ = lean_ctor_get(v___y_6292_, 0);
lean_inc(v_a_6293_);
lean_dec_ref_known(v___y_6292_, 1);
return v_a_6293_;
}
else
{
lean_object* v_a_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; 
v_a_6294_ = lean_ctor_get(v___y_6292_, 0);
lean_inc(v_a_6294_);
lean_dec_ref_known(v___y_6292_, 1);
v___x_6295_ = lean_unsigned_to_nat(1u);
v___x_6296_ = lean_nat_add(v_a_6289_, v___x_6295_);
lean_dec(v_a_6289_);
v_a_6289_ = v___x_6296_;
v_b_6290_ = v_a_6294_;
goto _start;
}
}
v___jp_6299_:
{
lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; 
v___x_6302_ = lean_box(0);
v___x_6303_ = lean_box(v___x_6298_);
v___x_6304_ = lean_apply_3(v___y_6300_, v___x_6302_, v___x_6303_, v___y_6301_);
v___y_6292_ = v___x_6304_;
goto v___jp_6291_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___boxed(lean_object* v_upperBound_6373_, lean_object* v_comments_6374_, lean_object* v_numNewlinesBeforeComments_6375_, lean_object* v_a_6376_, lean_object* v_b_6377_){
_start:
{
lean_object* v_res_6378_; 
v_res_6378_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6373_, v_comments_6374_, v_numNewlinesBeforeComments_6375_, v_a_6376_, v_b_6377_);
lean_dec_ref(v_numNewlinesBeforeComments_6375_);
lean_dec_ref(v_comments_6374_);
lean_dec(v_upperBound_6373_);
return v_res_6378_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object* v_upperBound_6379_, lean_object* v_a_6380_, lean_object* v_b_6381_){
_start:
{
uint8_t v___x_6382_; 
v___x_6382_ = lean_nat_dec_lt(v_a_6380_, v_upperBound_6379_);
if (v___x_6382_ == 0)
{
lean_dec(v_a_6380_);
return v_b_6381_;
}
else
{
lean_object* v_fst_6383_; lean_object* v___x_6385_; uint8_t v_isShared_6386_; uint8_t v_isSharedCheck_6396_; 
v_fst_6383_ = lean_ctor_get(v_b_6381_, 0);
v_isSharedCheck_6396_ = !lean_is_exclusive(v_b_6381_);
if (v_isSharedCheck_6396_ == 0)
{
lean_object* v_unused_6397_; 
v_unused_6397_ = lean_ctor_get(v_b_6381_, 1);
lean_dec(v_unused_6397_);
v___x_6385_ = v_b_6381_;
v_isShared_6386_ = v_isSharedCheck_6396_;
goto v_resetjp_6384_;
}
else
{
lean_inc(v_fst_6383_);
lean_dec(v_b_6381_);
v___x_6385_ = lean_box(0);
v_isShared_6386_ = v_isSharedCheck_6396_;
goto v_resetjp_6384_;
}
v_resetjp_6384_:
{
lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; lean_object* v___x_6391_; 
v___x_6387_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6388_ = lean_array_push(v_fst_6383_, v___x_6387_);
v___x_6389_ = lean_box(v___x_6382_);
if (v_isShared_6386_ == 0)
{
lean_ctor_set(v___x_6385_, 1, v___x_6389_);
lean_ctor_set(v___x_6385_, 0, v___x_6388_);
v___x_6391_ = v___x_6385_;
goto v_reusejp_6390_;
}
else
{
lean_object* v_reuseFailAlloc_6395_; 
v_reuseFailAlloc_6395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6395_, 0, v___x_6388_);
lean_ctor_set(v_reuseFailAlloc_6395_, 1, v___x_6389_);
v___x_6391_ = v_reuseFailAlloc_6395_;
goto v_reusejp_6390_;
}
v_reusejp_6390_:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; 
v___x_6392_ = lean_unsigned_to_nat(1u);
v___x_6393_ = lean_nat_add(v_a_6380_, v___x_6392_);
lean_dec(v_a_6380_);
v_a_6380_ = v___x_6393_;
v_b_6381_ = v___x_6391_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object* v_upperBound_6398_, lean_object* v_a_6399_, lean_object* v_b_6400_){
_start:
{
lean_object* v_res_6401_; 
v_res_6401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6398_, v_a_6399_, v_b_6400_);
lean_dec(v_upperBound_6398_);
return v_res_6401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(lean_object* v_as_6402_, size_t v_i_6403_, size_t v_stop_6404_, lean_object* v_b_6405_){
_start:
{
lean_object* v___y_6407_; uint8_t v___x_6411_; 
v___x_6411_ = lean_usize_dec_eq(v_i_6403_, v_stop_6404_);
if (v___x_6411_ == 0)
{
lean_object* v___x_6412_; uint8_t v_placement_6413_; 
v___x_6412_ = lean_array_uget_borrowed(v_as_6402_, v_i_6403_);
v_placement_6413_ = lean_ctor_get_uint8(v___x_6412_, sizeof(void*)*3 + 1);
if (v_placement_6413_ == 0)
{
v___y_6407_ = v_b_6405_;
goto v___jp_6406_;
}
else
{
lean_object* v___x_6414_; 
lean_inc(v___x_6412_);
v___x_6414_ = lean_array_push(v_b_6405_, v___x_6412_);
v___y_6407_ = v___x_6414_;
goto v___jp_6406_;
}
}
else
{
return v_b_6405_;
}
v___jp_6406_:
{
size_t v___x_6408_; size_t v___x_6409_; 
v___x_6408_ = ((size_t)1ULL);
v___x_6409_ = lean_usize_add(v_i_6403_, v___x_6408_);
v_i_6403_ = v___x_6409_;
v_b_6405_ = v___y_6407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8___boxed(lean_object* v_as_6415_, lean_object* v_i_6416_, lean_object* v_stop_6417_, lean_object* v_b_6418_){
_start:
{
size_t v_i_boxed_6419_; size_t v_stop_boxed_6420_; lean_object* v_res_6421_; 
v_i_boxed_6419_ = lean_unbox_usize(v_i_6416_);
lean_dec(v_i_6416_);
v_stop_boxed_6420_ = lean_unbox_usize(v_stop_6417_);
lean_dec(v_stop_6417_);
v_res_6421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_as_6415_, v_i_boxed_6419_, v_stop_boxed_6420_, v_b_6418_);
lean_dec_ref(v_as_6415_);
return v_res_6421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object* v_comments_6428_, lean_object* v_whitespace_6429_, uint8_t v_isLeading_6430_){
_start:
{
lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___y_6434_; lean_object* v___y_6435_; lean_object* v___y_6436_; lean_object* v___y_6449_; lean_object* v___y_6450_; lean_object* v___y_6451_; lean_object* v___y_6452_; lean_object* v___x_6454_; uint8_t v___y_6456_; lean_object* v___y_6457_; lean_object* v___y_6458_; lean_object* v___y_6459_; uint8_t v___y_6465_; lean_object* v___y_6466_; lean_object* v___y_6467_; lean_object* v___y_6468_; lean_object* v___y_6472_; lean_object* v___y_6473_; lean_object* v___y_6474_; uint8_t v___y_6475_; lean_object* v___y_6479_; lean_object* v___x_6492_; uint8_t v___x_6493_; 
v___x_6431_ = l_Lean_Fmt_instInhabitedComment_default;
v___x_6432_ = lean_unsigned_to_nat(0u);
v___x_6454_ = lean_array_get_size(v_comments_6428_);
v___x_6492_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6493_ = lean_nat_dec_lt(v___x_6432_, v___x_6454_);
if (v___x_6493_ == 0)
{
v___y_6479_ = v___x_6492_;
goto v___jp_6478_;
}
else
{
size_t v___x_6494_; size_t v___x_6495_; lean_object* v___x_6496_; 
v___x_6494_ = ((size_t)0ULL);
v___x_6495_ = lean_usize_of_nat(v___x_6454_);
v___x_6496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_comments_6428_, v___x_6494_, v___x_6495_, v___x_6492_);
v___y_6479_ = v___x_6496_;
goto v___jp_6478_;
}
v___jp_6433_:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v_fst_6439_; lean_object* v_snd_6440_; lean_object* v___x_6442_; uint8_t v_isShared_6443_; uint8_t v_isSharedCheck_6447_; 
v___x_6437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6437_, 0, v___y_6434_);
lean_ctor_set(v___x_6437_, 1, v___y_6435_);
v___x_6438_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v___y_6436_, v___x_6432_, v___x_6437_);
lean_dec(v___y_6436_);
v_fst_6439_ = lean_ctor_get(v___x_6438_, 0);
v_snd_6440_ = lean_ctor_get(v___x_6438_, 1);
v_isSharedCheck_6447_ = !lean_is_exclusive(v___x_6438_);
if (v_isSharedCheck_6447_ == 0)
{
v___x_6442_ = v___x_6438_;
v_isShared_6443_ = v_isSharedCheck_6447_;
goto v_resetjp_6441_;
}
else
{
lean_inc(v_snd_6440_);
lean_inc(v_fst_6439_);
lean_dec(v___x_6438_);
v___x_6442_ = lean_box(0);
v_isShared_6443_ = v_isSharedCheck_6447_;
goto v_resetjp_6441_;
}
v_resetjp_6441_:
{
lean_object* v___x_6445_; 
if (v_isShared_6443_ == 0)
{
v___x_6445_ = v___x_6442_;
goto v_reusejp_6444_;
}
else
{
lean_object* v_reuseFailAlloc_6446_; 
v_reuseFailAlloc_6446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_fst_6439_);
lean_ctor_set(v_reuseFailAlloc_6446_, 1, v_snd_6440_);
v___x_6445_ = v_reuseFailAlloc_6446_;
goto v_reusejp_6444_;
}
v_reusejp_6444_:
{
return v___x_6445_;
}
}
}
v___jp_6448_:
{
uint8_t v___x_6453_; 
v___x_6453_ = lean_nat_dec_le(v___y_6449_, v___y_6452_);
if (v___x_6453_ == 0)
{
lean_dec(v___y_6449_);
v___y_6434_ = v___y_6450_;
v___y_6435_ = v___y_6451_;
v___y_6436_ = v___y_6452_;
goto v___jp_6433_;
}
else
{
lean_dec(v___y_6452_);
v___y_6434_ = v___y_6450_;
v___y_6435_ = v___y_6451_;
v___y_6436_ = v___y_6449_;
goto v___jp_6433_;
}
}
v___jp_6455_:
{
uint8_t v___x_6460_; 
v___x_6460_ = lean_nat_dec_eq(v___x_6454_, v___x_6432_);
if (v___x_6460_ == 0)
{
if (v___y_6456_ == 0)
{
lean_object* v___x_6461_; 
v___x_6461_ = lean_unsigned_to_nat(1u);
v___y_6449_ = v___y_6459_;
v___y_6450_ = v___y_6457_;
v___y_6451_ = v___y_6458_;
v___y_6452_ = v___x_6461_;
goto v___jp_6448_;
}
else
{
lean_object* v___x_6462_; 
v___x_6462_ = lean_unsigned_to_nat(2u);
v___y_6449_ = v___y_6459_;
v___y_6450_ = v___y_6457_;
v___y_6451_ = v___y_6458_;
v___y_6452_ = v___x_6462_;
goto v___jp_6448_;
}
}
else
{
if (v_isLeading_6430_ == 0)
{
lean_object* v___x_6463_; 
v___x_6463_ = lean_unsigned_to_nat(2u);
v___y_6449_ = v___y_6459_;
v___y_6450_ = v___y_6457_;
v___y_6451_ = v___y_6458_;
v___y_6452_ = v___x_6463_;
goto v___jp_6448_;
}
else
{
v___y_6449_ = v___y_6459_;
v___y_6450_ = v___y_6457_;
v___y_6451_ = v___y_6458_;
v___y_6452_ = v___x_6432_;
goto v___jp_6448_;
}
}
}
v___jp_6464_:
{
if (v___y_6465_ == 0)
{
v___y_6456_ = v___y_6465_;
v___y_6457_ = v___y_6466_;
v___y_6458_ = v___y_6467_;
v___y_6459_ = v___y_6468_;
goto v___jp_6455_;
}
else
{
lean_object* v___x_6469_; uint8_t v___x_6470_; 
v___x_6469_ = lean_unsigned_to_nat(1u);
v___x_6470_ = lean_nat_dec_le(v___y_6468_, v___x_6469_);
if (v___x_6470_ == 0)
{
v___y_6456_ = v___y_6465_;
v___y_6457_ = v___y_6466_;
v___y_6458_ = v___y_6467_;
v___y_6459_ = v___y_6468_;
goto v___jp_6455_;
}
else
{
lean_dec(v___y_6468_);
v___y_6456_ = v___y_6465_;
v___y_6457_ = v___y_6466_;
v___y_6458_ = v___y_6467_;
v___y_6459_ = v___x_6469_;
goto v___jp_6455_;
}
}
}
v___jp_6471_:
{
lean_object* v___x_6476_; 
v___x_6476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v___y_6472_, v___x_6454_);
lean_dec_ref(v___y_6472_);
if (lean_obj_tag(v___x_6476_) == 0)
{
v___y_6465_ = v___y_6475_;
v___y_6466_ = v___y_6473_;
v___y_6467_ = v___y_6474_;
v___y_6468_ = v___x_6432_;
goto v___jp_6464_;
}
else
{
lean_object* v_val_6477_; 
v_val_6477_ = lean_ctor_get(v___x_6476_, 0);
lean_inc(v_val_6477_);
lean_dec_ref_known(v___x_6476_, 1);
v___y_6465_ = v___y_6475_;
v___y_6466_ = v___y_6473_;
v___y_6467_ = v___y_6474_;
v___y_6468_ = v_val_6477_;
goto v___jp_6464_;
}
}
v___jp_6478_:
{
lean_object* v_numNewlinesBeforeComments_6480_; uint8_t v_insertedAnyNewlines_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v_fst_6484_; lean_object* v_snd_6485_; uint8_t v___x_6486_; 
v_numNewlinesBeforeComments_6480_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v___y_6479_, v_whitespace_6429_);
lean_dec_ref(v___y_6479_);
v_insertedAnyNewlines_6481_ = 0;
v___x_6482_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0));
v___x_6483_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v___x_6454_, v_comments_6428_, v_numNewlinesBeforeComments_6480_, v___x_6432_, v___x_6482_);
v_fst_6484_ = lean_ctor_get(v___x_6483_, 0);
lean_inc(v_fst_6484_);
v_snd_6485_ = lean_ctor_get(v___x_6483_, 1);
lean_inc(v_snd_6485_);
lean_dec_ref(v___x_6483_);
v___x_6486_ = lean_nat_dec_eq(v___x_6454_, v___x_6432_);
if (v___x_6486_ == 0)
{
lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; uint8_t v_kind_6490_; 
v___x_6487_ = lean_unsigned_to_nat(1u);
v___x_6488_ = lean_nat_sub(v___x_6454_, v___x_6487_);
v___x_6489_ = lean_array_get_borrowed(v___x_6431_, v_comments_6428_, v___x_6488_);
lean_dec(v___x_6488_);
v_kind_6490_ = lean_ctor_get_uint8(v___x_6489_, sizeof(void*)*3);
if (v_kind_6490_ == 1)
{
uint8_t v___x_6491_; 
v___x_6491_ = 1;
v___y_6472_ = v_numNewlinesBeforeComments_6480_;
v___y_6473_ = v_fst_6484_;
v___y_6474_ = v_snd_6485_;
v___y_6475_ = v___x_6491_;
goto v___jp_6471_;
}
else
{
v___y_6472_ = v_numNewlinesBeforeComments_6480_;
v___y_6473_ = v_fst_6484_;
v___y_6474_ = v_snd_6485_;
v___y_6475_ = v_insertedAnyNewlines_6481_;
goto v___jp_6471_;
}
}
else
{
v___y_6472_ = v_numNewlinesBeforeComments_6480_;
v___y_6473_ = v_fst_6484_;
v___y_6474_ = v_snd_6485_;
v___y_6475_ = v_insertedAnyNewlines_6481_;
goto v___jp_6471_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object* v_comments_6497_, lean_object* v_whitespace_6498_, lean_object* v_isLeading_6499_){
_start:
{
uint8_t v_isLeading_boxed_6500_; lean_object* v_res_6501_; 
v_isLeading_boxed_6500_ = lean_unbox(v_isLeading_6499_);
v_res_6501_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v_comments_6497_, v_whitespace_6498_, v_isLeading_boxed_6500_);
lean_dec_ref(v_whitespace_6498_);
lean_dec_ref(v_comments_6497_);
return v_res_6501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object* v_a_6502_, lean_object* v___x_6503_, lean_object* v___x_6504_, lean_object* v_inst_6505_, lean_object* v_R_6506_, lean_object* v_a_6507_, lean_object* v_b_6508_){
_start:
{
lean_object* v___x_6509_; 
v___x_6509_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6502_, v___x_6503_, v___x_6504_, v_a_6507_, v_b_6508_);
return v___x_6509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object* v_a_6510_, lean_object* v___x_6511_, lean_object* v___x_6512_, lean_object* v_inst_6513_, lean_object* v_R_6514_, lean_object* v_a_6515_, lean_object* v_b_6516_){
_start:
{
lean_object* v_res_6517_; 
v_res_6517_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(v_a_6510_, v___x_6511_, v___x_6512_, v_inst_6513_, v_R_6514_, v_a_6515_, v_b_6516_);
lean_dec_ref(v___x_6511_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(lean_object* v_as_6518_, size_t v_sz_6519_, size_t v_i_6520_, lean_object* v_bs_6521_){
_start:
{
lean_object* v___x_6522_; 
v___x_6522_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6519_, v_i_6520_, v_bs_6521_);
return v___x_6522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object* v_as_6523_, lean_object* v_sz_6524_, lean_object* v_i_6525_, lean_object* v_bs_6526_){
_start:
{
size_t v_sz_boxed_6527_; size_t v_i_boxed_6528_; lean_object* v_res_6529_; 
v_sz_boxed_6527_ = lean_unbox_usize(v_sz_6524_);
lean_dec(v_sz_6524_);
v_i_boxed_6528_ = lean_unbox_usize(v_i_6525_);
lean_dec(v_i_6525_);
v_res_6529_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(v_as_6523_, v_sz_boxed_6527_, v_i_boxed_6528_, v_bs_6526_);
lean_dec_ref(v_as_6523_);
return v_res_6529_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object* v_upperBound_6530_, lean_object* v_next_6531_, lean_object* v_upperBound_6532_, lean_object* v_inst_6533_, lean_object* v_R_6534_, lean_object* v_a_6535_, lean_object* v_b_6536_, lean_object* v_c_6537_){
_start:
{
lean_object* v___x_6538_; 
v___x_6538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6530_, v_next_6531_, v_upperBound_6532_, v_a_6535_, v_b_6536_);
return v___x_6538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object* v_upperBound_6539_, lean_object* v_next_6540_, lean_object* v_upperBound_6541_, lean_object* v_inst_6542_, lean_object* v_R_6543_, lean_object* v_a_6544_, lean_object* v_b_6545_, lean_object* v_c_6546_){
_start:
{
lean_object* v_res_6547_; 
v_res_6547_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(v_upperBound_6539_, v_next_6540_, v_upperBound_6541_, v_inst_6542_, v_R_6543_, v_a_6544_, v_b_6545_, v_c_6546_);
lean_dec(v_upperBound_6541_);
lean_dec(v_next_6540_);
lean_dec(v_upperBound_6539_);
return v_res_6547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object* v_00_u03b2_6548_, lean_object* v_m_6549_, lean_object* v_a_6550_){
_start:
{
lean_object* v___x_6551_; 
v___x_6551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6549_, v_a_6550_);
return v___x_6551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object* v_00_u03b2_6552_, lean_object* v_m_6553_, lean_object* v_a_6554_){
_start:
{
lean_object* v_res_6555_; 
v_res_6555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(v_00_u03b2_6552_, v_m_6553_, v_a_6554_);
lean_dec(v_a_6554_);
lean_dec_ref(v_m_6553_);
return v_res_6555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object* v_upperBound_6556_, lean_object* v_inst_6557_, lean_object* v_R_6558_, lean_object* v_a_6559_, lean_object* v_b_6560_, lean_object* v_c_6561_){
_start:
{
lean_object* v___x_6562_; 
v___x_6562_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6556_, v_a_6559_, v_b_6560_);
return v___x_6562_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object* v_upperBound_6563_, lean_object* v_inst_6564_, lean_object* v_R_6565_, lean_object* v_a_6566_, lean_object* v_b_6567_, lean_object* v_c_6568_){
_start:
{
lean_object* v_res_6569_; 
v_res_6569_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(v_upperBound_6563_, v_inst_6564_, v_R_6565_, v_a_6566_, v_b_6567_, v_c_6568_);
lean_dec(v_upperBound_6563_);
return v_res_6569_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object* v_upperBound_6570_, lean_object* v_comments_6571_, lean_object* v_numNewlinesBeforeComments_6572_, lean_object* v_inst_6573_, lean_object* v_R_6574_, lean_object* v_a_6575_, lean_object* v_b_6576_, lean_object* v_c_6577_){
_start:
{
lean_object* v___x_6578_; 
v___x_6578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6570_, v_comments_6571_, v_numNewlinesBeforeComments_6572_, v_a_6575_, v_b_6576_);
return v___x_6578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object* v_upperBound_6579_, lean_object* v_comments_6580_, lean_object* v_numNewlinesBeforeComments_6581_, lean_object* v_inst_6582_, lean_object* v_R_6583_, lean_object* v_a_6584_, lean_object* v_b_6585_, lean_object* v_c_6586_){
_start:
{
lean_object* v_res_6587_; 
v_res_6587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_upperBound_6579_, v_comments_6580_, v_numNewlinesBeforeComments_6581_, v_inst_6582_, v_R_6583_, v_a_6584_, v_b_6585_, v_c_6586_);
lean_dec_ref(v_numNewlinesBeforeComments_6581_);
lean_dec_ref(v_comments_6580_);
lean_dec(v_upperBound_6579_);
return v_res_6587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object* v_00_u03b2_6588_, lean_object* v_a_6589_, lean_object* v_x_6590_){
_start:
{
lean_object* v___x_6591_; 
v___x_6591_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6589_, v_x_6590_);
return v___x_6591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object* v_00_u03b2_6592_, lean_object* v_a_6593_, lean_object* v_x_6594_){
_start:
{
lean_object* v_res_6595_; 
v_res_6595_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(v_00_u03b2_6592_, v_a_6593_, v_x_6594_);
lean_dec(v_x_6594_);
lean_dec(v_a_6593_);
return v_res_6595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object* v_leadingTk_6598_, lean_object* v_leading_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_){
_start:
{
uint8_t v___x_6608_; lean_object* v___x_6609_; 
v___x_6608_ = 0;
v___x_6609_ = l_Lean_Syntax_getRange_x3f(v_leadingTk_6598_, v___x_6608_);
if (lean_obj_tag(v___x_6609_) == 1)
{
lean_object* v_val_6610_; lean_object* v_str_6611_; lean_object* v_startPos_6612_; lean_object* v_stopPos_6613_; lean_object* v___x_6615_; uint8_t v_isShared_6616_; uint8_t v_isSharedCheck_6636_; 
v_val_6610_ = lean_ctor_get(v___x_6609_, 0);
lean_inc(v_val_6610_);
lean_dec_ref_known(v___x_6609_, 1);
v_str_6611_ = lean_ctor_get(v_leading_6599_, 0);
v_startPos_6612_ = lean_ctor_get(v_leading_6599_, 1);
v_stopPos_6613_ = lean_ctor_get(v_leading_6599_, 2);
v_isSharedCheck_6636_ = !lean_is_exclusive(v_leading_6599_);
if (v_isSharedCheck_6636_ == 0)
{
v___x_6615_ = v_leading_6599_;
v_isShared_6616_ = v_isSharedCheck_6636_;
goto v_resetjp_6614_;
}
else
{
lean_inc(v_stopPos_6613_);
lean_inc(v_startPos_6612_);
lean_inc(v_str_6611_);
lean_dec(v_leading_6599_);
v___x_6615_ = lean_box(0);
v_isShared_6616_ = v_isSharedCheck_6636_;
goto v_resetjp_6614_;
}
v_resetjp_6614_:
{
uint8_t v___x_6617_; 
v___x_6617_ = lean_string_is_valid_pos(v_str_6611_, v_startPos_6612_);
if (v___x_6617_ == 0)
{
lean_del_object(v___x_6615_);
lean_dec(v_stopPos_6613_);
lean_dec(v_startPos_6612_);
lean_dec_ref(v_str_6611_);
lean_dec(v_val_6610_);
goto v___jp_6602_;
}
else
{
uint8_t v___x_6618_; 
v___x_6618_ = lean_string_is_valid_pos(v_str_6611_, v_stopPos_6613_);
if (v___x_6618_ == 0)
{
lean_del_object(v___x_6615_);
lean_dec(v_stopPos_6613_);
lean_dec(v_startPos_6612_);
lean_dec_ref(v_str_6611_);
lean_dec(v_val_6610_);
goto v___jp_6602_;
}
else
{
uint8_t v___x_6619_; 
v___x_6619_ = lean_nat_dec_le(v_startPos_6612_, v_stopPos_6613_);
if (v___x_6619_ == 0)
{
lean_del_object(v___x_6615_);
lean_dec(v_stopPos_6613_);
lean_dec(v_startPos_6612_);
lean_dec_ref(v_str_6611_);
lean_dec(v_val_6610_);
goto v___jp_6602_;
}
else
{
lean_object* v_lineInfos_6620_; lean_object* v___x_6622_; 
lean_dec(v_leadingTk_6598_);
v_lineInfos_6620_ = lean_ctor_get(v___y_6600_, 4);
if (v_isShared_6616_ == 0)
{
v___x_6622_ = v___x_6615_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6635_; 
v_reuseFailAlloc_6635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6635_, 0, v_str_6611_);
lean_ctor_set(v_reuseFailAlloc_6635_, 1, v_startPos_6612_);
lean_ctor_set(v_reuseFailAlloc_6635_, 2, v_stopPos_6613_);
v___x_6622_ = v_reuseFailAlloc_6635_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
uint8_t v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v_fst_6626_; lean_object* v___x_6628_; uint8_t v_isShared_6629_; uint8_t v_isSharedCheck_6633_; 
v___x_6623_ = 0;
lean_inc_ref(v___x_6622_);
v___x_6624_ = l_Lean_Fmt_parseComments(v_lineInfos_6620_, v_val_6610_, v___x_6623_, v___x_6622_);
v___x_6625_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___x_6624_, v___x_6622_, v___x_6619_);
lean_dec_ref(v___x_6622_);
lean_dec_ref(v___x_6624_);
v_fst_6626_ = lean_ctor_get(v___x_6625_, 0);
v_isSharedCheck_6633_ = !lean_is_exclusive(v___x_6625_);
if (v_isSharedCheck_6633_ == 0)
{
lean_object* v_unused_6634_; 
v_unused_6634_ = lean_ctor_get(v___x_6625_, 1);
lean_dec(v_unused_6634_);
v___x_6628_ = v___x_6625_;
v_isShared_6629_ = v_isSharedCheck_6633_;
goto v_resetjp_6627_;
}
else
{
lean_inc(v_fst_6626_);
lean_dec(v___x_6625_);
v___x_6628_ = lean_box(0);
v_isShared_6629_ = v_isSharedCheck_6633_;
goto v_resetjp_6627_;
}
v_resetjp_6627_:
{
lean_object* v___x_6631_; 
if (v_isShared_6629_ == 0)
{
lean_ctor_set(v___x_6628_, 1, v___y_6601_);
v___x_6631_ = v___x_6628_;
goto v_reusejp_6630_;
}
else
{
lean_object* v_reuseFailAlloc_6632_; 
v_reuseFailAlloc_6632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_fst_6626_);
lean_ctor_set(v_reuseFailAlloc_6632_, 1, v___y_6601_);
v___x_6631_ = v_reuseFailAlloc_6632_;
goto v_reusejp_6630_;
}
v_reusejp_6630_:
{
return v___x_6631_;
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
lean_object* v___x_6637_; lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; 
lean_dec(v___x_6609_);
lean_dec_ref(v_leading_6599_);
v___x_6637_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6638_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6639_, 0, v_leadingTk_6598_);
lean_ctor_set(v___x_6639_, 1, v___x_6637_);
lean_ctor_set(v___x_6639_, 2, v___x_6638_);
v___x_6640_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6640_, 0, v___x_6639_);
v___x_6641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6641_, 0, v___x_6640_);
lean_ctor_set(v___x_6641_, 1, v___y_6601_);
return v___x_6641_;
}
v___jp_6602_:
{
lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; 
v___x_6603_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6604_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6605_, 0, v_leadingTk_6598_);
lean_ctor_set(v___x_6605_, 1, v___x_6603_);
lean_ctor_set(v___x_6605_, 2, v___x_6604_);
v___x_6606_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6606_, 0, v___x_6605_);
v___x_6607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6607_, 0, v___x_6606_);
lean_ctor_set(v___x_6607_, 1, v___y_6601_);
return v___x_6607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_leadingTk_6642_, lean_object* v_leading_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_){
_start:
{
lean_object* v_res_6646_; 
v_res_6646_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(v_leadingTk_6642_, v_leading_6643_, v___y_6644_, v___y_6645_);
lean_dec_ref(v___y_6644_);
return v_res_6646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object* v_stx_6648_, lean_object* v_a_6649_, lean_object* v_a_6650_){
_start:
{
lean_object* v___f_6651_; lean_object* v___x_6652_; 
v___f_6651_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0));
v___x_6652_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_6648_, v___f_6651_, v_a_6649_, v_a_6650_);
return v___x_6652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_){
_start:
{
lean_object* v_res_6656_; 
v_res_6656_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v_stx_6653_, v_a_6654_, v_a_6655_);
lean_dec_ref(v_a_6654_);
return v_res_6656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t v_atleastOneNewline_6657_, lean_object* v_trailingTk_6658_, lean_object* v_trailing_6659_, lean_object* v___y_6660_, lean_object* v___y_6661_){
_start:
{
uint8_t v___x_6668_; lean_object* v___x_6669_; 
v___x_6668_ = 0;
v___x_6669_ = l_Lean_Syntax_getRange_x3f(v_trailingTk_6658_, v___x_6668_);
if (lean_obj_tag(v___x_6669_) == 1)
{
lean_object* v_val_6670_; lean_object* v_str_6671_; lean_object* v_startPos_6672_; lean_object* v_stopPos_6673_; lean_object* v___x_6675_; uint8_t v_isShared_6676_; uint8_t v_isSharedCheck_6727_; 
v_val_6670_ = lean_ctor_get(v___x_6669_, 0);
lean_inc(v_val_6670_);
lean_dec_ref_known(v___x_6669_, 1);
v_str_6671_ = lean_ctor_get(v_trailing_6659_, 0);
v_startPos_6672_ = lean_ctor_get(v_trailing_6659_, 1);
v_stopPos_6673_ = lean_ctor_get(v_trailing_6659_, 2);
v_isSharedCheck_6727_ = !lean_is_exclusive(v_trailing_6659_);
if (v_isSharedCheck_6727_ == 0)
{
v___x_6675_ = v_trailing_6659_;
v_isShared_6676_ = v_isSharedCheck_6727_;
goto v_resetjp_6674_;
}
else
{
lean_inc(v_stopPos_6673_);
lean_inc(v_startPos_6672_);
lean_inc(v_str_6671_);
lean_dec(v_trailing_6659_);
v___x_6675_ = lean_box(0);
v_isShared_6676_ = v_isSharedCheck_6727_;
goto v_resetjp_6674_;
}
v_resetjp_6674_:
{
uint8_t v___x_6677_; 
v___x_6677_ = lean_string_is_valid_pos(v_str_6671_, v_startPos_6672_);
if (v___x_6677_ == 0)
{
lean_del_object(v___x_6675_);
lean_dec(v_stopPos_6673_);
lean_dec(v_startPos_6672_);
lean_dec_ref(v_str_6671_);
lean_dec(v_val_6670_);
goto v___jp_6662_;
}
else
{
uint8_t v___x_6678_; 
v___x_6678_ = lean_string_is_valid_pos(v_str_6671_, v_stopPos_6673_);
if (v___x_6678_ == 0)
{
lean_del_object(v___x_6675_);
lean_dec(v_stopPos_6673_);
lean_dec(v_startPos_6672_);
lean_dec_ref(v_str_6671_);
lean_dec(v_val_6670_);
goto v___jp_6662_;
}
else
{
uint8_t v___x_6679_; 
v___x_6679_ = lean_nat_dec_le(v_startPos_6672_, v_stopPos_6673_);
if (v___x_6679_ == 0)
{
lean_del_object(v___x_6675_);
lean_dec(v_stopPos_6673_);
lean_dec(v_startPos_6672_);
lean_dec_ref(v_str_6671_);
lean_dec(v_val_6670_);
goto v___jp_6662_;
}
else
{
lean_object* v_lineInfos_6680_; lean_object* v___x_6682_; 
lean_dec(v_trailingTk_6658_);
v_lineInfos_6680_ = lean_ctor_get(v___y_6660_, 4);
if (v_isShared_6676_ == 0)
{
v___x_6682_ = v___x_6675_;
goto v_reusejp_6681_;
}
else
{
lean_object* v_reuseFailAlloc_6726_; 
v_reuseFailAlloc_6726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6726_, 0, v_str_6671_);
lean_ctor_set(v_reuseFailAlloc_6726_, 1, v_startPos_6672_);
lean_ctor_set(v_reuseFailAlloc_6726_, 2, v_stopPos_6673_);
v___x_6682_ = v_reuseFailAlloc_6726_;
goto v_reusejp_6681_;
}
v_reusejp_6681_:
{
lean_object* v___y_6684_; uint8_t v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; uint8_t v___x_6722_; 
v___x_6717_ = 1;
lean_inc_ref(v___x_6682_);
v___x_6718_ = l_Lean_Fmt_parseComments(v_lineInfos_6680_, v_val_6670_, v___x_6717_, v___x_6682_);
v___x_6719_ = lean_unsigned_to_nat(0u);
v___x_6720_ = lean_array_get_size(v___x_6718_);
v___x_6721_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6722_ = lean_nat_dec_lt(v___x_6719_, v___x_6720_);
if (v___x_6722_ == 0)
{
lean_dec_ref(v___x_6718_);
v___y_6684_ = v___x_6721_;
goto v___jp_6683_;
}
else
{
size_t v___x_6723_; size_t v___x_6724_; lean_object* v___x_6725_; 
v___x_6723_ = ((size_t)0ULL);
v___x_6724_ = lean_usize_of_nat(v___x_6720_);
v___x_6725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v___x_6718_, v___x_6723_, v___x_6724_, v___x_6721_);
lean_dec_ref(v___x_6718_);
v___y_6684_ = v___x_6725_;
goto v___jp_6683_;
}
v___jp_6683_:
{
lean_object* v___x_6685_; lean_object* v_snd_6686_; uint8_t v___x_6687_; 
v___x_6685_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___y_6684_, v___x_6682_, v___x_6668_);
lean_dec_ref(v___x_6682_);
lean_dec_ref(v___y_6684_);
v_snd_6686_ = lean_ctor_get(v___x_6685_, 1);
v___x_6687_ = lean_unbox(v_snd_6686_);
if (v___x_6687_ == 0)
{
if (v_atleastOneNewline_6657_ == 0)
{
lean_object* v_fst_6688_; lean_object* v___x_6690_; uint8_t v_isShared_6691_; uint8_t v_isSharedCheck_6695_; 
v_fst_6688_ = lean_ctor_get(v___x_6685_, 0);
v_isSharedCheck_6695_ = !lean_is_exclusive(v___x_6685_);
if (v_isSharedCheck_6695_ == 0)
{
lean_object* v_unused_6696_; 
v_unused_6696_ = lean_ctor_get(v___x_6685_, 1);
lean_dec(v_unused_6696_);
v___x_6690_ = v___x_6685_;
v_isShared_6691_ = v_isSharedCheck_6695_;
goto v_resetjp_6689_;
}
else
{
lean_inc(v_fst_6688_);
lean_dec(v___x_6685_);
v___x_6690_ = lean_box(0);
v_isShared_6691_ = v_isSharedCheck_6695_;
goto v_resetjp_6689_;
}
v_resetjp_6689_:
{
lean_object* v___x_6693_; 
if (v_isShared_6691_ == 0)
{
lean_ctor_set(v___x_6690_, 1, v___y_6661_);
v___x_6693_ = v___x_6690_;
goto v_reusejp_6692_;
}
else
{
lean_object* v_reuseFailAlloc_6694_; 
v_reuseFailAlloc_6694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6694_, 0, v_fst_6688_);
lean_ctor_set(v_reuseFailAlloc_6694_, 1, v___y_6661_);
v___x_6693_ = v_reuseFailAlloc_6694_;
goto v_reusejp_6692_;
}
v_reusejp_6692_:
{
return v___x_6693_;
}
}
}
else
{
lean_object* v_fst_6697_; lean_object* v___x_6699_; uint8_t v_isShared_6700_; uint8_t v_isSharedCheck_6706_; 
v_fst_6697_ = lean_ctor_get(v___x_6685_, 0);
v_isSharedCheck_6706_ = !lean_is_exclusive(v___x_6685_);
if (v_isSharedCheck_6706_ == 0)
{
lean_object* v_unused_6707_; 
v_unused_6707_ = lean_ctor_get(v___x_6685_, 1);
lean_dec(v_unused_6707_);
v___x_6699_ = v___x_6685_;
v_isShared_6700_ = v_isSharedCheck_6706_;
goto v_resetjp_6698_;
}
else
{
lean_inc(v_fst_6697_);
lean_dec(v___x_6685_);
v___x_6699_ = lean_box(0);
v_isShared_6700_ = v_isSharedCheck_6706_;
goto v_resetjp_6698_;
}
v_resetjp_6698_:
{
lean_object* v___x_6701_; lean_object* v___x_6702_; lean_object* v___x_6704_; 
v___x_6701_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6702_ = lean_array_push(v_fst_6697_, v___x_6701_);
if (v_isShared_6700_ == 0)
{
lean_ctor_set(v___x_6699_, 1, v___y_6661_);
lean_ctor_set(v___x_6699_, 0, v___x_6702_);
v___x_6704_ = v___x_6699_;
goto v_reusejp_6703_;
}
else
{
lean_object* v_reuseFailAlloc_6705_; 
v_reuseFailAlloc_6705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6705_, 0, v___x_6702_);
lean_ctor_set(v_reuseFailAlloc_6705_, 1, v___y_6661_);
v___x_6704_ = v_reuseFailAlloc_6705_;
goto v_reusejp_6703_;
}
v_reusejp_6703_:
{
return v___x_6704_;
}
}
}
}
else
{
lean_object* v_fst_6708_; lean_object* v___x_6710_; uint8_t v_isShared_6711_; uint8_t v_isSharedCheck_6715_; 
v_fst_6708_ = lean_ctor_get(v___x_6685_, 0);
v_isSharedCheck_6715_ = !lean_is_exclusive(v___x_6685_);
if (v_isSharedCheck_6715_ == 0)
{
lean_object* v_unused_6716_; 
v_unused_6716_ = lean_ctor_get(v___x_6685_, 1);
lean_dec(v_unused_6716_);
v___x_6710_ = v___x_6685_;
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
else
{
lean_inc(v_fst_6708_);
lean_dec(v___x_6685_);
v___x_6710_ = lean_box(0);
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
v_resetjp_6709_:
{
lean_object* v___x_6713_; 
if (v_isShared_6711_ == 0)
{
lean_ctor_set(v___x_6710_, 1, v___y_6661_);
v___x_6713_ = v___x_6710_;
goto v_reusejp_6712_;
}
else
{
lean_object* v_reuseFailAlloc_6714_; 
v_reuseFailAlloc_6714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_fst_6708_);
lean_ctor_set(v_reuseFailAlloc_6714_, 1, v___y_6661_);
v___x_6713_ = v_reuseFailAlloc_6714_;
goto v_reusejp_6712_;
}
v_reusejp_6712_:
{
return v___x_6713_;
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
lean_object* v___x_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; 
lean_dec(v___x_6669_);
lean_dec_ref(v_trailing_6659_);
v___x_6728_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6729_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6730_, 0, v_trailingTk_6658_);
lean_ctor_set(v___x_6730_, 1, v___x_6728_);
lean_ctor_set(v___x_6730_, 2, v___x_6729_);
v___x_6731_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6731_, 0, v___x_6730_);
v___x_6732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6732_, 0, v___x_6731_);
lean_ctor_set(v___x_6732_, 1, v___y_6661_);
return v___x_6732_;
}
v___jp_6662_:
{
lean_object* v___x_6663_; lean_object* v___x_6664_; lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; 
v___x_6663_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6664_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6665_, 0, v_trailingTk_6658_);
lean_ctor_set(v___x_6665_, 1, v___x_6663_);
lean_ctor_set(v___x_6665_, 2, v___x_6664_);
v___x_6666_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6666_, 0, v___x_6665_);
v___x_6667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6667_, 0, v___x_6666_);
lean_ctor_set(v___x_6667_, 1, v___y_6661_);
return v___x_6667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_atleastOneNewline_6733_, lean_object* v_trailingTk_6734_, lean_object* v_trailing_6735_, lean_object* v___y_6736_, lean_object* v___y_6737_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6738_; lean_object* v_res_6739_; 
v_atleastOneNewline_boxed_6738_ = lean_unbox(v_atleastOneNewline_6733_);
v_res_6739_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(v_atleastOneNewline_boxed_6738_, v_trailingTk_6734_, v_trailing_6735_, v___y_6736_, v___y_6737_);
lean_dec_ref(v___y_6736_);
return v_res_6739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object* v_stx_6740_, uint8_t v_atleastOneNewline_6741_, lean_object* v_a_6742_, lean_object* v_a_6743_){
_start:
{
lean_object* v___x_6744_; lean_object* v___f_6745_; lean_object* v___x_6746_; 
v___x_6744_ = lean_box(v_atleastOneNewline_6741_);
v___f_6745_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed), 5, 1);
lean_closure_set(v___f_6745_, 0, v___x_6744_);
v___x_6746_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_6740_, v___f_6745_, v_a_6742_, v_a_6743_);
return v___x_6746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6747_, lean_object* v_atleastOneNewline_6748_, lean_object* v_a_6749_, lean_object* v_a_6750_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6751_; lean_object* v_res_6752_; 
v_atleastOneNewline_boxed_6751_ = lean_unbox(v_atleastOneNewline_6748_);
v_res_6752_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_stx_6747_, v_atleastOneNewline_boxed_6751_, v_a_6749_, v_a_6750_);
lean_dec_ref(v_a_6749_);
return v_res_6752_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object* v_upperBound_6753_, lean_object* v_stxs_6754_, lean_object* v_f_6755_, lean_object* v___x_6756_, lean_object* v_a_6757_, lean_object* v_b_6758_, lean_object* v___y_6759_, lean_object* v___y_6760_){
_start:
{
uint8_t v___x_6761_; 
v___x_6761_ = lean_nat_dec_lt(v_a_6757_, v_upperBound_6753_);
if (v___x_6761_ == 0)
{
lean_object* v___x_6762_; 
lean_dec(v_a_6757_);
lean_dec_ref(v_f_6755_);
v___x_6762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6762_, 0, v_b_6758_);
lean_ctor_set(v___x_6762_, 1, v___y_6760_);
return v___x_6762_;
}
else
{
lean_object* v___x_6763_; lean_object* v___x_6764_; 
v___x_6763_ = lean_array_fget_borrowed(v_stxs_6754_, v_a_6757_);
lean_inc_ref(v_f_6755_);
lean_inc_ref(v___y_6759_);
lean_inc(v___x_6763_);
v___x_6764_ = lean_apply_3(v_f_6755_, v___x_6763_, v___y_6759_, v___y_6760_);
if (lean_obj_tag(v___x_6764_) == 0)
{
lean_object* v_a_6765_; lean_object* v_a_6766_; lean_object* v___x_6767_; lean_object* v___y_6769_; lean_object* v___x_6794_; uint8_t v___x_6795_; 
v_a_6765_ = lean_ctor_get(v___x_6764_, 0);
lean_inc(v_a_6765_);
v_a_6766_ = lean_ctor_get(v___x_6764_, 1);
lean_inc(v_a_6766_);
lean_dec_ref_known(v___x_6764_, 2);
v___x_6767_ = lean_unsigned_to_nat(1u);
v___x_6794_ = lean_nat_sub(v___x_6756_, v___x_6767_);
v___x_6795_ = lean_nat_dec_lt(v_a_6757_, v___x_6794_);
lean_dec(v___x_6794_);
if (v___x_6795_ == 0)
{
lean_object* v___x_6796_; lean_object* v___x_6797_; 
v___x_6796_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_6797_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6758_, v_a_6765_, v___x_6796_, v___y_6759_, v_a_6766_);
v___y_6769_ = v___x_6797_;
goto v___jp_6768_;
}
else
{
lean_object* v___x_6798_; 
lean_inc(v___x_6763_);
v___x_6798_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_6763_, v___x_6795_, v___y_6759_, v_a_6766_);
if (lean_obj_tag(v___x_6798_) == 0)
{
lean_object* v_a_6799_; lean_object* v_a_6800_; lean_object* v___x_6801_; 
v_a_6799_ = lean_ctor_get(v___x_6798_, 0);
lean_inc(v_a_6799_);
v_a_6800_ = lean_ctor_get(v___x_6798_, 1);
lean_inc(v_a_6800_);
lean_dec_ref_known(v___x_6798_, 2);
v___x_6801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6758_, v_a_6765_, v_a_6799_, v___y_6759_, v_a_6800_);
v___y_6769_ = v___x_6801_;
goto v___jp_6768_;
}
else
{
lean_object* v_a_6802_; lean_object* v_a_6803_; lean_object* v___x_6805_; uint8_t v_isShared_6806_; uint8_t v_isSharedCheck_6810_; 
lean_dec(v_a_6765_);
lean_dec_ref(v_b_6758_);
lean_dec(v_a_6757_);
lean_dec_ref(v_f_6755_);
v_a_6802_ = lean_ctor_get(v___x_6798_, 0);
v_a_6803_ = lean_ctor_get(v___x_6798_, 1);
v_isSharedCheck_6810_ = !lean_is_exclusive(v___x_6798_);
if (v_isSharedCheck_6810_ == 0)
{
v___x_6805_ = v___x_6798_;
v_isShared_6806_ = v_isSharedCheck_6810_;
goto v_resetjp_6804_;
}
else
{
lean_inc(v_a_6803_);
lean_inc(v_a_6802_);
lean_dec(v___x_6798_);
v___x_6805_ = lean_box(0);
v_isShared_6806_ = v_isSharedCheck_6810_;
goto v_resetjp_6804_;
}
v_resetjp_6804_:
{
lean_object* v___x_6808_; 
if (v_isShared_6806_ == 0)
{
v___x_6808_ = v___x_6805_;
goto v_reusejp_6807_;
}
else
{
lean_object* v_reuseFailAlloc_6809_; 
v_reuseFailAlloc_6809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6809_, 0, v_a_6802_);
lean_ctor_set(v_reuseFailAlloc_6809_, 1, v_a_6803_);
v___x_6808_ = v_reuseFailAlloc_6809_;
goto v_reusejp_6807_;
}
v_reusejp_6807_:
{
return v___x_6808_;
}
}
}
}
v___jp_6768_:
{
if (lean_obj_tag(v___y_6769_) == 0)
{
lean_object* v_a_6770_; 
v_a_6770_ = lean_ctor_get(v___y_6769_, 0);
lean_inc(v_a_6770_);
if (lean_obj_tag(v_a_6770_) == 0)
{
lean_object* v_a_6771_; lean_object* v___x_6773_; uint8_t v_isShared_6774_; uint8_t v_isSharedCheck_6779_; 
lean_dec(v_a_6757_);
lean_dec_ref(v_f_6755_);
v_a_6771_ = lean_ctor_get(v___y_6769_, 1);
v_isSharedCheck_6779_ = !lean_is_exclusive(v___y_6769_);
if (v_isSharedCheck_6779_ == 0)
{
lean_object* v_unused_6780_; 
v_unused_6780_ = lean_ctor_get(v___y_6769_, 0);
lean_dec(v_unused_6780_);
v___x_6773_ = v___y_6769_;
v_isShared_6774_ = v_isSharedCheck_6779_;
goto v_resetjp_6772_;
}
else
{
lean_inc(v_a_6771_);
lean_dec(v___y_6769_);
v___x_6773_ = lean_box(0);
v_isShared_6774_ = v_isSharedCheck_6779_;
goto v_resetjp_6772_;
}
v_resetjp_6772_:
{
lean_object* v_a_6775_; lean_object* v___x_6777_; 
v_a_6775_ = lean_ctor_get(v_a_6770_, 0);
lean_inc(v_a_6775_);
lean_dec_ref_known(v_a_6770_, 1);
if (v_isShared_6774_ == 0)
{
lean_ctor_set(v___x_6773_, 0, v_a_6775_);
v___x_6777_ = v___x_6773_;
goto v_reusejp_6776_;
}
else
{
lean_object* v_reuseFailAlloc_6778_; 
v_reuseFailAlloc_6778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6778_, 0, v_a_6775_);
lean_ctor_set(v_reuseFailAlloc_6778_, 1, v_a_6771_);
v___x_6777_ = v_reuseFailAlloc_6778_;
goto v_reusejp_6776_;
}
v_reusejp_6776_:
{
return v___x_6777_;
}
}
}
else
{
lean_object* v_a_6781_; lean_object* v_a_6782_; lean_object* v___x_6783_; 
v_a_6781_ = lean_ctor_get(v___y_6769_, 1);
lean_inc(v_a_6781_);
lean_dec_ref_known(v___y_6769_, 2);
v_a_6782_ = lean_ctor_get(v_a_6770_, 0);
lean_inc(v_a_6782_);
lean_dec_ref_known(v_a_6770_, 1);
v___x_6783_ = lean_nat_add(v_a_6757_, v___x_6767_);
lean_dec(v_a_6757_);
v_a_6757_ = v___x_6783_;
v_b_6758_ = v_a_6782_;
v___y_6760_ = v_a_6781_;
goto _start;
}
}
else
{
lean_object* v_a_6785_; lean_object* v_a_6786_; lean_object* v___x_6788_; uint8_t v_isShared_6789_; uint8_t v_isSharedCheck_6793_; 
lean_dec(v_a_6757_);
lean_dec_ref(v_f_6755_);
v_a_6785_ = lean_ctor_get(v___y_6769_, 0);
v_a_6786_ = lean_ctor_get(v___y_6769_, 1);
v_isSharedCheck_6793_ = !lean_is_exclusive(v___y_6769_);
if (v_isSharedCheck_6793_ == 0)
{
v___x_6788_ = v___y_6769_;
v_isShared_6789_ = v_isSharedCheck_6793_;
goto v_resetjp_6787_;
}
else
{
lean_inc(v_a_6786_);
lean_inc(v_a_6785_);
lean_dec(v___y_6769_);
v___x_6788_ = lean_box(0);
v_isShared_6789_ = v_isSharedCheck_6793_;
goto v_resetjp_6787_;
}
v_resetjp_6787_:
{
lean_object* v___x_6791_; 
if (v_isShared_6789_ == 0)
{
v___x_6791_ = v___x_6788_;
goto v_reusejp_6790_;
}
else
{
lean_object* v_reuseFailAlloc_6792_; 
v_reuseFailAlloc_6792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6792_, 0, v_a_6785_);
lean_ctor_set(v_reuseFailAlloc_6792_, 1, v_a_6786_);
v___x_6791_ = v_reuseFailAlloc_6792_;
goto v_reusejp_6790_;
}
v_reusejp_6790_:
{
return v___x_6791_;
}
}
}
}
}
else
{
lean_object* v_a_6811_; lean_object* v_a_6812_; lean_object* v___x_6814_; uint8_t v_isShared_6815_; uint8_t v_isSharedCheck_6819_; 
lean_dec_ref(v_b_6758_);
lean_dec(v_a_6757_);
lean_dec_ref(v_f_6755_);
v_a_6811_ = lean_ctor_get(v___x_6764_, 0);
v_a_6812_ = lean_ctor_get(v___x_6764_, 1);
v_isSharedCheck_6819_ = !lean_is_exclusive(v___x_6764_);
if (v_isSharedCheck_6819_ == 0)
{
v___x_6814_ = v___x_6764_;
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
else
{
lean_inc(v_a_6812_);
lean_inc(v_a_6811_);
lean_dec(v___x_6764_);
v___x_6814_ = lean_box(0);
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
v_resetjp_6813_:
{
lean_object* v___x_6817_; 
if (v_isShared_6815_ == 0)
{
v___x_6817_ = v___x_6814_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v_a_6811_);
lean_ctor_set(v_reuseFailAlloc_6818_, 1, v_a_6812_);
v___x_6817_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
return v___x_6817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object* v_upperBound_6820_, lean_object* v_stxs_6821_, lean_object* v_f_6822_, lean_object* v___x_6823_, lean_object* v_a_6824_, lean_object* v_b_6825_, lean_object* v___y_6826_, lean_object* v___y_6827_){
_start:
{
lean_object* v_res_6828_; 
v_res_6828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6820_, v_stxs_6821_, v_f_6822_, v___x_6823_, v_a_6824_, v_b_6825_, v___y_6826_, v___y_6827_);
lean_dec_ref(v___y_6826_);
lean_dec(v___x_6823_);
lean_dec_ref(v_stxs_6821_);
lean_dec(v_upperBound_6820_);
return v_res_6828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object* v_f_6829_, lean_object* v_stxs_6830_, lean_object* v_a_6831_, lean_object* v_a_6832_){
_start:
{
lean_object* v___x_6833_; lean_object* v___x_6834_; uint8_t v___x_6835_; 
v___x_6833_ = lean_array_get_size(v_stxs_6830_);
v___x_6834_ = lean_unsigned_to_nat(1u);
v___x_6835_ = lean_nat_dec_eq(v___x_6833_, v___x_6834_);
if (v___x_6835_ == 0)
{
lean_object* v___x_6836_; lean_object* v_acc_6837_; lean_object* v___x_6838_; 
v___x_6836_ = lean_unsigned_to_nat(0u);
v_acc_6837_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_6838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v___x_6833_, v_stxs_6830_, v_f_6829_, v___x_6833_, v___x_6836_, v_acc_6837_, v_a_6831_, v_a_6832_);
if (lean_obj_tag(v___x_6838_) == 0)
{
lean_object* v_a_6839_; lean_object* v_a_6840_; lean_object* v___x_6842_; uint8_t v_isShared_6843_; uint8_t v_isSharedCheck_6848_; 
v_a_6839_ = lean_ctor_get(v___x_6838_, 0);
v_a_6840_ = lean_ctor_get(v___x_6838_, 1);
v_isSharedCheck_6848_ = !lean_is_exclusive(v___x_6838_);
if (v_isSharedCheck_6848_ == 0)
{
v___x_6842_ = v___x_6838_;
v_isShared_6843_ = v_isSharedCheck_6848_;
goto v_resetjp_6841_;
}
else
{
lean_inc(v_a_6840_);
lean_inc(v_a_6839_);
lean_dec(v___x_6838_);
v___x_6842_ = lean_box(0);
v_isShared_6843_ = v_isSharedCheck_6848_;
goto v_resetjp_6841_;
}
v_resetjp_6841_:
{
lean_object* v___x_6844_; lean_object* v___x_6846_; 
v___x_6844_ = l_Lean_Fmt_TaggedDoc_join(v_a_6839_);
if (v_isShared_6843_ == 0)
{
lean_ctor_set(v___x_6842_, 0, v___x_6844_);
v___x_6846_ = v___x_6842_;
goto v_reusejp_6845_;
}
else
{
lean_object* v_reuseFailAlloc_6847_; 
v_reuseFailAlloc_6847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6847_, 0, v___x_6844_);
lean_ctor_set(v_reuseFailAlloc_6847_, 1, v_a_6840_);
v___x_6846_ = v_reuseFailAlloc_6847_;
goto v_reusejp_6845_;
}
v_reusejp_6845_:
{
return v___x_6846_;
}
}
}
else
{
lean_object* v_a_6849_; lean_object* v_a_6850_; lean_object* v___x_6852_; uint8_t v_isShared_6853_; uint8_t v_isSharedCheck_6857_; 
v_a_6849_ = lean_ctor_get(v___x_6838_, 0);
v_a_6850_ = lean_ctor_get(v___x_6838_, 1);
v_isSharedCheck_6857_ = !lean_is_exclusive(v___x_6838_);
if (v_isSharedCheck_6857_ == 0)
{
v___x_6852_ = v___x_6838_;
v_isShared_6853_ = v_isSharedCheck_6857_;
goto v_resetjp_6851_;
}
else
{
lean_inc(v_a_6850_);
lean_inc(v_a_6849_);
lean_dec(v___x_6838_);
v___x_6852_ = lean_box(0);
v_isShared_6853_ = v_isSharedCheck_6857_;
goto v_resetjp_6851_;
}
v_resetjp_6851_:
{
lean_object* v___x_6855_; 
if (v_isShared_6853_ == 0)
{
v___x_6855_ = v___x_6852_;
goto v_reusejp_6854_;
}
else
{
lean_object* v_reuseFailAlloc_6856_; 
v_reuseFailAlloc_6856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6856_, 0, v_a_6849_);
lean_ctor_set(v_reuseFailAlloc_6856_, 1, v_a_6850_);
v___x_6855_ = v_reuseFailAlloc_6856_;
goto v_reusejp_6854_;
}
v_reusejp_6854_:
{
return v___x_6855_;
}
}
}
}
else
{
lean_object* v___x_6858_; lean_object* v___x_6859_; lean_object* v___x_6860_; lean_object* v___x_6861_; 
v___x_6858_ = lean_box(0);
v___x_6859_ = lean_unsigned_to_nat(0u);
v___x_6860_ = lean_array_get_borrowed(v___x_6858_, v_stxs_6830_, v___x_6859_);
lean_inc_ref(v_a_6831_);
lean_inc(v___x_6860_);
v___x_6861_ = lean_apply_3(v_f_6829_, v___x_6860_, v_a_6831_, v_a_6832_);
return v___x_6861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object* v_f_6862_, lean_object* v_stxs_6863_, lean_object* v_a_6864_, lean_object* v_a_6865_){
_start:
{
lean_object* v_res_6866_; 
v_res_6866_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v_f_6862_, v_stxs_6863_, v_a_6864_, v_a_6865_);
lean_dec_ref(v_a_6864_);
lean_dec_ref(v_stxs_6863_);
return v_res_6866_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object* v_upperBound_6867_, lean_object* v_stxs_6868_, lean_object* v_f_6869_, lean_object* v___x_6870_, lean_object* v_inst_6871_, lean_object* v_R_6872_, lean_object* v_a_6873_, lean_object* v_b_6874_, lean_object* v_c_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_){
_start:
{
lean_object* v___x_6878_; 
v___x_6878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6867_, v_stxs_6868_, v_f_6869_, v___x_6870_, v_a_6873_, v_b_6874_, v___y_6876_, v___y_6877_);
return v___x_6878_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object* v_upperBound_6879_, lean_object* v_stxs_6880_, lean_object* v_f_6881_, lean_object* v___x_6882_, lean_object* v_inst_6883_, lean_object* v_R_6884_, lean_object* v_a_6885_, lean_object* v_b_6886_, lean_object* v_c_6887_, lean_object* v___y_6888_, lean_object* v___y_6889_){
_start:
{
lean_object* v_res_6890_; 
v_res_6890_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(v_upperBound_6879_, v_stxs_6880_, v_f_6881_, v___x_6882_, v_inst_6883_, v_R_6884_, v_a_6885_, v_b_6886_, v_c_6887_, v___y_6888_, v___y_6889_);
lean_dec_ref(v___y_6888_);
lean_dec(v___x_6882_);
lean_dec_ref(v_stxs_6880_);
lean_dec(v_upperBound_6879_);
return v_res_6890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_stxs_6891_, lean_object* v_a_6892_, lean_object* v_a_6893_){
_start:
{
lean_object* v___x_6894_; lean_object* v___x_6895_; 
v___x_6894_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 0);
v___x_6895_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v___x_6894_, v_stxs_6891_, v_a_6892_, v_a_6893_);
return v___x_6895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_stxs_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_){
_start:
{
lean_object* v_res_6899_; 
v_res_6899_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_stxs_6896_, v_a_6897_, v_a_6898_);
lean_dec_ref(v_a_6897_);
lean_dec_ref(v_stxs_6896_);
return v_res_6899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(lean_object* v_x_6900_){
_start:
{
lean_object* v___x_6901_; 
v___x_6901_ = lean_obj_tag_nat(v_x_6900_);
return v___x_6901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg___boxed(lean_object* v_x_6902_){
_start:
{
lean_object* v_res_6903_; 
v_res_6903_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(v_x_6902_);
lean_dec_ref(v_x_6902_);
return v_res_6903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl(lean_object* v_sep_6904_, lean_object* v_x_6905_){
_start:
{
lean_object* v___x_6906_; 
v___x_6906_ = lean_obj_tag_nat(v_x_6905_);
return v___x_6906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___boxed(lean_object* v_sep_6907_, lean_object* v_x_6908_){
_start:
{
lean_object* v_res_6909_; 
v_res_6909_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl(v_sep_6907_, v_x_6908_);
lean_dec_ref(v_x_6908_);
lean_dec_ref(v_sep_6907_);
return v_res_6909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object* v_t_6910_, lean_object* v_k_6911_){
_start:
{
lean_object* v_g_6912_; lean_object* v___x_6913_; 
v_g_6912_ = lean_ctor_get(v_t_6910_, 0);
lean_inc_ref(v_g_6912_);
lean_dec_ref(v_t_6910_);
v___x_6913_ = lean_apply_1(v_k_6911_, v_g_6912_);
return v___x_6913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim(lean_object* v_sep_6914_, lean_object* v_motive_6915_, lean_object* v_ctorIdx_6916_, lean_object* v_t_6917_, lean_object* v_h_6918_, lean_object* v_k_6919_){
_start:
{
lean_object* v___x_6920_; 
v___x_6920_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6917_, v_k_6919_);
return v___x_6920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object* v_sep_6921_, lean_object* v_motive_6922_, lean_object* v_ctorIdx_6923_, lean_object* v_t_6924_, lean_object* v_h_6925_, lean_object* v_k_6926_){
_start:
{
lean_object* v_res_6927_; 
v_res_6927_ = l_Lean_Fmt_TrailingGroup_ctorElim(v_sep_6921_, v_motive_6922_, v_ctorIdx_6923_, v_t_6924_, v_h_6925_, v_k_6926_);
lean_dec(v_ctorIdx_6923_);
lean_dec_ref(v_sep_6921_);
return v_res_6927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object* v_t_6928_, lean_object* v_group_6929_){
_start:
{
lean_object* v___x_6930_; 
v___x_6930_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6928_, v_group_6929_);
return v___x_6930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim(lean_object* v_sep_6931_, lean_object* v_motive_6932_, lean_object* v_t_6933_, lean_object* v_h_6934_, lean_object* v_group_6935_){
_start:
{
lean_object* v___x_6936_; 
v___x_6936_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6933_, v_group_6935_);
return v___x_6936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object* v_sep_6937_, lean_object* v_motive_6938_, lean_object* v_t_6939_, lean_object* v_h_6940_, lean_object* v_group_6941_){
_start:
{
lean_object* v_res_6942_; 
v_res_6942_ = l_Lean_Fmt_TrailingGroup_group_elim(v_sep_6937_, v_motive_6938_, v_t_6939_, v_h_6940_, v_group_6941_);
lean_dec_ref(v_sep_6937_);
return v_res_6942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object* v_t_6943_, lean_object* v_trailing_6944_){
_start:
{
lean_object* v___x_6945_; 
v___x_6945_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6943_, v_trailing_6944_);
return v___x_6945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim(lean_object* v_sep_6946_, lean_object* v_motive_6947_, lean_object* v_t_6948_, lean_object* v_h_6949_, lean_object* v_trailing_6950_){
_start:
{
lean_object* v___x_6951_; 
v___x_6951_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6948_, v_trailing_6950_);
return v___x_6951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object* v_sep_6952_, lean_object* v_motive_6953_, lean_object* v_t_6954_, lean_object* v_h_6955_, lean_object* v_trailing_6956_){
_start:
{
lean_object* v_res_6957_; 
v_res_6957_ = l_Lean_Fmt_TrailingGroup_trailing_elim(v_sep_6952_, v_motive_6953_, v_t_6954_, v_h_6955_, v_trailing_6956_);
lean_dec_ref(v_sep_6952_);
return v_res_6957_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_6958_; lean_object* v___x_6959_; 
v___x_6958_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_6959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6959_, 0, v___x_6958_);
return v___x_6959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg(){
_start:
{
lean_object* v___x_6961_; 
v___x_6961_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0);
return v___x_6961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___boxed(lean_object* v___dummy_6962_){
_start:
{
lean_object* v_res_6963_; 
v_res_6963_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v_res_6963_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0(void){
_start:
{
lean_object* v___x_6964_; 
v___x_6964_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v___x_6964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object* v_sep_6965_){
_start:
{
lean_object* v___x_6966_; 
v___x_6966_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object* v_sep_6967_){
_start:
{
lean_object* v_res_6968_; 
v_res_6968_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6967_);
lean_dec_ref(v_sep_6967_);
return v_res_6968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg(){
_start:
{
lean_object* v___x_6970_; 
v___x_6970_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg___boxed(lean_object* v___dummy_6971_){
_start:
{
lean_object* v_res_6972_; 
v_res_6972_ = l_Lean_Fmt_instInhabitedTrailingGroup___redArg();
return v_res_6972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup(lean_object* v_a_6973_){
_start:
{
lean_object* v___x_6974_; 
v___x_6974_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object* v_a_6975_){
_start:
{
lean_object* v_res_6976_; 
v_res_6976_ = l_Lean_Fmt_instInhabitedTrailingGroup(v_a_6975_);
lean_dec_ref(v_a_6975_);
return v_res_6976_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object* v_upperBound_6977_, lean_object* v_elemsAndSeps_6978_, lean_object* v_pendingGroup_6979_, lean_object* v___x_6980_, lean_object* v_a_6981_, lean_object* v_b_6982_, lean_object* v___y_6983_, lean_object* v___y_6984_){
_start:
{
lean_object* v_a_6986_; lean_object* v_a_6987_; uint8_t v___x_6991_; 
v___x_6991_ = lean_nat_dec_lt(v_a_6981_, v_upperBound_6977_);
if (v___x_6991_ == 0)
{
lean_object* v___x_6992_; 
lean_dec(v_a_6981_);
lean_dec_ref(v_pendingGroup_6979_);
v___x_6992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6992_, 0, v_b_6982_);
lean_ctor_set(v___x_6992_, 1, v___y_6984_);
return v___x_6992_;
}
else
{
lean_object* v___x_6993_; lean_object* v___x_6994_; 
v___x_6993_ = lean_array_fget_borrowed(v_elemsAndSeps_6978_, v_a_6981_);
lean_inc(v___x_6993_);
v___x_6994_ = l_Lean_Fmt_fmt(v___x_6993_, v___y_6983_, v___y_6984_);
if (lean_obj_tag(v___x_6994_) == 0)
{
lean_object* v_a_6995_; lean_object* v_a_6996_; lean_object* v_fst_6997_; lean_object* v_snd_6998_; lean_object* v___x_7000_; uint8_t v_isShared_7001_; uint8_t v_isSharedCheck_7045_; 
v_a_6995_ = lean_ctor_get(v___x_6994_, 0);
lean_inc(v_a_6995_);
v_a_6996_ = lean_ctor_get(v___x_6994_, 1);
lean_inc(v_a_6996_);
lean_dec_ref_known(v___x_6994_, 2);
v_fst_6997_ = lean_ctor_get(v_b_6982_, 0);
v_snd_6998_ = lean_ctor_get(v_b_6982_, 1);
v_isSharedCheck_7045_ = !lean_is_exclusive(v_b_6982_);
if (v_isSharedCheck_7045_ == 0)
{
v___x_7000_ = v_b_6982_;
v_isShared_7001_ = v_isSharedCheck_7045_;
goto v_resetjp_6999_;
}
else
{
lean_inc(v_snd_6998_);
lean_inc(v_fst_6997_);
lean_dec(v_b_6982_);
v___x_7000_ = lean_box(0);
v_isShared_7001_ = v_isSharedCheck_7045_;
goto v_resetjp_6999_;
}
v_resetjp_6999_:
{
lean_object* v___x_7002_; lean_object* v___x_7003_; lean_object* v___x_7004_; lean_object* v___y_7006_; uint8_t v___y_7034_; lean_object* v___x_7041_; lean_object* v___x_7042_; uint8_t v___x_7043_; 
v___x_7002_ = lean_unsigned_to_nat(0u);
v___x_7003_ = lean_box(0);
v___x_7004_ = lean_array_push(v_snd_6998_, v_a_6995_);
v___x_7041_ = lean_unsigned_to_nat(2u);
v___x_7042_ = lean_nat_mod(v_a_6981_, v___x_7041_);
v___x_7043_ = lean_nat_dec_eq(v___x_7042_, v___x_7002_);
lean_dec(v___x_7042_);
if (v___x_7043_ == 0)
{
v___y_7034_ = v___x_6991_;
goto v___jp_7033_;
}
else
{
uint8_t v___x_7044_; 
v___x_7044_ = 0;
v___y_7034_ = v___x_7044_;
goto v___jp_7033_;
}
v___jp_7005_:
{
uint8_t v___x_7007_; lean_object* v___x_7008_; 
v___x_7007_ = 0;
v___x_7008_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___y_7006_, v___x_7007_, v___y_6983_, v_a_6996_);
if (lean_obj_tag(v___x_7008_) == 0)
{
lean_object* v_a_7009_; lean_object* v_a_7010_; uint8_t v___x_7011_; 
v_a_7009_ = lean_ctor_get(v___x_7008_, 0);
lean_inc(v_a_7009_);
v_a_7010_ = lean_ctor_get(v___x_7008_, 1);
lean_inc(v_a_7010_);
lean_dec_ref_known(v___x_7008_, 2);
v___x_7011_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_7009_);
if (v___x_7011_ == 0)
{
lean_object* v___x_7012_; lean_object* v___x_7013_; lean_object* v___x_7014_; lean_object* v___x_7015_; lean_object* v___x_7017_; 
v___x_7012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7012_, 0, v___x_7004_);
v___x_7013_ = lean_array_push(v_fst_6997_, v___x_7012_);
v___x_7014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7014_, 0, v_a_7009_);
v___x_7015_ = lean_array_push(v___x_7013_, v___x_7014_);
lean_inc_ref(v_pendingGroup_6979_);
if (v_isShared_7001_ == 0)
{
lean_ctor_set(v___x_7000_, 1, v_pendingGroup_6979_);
lean_ctor_set(v___x_7000_, 0, v___x_7015_);
v___x_7017_ = v___x_7000_;
goto v_reusejp_7016_;
}
else
{
lean_object* v_reuseFailAlloc_7018_; 
v_reuseFailAlloc_7018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7018_, 0, v___x_7015_);
lean_ctor_set(v_reuseFailAlloc_7018_, 1, v_pendingGroup_6979_);
v___x_7017_ = v_reuseFailAlloc_7018_;
goto v_reusejp_7016_;
}
v_reusejp_7016_:
{
v_a_6986_ = v___x_7017_;
v_a_6987_ = v_a_7010_;
goto v___jp_6985_;
}
}
else
{
lean_object* v___x_7020_; 
lean_dec(v_a_7009_);
if (v_isShared_7001_ == 0)
{
lean_ctor_set(v___x_7000_, 1, v___x_7004_);
v___x_7020_ = v___x_7000_;
goto v_reusejp_7019_;
}
else
{
lean_object* v_reuseFailAlloc_7021_; 
v_reuseFailAlloc_7021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7021_, 0, v_fst_6997_);
lean_ctor_set(v_reuseFailAlloc_7021_, 1, v___x_7004_);
v___x_7020_ = v_reuseFailAlloc_7021_;
goto v_reusejp_7019_;
}
v_reusejp_7019_:
{
v_a_6986_ = v___x_7020_;
v_a_6987_ = v_a_7010_;
goto v___jp_6985_;
}
}
}
else
{
lean_object* v_a_7022_; lean_object* v_a_7023_; lean_object* v___x_7025_; uint8_t v_isShared_7026_; uint8_t v_isSharedCheck_7030_; 
lean_dec_ref(v___x_7004_);
lean_del_object(v___x_7000_);
lean_dec(v_fst_6997_);
lean_dec(v_a_6981_);
lean_dec_ref(v_pendingGroup_6979_);
v_a_7022_ = lean_ctor_get(v___x_7008_, 0);
v_a_7023_ = lean_ctor_get(v___x_7008_, 1);
v_isSharedCheck_7030_ = !lean_is_exclusive(v___x_7008_);
if (v_isSharedCheck_7030_ == 0)
{
v___x_7025_ = v___x_7008_;
v_isShared_7026_ = v_isSharedCheck_7030_;
goto v_resetjp_7024_;
}
else
{
lean_inc(v_a_7023_);
lean_inc(v_a_7022_);
lean_dec(v___x_7008_);
v___x_7025_ = lean_box(0);
v_isShared_7026_ = v_isSharedCheck_7030_;
goto v_resetjp_7024_;
}
v_resetjp_7024_:
{
lean_object* v___x_7028_; 
if (v_isShared_7026_ == 0)
{
v___x_7028_ = v___x_7025_;
goto v_reusejp_7027_;
}
else
{
lean_object* v_reuseFailAlloc_7029_; 
v_reuseFailAlloc_7029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7029_, 0, v_a_7022_);
lean_ctor_set(v_reuseFailAlloc_7029_, 1, v_a_7023_);
v___x_7028_ = v_reuseFailAlloc_7029_;
goto v_reusejp_7027_;
}
v_reusejp_7027_:
{
return v___x_7028_;
}
}
}
}
v___jp_7031_:
{
lean_object* v___x_7032_; 
v___x_7032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7032_, 0, v_fst_6997_);
lean_ctor_set(v___x_7032_, 1, v___x_7004_);
v_a_6986_ = v___x_7032_;
v_a_6987_ = v_a_6996_;
goto v___jp_6985_;
}
v___jp_7033_:
{
lean_object* v___x_7035_; lean_object* v___x_7036_; uint8_t v___x_7037_; 
v___x_7035_ = lean_unsigned_to_nat(1u);
v___x_7036_ = lean_nat_sub(v___x_6980_, v___x_7035_);
v___x_7037_ = lean_nat_dec_lt(v_a_6981_, v___x_7036_);
lean_dec(v___x_7036_);
if (v___x_7037_ == 0)
{
lean_del_object(v___x_7000_);
goto v___jp_7031_;
}
else
{
if (v___y_7034_ == 0)
{
lean_del_object(v___x_7000_);
goto v___jp_7031_;
}
else
{
uint8_t v___x_7038_; 
lean_inc(v___x_6993_);
v___x_7038_ = l_Lean_Syntax_matchesNull(v___x_6993_, v___x_7002_);
if (v___x_7038_ == 0)
{
lean_inc(v___x_6993_);
v___y_7006_ = v___x_6993_;
goto v___jp_7005_;
}
else
{
lean_object* v___x_7039_; lean_object* v___x_7040_; 
v___x_7039_ = lean_nat_sub(v_a_6981_, v___x_7035_);
v___x_7040_ = lean_array_get_borrowed(v___x_7003_, v_elemsAndSeps_6978_, v___x_7039_);
lean_dec(v___x_7039_);
lean_inc(v___x_7040_);
v___y_7006_ = v___x_7040_;
goto v___jp_7005_;
}
}
}
}
}
}
else
{
lean_object* v_a_7046_; lean_object* v_a_7047_; lean_object* v___x_7049_; uint8_t v_isShared_7050_; uint8_t v_isSharedCheck_7054_; 
lean_dec_ref(v_b_6982_);
lean_dec(v_a_6981_);
lean_dec_ref(v_pendingGroup_6979_);
v_a_7046_ = lean_ctor_get(v___x_6994_, 0);
v_a_7047_ = lean_ctor_get(v___x_6994_, 1);
v_isSharedCheck_7054_ = !lean_is_exclusive(v___x_6994_);
if (v_isSharedCheck_7054_ == 0)
{
v___x_7049_ = v___x_6994_;
v_isShared_7050_ = v_isSharedCheck_7054_;
goto v_resetjp_7048_;
}
else
{
lean_inc(v_a_7047_);
lean_inc(v_a_7046_);
lean_dec(v___x_6994_);
v___x_7049_ = lean_box(0);
v_isShared_7050_ = v_isSharedCheck_7054_;
goto v_resetjp_7048_;
}
v_resetjp_7048_:
{
lean_object* v___x_7052_; 
if (v_isShared_7050_ == 0)
{
v___x_7052_ = v___x_7049_;
goto v_reusejp_7051_;
}
else
{
lean_object* v_reuseFailAlloc_7053_; 
v_reuseFailAlloc_7053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7053_, 0, v_a_7046_);
lean_ctor_set(v_reuseFailAlloc_7053_, 1, v_a_7047_);
v___x_7052_ = v_reuseFailAlloc_7053_;
goto v_reusejp_7051_;
}
v_reusejp_7051_:
{
return v___x_7052_;
}
}
}
}
v___jp_6985_:
{
lean_object* v___x_6988_; lean_object* v___x_6989_; 
v___x_6988_ = lean_unsigned_to_nat(1u);
v___x_6989_ = lean_nat_add(v_a_6981_, v___x_6988_);
lean_dec(v_a_6981_);
v_a_6981_ = v___x_6989_;
v_b_6982_ = v_a_6986_;
v___y_6984_ = v_a_6987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object* v_upperBound_7055_, lean_object* v_elemsAndSeps_7056_, lean_object* v_pendingGroup_7057_, lean_object* v___x_7058_, lean_object* v_a_7059_, lean_object* v_b_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_){
_start:
{
lean_object* v_res_7063_; 
v_res_7063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7055_, v_elemsAndSeps_7056_, v_pendingGroup_7057_, v___x_7058_, v_a_7059_, v_b_7060_, v___y_7061_, v___y_7062_);
lean_dec_ref(v___y_7061_);
lean_dec(v___x_7058_);
lean_dec_ref(v_elemsAndSeps_7056_);
lean_dec(v_upperBound_7055_);
return v_res_7063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object* v_sep_7068_, lean_object* v_stxs_7069_, lean_object* v_a_7070_, lean_object* v_a_7071_){
_start:
{
lean_object* v___x_7072_; lean_object* v___x_7073_; lean_object* v_acc_7074_; lean_object* v___x_7075_; lean_object* v___x_7076_; 
v___x_7072_ = lean_unsigned_to_nat(0u);
v___x_7073_ = lean_array_get_size(v_stxs_7069_);
v_acc_7074_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0));
v___x_7075_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1));
v___x_7076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v___x_7073_, v_stxs_7069_, v_acc_7074_, v___x_7073_, v___x_7072_, v___x_7075_, v_a_7070_, v_a_7071_);
if (lean_obj_tag(v___x_7076_) == 0)
{
lean_object* v_a_7077_; lean_object* v_a_7078_; lean_object* v___x_7080_; uint8_t v_isShared_7081_; uint8_t v_isSharedCheck_7094_; 
v_a_7077_ = lean_ctor_get(v___x_7076_, 0);
v_a_7078_ = lean_ctor_get(v___x_7076_, 1);
v_isSharedCheck_7094_ = !lean_is_exclusive(v___x_7076_);
if (v_isSharedCheck_7094_ == 0)
{
v___x_7080_ = v___x_7076_;
v_isShared_7081_ = v_isSharedCheck_7094_;
goto v_resetjp_7079_;
}
else
{
lean_inc(v_a_7078_);
lean_inc(v_a_7077_);
lean_dec(v___x_7076_);
v___x_7080_ = lean_box(0);
v_isShared_7081_ = v_isSharedCheck_7094_;
goto v_resetjp_7079_;
}
v_resetjp_7079_:
{
lean_object* v_fst_7082_; lean_object* v_snd_7083_; lean_object* v___x_7084_; uint8_t v___x_7085_; 
v_fst_7082_ = lean_ctor_get(v_a_7077_, 0);
lean_inc(v_fst_7082_);
v_snd_7083_ = lean_ctor_get(v_a_7077_, 1);
lean_inc(v_snd_7083_);
lean_dec(v_a_7077_);
v___x_7084_ = lean_array_get_size(v_snd_7083_);
v___x_7085_ = lean_nat_dec_eq(v___x_7084_, v___x_7072_);
if (v___x_7085_ == 0)
{
lean_object* v___x_7086_; lean_object* v___x_7087_; lean_object* v___x_7089_; 
v___x_7086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7086_, 0, v_snd_7083_);
v___x_7087_ = lean_array_push(v_fst_7082_, v___x_7086_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 0, v___x_7087_);
v___x_7089_ = v___x_7080_;
goto v_reusejp_7088_;
}
else
{
lean_object* v_reuseFailAlloc_7090_; 
v_reuseFailAlloc_7090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7090_, 0, v___x_7087_);
lean_ctor_set(v_reuseFailAlloc_7090_, 1, v_a_7078_);
v___x_7089_ = v_reuseFailAlloc_7090_;
goto v_reusejp_7088_;
}
v_reusejp_7088_:
{
return v___x_7089_;
}
}
else
{
lean_object* v___x_7092_; 
lean_dec(v_snd_7083_);
if (v_isShared_7081_ == 0)
{
lean_ctor_set(v___x_7080_, 0, v_fst_7082_);
v___x_7092_ = v___x_7080_;
goto v_reusejp_7091_;
}
else
{
lean_object* v_reuseFailAlloc_7093_; 
v_reuseFailAlloc_7093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7093_, 0, v_fst_7082_);
lean_ctor_set(v_reuseFailAlloc_7093_, 1, v_a_7078_);
v___x_7092_ = v_reuseFailAlloc_7093_;
goto v_reusejp_7091_;
}
v_reusejp_7091_:
{
return v___x_7092_;
}
}
}
}
else
{
lean_object* v_a_7095_; lean_object* v_a_7096_; lean_object* v___x_7098_; uint8_t v_isShared_7099_; uint8_t v_isSharedCheck_7103_; 
v_a_7095_ = lean_ctor_get(v___x_7076_, 0);
v_a_7096_ = lean_ctor_get(v___x_7076_, 1);
v_isSharedCheck_7103_ = !lean_is_exclusive(v___x_7076_);
if (v_isSharedCheck_7103_ == 0)
{
v___x_7098_ = v___x_7076_;
v_isShared_7099_ = v_isSharedCheck_7103_;
goto v_resetjp_7097_;
}
else
{
lean_inc(v_a_7096_);
lean_inc(v_a_7095_);
lean_dec(v___x_7076_);
v___x_7098_ = lean_box(0);
v_isShared_7099_ = v_isSharedCheck_7103_;
goto v_resetjp_7097_;
}
v_resetjp_7097_:
{
lean_object* v___x_7101_; 
if (v_isShared_7099_ == 0)
{
v___x_7101_ = v___x_7098_;
goto v_reusejp_7100_;
}
else
{
lean_object* v_reuseFailAlloc_7102_; 
v_reuseFailAlloc_7102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7102_, 0, v_a_7095_);
lean_ctor_set(v_reuseFailAlloc_7102_, 1, v_a_7096_);
v___x_7101_ = v_reuseFailAlloc_7102_;
goto v_reusejp_7100_;
}
v_reusejp_7100_:
{
return v___x_7101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object* v_sep_7104_, lean_object* v_stxs_7105_, lean_object* v_a_7106_, lean_object* v_a_7107_){
_start:
{
lean_object* v_res_7108_; 
v_res_7108_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7104_, v_stxs_7105_, v_a_7106_, v_a_7107_);
lean_dec_ref(v_a_7106_);
lean_dec_ref(v_stxs_7105_);
lean_dec_ref(v_sep_7104_);
return v_res_7108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object* v_ks_7109_, lean_object* v_sep_7110_, lean_object* v_stxs_7111_, lean_object* v_a_7112_, lean_object* v_a_7113_){
_start:
{
lean_object* v___x_7114_; 
v___x_7114_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7110_, v_stxs_7111_, v_a_7112_, v_a_7113_);
return v___x_7114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object* v_ks_7115_, lean_object* v_sep_7116_, lean_object* v_stxs_7117_, lean_object* v_a_7118_, lean_object* v_a_7119_){
_start:
{
lean_object* v_res_7120_; 
v_res_7120_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups(v_ks_7115_, v_sep_7116_, v_stxs_7117_, v_a_7118_, v_a_7119_);
lean_dec_ref(v_a_7118_);
lean_dec_ref(v_stxs_7117_);
lean_dec_ref(v_sep_7116_);
lean_dec(v_ks_7115_);
return v_res_7120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object* v_upperBound_7121_, lean_object* v_elemsAndSeps_7122_, lean_object* v_sep_7123_, lean_object* v_pendingGroup_7124_, lean_object* v___x_7125_, lean_object* v_inst_7126_, lean_object* v_R_7127_, lean_object* v_a_7128_, lean_object* v_b_7129_, lean_object* v_c_7130_, lean_object* v___y_7131_, lean_object* v___y_7132_){
_start:
{
lean_object* v___x_7133_; 
v___x_7133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7121_, v_elemsAndSeps_7122_, v_pendingGroup_7124_, v___x_7125_, v_a_7128_, v_b_7129_, v___y_7131_, v___y_7132_);
return v___x_7133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object* v_upperBound_7134_, lean_object* v_elemsAndSeps_7135_, lean_object* v_sep_7136_, lean_object* v_pendingGroup_7137_, lean_object* v___x_7138_, lean_object* v_inst_7139_, lean_object* v_R_7140_, lean_object* v_a_7141_, lean_object* v_b_7142_, lean_object* v_c_7143_, lean_object* v___y_7144_, lean_object* v___y_7145_){
_start:
{
lean_object* v_res_7146_; 
v_res_7146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(v_upperBound_7134_, v_elemsAndSeps_7135_, v_sep_7136_, v_pendingGroup_7137_, v___x_7138_, v_inst_7139_, v_R_7140_, v_a_7141_, v_b_7142_, v_c_7143_, v___y_7144_, v___y_7145_);
lean_dec_ref(v___y_7144_);
lean_dec(v___x_7138_);
lean_dec_ref(v_sep_7136_);
lean_dec_ref(v_elemsAndSeps_7135_);
lean_dec(v_upperBound_7134_);
return v_res_7146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object* v_sep_7150_, size_t v_sz_7151_, size_t v_i_7152_, lean_object* v_bs_7153_){
_start:
{
uint8_t v___x_7154_; 
v___x_7154_ = lean_usize_dec_lt(v_i_7152_, v_sz_7151_);
if (v___x_7154_ == 0)
{
lean_dec_ref(v_sep_7150_);
return v_bs_7153_;
}
else
{
lean_object* v_v_7155_; lean_object* v___x_7156_; lean_object* v_bs_x27_7157_; lean_object* v___y_7159_; 
v_v_7155_ = lean_array_uget(v_bs_7153_, v_i_7152_);
v___x_7156_ = lean_unsigned_to_nat(0u);
v_bs_x27_7157_ = lean_array_uset(v_bs_7153_, v_i_7152_, v___x_7156_);
if (lean_obj_tag(v_v_7155_) == 0)
{
lean_object* v_g_7164_; lean_object* v___x_7165_; lean_object* v___x_7166_; 
v_g_7164_ = lean_ctor_get(v_v_7155_, 0);
lean_inc_ref(v_g_7164_);
lean_dec_ref_known(v_v_7155_, 1);
v___x_7165_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0));
lean_inc_ref(v_sep_7150_);
v___x_7166_ = l_Lean_Fmt_Layouts_sepArray(v_sep_7150_, v_g_7164_, v___x_7165_);
lean_dec_ref(v_g_7164_);
v___y_7159_ = v___x_7166_;
goto v___jp_7158_;
}
else
{
lean_object* v_t_7167_; 
v_t_7167_ = lean_ctor_get(v_v_7155_, 0);
lean_inc_ref(v_t_7167_);
lean_dec_ref_known(v_v_7155_, 1);
v___y_7159_ = v_t_7167_;
goto v___jp_7158_;
}
v___jp_7158_:
{
size_t v___x_7160_; size_t v___x_7161_; lean_object* v___x_7162_; 
v___x_7160_ = ((size_t)1ULL);
v___x_7161_ = lean_usize_add(v_i_7152_, v___x_7160_);
v___x_7162_ = lean_array_uset(v_bs_x27_7157_, v_i_7152_, v___y_7159_);
v_i_7152_ = v___x_7161_;
v_bs_7153_ = v___x_7162_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object* v_sep_7168_, lean_object* v_sz_7169_, lean_object* v_i_7170_, lean_object* v_bs_7171_){
_start:
{
size_t v_sz_boxed_7172_; size_t v_i_boxed_7173_; lean_object* v_res_7174_; 
v_sz_boxed_7172_ = lean_unbox_usize(v_sz_7169_);
lean_dec(v_sz_7169_);
v_i_boxed_7173_ = lean_unbox_usize(v_i_7170_);
lean_dec(v_i_7170_);
v_res_7174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7168_, v_sz_boxed_7172_, v_i_boxed_7173_, v_bs_7171_);
return v_res_7174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object* v_sep_7175_, lean_object* v_stxs_7176_, lean_object* v_a_7177_, lean_object* v_a_7178_){
_start:
{
lean_object* v___x_7179_; 
v___x_7179_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7175_, v_stxs_7176_, v_a_7177_, v_a_7178_);
if (lean_obj_tag(v___x_7179_) == 0)
{
lean_object* v_a_7180_; lean_object* v_a_7181_; lean_object* v___x_7183_; uint8_t v_isShared_7184_; uint8_t v_isSharedCheck_7192_; 
v_a_7180_ = lean_ctor_get(v___x_7179_, 0);
v_a_7181_ = lean_ctor_get(v___x_7179_, 1);
v_isSharedCheck_7192_ = !lean_is_exclusive(v___x_7179_);
if (v_isSharedCheck_7192_ == 0)
{
v___x_7183_ = v___x_7179_;
v_isShared_7184_ = v_isSharedCheck_7192_;
goto v_resetjp_7182_;
}
else
{
lean_inc(v_a_7181_);
lean_inc(v_a_7180_);
lean_dec(v___x_7179_);
v___x_7183_ = lean_box(0);
v_isShared_7184_ = v_isSharedCheck_7192_;
goto v_resetjp_7182_;
}
v_resetjp_7182_:
{
size_t v_sz_7185_; size_t v___x_7186_; lean_object* v___x_7187_; lean_object* v___x_7188_; lean_object* v___x_7190_; 
v_sz_7185_ = lean_array_size(v_a_7180_);
v___x_7186_ = ((size_t)0ULL);
v___x_7187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7175_, v_sz_7185_, v___x_7186_, v_a_7180_);
v___x_7188_ = l_Lean_Fmt_TaggedDoc_join(v___x_7187_);
if (v_isShared_7184_ == 0)
{
lean_ctor_set(v___x_7183_, 0, v___x_7188_);
v___x_7190_ = v___x_7183_;
goto v_reusejp_7189_;
}
else
{
lean_object* v_reuseFailAlloc_7191_; 
v_reuseFailAlloc_7191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7191_, 0, v___x_7188_);
lean_ctor_set(v_reuseFailAlloc_7191_, 1, v_a_7181_);
v___x_7190_ = v_reuseFailAlloc_7191_;
goto v_reusejp_7189_;
}
v_reusejp_7189_:
{
return v___x_7190_;
}
}
}
else
{
lean_object* v_a_7193_; lean_object* v_a_7194_; lean_object* v___x_7196_; uint8_t v_isShared_7197_; uint8_t v_isSharedCheck_7201_; 
lean_dec_ref(v_sep_7175_);
v_a_7193_ = lean_ctor_get(v___x_7179_, 0);
v_a_7194_ = lean_ctor_get(v___x_7179_, 1);
v_isSharedCheck_7201_ = !lean_is_exclusive(v___x_7179_);
if (v_isSharedCheck_7201_ == 0)
{
v___x_7196_ = v___x_7179_;
v_isShared_7197_ = v_isSharedCheck_7201_;
goto v_resetjp_7195_;
}
else
{
lean_inc(v_a_7194_);
lean_inc(v_a_7193_);
lean_dec(v___x_7179_);
v___x_7196_ = lean_box(0);
v_isShared_7197_ = v_isSharedCheck_7201_;
goto v_resetjp_7195_;
}
v_resetjp_7195_:
{
lean_object* v___x_7199_; 
if (v_isShared_7197_ == 0)
{
v___x_7199_ = v___x_7196_;
goto v_reusejp_7198_;
}
else
{
lean_object* v_reuseFailAlloc_7200_; 
v_reuseFailAlloc_7200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7200_, 0, v_a_7193_);
lean_ctor_set(v_reuseFailAlloc_7200_, 1, v_a_7194_);
v___x_7199_ = v_reuseFailAlloc_7200_;
goto v_reusejp_7198_;
}
v_reusejp_7198_:
{
return v___x_7199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object* v_sep_7202_, lean_object* v_stxs_7203_, lean_object* v_a_7204_, lean_object* v_a_7205_){
_start:
{
lean_object* v_res_7206_; 
v_res_7206_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7202_, v_stxs_7203_, v_a_7204_, v_a_7205_);
lean_dec_ref(v_a_7204_);
lean_dec_ref(v_stxs_7203_);
return v_res_7206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_ks_7207_, lean_object* v_sep_7208_, lean_object* v_stxs_7209_, lean_object* v_a_7210_, lean_object* v_a_7211_){
_start:
{
lean_object* v___x_7212_; 
v___x_7212_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7208_, v_stxs_7209_, v_a_7210_, v_a_7211_);
return v___x_7212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_ks_7213_, lean_object* v_sep_7214_, lean_object* v_stxs_7215_, lean_object* v_a_7216_, lean_object* v_a_7217_){
_start:
{
lean_object* v_res_7218_; 
v_res_7218_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(v_ks_7213_, v_sep_7214_, v_stxs_7215_, v_a_7216_, v_a_7217_);
lean_dec_ref(v_a_7216_);
lean_dec_ref(v_stxs_7215_);
lean_dec(v_ks_7213_);
return v_res_7218_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
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
res = runtime_initialize_Lean_Fmt_Util_Basic(builtin);
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
lean_object* initialize_Lean_Fmt_Util_Basic(uint8_t builtin);
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
res = initialize_Lean_Fmt_Util_Basic(builtin);
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
