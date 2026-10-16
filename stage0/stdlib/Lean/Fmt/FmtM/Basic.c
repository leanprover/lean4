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
lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object*);
lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedError_default;
lean_object* l_EStateM_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedState_default;
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
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
lean_object* l_Lean_Fmt_Layouts_conditional(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_addBuiltinFmtProvider(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_addBuiltinCommentCollector(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "A choice node was not disambiguated by the elaborator:\n"};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0;
static lean_once_cell_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__2, &l_Lean_FmtM_run___redArg___closed__2_once, _init_l_Lean_FmtM_run___redArg___closed__2);
v___x_315_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__1, &l_Lean_FmtM_run___redArg___closed__1_once, _init_l_Lean_FmtM_run___redArg___closed__1);
v___x_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
lean_ctor_set(v___x_316_, 3, v___x_315_);
lean_ctor_set(v___x_316_, 4, v___x_315_);
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
lean_object* v_toBacktrackableState_341_; lean_object* v_shareCommonState_342_; lean_object* v_freshTagId_343_; lean_object* v_missingFormatters_344_; lean_object* v_partialFormatters_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_363_; 
v_toBacktrackableState_341_ = lean_ctor_get(v___y_340_, 0);
v_shareCommonState_342_ = lean_ctor_get(v___y_340_, 1);
v_freshTagId_343_ = lean_ctor_get(v___y_340_, 2);
v_missingFormatters_344_ = lean_ctor_get(v___y_340_, 3);
v_partialFormatters_345_ = lean_ctor_get(v___y_340_, 4);
v_isSharedCheck_363_ = !lean_is_exclusive(v___y_340_);
if (v_isSharedCheck_363_ == 0)
{
v___x_347_ = v___y_340_;
v_isShared_348_ = v_isSharedCheck_363_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_partialFormatters_345_);
lean_inc(v_missingFormatters_344_);
lean_inc(v_freshTagId_343_);
lean_inc(v_shareCommonState_342_);
lean_inc(v_toBacktrackableState_341_);
lean_dec(v___y_340_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_363_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_362_; 
v___x_349_ = l_Lean_ShareCommon_objectFactory;
v___x_350_ = lean_state_sharecommon(v___x_349_, v_shareCommonState_342_, v_v_338_);
v_fst_351_ = lean_ctor_get(v___x_350_, 0);
v_snd_352_ = lean_ctor_get(v___x_350_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_362_ == 0)
{
v___x_354_ = v___x_350_;
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_snd_352_);
lean_inc(v_fst_351_);
lean_dec(v___x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_snd_352_);
v___x_357_ = v___x_347_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_toBacktrackableState_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_snd_352_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_freshTagId_343_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_missingFormatters_344_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_partialFormatters_345_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_357_);
v___x_359_ = v___x_354_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed(lean_object* v_00_u03b1_364_, lean_object* v_v_365_, lean_object* v_x_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(v_00_u03b1_364_, v_v_365_, v_x_366_, v___y_367_);
lean_dec_ref(v_x_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_FormattedWhitespace_merge(lean_object* v_t1_371_, lean_object* v_t2_372_){
_start:
{
lean_object* v_formattedLeadingRanges_373_; lean_object* v_formattedTrailingRanges_374_; lean_object* v_formattedLeadingRanges_375_; lean_object* v_formattedTrailingRanges_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_385_; 
v_formattedLeadingRanges_373_ = lean_ctor_get(v_t1_371_, 0);
lean_inc_ref(v_formattedLeadingRanges_373_);
v_formattedTrailingRanges_374_ = lean_ctor_get(v_t1_371_, 1);
lean_inc_ref(v_formattedTrailingRanges_374_);
lean_dec_ref(v_t1_371_);
v_formattedLeadingRanges_375_ = lean_ctor_get(v_t2_372_, 0);
v_formattedTrailingRanges_376_ = lean_ctor_get(v_t2_372_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v_t2_372_);
if (v_isSharedCheck_385_ == 0)
{
v___x_378_ = v_t2_372_;
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_formattedTrailingRanges_376_);
lean_inc(v_formattedLeadingRanges_375_);
lean_dec(v_t2_372_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_385_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_380_ = l_Array_append___redArg(v_formattedLeadingRanges_373_, v_formattedLeadingRanges_375_);
lean_dec_ref(v_formattedLeadingRanges_375_);
v___x_381_ = l_Array_append___redArg(v_formattedTrailingRanges_374_, v_formattedTrailingRanges_376_);
lean_dec_ref(v_formattedTrailingRanges_376_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_381_);
lean_ctor_set(v___x_378_, 0, v___x_380_);
v___x_383_ = v___x_378_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object* v_stx_386_, lean_object* v_i_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_arg_389_; uint8_t v___x_390_; 
v_arg_389_ = l_Lean_Syntax_getArg(v_stx_386_, v_i_387_);
v___x_390_ = l_Lean_Syntax_isMissing(v_arg_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_arg_389_);
lean_ctor_set(v___x_391_, 1, v_a_388_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v_arg_389_);
v___x_392_ = l_Lean_Fmt_Error_partialFormatter;
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_a_388_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg___boxed(lean_object* v_stx_394_, lean_object* v_i_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_394_, v_i_395_, v_a_396_);
lean_dec(v_i_395_);
lean_dec(v_stx_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21(lean_object* v_stx_398_, lean_object* v_i_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_398_, v_i_399_, v_a_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___boxed(lean_object* v_stx_403_, lean_object* v_i_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Fmt_getStxArg_x21(v_stx_403_, v_i_404_, v_a_405_, v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_i_404_);
lean_dec(v_stx_403_);
return v_res_407_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0(void){
_start:
{
lean_object* v___x_408_; lean_object* v___f_409_; 
v___x_408_ = l_Lean_Fmt_instInhabitedError_default;
v___f_409_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_409_, 0, v___x_408_);
return v___f_409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___f_413_; lean_object* v___f_414_; lean_object* v___x_703__overap_415_; lean_object* v___x_416_; 
v___f_413_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_414_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_414_, 0, v___f_413_);
v___x_703__overap_415_ = lean_panic_fn_borrowed(v___f_414_, v_msg_410_);
lean_dec_ref(v___f_414_);
lean_inc_ref(v___y_411_);
v___x_416_ = lean_apply_2(v___x_703__overap_415_, v___y_411_, v___y_412_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___boxed(lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v_msg_417_, v___y_418_, v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_420_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(lean_object* v_msg_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0);
v___x_426_ = lean_panic_fn_borrowed(v___x_425_, v_msg_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object* v_x_427_){
_start:
{
lean_object* v_startPos_428_; 
v_startPos_428_ = lean_ctor_get(v_x_427_, 4);
lean_inc(v_startPos_428_);
return v_startPos_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Fmt_getLineInfo_x21___lam__0(v_x_429_);
lean_dec_ref(v_x_429_);
return v_res_430_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_getLineInfo_x21___lam__1(lean_object* v_x1_431_, lean_object* v_x2_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_x1_431_, v___x_433_);
v___x_435_ = lean_nat_dec_le(v___x_434_, v_x2_432_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1___boxed(lean_object* v_x1_436_, lean_object* v_x2_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lean_Fmt_getLineInfo_x21___lam__1(v_x1_436_, v_x2_437_);
lean_dec(v_x2_437_);
lean_dec(v_x1_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__3(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_443_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__2));
v___x_444_ = lean_unsigned_to_nat(2u);
v___x_445_ = lean_unsigned_to_nat(84u);
v___x_446_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__1));
v___x_447_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_448_ = l_mkPanicMessageWithDecl(v___x_447_, v___x_446_, v___x_445_, v___x_444_, v___x_443_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__9(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_454_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__8));
v___x_455_ = lean_unsigned_to_nat(14u);
v___x_456_ = lean_unsigned_to_nat(22u);
v___x_457_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__7));
v___x_458_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__6));
v___x_459_ = l_mkPanicMessageWithDecl(v___x_458_, v___x_457_, v___x_456_, v___x_455_, v___x_454_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21(lean_object* v_pos_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___y_467_; lean_object* v_lineInfos_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___x_484_; 
v_lineInfos_481_ = lean_ctor_get(v_a_461_, 4);
v___f_482_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_483_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
lean_inc(v_pos_460_);
v___x_484_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_481_, v_pos_460_, v___f_482_, v___f_483_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_486_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_485_);
v___y_467_ = v___x_486_;
goto v___jp_466_;
}
else
{
lean_object* v_val_487_; 
v_val_487_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v___x_484_, 1);
v___y_467_ = v_val_487_;
goto v___jp_466_;
}
v___jp_463_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__3, &l_Lean_Fmt_getLineInfo_x21___closed__3_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__3);
v___x_465_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v___x_464_, v_a_461_, v_a_462_);
return v___x_465_;
}
v___jp_466_:
{
lean_object* v_snd_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_479_; 
v_snd_468_ = lean_ctor_get(v___y_467_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v___y_467_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; 
v_unused_480_ = lean_ctor_get(v___y_467_, 0);
lean_dec(v_unused_480_);
v___x_470_ = v___y_467_;
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_snd_468_);
lean_dec(v___y_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_startPos_472_; lean_object* v_endPos_473_; uint8_t v___x_474_; 
v_startPos_472_ = lean_ctor_get(v_snd_468_, 4);
v_endPos_473_ = lean_ctor_get(v_snd_468_, 5);
v___x_474_ = lean_nat_dec_le(v_startPos_472_, v_pos_460_);
if (v___x_474_ == 0)
{
lean_del_object(v___x_470_);
lean_dec(v_snd_468_);
lean_dec(v_pos_460_);
goto v___jp_463_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = lean_nat_dec_le(v_pos_460_, v_endPos_473_);
lean_dec(v_pos_460_);
if (v___x_475_ == 0)
{
lean_del_object(v___x_470_);
lean_dec(v_snd_468_);
goto v___jp_463_;
}
else
{
lean_object* v___x_477_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_a_462_);
lean_ctor_set(v___x_470_, 0, v_snd_468_);
v___x_477_ = v___x_470_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_snd_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_a_462_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___boxed(lean_object* v_pos_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Fmt_getLineInfo_x21(v_pos_488_, v_a_489_, v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1(lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___f_495_; lean_object* v___f_496_; lean_object* v___x_1262__overap_497_; lean_object* v___x_498_; 
v___f_495_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_496_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_496_, 0, v___f_495_);
v___x_1262__overap_497_ = lean_panic_fn_borrowed(v___f_496_, v_msg_492_);
lean_dec_ref(v___f_496_);
lean_inc_ref(v___y_493_);
v___x_498_ = lean_apply_2(v___x_1262__overap_497_, v___y_493_, v___y_494_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfos_spec__1___boxed(lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v_msg_499_, v___y_500_, v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
lean_object* v_array_505_; lean_object* v_start_506_; lean_object* v_stop_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_520_; 
v_array_505_ = lean_ctor_get(v_a_503_, 0);
v_start_506_ = lean_ctor_get(v_a_503_, 1);
v_stop_507_ = lean_ctor_get(v_a_503_, 2);
v_isSharedCheck_520_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_520_ == 0)
{
v___x_509_ = v_a_503_;
v_isShared_510_ = v_isSharedCheck_520_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_stop_507_);
lean_inc(v_start_506_);
lean_inc(v_array_505_);
lean_dec(v_a_503_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_520_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = lean_nat_dec_lt(v_start_506_, v_stop_507_);
if (v___x_511_ == 0)
{
lean_del_object(v___x_509_);
lean_dec(v_stop_507_);
lean_dec(v_start_506_);
lean_dec_ref(v_array_505_);
return v_b_504_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_start_506_, v___x_512_);
lean_inc_ref(v_array_505_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_513_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_array_505_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 2, v_stop_507_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_array_fget(v_array_505_, v_start_506_);
lean_dec(v_start_506_);
lean_dec_ref(v_array_505_);
v___x_517_ = lean_array_push(v_b_504_, v___x_516_);
v_a_503_ = v___x_515_;
v_b_504_ = v___x_517_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfos___closed__3(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_525_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__2));
v___x_526_ = lean_unsigned_to_nat(2u);
v___x_527_ = lean_unsigned_to_nat(92u);
v___x_528_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__1));
v___x_529_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_530_ = l_mkPanicMessageWithDecl(v___x_529_, v___x_528_, v___x_527_, v___x_526_, v___x_525_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos(lean_object* v_pos_531_, lean_object* v_tailPos_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_lineInfos_535_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___f_558_; lean_object* v___f_559_; lean_object* v___y_561_; lean_object* v___x_567_; 
v_lineInfos_535_ = lean_ctor_get(v_a_533_, 4);
v___f_558_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_559_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_567_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_535_, v_pos_531_, v___f_558_, v___f_559_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_569_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_568_);
v___y_561_ = v___x_569_;
goto v___jp_560_;
}
else
{
lean_object* v_val_570_; 
v_val_570_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v___x_567_, 1);
v___y_561_ = v_val_570_;
goto v___jp_560_;
}
v___jp_536_:
{
lean_object* v_fst_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_556_; 
v_fst_539_ = lean_ctor_get(v___y_538_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___y_538_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___y_538_, 1);
lean_dec(v_unused_557_);
v___x_541_ = v___y_538_;
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_fst_539_);
lean_dec(v___y_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_556_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_fst_539_, v___x_543_);
lean_dec(v_fst_539_);
lean_inc_ref(v_lineInfos_535_);
v___x_545_ = l_Array_toSubarray___redArg(v_lineInfos_535_, v___y_537_, v___x_544_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_548_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_545_, v___x_547_);
v___x_549_ = lean_array_get_size(v___x_548_);
v___x_550_ = lean_nat_dec_eq(v___x_549_, v___x_546_);
if (v___x_550_ == 0)
{
lean_object* v___x_552_; 
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v_a_534_);
lean_ctor_set(v___x_541_, 0, v___x_548_);
v___x_552_ = v___x_541_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_a_534_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v___x_548_);
lean_del_object(v___x_541_);
v___x_554_ = lean_obj_once(&l_Lean_Fmt_getLineInfos___closed__3, &l_Lean_Fmt_getLineInfos___closed__3_once, _init_l_Lean_Fmt_getLineInfos___closed__3);
v___x_555_ = l_panic___at___00Lean_Fmt_getLineInfos_spec__1(v___x_554_, v_a_533_, v_a_534_);
return v___x_555_;
}
}
}
v___jp_560_:
{
lean_object* v_fst_562_; lean_object* v___x_563_; 
v_fst_562_ = lean_ctor_get(v___y_561_, 0);
lean_inc(v_fst_562_);
lean_dec_ref(v___y_561_);
v___x_563_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_535_, v_tailPos_532_, v___f_558_, v___f_559_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_565_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_564_);
v___y_537_ = v_fst_562_;
v___y_538_ = v___x_565_;
goto v___jp_536_;
}
else
{
lean_object* v_val_566_; 
v_val_566_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v___x_563_, 1);
v___y_537_ = v_fst_562_;
v___y_538_ = v_val_566_;
goto v___jp_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfos___boxed(lean_object* v_pos_571_, lean_object* v_tailPos_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Fmt_getLineInfos(v_pos_571_, v_tailPos_572_, v_a_573_, v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0(lean_object* v_inst_576_, lean_object* v_R_577_, lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v_a_578_, v_b_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f(lean_object* v_pos_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_lineInfos_584_; lean_object* v___y_586_; lean_object* v___f_606_; lean_object* v___f_607_; lean_object* v___x_608_; 
v_lineInfos_584_ = lean_ctor_get(v_a_582_, 4);
v___f_606_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_607_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_608_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_584_, v_pos_581_, v___f_606_, v___f_607_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_610_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_609_);
v___y_586_ = v___x_610_;
goto v___jp_585_;
}
else
{
lean_object* v_val_611_; 
v_val_611_ = lean_ctor_get(v___x_608_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v___x_608_, 1);
v___y_586_ = v_val_611_;
goto v___jp_585_;
}
v___jp_585_:
{
lean_object* v_fst_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_604_; 
v_fst_587_ = lean_ctor_get(v___y_586_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___y_586_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v___y_586_, 1);
lean_dec(v_unused_605_);
v___x_589_ = v___y_586_;
v_isShared_590_ = v_isSharedCheck_604_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_fst_587_);
lean_dec(v___y_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_604_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_add(v_fst_587_, v___x_591_);
lean_dec(v_fst_587_);
v___x_593_ = lean_array_get_size(v_lineInfos_584_);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_597_; 
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_a_583_);
lean_ctor_set(v___x_589_, 0, v___x_595_);
v___x_597_ = v___x_589_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_a_583_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_599_ = lean_array_fget_borrowed(v_lineInfos_584_, v___x_592_);
lean_dec(v___x_592_);
lean_inc(v___x_599_);
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_a_583_);
lean_ctor_set(v___x_589_, 0, v___x_600_);
v___x_602_ = v___x_589_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_a_583_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getNextLineInfo_x3f___boxed(lean_object* v_pos_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Fmt_getNextLineInfo_x3f(v_pos_612_, v_a_613_, v_a_614_);
lean_dec_ref(v_a_613_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(size_t v_sz_616_, size_t v_i_617_, lean_object* v_bs_618_, lean_object* v___y_619_){
_start:
{
uint8_t v___x_620_; 
v___x_620_ = lean_usize_dec_lt(v_i_617_, v_sz_616_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_bs_618_);
lean_ctor_set(v___x_621_, 1, v___y_619_);
return v___x_621_;
}
else
{
lean_object* v_v_622_; lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___x_625_; lean_object* v_bs_x27_626_; lean_object* v_a_628_; lean_object* v_a_629_; 
v_v_622_ = lean_array_uget_borrowed(v_bs_618_, v_i_617_);
v_fst_623_ = lean_ctor_get(v_v_622_, 0);
lean_inc(v_fst_623_);
v_snd_624_ = lean_ctor_get(v_v_622_, 1);
lean_inc(v_snd_624_);
v___x_625_ = lean_unsigned_to_nat(0u);
v_bs_x27_626_ = lean_array_uset(v_bs_618_, v_i_617_, v___x_625_);
if (lean_obj_tag(v_snd_624_) == 0)
{
v_a_628_ = v_fst_623_;
v_a_629_ = v___y_619_;
goto v___jp_627_;
}
else
{
lean_object* v_val_634_; lean_object* v_doc_635_; lean_object* v_metaData_636_; lean_object* v___x_637_; 
v_val_634_ = lean_ctor_get(v_snd_624_, 0);
lean_inc(v_val_634_);
lean_dec_ref_known(v_snd_624_, 1);
v_doc_635_ = lean_ctor_get(v_fst_623_, 0);
lean_inc(v_doc_635_);
v_metaData_636_ = lean_ctor_get(v_fst_623_, 1);
lean_inc(v_metaData_636_);
lean_dec(v_fst_623_);
v___x_637_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_635_, v_val_634_, v___y_619_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v_a_639_; lean_object* v_doc_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
v_a_639_ = lean_ctor_get(v___x_637_, 1);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_637_, 2);
v_doc_640_ = lean_ctor_get(v_a_638_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_a_638_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v_a_638_, 1);
lean_dec(v_unused_648_);
v___x_642_ = v_a_638_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_doc_640_);
lean_dec(v_a_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_metaData_636_);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_doc_640_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_metaData_636_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
v_a_628_ = v___x_645_;
v_a_629_ = v_a_639_;
goto v___jp_627_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_metaData_636_);
lean_dec_ref(v_bs_x27_626_);
v_a_649_ = lean_ctor_get(v___x_637_, 0);
v_a_650_ = lean_ctor_get(v___x_637_, 1);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_637_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_inc(v_a_649_);
lean_dec(v___x_637_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_649_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
v___jp_627_:
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_617_, v___x_630_);
v___x_632_ = lean_array_uset(v_bs_x27_626_, v_i_617_, v_a_628_);
v_i_617_ = v___x_631_;
v_bs_618_ = v___x_632_;
v___y_619_ = v_a_629_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg___boxed(lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_bs_660_, lean_object* v___y_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_663_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_boxed_662_, v_i_boxed_663_, v_bs_660_, v___y_661_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace(lean_object* v_stx_665_, lean_object* v_fmtLeading_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_stx_665_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_671_; 
v_val_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_Lean_Syntax_getLeading_x3f(v_val_670_);
if (lean_obj_tag(v___x_671_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; 
v_val_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v___x_671_, 1);
lean_inc_ref(v_a_667_);
v___x_673_ = lean_apply_4(v_fmtLeading_666_, v_val_670_, v_val_672_, v_a_667_, v_a_668_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v_a_675_; size_t v_sz_676_; size_t v___x_677_; lean_object* v___x_678_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
v_a_675_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_673_, 2);
v_sz_676_ = lean_array_size(v_a_674_);
v___x_677_ = ((size_t)0ULL);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_676_, v___x_677_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_a_680_ = lean_ctor_get(v___x_678_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_688_ == 0)
{
v___x_682_ = v___x_678_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = l_Lean_Fmt_TaggedDoc_join(v_a_679_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_680_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_689_; lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_689_ = lean_ctor_get(v___x_678_, 0);
v_a_690_ = lean_ctor_get(v___x_678_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_678_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_inc(v_a_689_);
lean_dec(v___x_678_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_689_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_698_ = lean_ctor_get(v___x_673_, 0);
v_a_699_ = lean_ctor_get(v___x_673_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_673_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_inc(v_a_698_);
lean_dec(v___x_673_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_698_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v___x_671_);
lean_dec(v_val_670_);
lean_dec_ref(v_fmtLeading_666_);
v___x_707_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v_a_668_);
return v___x_708_;
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v___x_669_);
lean_dec_ref(v_fmtLeading_666_);
v___x_709_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_a_668_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace___boxed(lean_object* v_stx_711_, lean_object* v_fmtLeading_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_711_, v_fmtLeading_712_, v_a_713_, v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(size_t v_sz_716_, size_t v_i_717_, lean_object* v_bs_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_716_, v_i_717_, v_bs_718_, v___y_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___boxed(lean_object* v_sz_722_, lean_object* v_i_723_, lean_object* v_bs_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
size_t v_sz_boxed_727_; size_t v_i_boxed_728_; lean_object* v_res_729_; 
v_sz_boxed_727_ = lean_unbox_usize(v_sz_722_);
lean_dec(v_sz_722_);
v_i_boxed_728_ = lean_unbox_usize(v_i_723_);
lean_dec(v_i_723_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(v_sz_boxed_727_, v_i_boxed_728_, v_bs_724_, v___y_725_, v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace(lean_object* v_stx_730_, lean_object* v_fmtTrailing_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v_stx_730_);
if (lean_obj_tag(v___x_734_) == 1)
{
lean_object* v_val_735_; lean_object* v___x_736_; 
v_val_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_Syntax_getTrailing_x3f(v_val_735_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_738_; 
v_val_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___x_736_, 1);
lean_inc_ref(v_a_732_);
v___x_738_ = lean_apply_4(v_fmtTrailing_731_, v_val_735_, v_val_737_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v_a_740_; size_t v_sz_741_; size_t v___x_742_; lean_object* v___x_743_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
v_a_740_ = lean_ctor_get(v___x_738_, 1);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_738_, 2);
v_sz_741_ = lean_array_size(v_a_739_);
v___x_742_ = ((size_t)0ULL);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_741_, v___x_742_, v_a_739_, v_a_740_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_753_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_a_745_ = lean_ctor_get(v___x_743_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_753_ == 0)
{
v___x_747_ = v___x_743_;
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = l_Lean_Fmt_TaggedDoc_join(v_a_744_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_a_745_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
else
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_754_ = lean_ctor_get(v___x_743_, 0);
v_a_755_ = lean_ctor_get(v___x_743_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_743_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_inc(v_a_754_);
lean_dec(v___x_743_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_754_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
v_a_763_ = lean_ctor_get(v___x_738_, 0);
v_a_764_ = lean_ctor_get(v___x_738_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_738_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_inc(v_a_763_);
lean_dec(v___x_738_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_763_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v___x_736_);
lean_dec(v_val_735_);
lean_dec_ref(v_fmtTrailing_731_);
v___x_772_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_a_733_);
return v___x_773_;
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v___x_734_);
lean_dec_ref(v_fmtTrailing_731_);
v___x_774_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v_a_733_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace___boxed(lean_object* v_stx_776_, lean_object* v_fmtTrailing_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_776_, v_fmtTrailing_777_, v_a_778_, v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(lean_object* v_env_781_, lean_object* v_opts_782_, lean_object* v_kind_783_){
_start:
{
uint8_t v___x_784_; lean_object* v___x_785_; 
v___x_784_ = 1;
v___x_785_ = l_Lean_Environment_evalConst___redArg(v_env_781_, v_opts_782_, v_kind_783_, v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___x_786_; 
lean_dec_ref_known(v___x_785_, 1);
v___x_786_ = lean_box(0);
return v___x_786_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_785_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1___boxed(lean_object* v_env_795_, lean_object* v_opts_796_, lean_object* v_kind_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(v_env_795_, v_opts_796_, v_kind_797_);
lean_dec(v_kind_797_);
lean_dec_ref(v_opts_796_);
lean_dec_ref(v_env_795_);
return v_res_798_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_box(0);
v___x_800_ = lean_unsigned_to_nat(16u);
v___x_801_ = lean_mk_array(v___x_800_, v___x_799_);
return v___x_801_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v___x_802_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(lean_object* v_env_816_, lean_object* v_opts_817_, lean_object* v_kind_818_){
_start:
{
uint8_t v___x_819_; uint8_t v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; uint8_t v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; uint8_t v___y_840_; lean_object* v___x_888_; 
v___x_819_ = 0;
lean_inc(v_kind_818_);
lean_inc_ref(v_env_816_);
v___x_888_ = l_Lean_Environment_find_x3f(v_env_816_, v_kind_818_, v___x_819_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; 
lean_dec(v_kind_818_);
lean_dec_ref(v_env_816_);
v___x_889_ = lean_box(0);
return v___x_889_;
}
else
{
lean_object* v_val_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v_val_890_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_888_, 1);
v___x_891_ = l_Lean_ConstantInfo_type(v_val_890_);
lean_dec(v_val_890_);
v___x_892_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_893_ = l_Lean_Expr_isConstOf(v___x_891_, v___x_892_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_895_ = l_Lean_Expr_isConstOf(v___x_891_, v___x_894_);
lean_dec_ref(v___x_891_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_dec(v_kind_818_);
lean_dec_ref(v_env_816_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
else
{
goto v___jp_853_;
}
}
else
{
lean_dec_ref(v___x_891_);
goto v___jp_853_;
}
}
v___jp_820_:
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_nat_add(v___y_824_, v___x_826_);
lean_dec(v___y_824_);
v___x_828_ = lean_nat_dec_eq(v___x_827_, v___y_822_);
lean_dec(v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v___y_825_);
lean_dec(v___y_823_);
lean_dec(v___y_822_);
v___x_829_ = lean_box(0);
return v___x_829_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = lean_nat_dec_eq(v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec(v___y_822_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec(v___y_825_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_833_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_833_, 0, v___y_825_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*2, v___y_821_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*2 + 1, v___x_819_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
}
v___jp_835_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_inc(v___y_838_);
lean_inc(v___y_837_);
lean_inc(v___y_839_);
v___x_841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_841_, 0, v___y_839_);
lean_ctor_set(v___x_841_, 1, v___y_837_);
lean_ctor_set(v___x_841_, 2, v___y_838_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
if (v___y_840_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_eq(v___y_839_, v___y_838_);
if (v___x_843_ == 0)
{
v___y_821_ = v___y_836_;
v___y_822_ = v___y_837_;
v___y_823_ = v___y_838_;
v___y_824_ = v___y_839_;
v___y_825_ = v___x_842_;
goto v___jp_820_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_add(v___y_838_, v___x_844_);
v___x_846_ = lean_nat_dec_eq(v___y_837_, v___x_845_);
lean_dec(v___x_845_);
if (v___x_846_ == 0)
{
v___y_821_ = v___y_836_;
v___y_822_ = v___y_837_;
v___y_823_ = v___y_838_;
v___y_824_ = v___y_839_;
v___y_825_ = v___x_842_;
goto v___jp_820_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
v___x_847_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_848_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_848_, 0, v___x_842_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*2, v___x_819_);
lean_ctor_set_uint8(v___x_848_, sizeof(void*)*2 + 1, v___x_819_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
v___x_850_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_851_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_851_, 0, v___x_842_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*2, v___x_819_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*2 + 1, v___x_819_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
v___jp_853_:
{
uint8_t v___x_854_; lean_object* v___x_855_; 
v___x_854_ = 1;
v___x_855_ = l_Lean_Environment_evalConst___redArg(v_env_816_, v_opts_817_, v_kind_818_, v___x_854_);
lean_dec(v_kind_818_);
lean_dec_ref(v_env_816_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_856_; 
lean_dec_ref_known(v___x_855_, 1);
v___x_856_ = lean_box(0);
return v___x_856_;
}
else
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_855_, 1);
if (lean_obj_tag(v_a_857_) == 4)
{
lean_object* v_p_858_; 
v_p_858_ = lean_ctor_get(v_a_857_, 3);
lean_inc_ref(v_p_858_);
if (lean_obj_tag(v_p_858_) == 2)
{
lean_object* v_name_859_; 
v_name_859_ = lean_ctor_get(v_p_858_, 0);
lean_inc(v_name_859_);
if (lean_obj_tag(v_name_859_) == 1)
{
lean_object* v_pre_860_; 
v_pre_860_ = lean_ctor_get(v_name_859_, 0);
if (lean_obj_tag(v_pre_860_) == 0)
{
lean_object* v_prec_861_; lean_object* v_lhsPrec_862_; lean_object* v_p_u2081_863_; lean_object* v_p_u2082_864_; lean_object* v_str_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_prec_861_ = lean_ctor_get(v_a_857_, 1);
lean_inc(v_prec_861_);
v_lhsPrec_862_ = lean_ctor_get(v_a_857_, 2);
lean_inc(v_lhsPrec_862_);
lean_dec_ref_known(v_a_857_, 4);
v_p_u2081_863_ = lean_ctor_get(v_p_858_, 1);
lean_inc_ref(v_p_u2081_863_);
v_p_u2082_864_ = lean_ctor_get(v_p_858_, 2);
lean_inc_ref(v_p_u2082_864_);
lean_dec_ref_known(v_p_858_, 3);
v_str_865_ = lean_ctor_get(v_name_859_, 1);
lean_inc_ref(v_str_865_);
lean_dec_ref_known(v_name_859_, 2);
v___x_866_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_867_ = lean_string_dec_eq(v_str_865_, v___x_866_);
lean_dec_ref(v_str_865_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec_ref(v_p_u2082_864_);
lean_dec_ref(v_p_u2081_863_);
lean_dec(v_lhsPrec_862_);
lean_dec(v_prec_861_);
v___x_868_ = lean_box(0);
return v___x_868_;
}
else
{
if (lean_obj_tag(v_p_u2081_863_) == 5)
{
lean_dec_ref_known(v_p_u2081_863_, 1);
if (lean_obj_tag(v_p_u2082_864_) == 7)
{
lean_object* v_catName_869_; 
v_catName_869_ = lean_ctor_get(v_p_u2082_864_, 0);
lean_inc(v_catName_869_);
if (lean_obj_tag(v_catName_869_) == 1)
{
lean_object* v_pre_870_; 
v_pre_870_ = lean_ctor_get(v_catName_869_, 0);
if (lean_obj_tag(v_pre_870_) == 0)
{
lean_object* v_rbp_871_; lean_object* v_str_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_rbp_871_ = lean_ctor_get(v_p_u2082_864_, 1);
lean_inc(v_rbp_871_);
lean_dec_ref_known(v_p_u2082_864_, 2);
v_str_872_ = lean_ctor_get(v_catName_869_, 1);
lean_inc_ref(v_str_872_);
lean_dec_ref_known(v_catName_869_, 2);
v___x_873_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_874_ = lean_string_dec_eq(v_str_872_, v___x_873_);
lean_dec_ref(v_str_872_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; 
lean_dec(v_rbp_871_);
lean_dec(v_lhsPrec_862_);
lean_dec(v_prec_861_);
v___x_875_ = lean_box(0);
return v___x_875_;
}
else
{
uint8_t v___x_876_; 
v___x_876_ = lean_nat_dec_eq(v_prec_861_, v_lhsPrec_862_);
if (v___x_876_ == 0)
{
v___y_836_ = v___x_874_;
v___y_837_ = v_lhsPrec_862_;
v___y_838_ = v_rbp_871_;
v___y_839_ = v_prec_861_;
v___y_840_ = v___x_819_;
goto v___jp_835_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_unsigned_to_nat(1u);
v___x_878_ = lean_nat_add(v_lhsPrec_862_, v___x_877_);
v___x_879_ = lean_nat_dec_eq(v___x_878_, v_rbp_871_);
lean_dec(v___x_878_);
v___y_836_ = v___x_874_;
v___y_837_ = v_lhsPrec_862_;
v___y_838_ = v_rbp_871_;
v___y_839_ = v_prec_861_;
v___y_840_ = v___x_879_;
goto v___jp_835_;
}
}
}
else
{
lean_object* v___x_880_; 
lean_dec_ref_known(v_catName_869_, 2);
lean_dec_ref_known(v_p_u2082_864_, 2);
lean_dec(v_lhsPrec_862_);
lean_dec(v_prec_861_);
v___x_880_ = lean_box(0);
return v___x_880_;
}
}
else
{
lean_object* v___x_881_; 
lean_dec(v_catName_869_);
lean_dec_ref_known(v_p_u2082_864_, 2);
lean_dec(v_lhsPrec_862_);
lean_dec(v_prec_861_);
v___x_881_ = lean_box(0);
return v___x_881_;
}
}
else
{
lean_object* v___x_882_; 
lean_dec_ref(v_p_u2082_864_);
lean_dec(v_lhsPrec_862_);
lean_dec(v_prec_861_);
v___x_882_ = lean_box(0);
return v___x_882_;
}
}
else
{
lean_object* v___x_883_; 
lean_dec_ref(v_p_u2082_864_);
lean_dec_ref(v_p_u2081_863_);
lean_dec(v_lhsPrec_862_);
lean_dec(v_prec_861_);
v___x_883_ = lean_box(0);
return v___x_883_;
}
}
}
else
{
lean_object* v___x_884_; 
lean_dec_ref_known(v_name_859_, 2);
lean_dec_ref_known(v_p_858_, 3);
lean_dec_ref_known(v_a_857_, 4);
v___x_884_ = lean_box(0);
return v___x_884_;
}
}
else
{
lean_object* v___x_885_; 
lean_dec(v_name_859_);
lean_dec_ref_known(v_p_858_, 3);
lean_dec_ref_known(v_a_857_, 4);
v___x_885_ = lean_box(0);
return v___x_885_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec_ref_known(v_a_857_, 4);
lean_dec_ref(v_p_858_);
v___x_886_ = lean_box(0);
return v___x_886_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v_a_857_);
v___x_887_ = lean_box(0);
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___boxed(lean_object* v_env_897_, lean_object* v_opts_898_, lean_object* v_kind_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_897_, v_opts_898_, v_kind_899_);
lean_dec_ref(v_opts_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(lean_object* v_env_901_, lean_object* v_opts_902_, lean_object* v_kind_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = l_Lean_Fmt_infixFmtAttribute;
lean_inc_ref(v_env_901_);
v___x_905_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_904_, v_env_901_, v_kind_903_);
v___x_906_ = l_List_head_x3f___redArg(v___x_905_);
lean_dec(v___x_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_907_; 
v___x_907_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_901_, v_opts_902_, v_kind_903_);
return v___x_907_;
}
else
{
lean_dec(v_kind_903_);
lean_dec_ref(v_env_901_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f___boxed(lean_object* v_env_908_, lean_object* v_opts_909_, lean_object* v_kind_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_908_, v_opts_909_, v_kind_910_);
lean_dec_ref(v_opts_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(lean_object* v_env_912_, lean_object* v_opts_913_, lean_object* v_kind_914_){
_start:
{
uint8_t v___x_915_; lean_object* v___x_916_; 
v___x_915_ = 1;
v___x_916_ = l_Lean_Environment_evalConst___redArg(v_env_912_, v_opts_913_, v_kind_914_, v___x_915_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; 
lean_dec_ref_known(v___x_916_, 1);
v___x_917_ = lean_box(0);
return v___x_917_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
v_a_918_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_916_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_916_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1___boxed(lean_object* v_env_926_, lean_object* v_opts_927_, lean_object* v_kind_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(v_env_926_, v_opts_927_, v_kind_928_);
lean_dec(v_kind_928_);
lean_dec_ref(v_opts_927_);
lean_dec_ref(v_env_926_);
return v_res_929_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(lean_object* v_env_930_, lean_object* v_opts_931_, lean_object* v_kind_932_){
_start:
{
uint8_t v___x_933_; lean_object* v___x_934_; 
v___x_933_ = 0;
lean_inc(v_kind_932_);
lean_inc_ref(v_env_930_);
v___x_934_ = l_Lean_Environment_find_x3f(v_env_930_, v_kind_932_, v___x_933_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_dec(v_kind_932_);
lean_dec_ref(v_env_930_);
return v___x_933_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_val_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = l_Lean_ConstantInfo_type(v_val_935_);
lean_dec(v_val_935_);
v___x_937_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_938_ = l_Lean_Expr_isConstOf(v___x_936_, v___x_937_);
lean_dec_ref(v___x_936_);
if (v___x_938_ == 0)
{
lean_dec(v_kind_932_);
lean_dec_ref(v_env_930_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Environment_evalConst___redArg(v_env_930_, v_opts_931_, v_kind_932_, v___x_938_);
lean_dec(v_kind_932_);
lean_dec_ref(v_env_930_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_dec_ref_known(v___x_939_, 1);
return v___x_933_;
}
else
{
lean_object* v_a_940_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_939_, 1);
if (lean_obj_tag(v_a_940_) == 3)
{
lean_object* v_p_941_; 
v_p_941_ = lean_ctor_get(v_a_940_, 2);
lean_inc_ref(v_p_941_);
if (lean_obj_tag(v_p_941_) == 2)
{
lean_object* v_name_942_; 
v_name_942_ = lean_ctor_get(v_p_941_, 0);
lean_inc(v_name_942_);
if (lean_obj_tag(v_name_942_) == 1)
{
lean_object* v_pre_943_; 
v_pre_943_ = lean_ctor_get(v_name_942_, 0);
if (lean_obj_tag(v_pre_943_) == 0)
{
lean_object* v_prec_944_; lean_object* v_p_u2081_945_; lean_object* v_p_u2082_946_; lean_object* v_str_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_prec_944_ = lean_ctor_get(v_a_940_, 1);
lean_inc(v_prec_944_);
lean_dec_ref_known(v_a_940_, 3);
v_p_u2081_945_ = lean_ctor_get(v_p_941_, 1);
lean_inc_ref(v_p_u2081_945_);
v_p_u2082_946_ = lean_ctor_get(v_p_941_, 2);
lean_inc_ref(v_p_u2082_946_);
lean_dec_ref_known(v_p_941_, 3);
v_str_947_ = lean_ctor_get(v_name_942_, 1);
lean_inc_ref(v_str_947_);
lean_dec_ref_known(v_name_942_, 2);
v___x_948_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_949_ = lean_string_dec_eq(v_str_947_, v___x_948_);
lean_dec_ref(v_str_947_);
if (v___x_949_ == 0)
{
lean_dec_ref(v_p_u2082_946_);
lean_dec_ref(v_p_u2081_945_);
lean_dec(v_prec_944_);
return v___x_949_;
}
else
{
if (lean_obj_tag(v_p_u2081_945_) == 5)
{
lean_dec_ref_known(v_p_u2081_945_, 1);
if (lean_obj_tag(v_p_u2082_946_) == 7)
{
lean_object* v_catName_950_; 
v_catName_950_ = lean_ctor_get(v_p_u2082_946_, 0);
lean_inc(v_catName_950_);
if (lean_obj_tag(v_catName_950_) == 1)
{
lean_object* v_pre_951_; 
v_pre_951_ = lean_ctor_get(v_catName_950_, 0);
if (lean_obj_tag(v_pre_951_) == 0)
{
lean_object* v_rbp_952_; lean_object* v_str_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v_rbp_952_ = lean_ctor_get(v_p_u2082_946_, 1);
lean_inc(v_rbp_952_);
lean_dec_ref_known(v_p_u2082_946_, 2);
v_str_953_ = lean_ctor_get(v_catName_950_, 1);
lean_inc_ref(v_str_953_);
lean_dec_ref_known(v_catName_950_, 2);
v___x_954_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_955_ = lean_string_dec_eq(v_str_953_, v___x_954_);
lean_dec_ref(v_str_953_);
if (v___x_955_ == 0)
{
lean_dec(v_rbp_952_);
lean_dec(v_prec_944_);
return v___x_955_;
}
else
{
uint8_t v___x_956_; 
v___x_956_ = lean_nat_dec_eq(v_prec_944_, v_rbp_952_);
lean_dec(v_rbp_952_);
lean_dec(v_prec_944_);
return v___x_956_;
}
}
else
{
lean_dec_ref_known(v_catName_950_, 2);
lean_dec_ref_known(v_p_u2082_946_, 2);
lean_dec(v_prec_944_);
return v___x_933_;
}
}
else
{
lean_dec_ref_known(v_p_u2082_946_, 2);
lean_dec(v_catName_950_);
lean_dec(v_prec_944_);
return v___x_933_;
}
}
else
{
lean_dec_ref(v_p_u2082_946_);
lean_dec(v_prec_944_);
return v___x_933_;
}
}
else
{
lean_dec_ref(v_p_u2082_946_);
lean_dec_ref(v_p_u2081_945_);
lean_dec(v_prec_944_);
return v___x_933_;
}
}
}
else
{
lean_dec_ref_known(v_name_942_, 2);
lean_dec_ref_known(v_p_941_, 3);
lean_dec_ref_known(v_a_940_, 3);
return v___x_933_;
}
}
else
{
lean_dec_ref_known(v_p_941_, 3);
lean_dec(v_name_942_);
lean_dec_ref_known(v_a_940_, 3);
return v___x_933_;
}
}
else
{
lean_dec_ref(v_p_941_);
lean_dec_ref_known(v_a_940_, 3);
return v___x_933_;
}
}
else
{
lean_dec(v_a_940_);
return v___x_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter___boxed(lean_object* v_env_957_, lean_object* v_opts_958_, lean_object* v_kind_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_957_, v_opts_958_, v_kind_959_);
lean_dec_ref(v_opts_958_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(lean_object* v_env_962_, lean_object* v_opts_963_, lean_object* v_kind_964_){
_start:
{
uint8_t v___x_965_; lean_object* v___x_966_; 
v___x_965_ = 1;
v___x_966_ = l_Lean_Environment_evalConst___redArg(v_env_962_, v_opts_963_, v_kind_964_, v___x_965_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; 
lean_dec_ref_known(v___x_966_, 1);
v___x_967_ = lean_box(0);
return v___x_967_;
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_966_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1___boxed(lean_object* v_env_976_, lean_object* v_opts_977_, lean_object* v_kind_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(v_env_976_, v_opts_977_, v_kind_978_);
lean_dec(v_kind_978_);
lean_dec_ref(v_opts_977_);
lean_dec_ref(v_env_976_);
return v_res_979_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(lean_object* v_env_980_, lean_object* v_opts_981_, lean_object* v_kind_982_){
_start:
{
uint8_t v___x_983_; lean_object* v___x_984_; 
v___x_983_ = 0;
lean_inc(v_kind_982_);
lean_inc_ref(v_env_980_);
v___x_984_ = l_Lean_Environment_find_x3f(v_env_980_, v_kind_982_, v___x_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_dec(v_kind_982_);
lean_dec_ref(v_env_980_);
return v___x_983_;
}
else
{
lean_object* v_val_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_val_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v___x_984_, 1);
v___x_986_ = l_Lean_ConstantInfo_type(v_val_985_);
lean_dec(v_val_985_);
v___x_987_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_988_ = l_Lean_Expr_isConstOf(v___x_986_, v___x_987_);
lean_dec_ref(v___x_986_);
if (v___x_988_ == 0)
{
lean_dec(v_kind_982_);
lean_dec_ref(v_env_980_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Environment_evalConst___redArg(v_env_980_, v_opts_981_, v_kind_982_, v___x_988_);
lean_dec(v_kind_982_);
lean_dec_ref(v_env_980_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_dec_ref_known(v___x_989_, 1);
return v___x_983_;
}
else
{
lean_object* v_a_990_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
if (lean_obj_tag(v_a_990_) == 4)
{
lean_object* v_p_991_; 
v_p_991_ = lean_ctor_get(v_a_990_, 3);
if (lean_obj_tag(v_p_991_) == 5)
{
lean_object* v_prec_992_; lean_object* v_lhsPrec_993_; uint8_t v___x_994_; 
v_prec_992_ = lean_ctor_get(v_a_990_, 1);
lean_inc(v_prec_992_);
v_lhsPrec_993_ = lean_ctor_get(v_a_990_, 2);
lean_inc(v_lhsPrec_993_);
lean_dec_ref_known(v_a_990_, 4);
v___x_994_ = lean_nat_dec_eq(v_prec_992_, v_lhsPrec_993_);
lean_dec(v_lhsPrec_993_);
lean_dec(v_prec_992_);
return v___x_994_;
}
else
{
lean_dec_ref_known(v_a_990_, 4);
return v___x_983_;
}
}
else
{
lean_dec(v_a_990_);
return v___x_983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter___boxed(lean_object* v_env_995_, lean_object* v_opts_996_, lean_object* v_kind_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_995_, v_opts_996_, v_kind_997_);
lean_dec_ref(v_opts_996_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(lean_object* v_a_1126_, lean_object* v_as_1127_, size_t v_i_1128_, size_t v_stop_1129_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_usize_dec_eq(v_i_1128_, v_stop_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_array_uget_borrowed(v_as_1127_, v_i_1128_);
v___x_1132_ = lean_name_eq(v_a_1126_, v___x_1131_);
if (v___x_1132_ == 0)
{
size_t v___x_1133_; size_t v___x_1134_; 
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_add(v_i_1128_, v___x_1133_);
v_i_1128_ = v___x_1134_;
goto _start;
}
else
{
return v___x_1132_;
}
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = 0;
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0___boxed(lean_object* v_a_1137_, lean_object* v_as_1138_, lean_object* v_i_1139_, lean_object* v_stop_1140_){
_start:
{
size_t v_i_boxed_1141_; size_t v_stop_boxed_1142_; uint8_t v_res_1143_; lean_object* v_r_1144_; 
v_i_boxed_1141_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_stop_boxed_1142_ = lean_unbox_usize(v_stop_1140_);
lean_dec(v_stop_1140_);
v_res_1143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1137_, v_as_1138_, v_i_boxed_1141_, v_stop_boxed_1142_);
lean_dec_ref(v_as_1138_);
lean_dec(v_a_1137_);
v_r_1144_ = lean_box(v_res_1143_);
return v_r_1144_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(lean_object* v_as_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_array_get_size(v_as_1145_);
v___x_1149_ = lean_nat_dec_lt(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
return v___x_1149_;
}
else
{
size_t v___x_1150_; size_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = lean_usize_of_nat(v___x_1148_);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1146_, v_as_1145_, v___x_1150_, v___x_1151_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0___boxed(lean_object* v_as_1153_, lean_object* v_a_1154_){
_start:
{
uint8_t v_res_1155_; lean_object* v_r_1156_; 
v_res_1155_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v_as_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_as_1153_);
v_r_1156_ = lean_box(v_res_1155_);
return v_r_1156_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(lean_object* v_x_1162_){
_start:
{
switch(lean_obj_tag(v_x_1162_))
{
case 5:
{
uint8_t v___x_1163_; 
v___x_1163_ = 1;
return v___x_1163_;
}
case 6:
{
uint8_t v___x_1164_; 
v___x_1164_ = 1;
return v___x_1164_;
}
case 12:
{
uint8_t v___x_1165_; 
v___x_1165_ = 1;
return v___x_1165_;
}
case 0:
{
lean_object* v_name_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_name_1166_ = lean_ctor_get(v_x_1162_, 0);
v___x_1167_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases));
v___x_1168_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1167_, v_name_1166_);
return v___x_1168_;
}
case 1:
{
lean_object* v_name_1169_; lean_object* v_p_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_name_1169_ = lean_ctor_get(v_x_1162_, 0);
v_p_1170_ = lean_ctor_get(v_x_1162_, 1);
v___x_1171_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases));
v___x_1172_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1171_, v_name_1169_);
if (v___x_1172_ == 0)
{
return v___x_1172_;
}
else
{
v_x_1162_ = v_p_1170_;
goto _start;
}
}
case 2:
{
lean_object* v_name_1174_; lean_object* v_p_u2081_1175_; lean_object* v_p_u2082_1176_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_name_1174_ = lean_ctor_get(v_x_1162_, 0);
v_p_u2081_1175_ = lean_ctor_get(v_x_1162_, 1);
v_p_u2082_1176_ = lean_ctor_get(v_x_1162_, 2);
v___x_1180_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0));
v___x_1181_ = lean_name_eq(v_name_1174_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2));
v___x_1183_ = lean_name_eq(v_name_1174_, v___x_1182_);
if (v___x_1183_ == 0)
{
return v___x_1183_;
}
else
{
goto v___jp_1177_;
}
}
else
{
goto v___jp_1177_;
}
v___jp_1177_:
{
uint8_t v___x_1178_; 
v___x_1178_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_p_u2081_1175_);
if (v___x_1178_ == 0)
{
return v___x_1178_;
}
else
{
v_x_1162_ = v_p_u2082_1176_;
goto _start;
}
}
}
case 3:
{
lean_object* v_p_1184_; 
v_p_1184_ = lean_ctor_get(v_x_1162_, 2);
v_x_1162_ = v_p_1184_;
goto _start;
}
case 9:
{
lean_object* v_p_1186_; 
v_p_1186_ = lean_ctor_get(v_x_1162_, 2);
v_x_1162_ = v_p_1186_;
goto _start;
}
default: 
{
uint8_t v___x_1188_; 
v___x_1188_ = 0;
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___boxed(lean_object* v_x_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_x_1189_);
lean_dec_ref(v_x_1189_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(lean_object* v_env_1192_, lean_object* v_opts_1193_, lean_object* v_kind_1194_){
_start:
{
uint8_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = 1;
v___x_1196_ = l_Lean_Environment_evalConst___redArg(v_env_1192_, v_opts_1193_, v_kind_1194_, v___x_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref_known(v___x_1196_, 1);
v___x_1197_ = lean_box(0);
return v___x_1197_;
}
else
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1___boxed(lean_object* v_env_1206_, lean_object* v_opts_1207_, lean_object* v_kind_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(v_env_1206_, v_opts_1207_, v_kind_1208_);
lean_dec(v_kind_1208_);
lean_dec_ref(v_opts_1207_);
lean_dec_ref(v_env_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(lean_object* v_env_1210_, lean_object* v_opts_1211_, lean_object* v_kind_1212_){
_start:
{
uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = 0;
lean_inc(v_kind_1212_);
lean_inc_ref(v_env_1210_);
v___x_1214_ = l_Lean_Environment_find_x3f(v_env_1210_, v_kind_1212_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_dec(v_kind_1212_);
lean_dec_ref(v_env_1210_);
return v___x_1213_;
}
else
{
lean_object* v_val_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l_Lean_ConstantInfo_type(v_val_1215_);
lean_dec(v_val_1215_);
v___x_1217_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_1218_ = l_Lean_Expr_isConstOf(v___x_1216_, v___x_1217_);
lean_dec_ref(v___x_1216_);
if (v___x_1218_ == 0)
{
lean_dec(v_kind_1212_);
lean_dec_ref(v_env_1210_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Environment_evalConst___redArg(v_env_1210_, v_opts_1211_, v_kind_1212_, v___x_1218_);
lean_dec(v_kind_1212_);
lean_dec_ref(v_env_1210_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_dec_ref_known(v___x_1219_, 1);
return v___x_1213_;
}
else
{
lean_object* v_a_1220_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
if (lean_obj_tag(v_a_1220_) == 4)
{
lean_dec_ref_known(v_a_1220_, 4);
return v___x_1213_;
}
else
{
uint8_t v___x_1221_; 
v___x_1221_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_a_1220_);
lean_dec(v_a_1220_);
return v___x_1221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter___boxed(lean_object* v_env_1222_, lean_object* v_opts_1223_, lean_object* v_kind_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_1222_, v_opts_1223_, v_kind_1224_);
lean_dec_ref(v_opts_1223_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f(lean_object* v_env_1227_, lean_object* v_kind_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1230_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1229_, v_env_1227_, v_kind_1228_);
v___x_1231_ = l_List_head_x3f___redArg(v___x_1230_);
lean_dec(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f___boxed(lean_object* v_env_1232_, lean_object* v_kind_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Fmt_getConditionalFormatter_x3f(v_env_1232_, v_kind_1233_);
lean_dec(v_kind_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f(lean_object* v_env_1235_, lean_object* v_kind_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_1238_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1237_, v_env_1235_, v_kind_1236_);
v___x_1239_ = l_List_head_x3f___redArg(v___x_1238_);
lean_dec(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f___boxed(lean_object* v_env_1240_, lean_object* v_kind_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1240_, v_kind_1241_);
lean_dec(v_kind_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(lean_object* v_msg_1257_){
_start:
{
lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___f_1258_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0));
v___f_1259_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1));
v___f_1260_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2));
v___f_1261_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3));
v___f_1262_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4));
v___f_1263_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5));
v___f_1264_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6));
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___f_1258_);
lean_ctor_set(v___x_1265_, 1, v___f_1259_);
v___x_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___f_1260_);
lean_ctor_set(v___x_1266_, 2, v___f_1261_);
lean_ctor_set(v___x_1266_, 3, v___f_1262_);
lean_ctor_set(v___x_1266_, 4, v___f_1263_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___f_1264_);
v___x_1268_ = ((lean_object*)(l_Lean_Fmt_instInhabitedQuantifierChain_default));
v___x_1269_ = l_instInhabitedOfMonad___redArg(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_panic_fn_borrowed(v___x_1269_, v_msg_1257_);
lean_dec(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(lean_object* v_env_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_snd_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1336_; 
v_snd_1273_ = lean_ctor_get(v_a_1272_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_a_1272_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_a_1272_, 0);
lean_dec(v_unused_1337_);
v___x_1275_ = v_a_1272_;
v_isShared_1276_ = v_isSharedCheck_1336_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_snd_1273_);
lean_dec(v_a_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1336_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_snd_1277_; lean_object* v_fst_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1335_; 
v_snd_1277_ = lean_ctor_get(v_snd_1273_, 1);
v_fst_1278_ = lean_ctor_get(v_snd_1273_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_snd_1273_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1280_ = v_snd_1273_;
v_isShared_1281_ = v_isSharedCheck_1335_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_snd_1277_);
lean_inc(v_fst_1278_);
lean_dec(v_snd_1273_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1335_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
if (lean_obj_tag(v_fst_1278_) == 1)
{
lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1317_; 
v_fst_1282_ = lean_ctor_get(v_snd_1277_, 0);
v_snd_1283_ = lean_ctor_get(v_snd_1277_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_snd_1277_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1285_ = v_snd_1277_;
v_isShared_1286_ = v_isSharedCheck_1317_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_inc(v_fst_1282_);
lean_dec(v_snd_1277_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1317_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_val_1287_; lean_object* v___x_1288_; 
v_val_1287_ = lean_ctor_get(v_fst_1278_, 0);
lean_inc(v_val_1287_);
lean_inc(v_fst_1282_);
v___x_1288_ = lean_apply_1(v_val_1287_, v_fst_1282_);
if (lean_obj_tag(v___x_1288_) == 1)
{
lean_object* v_val_1289_; lean_object* v_toQuantifierHeadComponents_1290_; lean_object* v_body_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_dec_ref_known(v_fst_1278_, 1);
lean_dec(v_fst_1282_);
v_val_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v___x_1288_, 1);
v_toQuantifierHeadComponents_1290_ = lean_ctor_get(v_val_1289_, 0);
lean_inc_ref(v_toQuantifierHeadComponents_1290_);
v_body_1291_ = lean_ctor_get(v_val_1289_, 1);
lean_inc_n(v_body_1291_, 2);
lean_dec(v_val_1289_);
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_array_push(v_snd_1283_, v_toQuantifierHeadComponents_1290_);
v___x_1294_ = l_Lean_Syntax_getKind(v_body_1291_);
lean_inc_ref(v_env_1271_);
v___x_1295_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1271_, v___x_1294_);
lean_dec(v___x_1294_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1293_);
lean_ctor_set(v___x_1285_, 0, v_body_1291_);
v___x_1297_ = v___x_1285_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_body_1291_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1293_);
v___x_1297_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
lean_object* v___x_1299_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1297_);
lean_ctor_set(v___x_1280_, 0, v___x_1295_);
v___x_1299_ = v___x_1280_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1299_);
lean_ctor_set(v___x_1275_, 0, v___x_1292_);
v___x_1301_ = v___x_1275_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
v_a_1272_ = v___x_1301_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
lean_dec(v___x_1288_);
lean_dec_ref(v_env_1271_);
lean_inc(v_fst_1282_);
lean_inc(v_snd_1283_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_snd_1283_);
lean_ctor_set(v___x_1306_, 1, v_fst_1282_);
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
if (v_isShared_1286_ == 0)
{
v___x_1309_ = v___x_1285_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_fst_1282_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_snd_1283_);
v___x_1309_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1309_);
v___x_1311_ = v___x_1280_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_fst_1278_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1313_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1311_);
lean_ctor_set(v___x_1275_, 0, v___x_1307_);
v___x_1313_ = v___x_1275_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1318_; lean_object* v_snd_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_env_1271_);
v_fst_1318_ = lean_ctor_get(v_snd_1277_, 0);
v_snd_1319_ = lean_ctor_get(v_snd_1277_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_snd_1277_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1321_ = v_snd_1277_;
v_isShared_1322_ = v_isSharedCheck_1334_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_snd_1319_);
lean_inc(v_fst_1318_);
lean_dec(v_snd_1277_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1334_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
lean_inc(v_fst_1318_);
lean_inc(v_snd_1319_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_snd_1319_);
lean_ctor_set(v___x_1323_, 1, v_fst_1318_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
if (v_isShared_1322_ == 0)
{
v___x_1326_ = v___x_1321_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_fst_1318_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_snd_1319_);
v___x_1326_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v___x_1326_);
v___x_1328_ = v___x_1280_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_fst_1278_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v___x_1328_);
lean_ctor_set(v___x_1275_, 0, v___x_1324_);
v___x_1330_ = v___x_1275_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1328_);
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
}
}
}
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2));
v___x_1343_ = lean_unsigned_to_nat(2u);
v___x_1344_ = lean_unsigned_to_nat(250u);
v___x_1345_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1));
v___x_1346_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_1347_ = l_mkPanicMessageWithDecl(v___x_1346_, v___x_1345_, v___x_1344_, v___x_1343_, v___x_1342_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(lean_object* v_env_1348_, lean_object* v_deconstructQuantifier_x3f_1349_, lean_object* v_stx_1350_){
_start:
{
lean_object* v_deconstructQuantifier_x3f_1351_; lean_object* v_quantifiers_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_fst_1358_; 
v_deconstructQuantifier_x3f_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_deconstructQuantifier_x3f_1351_, 0, v_deconstructQuantifier_x3f_1349_);
v_quantifiers_1352_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0));
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v_stx_1350_);
lean_ctor_set(v___x_1354_, 1, v_quantifiers_1352_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_deconstructQuantifier_x3f_1351_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1348_, v___x_1356_);
v_fst_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_fst_1358_);
lean_dec_ref(v___x_1357_);
if (lean_obj_tag(v_fst_1358_) == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3);
v___x_1360_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(v___x_1359_);
return v___x_1360_;
}
else
{
lean_object* v_val_1361_; 
v_val_1361_ = lean_ctor_get(v_fst_1358_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v_fst_1358_, 1);
return v_val_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0(lean_object* v_env_1362_, lean_object* v_inst_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1362_, v_a_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(lean_object* v_x_1366_, lean_object* v_x_1367_){
_start:
{
if (lean_obj_tag(v_x_1366_) == 0)
{
if (lean_obj_tag(v_x_1367_) == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = 1;
return v___x_1368_;
}
else
{
uint8_t v___x_1369_; 
v___x_1369_ = 0;
return v___x_1369_;
}
}
else
{
if (lean_obj_tag(v_x_1367_) == 0)
{
uint8_t v___x_1370_; 
v___x_1370_ = 0;
return v___x_1370_;
}
else
{
lean_object* v_val_1371_; lean_object* v_val_1372_; uint8_t v___x_1373_; 
v_val_1371_ = lean_ctor_get(v_x_1366_, 0);
v_val_1372_ = lean_ctor_get(v_x_1367_, 0);
v___x_1373_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_1371_, v_val_1372_);
return v___x_1373_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1___boxed(lean_object* v_x_1374_, lean_object* v_x_1375_){
_start:
{
uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_res_1376_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_x_1374_, v_x_1375_);
lean_dec(v_x_1375_);
lean_dec(v_x_1374_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(lean_object* v_a_1378_, lean_object* v_x_1379_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 0)
{
uint8_t v___x_1380_; 
v___x_1380_ = 0;
return v___x_1380_;
}
else
{
lean_object* v_key_1381_; lean_object* v_tail_1382_; uint8_t v___x_1383_; 
v_key_1381_ = lean_ctor_get(v_x_1379_, 0);
v_tail_1382_ = lean_ctor_get(v_x_1379_, 2);
v___x_1383_ = lean_name_eq(v_key_1381_, v_a_1378_);
if (v___x_1383_ == 0)
{
v_x_1379_ = v_tail_1382_;
goto _start;
}
else
{
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg___boxed(lean_object* v_a_1385_, lean_object* v_x_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1385_, v_x_1386_);
lean_dec(v_x_1386_);
lean_dec(v_a_1385_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(lean_object* v_m_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_buckets_1391_; lean_object* v___x_1392_; uint64_t v___y_1394_; 
v_buckets_1391_ = lean_ctor_get(v_m_1389_, 1);
v___x_1392_ = lean_array_get_size(v_buckets_1391_);
if (lean_obj_tag(v_a_1390_) == 0)
{
uint64_t v___x_1408_; 
v___x_1408_ = 1723ULL;
v___y_1394_ = v___x_1408_;
goto v___jp_1393_;
}
else
{
uint64_t v_hash_1409_; 
v_hash_1409_ = lean_ctor_get_uint64(v_a_1390_, sizeof(void*)*2);
v___y_1394_ = v_hash_1409_;
goto v___jp_1393_;
}
v___jp_1393_:
{
uint64_t v___x_1395_; uint64_t v___x_1396_; uint64_t v_fold_1397_; uint64_t v___x_1398_; uint64_t v___x_1399_; uint64_t v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1395_ = 32ULL;
v___x_1396_ = lean_uint64_shift_right(v___y_1394_, v___x_1395_);
v_fold_1397_ = lean_uint64_xor(v___y_1394_, v___x_1396_);
v___x_1398_ = 16ULL;
v___x_1399_ = lean_uint64_shift_right(v_fold_1397_, v___x_1398_);
v___x_1400_ = lean_uint64_xor(v_fold_1397_, v___x_1399_);
v___x_1401_ = lean_uint64_to_usize(v___x_1400_);
v___x_1402_ = lean_usize_of_nat(v___x_1392_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_sub(v___x_1402_, v___x_1403_);
v___x_1405_ = lean_usize_land(v___x_1401_, v___x_1404_);
v___x_1406_ = lean_array_uget_borrowed(v_buckets_1391_, v___x_1405_);
v___x_1407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1390_, v___x_1406_);
return v___x_1407_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg___boxed(lean_object* v_m_1410_, lean_object* v_a_1411_){
_start:
{
uint8_t v_res_1412_; lean_object* v_r_1413_; 
v_res_1412_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_m_1410_);
v_r_1413_ = lean_box(v_res_1412_);
return v_r_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(lean_object* v_env_1414_, lean_object* v_opts_1415_, lean_object* v_op_1416_, lean_object* v_stx_1417_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = l_Lean_Syntax_getNumArgs(v_stx_1417_);
v___x_1435_ = lean_unsigned_to_nat(3u);
v___x_1436_ = lean_nat_dec_eq(v___x_1434_, v___x_1435_);
lean_dec(v___x_1434_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_env_1414_);
v___x_1437_ = lean_unsigned_to_nat(1u);
v___x_1438_ = lean_mk_empty_array_with_capacity(v___x_1437_);
v___x_1439_ = lean_array_push(v___x_1438_, v_stx_1417_);
return v___x_1439_;
}
else
{
lean_object* v_precs_x3f_1440_; lean_object* v_extendedChainKinds_1441_; lean_object* v___x_1442_; 
v_precs_x3f_1440_ = lean_ctor_get(v_op_1416_, 0);
v_extendedChainKinds_1441_ = lean_ctor_get(v_op_1416_, 1);
lean_inc(v_stx_1417_);
v___x_1442_ = l_Lean_Syntax_getKind(v_stx_1417_);
if (lean_obj_tag(v_precs_x3f_1440_) == 0)
{
goto v___jp_1443_;
}
else
{
lean_object* v_op_x27_x3f_1448_; 
lean_inc(v___x_1442_);
lean_inc_ref(v_env_1414_);
v_op_x27_x3f_1448_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_1414_, v_opts_1415_, v___x_1442_);
if (lean_obj_tag(v_op_x27_x3f_1448_) == 0)
{
goto v___jp_1443_;
}
else
{
lean_object* v_val_1449_; lean_object* v_precs_x3f_1450_; uint8_t v___x_1451_; 
v_val_1449_ = lean_ctor_get(v_op_x27_x3f_1448_, 0);
lean_inc(v_val_1449_);
lean_dec_ref_known(v_op_x27_x3f_1448_, 1);
v_precs_x3f_1450_ = lean_ctor_get(v_val_1449_, 0);
lean_inc(v_precs_x3f_1450_);
lean_dec(v_val_1449_);
v___x_1451_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_precs_x3f_1450_, v_precs_x3f_1440_);
lean_dec(v_precs_x3f_1450_);
if (v___x_1451_ == 0)
{
goto v___jp_1443_;
}
else
{
lean_dec(v___x_1442_);
goto v___jp_1418_;
}
}
}
v___jp_1443_:
{
uint8_t v___x_1444_; 
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_extendedChainKinds_1441_, v___x_1442_);
lean_dec(v___x_1442_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_dec_ref(v_env_1414_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_mk_empty_array_with_capacity(v___x_1445_);
v___x_1447_ = lean_array_push(v___x_1446_, v_stx_1417_);
return v___x_1447_;
}
else
{
goto v___jp_1418_;
}
}
}
v___jp_1418_:
{
lean_object* v___x_1419_; lean_object* v_op_1420_; uint8_t v___x_1421_; 
v___x_1419_ = lean_unsigned_to_nat(1u);
v_op_1420_ = l_Lean_Syntax_getArg(v_stx_1417_, v___x_1419_);
v___x_1421_ = l_Lean_Syntax_isAtom(v_op_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec(v_op_1420_);
lean_dec_ref(v_env_1414_);
v___x_1422_ = lean_mk_empty_array_with_capacity(v___x_1419_);
v___x_1423_ = lean_array_push(v___x_1422_, v_stx_1417_);
return v___x_1423_;
}
else
{
lean_object* v___x_1424_; lean_object* v_left_1425_; lean_object* v___x_1426_; lean_object* v_right_1427_; lean_object* v_leftChain_1428_; lean_object* v_rightChain_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1424_ = lean_unsigned_to_nat(0u);
v_left_1425_ = l_Lean_Syntax_getArg(v_stx_1417_, v___x_1424_);
v___x_1426_ = lean_unsigned_to_nat(2u);
v_right_1427_ = l_Lean_Syntax_getArg(v_stx_1417_, v___x_1426_);
lean_dec(v_stx_1417_);
lean_inc_ref(v_env_1414_);
v_leftChain_1428_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1414_, v_opts_1415_, v_op_1416_, v_left_1425_);
v_rightChain_1429_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1414_, v_opts_1415_, v_op_1416_, v_right_1427_);
v___x_1430_ = lean_mk_empty_array_with_capacity(v___x_1419_);
v___x_1431_ = lean_array_push(v___x_1430_, v_op_1420_);
v___x_1432_ = l_Array_append___redArg(v_leftChain_1428_, v___x_1431_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = l_Array_append___redArg(v___x_1432_, v_rightChain_1429_);
lean_dec_ref(v_rightChain_1429_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain___boxed(lean_object* v_env_1452_, lean_object* v_opts_1453_, lean_object* v_op_1454_, lean_object* v_stx_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1452_, v_opts_1453_, v_op_1454_, v_stx_1455_);
lean_dec_ref(v_op_1454_);
lean_dec_ref(v_opts_1453_);
return v_res_1456_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(lean_object* v_00_u03b2_1457_, lean_object* v_m_1458_, lean_object* v_a_1459_){
_start:
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1458_, v_a_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___boxed(lean_object* v_00_u03b2_1461_, lean_object* v_m_1462_, lean_object* v_a_1463_){
_start:
{
uint8_t v_res_1464_; lean_object* v_r_1465_; 
v_res_1464_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(v_00_u03b2_1461_, v_m_1462_, v_a_1463_);
lean_dec(v_a_1463_);
lean_dec_ref(v_m_1462_);
v_r_1465_ = lean_box(v_res_1464_);
return v_r_1465_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(lean_object* v_00_u03b2_1466_, lean_object* v_a_1467_, lean_object* v_x_1468_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1467_, v_x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1470_, lean_object* v_a_1471_, lean_object* v_x_1472_){
_start:
{
uint8_t v_res_1473_; lean_object* v_r_1474_; 
v_res_1473_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(v_00_u03b2_1470_, v_a_1471_, v_x_1472_);
lean_dec(v_x_1472_);
lean_dec(v_a_1471_);
v_r_1474_ = lean_box(v_res_1473_);
return v_r_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v_a_1478_, lean_object* v_b_1479_){
_start:
{
lean_object* v_it_1481_; lean_object* v_startInclusive_1482_; lean_object* v_endExclusive_1483_; 
if (lean_obj_tag(v_a_1478_) == 0)
{
lean_object* v_currPos_1489_; lean_object* v_searcher_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1596_; 
v_currPos_1489_ = lean_ctor_get(v_a_1478_, 0);
v_searcher_1490_ = lean_ctor_get(v_a_1478_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1478_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1492_ = v_a_1478_;
v_isShared_1493_ = v_isSharedCheck_1596_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_searcher_1490_);
lean_inc(v_currPos_1489_);
lean_dec(v_a_1478_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1596_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_it_1495_; lean_object* v_it_1501_; lean_object* v_startPos_1502_; lean_object* v_endPos_1503_; 
switch(lean_obj_tag(v_searcher_1490_))
{
case 0:
{
lean_object* v_pos_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1528_; 
lean_del_object(v___x_1492_);
v_pos_1516_ = lean_ctor_get(v_searcher_1490_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_searcher_1490_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1518_ = v_searcher_1490_;
v_isShared_1519_ = v_isSharedCheck_1528_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_pos_1516_);
lean_dec(v_searcher_1490_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1528_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_startInclusive_1520_; lean_object* v_endExclusive_1521_; lean_object* v___x_1522_; uint8_t v_decide_1523_; 
v_startInclusive_1520_ = lean_ctor_get(v___x_1476_, 1);
v_endExclusive_1521_ = lean_ctor_get(v___x_1476_, 2);
v___x_1522_ = lean_nat_sub(v_endExclusive_1521_, v_startInclusive_1520_);
v_decide_1523_ = lean_nat_dec_eq(v_pos_1516_, v___x_1522_);
lean_dec(v___x_1522_);
if (v_decide_1523_ == 0)
{
lean_object* v___x_1525_; 
lean_inc(v_pos_1516_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
v___x_1525_ = v___x_1518_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_pos_1516_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_inc(v_pos_1516_);
v_it_1501_ = v___x_1525_;
v_startPos_1502_ = v_pos_1516_;
v_endPos_1503_ = v_pos_1516_;
goto v___jp_1500_;
}
}
else
{
lean_object* v___x_1527_; 
lean_del_object(v___x_1518_);
v___x_1527_ = lean_box(3);
lean_inc(v_pos_1516_);
v_it_1501_ = v___x_1527_;
v_startPos_1502_ = v_pos_1516_;
v_endPos_1503_ = v_pos_1516_;
goto v___jp_1500_;
}
}
}
case 1:
{
lean_object* v_pos_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
v_pos_1529_ = lean_ctor_get(v_searcher_1490_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_searcher_1490_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1531_ = v_searcher_1490_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_pos_1529_);
lean_dec(v_searcher_1490_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_string_utf8_next_fast(v___x_1475_, v_pos_1529_);
lean_dec(v_pos_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
v_it_1495_ = v___x_1535_;
goto v___jp_1494_;
}
}
}
case 2:
{
lean_object* v_needle_1538_; lean_object* v_table_1539_; lean_object* v_stackPos_1540_; lean_object* v_needlePos_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1595_; 
v_needle_1538_ = lean_ctor_get(v_searcher_1490_, 0);
v_table_1539_ = lean_ctor_get(v_searcher_1490_, 1);
v_stackPos_1540_ = lean_ctor_get(v_searcher_1490_, 2);
v_needlePos_1541_ = lean_ctor_get(v_searcher_1490_, 3);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_searcher_1490_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1543_ = v_searcher_1490_;
v_isShared_1544_ = v_isSharedCheck_1595_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_needlePos_1541_);
lean_inc(v_stackPos_1540_);
lean_inc(v_table_1539_);
lean_inc(v_needle_1538_);
lean_dec(v_searcher_1490_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1595_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_str_1545_; lean_object* v_startInclusive_1546_; lean_object* v_endExclusive_1547_; lean_object* v_basePos_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_str_1545_ = lean_ctor_get(v_needle_1538_, 0);
v_startInclusive_1546_ = lean_ctor_get(v_needle_1538_, 1);
v_endExclusive_1547_ = lean_ctor_get(v_needle_1538_, 2);
v_basePos_1548_ = lean_nat_sub(v_stackPos_1540_, v_needlePos_1541_);
v___x_1549_ = lean_nat_sub(v_endExclusive_1547_, v_startInclusive_1546_);
v___x_1550_ = lean_nat_add(v_basePos_1548_, v___x_1549_);
v___x_1551_ = lean_nat_dec_le(v___x_1550_, v___x_1477_);
lean_dec(v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
lean_dec(v___x_1549_);
lean_del_object(v___x_1543_);
lean_dec(v_needlePos_1541_);
lean_dec(v_stackPos_1540_);
lean_dec_ref(v_table_1539_);
lean_dec_ref(v_needle_1538_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_add(v_basePos_1548_, v___x_1552_);
lean_dec(v_basePos_1548_);
v___x_1554_ = lean_nat_dec_le(v___x_1553_, v___x_1477_);
lean_dec(v___x_1553_);
if (v___x_1554_ == 0)
{
lean_del_object(v___x_1492_);
goto v___jp_1514_;
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_box(3);
v_it_1495_ = v___x_1555_;
goto v___jp_1494_;
}
}
else
{
uint8_t v_stackByte_1556_; lean_object* v___x_1557_; uint8_t v_patByte_1558_; uint8_t v___x_1559_; 
lean_dec(v_basePos_1548_);
lean_inc(v_stackPos_1540_);
v_stackByte_1556_ = lean_string_get_byte_fast(v___x_1475_, v_stackPos_1540_);
v___x_1557_ = lean_nat_add(v_startInclusive_1546_, v_needlePos_1541_);
v_patByte_1558_ = lean_string_get_byte_fast(v_str_1545_, v___x_1557_);
v___x_1559_ = lean_uint8_dec_eq(v_stackByte_1556_, v_patByte_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; uint8_t v_decide_1561_; 
lean_dec(v___x_1549_);
v___x_1560_ = lean_unsigned_to_nat(0u);
v_decide_1561_ = lean_nat_dec_eq(v_needlePos_1541_, v___x_1560_);
if (v_decide_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_newNeedlePos_1564_; uint8_t v___x_1565_; 
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_sub(v_needlePos_1541_, v___x_1562_);
lean_dec(v_needlePos_1541_);
v_newNeedlePos_1564_ = lean_array_fget_borrowed(v_table_1539_, v___x_1563_);
lean_dec(v___x_1563_);
v___x_1565_ = lean_nat_dec_eq(v_newNeedlePos_1564_, v___x_1560_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1567_; 
lean_inc(v_newNeedlePos_1564_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 3, v_newNeedlePos_1564_);
v___x_1567_ = v___x_1543_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_needle_1538_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_table_1539_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_stackPos_1540_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v_newNeedlePos_1564_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
v_it_1495_ = v___x_1567_;
goto v___jp_1494_;
}
}
else
{
lean_object* v_nextStackPos_1569_; lean_object* v___x_1571_; 
v_nextStackPos_1569_ = l_String_Slice_posGE___redArg(v___x_1476_, v_stackPos_1540_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 3, v___x_1560_);
lean_ctor_set(v___x_1543_, 2, v_nextStackPos_1569_);
v___x_1571_ = v___x_1543_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_needle_1538_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_table_1539_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_nextStackPos_1569_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v___x_1560_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
v_it_1495_ = v___x_1571_;
goto v___jp_1494_;
}
}
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v_nextStackPos_1575_; lean_object* v___x_1577_; 
lean_dec(v_needlePos_1541_);
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = lean_nat_add(v_stackPos_1540_, v___x_1573_);
lean_dec(v_stackPos_1540_);
v_nextStackPos_1575_ = l_String_Slice_posGE___redArg(v___x_1476_, v___x_1574_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 3, v___x_1560_);
lean_ctor_set(v___x_1543_, 2, v_nextStackPos_1575_);
v___x_1577_ = v___x_1543_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_needle_1538_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_table_1539_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_nextStackPos_1575_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v___x_1560_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
v_it_1495_ = v___x_1577_;
goto v___jp_1494_;
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v_nextStackPos_1580_; lean_object* v_nextNeedlePos_1581_; uint8_t v_decide_1582_; 
lean_del_object(v___x_1492_);
v___x_1579_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1580_ = lean_nat_add(v_stackPos_1540_, v___x_1579_);
lean_dec(v_stackPos_1540_);
v_nextNeedlePos_1581_ = lean_nat_add(v_needlePos_1541_, v___x_1579_);
lean_dec(v_needlePos_1541_);
v_decide_1582_ = lean_nat_dec_eq(v_nextNeedlePos_1581_, v___x_1549_);
lean_dec(v___x_1549_);
if (v_decide_1582_ == 0)
{
lean_object* v___x_1584_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 3, v_nextNeedlePos_1581_);
lean_ctor_set(v___x_1543_, 2, v_nextStackPos_1580_);
v___x_1584_ = v___x_1543_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_needle_1538_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_table_1539_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_nextStackPos_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 3, v_nextNeedlePos_1581_);
v___x_1584_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v_currPos_1489_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v_a_1478_ = v___x_1585_;
goto _start;
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1588_ = lean_nat_sub(v_nextStackPos_1580_, v_nextNeedlePos_1581_);
lean_dec(v_nextNeedlePos_1581_);
v___x_1589_ = l_String_Slice_pos_x21(v___x_1476_, v___x_1588_);
lean_dec(v___x_1588_);
v___x_1590_ = l_String_Slice_pos_x21(v___x_1476_, v_nextStackPos_1580_);
v___x_1591_ = lean_unsigned_to_nat(0u);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 3, v___x_1591_);
lean_ctor_set(v___x_1543_, 2, v_nextStackPos_1580_);
v___x_1593_ = v___x_1543_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_needle_1538_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_table_1539_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_nextStackPos_1580_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
v_it_1501_ = v___x_1593_;
v_startPos_1502_ = v___x_1589_;
v_endPos_1503_ = v___x_1590_;
goto v___jp_1500_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_1492_);
goto v___jp_1514_;
}
}
v___jp_1494_:
{
lean_object* v___x_1497_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 1, v_it_1495_);
v___x_1497_ = v___x_1492_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_currPos_1489_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_it_1495_);
v___x_1497_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v_a_1478_ = v___x_1497_;
goto _start;
}
}
v___jp_1500_:
{
lean_object* v_slice_1504_; lean_object* v_startInclusive_1505_; lean_object* v_endExclusive_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_slice_1504_ = l_String_Slice_subslice_x21(v___x_1476_, v_currPos_1489_, v_startPos_1502_);
v_startInclusive_1505_ = lean_ctor_get(v_slice_1504_, 0);
v_endExclusive_1506_ = lean_ctor_get(v_slice_1504_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_slice_1504_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v_slice_1504_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_endExclusive_1506_);
lean_inc(v_startInclusive_1505_);
lean_dec(v_slice_1504_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v_nextIt_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 1, v_it_1501_);
lean_ctor_set(v___x_1508_, 0, v_endPos_1503_);
v_nextIt_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_endPos_1503_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_it_1501_);
v_nextIt_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
v_it_1481_ = v_nextIt_1511_;
v_startInclusive_1482_ = v_startInclusive_1505_;
v_endExclusive_1483_ = v_endExclusive_1506_;
goto v___jp_1480_;
}
}
}
v___jp_1514_:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_box(1);
lean_inc(v___x_1477_);
v_it_1481_ = v___x_1515_;
v_startInclusive_1482_ = v_currPos_1489_;
v_endExclusive_1483_ = v___x_1477_;
goto v___jp_1480_;
}
}
}
else
{
lean_dec(v___x_1477_);
lean_dec_ref(v___x_1475_);
return v_b_1479_;
}
v___jp_1480_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_inc_ref(v___x_1475_);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1475_);
lean_ctor_set(v___x_1484_, 1, v_startInclusive_1482_);
lean_ctor_set(v___x_1484_, 2, v_endExclusive_1483_);
v___x_1485_ = l_String_Slice_toString(v___x_1484_);
lean_dec_ref_known(v___x_1484_, 3);
v___x_1486_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_1485_);
v___x_1487_ = lean_array_push(v_b_1479_, v___x_1486_);
v_a_1478_ = v_it_1481_;
v_b_1479_ = v___x_1487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg___boxed(lean_object* v___x_1597_, lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v_a_1600_, lean_object* v_b_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1597_, v___x_1598_, v___x_1599_, v_a_1600_, v_b_1601_);
lean_dec_ref(v___x_1598_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtRawAsInSource___closed__3(void){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource(uint8_t v_isFallback_1609_, lean_object* v_stx_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = 0;
v___x_1614_ = l_Lean_Syntax_getPos_x3f(v_stx_1610_, v___x_1613_);
if (lean_obj_tag(v___x_1614_) == 1)
{
lean_object* v_val_1615_; lean_object* v___x_1616_; 
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1610_, v___x_1613_);
if (lean_obj_tag(v___x_1616_) == 1)
{
lean_object* v_text_1617_; lean_object* v_val_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1668_; 
v_text_1617_ = lean_ctor_get(v_a_1611_, 1);
v_val_1618_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1620_ = v___x_1616_;
v_isShared_1621_ = v_isSharedCheck_1668_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_val_1618_);
lean_dec(v___x_1616_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1668_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v_source_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_source_1622_ = lean_ctor_get(v_text_1617_, 0);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_string_utf8_byte_size(v_source_1622_);
lean_inc_ref(v_source_1622_);
v___x_1625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1625_, 0, v_source_1622_);
lean_ctor_set(v___x_1625_, 1, v___x_1623_);
lean_ctor_set(v___x_1625_, 2, v___x_1624_);
v___x_1626_ = l_String_Slice_pos_x3f(v___x_1625_, v_val_1615_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec_ref_known(v___x_1625_, 3);
lean_dec(v_val_1618_);
v___x_1627_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1628_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1629_, 0, v_stx_1610_);
lean_ctor_set(v___x_1629_, 1, v___x_1627_);
lean_ctor_set(v___x_1629_, 2, v___x_1628_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set_tag(v___x_1620_, 2);
lean_ctor_set(v___x_1620_, 0, v___x_1629_);
v___x_1631_ = v___x_1620_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v_a_1612_);
return v___x_1632_;
}
}
else
{
lean_object* v_val_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1667_; 
lean_del_object(v___x_1620_);
v_val_1634_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1636_ = v___x_1626_;
v_isShared_1637_ = v_isSharedCheck_1667_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_val_1634_);
lean_dec(v___x_1626_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1667_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_String_Slice_pos_x3f(v___x_1625_, v_val_1618_);
lean_dec_ref_known(v___x_1625_, 3);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
lean_dec(v_val_1634_);
v___x_1639_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1640_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1641_, 0, v_stx_1610_);
lean_ctor_set(v___x_1641_, 1, v___x_1639_);
lean_ctor_set(v___x_1641_, 2, v___x_1640_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 2);
lean_ctor_set(v___x_1636_, 0, v___x_1641_);
v___x_1643_ = v___x_1636_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_a_1612_);
return v___x_1644_;
}
}
else
{
lean_object* v_val_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_del_object(v___x_1636_);
v_val_1646_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_val_1646_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1647_ = lean_string_utf8_extract_fast(v_source_1622_, v_val_1634_, v_val_1646_);
lean_dec(v_val_1646_);
lean_dec(v_val_1634_);
v___x_1648_ = lean_string_utf8_byte_size(v___x_1647_);
lean_inc_ref(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1623_);
lean_ctor_set(v___x_1649_, 2, v___x_1648_);
v___x_1650_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1651_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1652_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1647_, v___x_1649_, v___x_1648_, v___x_1650_, v___x_1651_);
lean_dec_ref_known(v___x_1649_, 3);
v___x_1653_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1654_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1653_, v___x_1652_);
v___x_1655_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1613_, v___x_1654_);
v___x_1656_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___x_1655_, v_stx_1610_, v_a_1612_);
lean_dec(v_stx_1610_);
if (lean_obj_tag(v___x_1656_) == 0)
{
if (v_isFallback_1609_ == 0)
{
return v___x_1656_;
}
else
{
lean_object* v_a_1657_; lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_a_1658_ = lean_ctor_get(v___x_1656_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1660_ = v___x_1656_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_1657_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1658_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
return v___x_1656_;
}
}
}
}
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec(v___x_1616_);
lean_dec(v_val_1615_);
v___x_1669_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1670_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1669_, v_stx_1610_, v_a_1612_);
lean_dec(v_stx_1610_);
return v___x_1670_;
}
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec(v___x_1614_);
v___x_1671_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1672_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1671_, v_stx_1610_, v_a_1612_);
lean_dec(v_stx_1610_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource___boxed(lean_object* v_isFallback_1673_, lean_object* v_stx_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
uint8_t v_isFallback_boxed_1677_; lean_object* v_res_1678_; 
v_isFallback_boxed_1677_ = lean_unbox(v_isFallback_1673_);
v_res_1678_ = l_Lean_Fmt_fmtRawAsInSource(v_isFallback_boxed_1677_, v_stx_1674_, v_a_1675_, v_a_1676_);
lean_dec_ref(v_a_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(lean_object* v___x_1679_, lean_object* v___x_1680_, lean_object* v___x_1681_, lean_object* v_inst_1682_, lean_object* v_R_1683_, lean_object* v_a_1684_, lean_object* v_b_1685_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1679_, v___x_1680_, v___x_1681_, v_a_1684_, v_b_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___boxed(lean_object* v___x_1687_, lean_object* v___x_1688_, lean_object* v___x_1689_, lean_object* v_inst_1690_, lean_object* v_R_1691_, lean_object* v_a_1692_, lean_object* v_b_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(v___x_1687_, v___x_1688_, v___x_1689_, v_inst_1690_, v_R_1691_, v_a_1692_, v_b_1693_);
lean_dec_ref(v___x_1688_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(size_t v_sz_1695_, size_t v_i_1696_, lean_object* v_bs_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_lt(v_i_1696_, v_sz_1695_);
if (v___x_1698_ == 0)
{
return v_bs_1697_;
}
else
{
lean_object* v_v_1699_; lean_object* v___x_1700_; lean_object* v_bs_x27_1701_; lean_object* v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; lean_object* v___x_1705_; 
v_v_1699_ = lean_array_uget(v_bs_1697_, v_i_1696_);
v___x_1700_ = lean_unsigned_to_nat(0u);
v_bs_x27_1701_ = lean_array_uset(v_bs_1697_, v_i_1696_, v___x_1700_);
v___x_1702_ = l_Lean_Fmt_Doc_text___override___redArg(v_v_1699_);
v___x_1703_ = ((size_t)1ULL);
v___x_1704_ = lean_usize_add(v_i_1696_, v___x_1703_);
v___x_1705_ = lean_array_uset(v_bs_x27_1701_, v_i_1696_, v___x_1702_);
v_i_1696_ = v___x_1704_;
v_bs_1697_ = v___x_1705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2___boxed(lean_object* v_sz_1707_, lean_object* v_i_1708_, lean_object* v_bs_1709_){
_start:
{
size_t v_sz_boxed_1710_; size_t v_i_boxed_1711_; lean_object* v_res_1712_; 
v_sz_boxed_1710_ = lean_unbox_usize(v_sz_1707_);
lean_dec(v_sz_1707_);
v_i_boxed_1711_ = lean_unbox_usize(v_i_1708_);
lean_dec(v_i_1708_);
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_boxed_1710_, v_i_boxed_1711_, v_bs_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(lean_object* v_ctx_1713_, size_t v_sz_1714_, size_t v_i_1715_, lean_object* v_bs_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_usize_dec_lt(v_i_1715_, v_sz_1714_);
if (v___x_1717_ == 0)
{
lean_dec_ref(v_ctx_1713_);
return v_bs_1716_;
}
else
{
lean_object* v_v_1718_; lean_object* v_str_1719_; lean_object* v_startPos_1720_; lean_object* v_stopPos_1721_; lean_object* v_anchorColumnPos_1722_; lean_object* v___x_1723_; lean_object* v_bs_x27_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; lean_object* v___x_1729_; 
v_v_1718_ = lean_array_uget_borrowed(v_bs_1716_, v_i_1715_);
v_str_1719_ = lean_ctor_get(v_v_1718_, 0);
lean_inc_ref(v_str_1719_);
v_startPos_1720_ = lean_ctor_get(v_v_1718_, 1);
lean_inc(v_startPos_1720_);
v_stopPos_1721_ = lean_ctor_get(v_v_1718_, 2);
lean_inc(v_stopPos_1721_);
v_anchorColumnPos_1722_ = lean_ctor_get(v_ctx_1713_, 0);
v___x_1723_ = lean_unsigned_to_nat(0u);
v_bs_x27_1724_ = lean_array_uset(v_bs_1716_, v_i_1715_, v___x_1723_);
v___x_1725_ = lean_string_utf8_extract(v_str_1719_, v_startPos_1720_, v_stopPos_1721_);
lean_dec(v_stopPos_1721_);
lean_dec(v_startPos_1720_);
lean_dec_ref(v_str_1719_);
lean_inc(v_anchorColumnPos_1722_);
v___x_1726_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(v___x_1725_, v_anchorColumnPos_1722_);
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_add(v_i_1715_, v___x_1727_);
v___x_1729_ = lean_array_uset(v_bs_x27_1724_, v_i_1715_, v___x_1726_);
v_i_1715_ = v___x_1728_;
v_bs_1716_ = v___x_1729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1___boxed(lean_object* v_ctx_1731_, lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_bs_1734_){
_start:
{
size_t v_sz_boxed_1735_; size_t v_i_boxed_1736_; lean_object* v_res_1737_; 
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1736_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1731_, v_sz_boxed_1735_, v_i_boxed_1736_, v_bs_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(lean_object* v_a_1738_, lean_object* v_b_1739_){
_start:
{
lean_object* v_array_1740_; lean_object* v_start_1741_; lean_object* v_stop_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1755_; 
v_array_1740_ = lean_ctor_get(v_a_1738_, 0);
v_start_1741_ = lean_ctor_get(v_a_1738_, 1);
v_stop_1742_ = lean_ctor_get(v_a_1738_, 2);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1744_ = v_a_1738_;
v_isShared_1745_ = v_isSharedCheck_1755_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_stop_1742_);
lean_inc(v_start_1741_);
lean_inc(v_array_1740_);
lean_dec(v_a_1738_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1755_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_nat_dec_lt(v_start_1741_, v_stop_1742_);
if (v___x_1746_ == 0)
{
lean_del_object(v___x_1744_);
lean_dec(v_stop_1742_);
lean_dec(v_start_1741_);
lean_dec_ref(v_array_1740_);
return v_b_1739_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_add(v_start_1741_, v___x_1747_);
lean_inc_ref(v_array_1740_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v___x_1748_);
v___x_1750_ = v___x_1744_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_array_1740_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_stop_1742_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_array_fget(v_array_1740_, v_start_1741_);
lean_dec(v_start_1741_);
lean_dec_ref(v_array_1740_);
v___x_1752_ = lean_array_push(v_b_1739_, v___x_1751_);
v_a_1738_ = v___x_1750_;
v_b_1739_ = v___x_1752_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(lean_object* v_ctx_1760_, lean_object* v_trailing_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_lastTokenTailPos_1763_; lean_object* v_startPos_1764_; uint8_t v___x_1765_; 
v_lastTokenTailPos_1763_ = lean_ctor_get(v_ctx_1760_, 2);
v_startPos_1764_ = lean_ctor_get(v_trailing_1761_, 1);
v___x_1765_ = lean_nat_dec_le(v_lastTokenTailPos_1763_, v_startPos_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v_lines_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v_str_1772_; lean_object* v_startPos_1773_; lean_object* v_stopPos_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_1785_; lean_object* v_newLines_1786_; size_t v_sz_1787_; lean_object* v_formatted_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1766_ = l_instInhabitedRaw__1;
v___x_1767_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_trailing_1761_);
v___x_1768_ = l_Substring_Raw_splitOn(v_trailing_1761_, v___x_1767_);
v_lines_1769_ = lean_array_mk(v___x_1768_);
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_array_get_borrowed(v___x_1766_, v_lines_1769_, v___x_1770_);
v_str_1772_ = lean_ctor_get(v___x_1771_, 0);
v_startPos_1773_ = lean_ctor_get(v___x_1771_, 1);
v_stopPos_1774_ = lean_ctor_get(v___x_1771_, 2);
v___x_1775_ = lean_string_utf8_extract(v_str_1772_, v_startPos_1773_, v_stopPos_1774_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_mk_empty_array_with_capacity(v___x_1776_);
lean_inc_ref(v___x_1777_);
v___x_1778_ = lean_array_push(v___x_1777_, v___x_1775_);
v___x_1779_ = lean_array_get_size(v_lines_1769_);
v___x_1780_ = l_Array_toSubarray___redArg(v_lines_1769_, v___x_1776_, v___x_1779_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0));
v___x_1782_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v___x_1780_, v___x_1781_);
v_sz_1783_ = lean_array_size(v___x_1782_);
v___x_1784_ = ((size_t)0ULL);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1760_, v_sz_1783_, v___x_1784_, v___x_1782_);
v_newLines_1786_ = l_Array_append___redArg(v___x_1778_, v___x_1785_);
lean_dec_ref(v___x_1785_);
v_sz_1787_ = lean_array_size(v_newLines_1786_);
v_formatted_1788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1787_, v___x_1784_, v_newLines_1786_);
v___x_1789_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1790_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1789_, v_formatted_1788_);
v___x_1791_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1790_);
v___x_1792_ = l_Lean_Syntax_Range_ofSubstring(v_trailing_1761_);
lean_dec_ref(v_trailing_1761_);
v___x_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1791_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_array_push(v___x_1777_, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v_a_1762_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
lean_dec_ref(v_trailing_1761_);
lean_dec_ref(v_ctx_1760_);
v___x_1797_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v_a_1762_);
return v___x_1798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(lean_object* v_ctx_1799_, lean_object* v___trailingTk_1800_, lean_object* v_trailing_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(v_ctx_1799_, v_trailing_1801_, v_a_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed(lean_object* v_ctx_1805_, lean_object* v___trailingTk_1806_, lean_object* v_trailing_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(v_ctx_1805_, v___trailingTk_1806_, v_trailing_1807_, v_a_1808_, v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v___trailingTk_1806_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0(lean_object* v_inst_1811_, lean_object* v_R_1812_, lean_object* v_a_1813_, lean_object* v_b_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v_a_1813_, v_b_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(lean_object* v_ctx_1816_, lean_object* v_leading_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_stopPos_1819_; lean_object* v_firstTokenPos_1820_; uint8_t v___x_1821_; 
v_stopPos_1819_ = lean_ctor_get(v_leading_1817_, 2);
v_firstTokenPos_1820_ = lean_ctor_get(v_ctx_1816_, 1);
v___x_1821_ = lean_nat_dec_le(v_stopPos_1819_, v_firstTokenPos_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_lines_1824_; size_t v_sz_1825_; size_t v___x_1826_; lean_object* v_newLines_1827_; size_t v_sz_1828_; lean_object* v_formatted_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1822_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_leading_1817_);
v___x_1823_ = l_Substring_Raw_splitOn(v_leading_1817_, v___x_1822_);
v_lines_1824_ = lean_array_mk(v___x_1823_);
v_sz_1825_ = lean_array_size(v_lines_1824_);
v___x_1826_ = ((size_t)0ULL);
v_newLines_1827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1816_, v_sz_1825_, v___x_1826_, v_lines_1824_);
v_sz_1828_ = lean_array_size(v_newLines_1827_);
v_formatted_1829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1828_, v___x_1826_, v_newLines_1827_);
v___x_1830_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1831_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1830_, v_formatted_1829_);
v___x_1832_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1831_);
v___x_1833_ = l_Lean_Syntax_Range_ofSubstring(v_leading_1817_);
lean_dec_ref(v_leading_1817_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1832_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = lean_mk_empty_array_with_capacity(v___x_1836_);
v___x_1838_ = lean_array_push(v___x_1837_, v___x_1835_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v_a_1818_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec_ref(v_leading_1817_);
lean_dec_ref(v_ctx_1816_);
v___x_1840_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v_a_1818_);
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(lean_object* v_ctx_1842_, lean_object* v___leadingTk_1843_, lean_object* v_leading_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(v_ctx_1842_, v_leading_1844_, v_a_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed(lean_object* v_ctx_1848_, lean_object* v___leadingTk_1849_, lean_object* v_leading_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(v_ctx_1848_, v___leadingTk_1849_, v_leading_1850_, v_a_1851_, v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v___leadingTk_1849_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(lean_object* v_stx_1854_, lean_object* v_token_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_inc_ref(v_a_1856_);
v___x_1859_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed), 5, 1);
lean_closure_set(v___x_1859_, 0, v_a_1856_);
lean_inc(v_stx_1854_);
v___x_1860_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_1854_, v___x_1859_, v_a_1857_, v_a_1858_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v_a_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
v_a_1862_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1860_, 2);
lean_inc_ref(v_a_1856_);
v___x_1863_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed), 5, 1);
lean_closure_set(v___x_1863_, 0, v_a_1856_);
lean_inc(v_stx_1854_);
v___x_1864_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_1854_, v___x_1863_, v_a_1857_, v_a_1862_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1927_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_a_1866_ = lean_ctor_get(v___x_1864_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1868_ = v___x_1864_;
v_isShared_1869_ = v_isSharedCheck_1927_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1927_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1899_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = lean_string_utf8_byte_size(v_token_1855_);
lean_inc_ref(v_token_1855_);
v___x_1915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1915_, 0, v_token_1855_);
lean_ctor_set(v___x_1915_, 1, v___x_1913_);
lean_ctor_set(v___x_1915_, 2, v___x_1914_);
v___x_1916_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1917_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1918_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_token_1855_, v___x_1915_, v___x_1914_, v___x_1916_, v___x_1917_);
lean_dec_ref_known(v___x_1915_, 3);
v___x_1919_ = lean_array_get_size(v___x_1918_);
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = lean_nat_dec_eq(v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1923_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1922_, v___x_1918_);
v___x_1924_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1921_, v___x_1923_);
v___y_1899_ = v___x_1924_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_array_get(v___x_1925_, v___x_1918_, v___x_1913_);
lean_dec_ref(v___x_1918_);
v___y_1899_ = v___x_1926_;
goto v___jp_1898_;
}
v___jp_1870_:
{
uint8_t v___x_1873_; 
v___x_1873_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1872_);
if (v___x_1873_ == 0)
{
uint8_t v___x_1874_; 
v___x_1874_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1865_);
if (v___x_1874_ == 0)
{
lean_object* v_doc_1875_; lean_object* v_doc_1876_; uint8_t v___x_1877_; 
v_doc_1875_ = lean_ctor_get(v___y_1872_, 0);
lean_inc(v_doc_1875_);
lean_dec_ref(v___y_1872_);
v_doc_1876_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_doc_1876_);
lean_dec(v_a_1865_);
v___x_1877_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1875_);
if (v___x_1877_ == 0)
{
uint8_t v___x_1878_; 
v___x_1878_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1876_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v___x_1879_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1875_, v_doc_1876_);
v___x_1880_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1879_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___y_1871_);
lean_ctor_set(v___x_1868_, 0, v___x_1880_);
v___x_1882_ = v___x_1868_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___y_1871_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
lean_dec(v_doc_1876_);
v___x_1884_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1875_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___y_1871_);
lean_ctor_set(v___x_1868_, 0, v___x_1884_);
v___x_1886_ = v___x_1868_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___y_1871_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1890_; 
lean_dec(v_doc_1875_);
v___x_1888_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1876_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___y_1871_);
lean_ctor_set(v___x_1868_, 0, v___x_1888_);
v___x_1890_ = v___x_1868_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v___y_1871_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
else
{
lean_object* v___x_1893_; 
lean_dec(v_a_1865_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___y_1871_);
lean_ctor_set(v___x_1868_, 0, v___y_1872_);
v___x_1893_ = v___x_1868_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___y_1872_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___y_1871_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v___x_1896_; 
lean_dec_ref(v___y_1872_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___y_1871_);
v___x_1896_ = v___x_1868_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1865_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___y_1871_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
v___jp_1898_:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___y_1899_, v_stx_1854_, v_a_1866_);
lean_dec(v_stx_1854_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v_a_1902_; uint8_t v___x_1903_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
v_a_1902_ = lean_ctor_get(v___x_1900_, 1);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1900_, 2);
v___x_1903_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1861_);
if (v___x_1903_ == 0)
{
uint8_t v___x_1904_; 
v___x_1904_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1901_);
if (v___x_1904_ == 0)
{
lean_object* v_doc_1905_; lean_object* v_doc_1906_; uint8_t v___x_1907_; 
v_doc_1905_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_doc_1905_);
lean_dec(v_a_1861_);
v_doc_1906_ = lean_ctor_get(v_a_1901_, 0);
lean_inc(v_doc_1906_);
lean_dec(v_a_1901_);
v___x_1907_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1905_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1906_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1905_, v_doc_1906_);
v___x_1910_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1909_);
v___y_1871_ = v_a_1902_;
v___y_1872_ = v___x_1910_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1911_; 
lean_dec(v_doc_1906_);
v___x_1911_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1905_);
v___y_1871_ = v_a_1902_;
v___y_1872_ = v___x_1911_;
goto v___jp_1870_;
}
}
else
{
lean_object* v___x_1912_; 
lean_dec(v_doc_1905_);
v___x_1912_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1906_);
v___y_1871_ = v_a_1902_;
v___y_1872_ = v___x_1912_;
goto v___jp_1870_;
}
}
else
{
lean_dec(v_a_1901_);
v___y_1871_ = v_a_1902_;
v___y_1872_ = v_a_1861_;
goto v___jp_1870_;
}
}
else
{
lean_dec(v_a_1861_);
v___y_1871_ = v_a_1902_;
v___y_1872_ = v_a_1901_;
goto v___jp_1870_;
}
}
else
{
lean_del_object(v___x_1868_);
lean_dec(v_a_1865_);
lean_dec(v_a_1861_);
return v___x_1900_;
}
}
}
}
else
{
lean_dec(v_a_1861_);
lean_dec_ref(v_token_1855_);
lean_dec(v_stx_1854_);
return v___x_1864_;
}
}
else
{
lean_dec_ref(v_token_1855_);
lean_dec(v_stx_1854_);
return v___x_1860_;
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object* v_stx_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
switch(lean_obj_tag(v_stx_1937_))
{
case 0:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_a_1940_);
return v___x_1942_;
}
case 1:
{
lean_object* v_kind_1943_; lean_object* v_args_1944_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_kind_1943_ = lean_ctor_get(v_stx_1937_, 1);
lean_inc(v_kind_1943_);
v_args_1944_ = lean_ctor_get(v_stx_1937_, 2);
lean_inc_ref(v_args_1944_);
lean_dec_ref_known(v_stx_1937_, 3);
v___x_1971_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_1972_ = lean_name_eq(v_kind_1943_, v___x_1971_);
lean_dec(v_kind_1943_);
if (v___x_1972_ == 0)
{
v___y_1946_ = v_a_1938_;
v___y_1947_ = v_a_1939_;
v___y_1948_ = v_a_1940_;
goto v___jp_1945_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_array_get_size(v_args_1944_);
v___x_1975_ = lean_nat_dec_lt(v___x_1973_, v___x_1974_);
if (v___x_1975_ == 0)
{
v___y_1946_ = v_a_1938_;
v___y_1947_ = v_a_1939_;
v___y_1948_ = v_a_1940_;
goto v___jp_1945_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_array_fget(v_args_1944_, v___x_1973_);
lean_dec_ref(v_args_1944_);
v_stx_1937_ = v___x_1976_;
goto _start;
}
}
v___jp_1945_:
{
size_t v_sz_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v_sz_1949_ = lean_array_size(v_args_1944_);
v___x_1950_ = ((size_t)0ULL);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_1949_, v___x_1950_, v_args_1944_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1961_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_a_1953_ = lean_ctor_get(v___x_1951_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1955_ = v___x_1951_;
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = l_Lean_Fmt_TaggedDoc_join(v_a_1952_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1957_);
v___x_1959_ = v___x_1955_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_a_1953_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
v_a_1962_ = lean_ctor_get(v___x_1951_, 0);
v_a_1963_ = lean_ctor_get(v___x_1951_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1951_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_inc(v_a_1962_);
lean_dec(v___x_1951_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
case 2:
{
lean_object* v_val_1978_; lean_object* v___x_1979_; 
v_val_1978_ = lean_ctor_get(v_stx_1937_, 1);
lean_inc_ref(v_val_1978_);
v___x_1979_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1937_, v_val_1978_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1979_;
}
default: 
{
lean_object* v_rawVal_1980_; lean_object* v_str_1981_; lean_object* v_startPos_1982_; lean_object* v_stopPos_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v_rawVal_1980_ = lean_ctor_get(v_stx_1937_, 1);
v_str_1981_ = lean_ctor_get(v_rawVal_1980_, 0);
v_startPos_1982_ = lean_ctor_get(v_rawVal_1980_, 1);
v_stopPos_1983_ = lean_ctor_get(v_rawVal_1980_, 2);
v___x_1984_ = lean_string_utf8_extract(v_str_1981_, v_startPos_1982_, v_stopPos_1983_);
v___x_1985_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1937_, v___x_1984_, v_a_1938_, v_a_1939_, v_a_1940_);
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t v_sz_1986_, size_t v_i_1987_, lean_object* v_bs_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_lt(v_i_1987_, v_sz_1986_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v_bs_1988_);
lean_ctor_set(v___x_1993_, 1, v___y_1991_);
return v___x_1993_;
}
else
{
lean_object* v_v_1994_; lean_object* v___x_1995_; 
v_v_1994_ = lean_array_uget_borrowed(v_bs_1988_, v_i_1987_);
lean_inc(v_v_1994_);
v___x_1995_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_v_1994_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v_a_1997_; lean_object* v___x_1998_; lean_object* v_bs_x27_1999_; size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
v_a_1997_ = lean_ctor_get(v___x_1995_, 1);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1995_, 2);
v___x_1998_ = lean_unsigned_to_nat(0u);
v_bs_x27_1999_ = lean_array_uset(v_bs_1988_, v_i_1987_, v___x_1998_);
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_add(v_i_1987_, v___x_2000_);
v___x_2002_ = lean_array_uset(v_bs_x27_1999_, v_i_1987_, v_a_1996_);
v_i_1987_ = v___x_2001_;
v_bs_1988_ = v___x_2002_;
v___y_1991_ = v_a_1997_;
goto _start;
}
else
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v_bs_1988_);
v_a_2004_ = lean_ctor_get(v___x_1995_, 0);
v_a_2005_ = lean_ctor_get(v___x_1995_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1995_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_inc(v_a_2004_);
lean_dec(v___x_1995_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2004_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object* v_sz_2013_, lean_object* v_i_2014_, lean_object* v_bs_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
size_t v_sz_boxed_2019_; size_t v_i_boxed_2020_; lean_object* v_res_2021_; 
v_sz_boxed_2019_ = lean_unbox_usize(v_sz_2013_);
lean_dec(v_sz_2013_);
v_i_boxed_2020_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_res_2021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_boxed_2019_, v_i_boxed_2020_, v_bs_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec_ref(v___y_2016_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object* v_stx_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec_ref(v_a_2023_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object* v_stx_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
uint8_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = 0;
v___x_2031_ = l_Lean_Syntax_getPos_x3f(v_stx_2027_, v___x_2030_);
if (lean_obj_tag(v___x_2031_) == 1)
{
lean_object* v_val_2032_; lean_object* v___x_2033_; 
v_val_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_val_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2027_, v___x_2030_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_val_2034_; lean_object* v___x_2035_; 
v_val_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = l_Lean_Fmt_getLineInfos(v_val_2032_, v_val_2034_, v_a_2028_, v_a_2029_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2048_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_a_2037_ = lean_ctor_get(v___x_2035_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2039_ = v___x_2035_;
v_isShared_2040_ = v_isSharedCheck_2048_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2048_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_array_get_size(v_a_2036_);
lean_dec(v_a_2036_);
v___x_2043_ = lean_nat_dec_lt(v___x_2041_, v___x_2042_);
v___x_2044_ = lean_box(v___x_2043_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2044_);
v___x_2046_ = v___x_2039_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_a_2037_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_a_2049_ = lean_ctor_get(v___x_2035_, 0);
v_a_2050_ = lean_ctor_get(v___x_2035_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2035_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_inc(v_a_2049_);
lean_dec(v___x_2035_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2049_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec(v___x_2033_);
lean_dec(v_val_2032_);
v___x_2058_ = lean_box(v___x_2030_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_a_2029_);
return v___x_2059_;
}
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec(v___x_2031_);
v___x_2060_ = lean_box(v___x_2030_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v_a_2029_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object* v_stx_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_2062_, v_a_2063_, v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_stx_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object* v_msg_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_panic_fn_borrowed(v___x_2067_, v_msg_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object* v_x2_2069_, lean_object* v_as_2070_, size_t v_i_2071_, size_t v_stop_2072_){
_start:
{
uint8_t v___x_2073_; 
v___x_2073_ = lean_usize_dec_eq(v_i_2071_, v_stop_2072_);
if (v___x_2073_ == 0)
{
lean_object* v_startPos_2074_; lean_object* v___x_2075_; lean_object* v_start_2076_; uint8_t v___x_2077_; 
v_startPos_2074_ = lean_ctor_get(v_x2_2069_, 4);
v___x_2075_ = lean_array_uget_borrowed(v_as_2070_, v_i_2071_);
v_start_2076_ = lean_ctor_get(v___x_2075_, 0);
v___x_2077_ = lean_nat_dec_le(v_startPos_2074_, v_start_2076_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2078_; 
v___x_2078_ = 1;
return v___x_2078_;
}
else
{
size_t v___x_2079_; size_t v___x_2080_; 
v___x_2079_ = ((size_t)1ULL);
v___x_2080_ = lean_usize_add(v_i_2071_, v___x_2079_);
v_i_2071_ = v___x_2080_;
goto _start;
}
}
else
{
uint8_t v___x_2082_; 
v___x_2082_ = 0;
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object* v_x2_2083_, lean_object* v_as_2084_, lean_object* v_i_2085_, lean_object* v_stop_2086_){
_start:
{
size_t v_i_boxed_2087_; size_t v_stop_boxed_2088_; uint8_t v_res_2089_; lean_object* v_r_2090_; 
v_i_boxed_2087_ = lean_unbox_usize(v_i_2085_);
lean_dec(v_i_2085_);
v_stop_boxed_2088_ = lean_unbox_usize(v_stop_2086_);
lean_dec(v_stop_2086_);
v_res_2089_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v_x2_2083_, v_as_2084_, v_i_boxed_2087_, v_stop_boxed_2088_);
lean_dec_ref(v_as_2084_);
lean_dec_ref(v_x2_2083_);
v_r_2090_ = lean_box(v_res_2089_);
return v_r_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object* v_as_2091_, size_t v_i_2092_, size_t v_stop_2093_, lean_object* v_b_2094_){
_start:
{
lean_object* v___y_2096_; uint8_t v___x_2100_; 
v___x_2100_ = lean_usize_dec_eq(v_i_2092_, v_stop_2093_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v_length_2102_; lean_object* v_indentation_2103_; lean_object* v_tokenRanges_2104_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2101_ = lean_array_uget_borrowed(v_as_2091_, v_i_2092_);
v_length_2102_ = lean_ctor_get(v___x_2101_, 0);
v_indentation_2103_ = lean_ctor_get(v___x_2101_, 1);
v_tokenRanges_2104_ = lean_ctor_get(v___x_2101_, 3);
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lean_array_get_size(v_tokenRanges_2104_);
v___x_2110_ = lean_nat_dec_lt(v___x_2108_, v___x_2109_);
if (v___x_2110_ == 0)
{
goto v___jp_2105_;
}
else
{
if (v___x_2110_ == 0)
{
goto v___jp_2105_;
}
else
{
size_t v___x_2111_; size_t v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = lean_usize_of_nat(v___x_2109_);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v___x_2101_, v_tokenRanges_2104_, v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
goto v___jp_2105_;
}
else
{
v___y_2096_ = v_b_2094_;
goto v___jp_2095_;
}
}
}
v___jp_2105_:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_nat_dec_lt(v_indentation_2103_, v_length_2102_);
if (v___x_2106_ == 0)
{
v___y_2096_ = v_b_2094_;
goto v___jp_2095_;
}
else
{
lean_object* v___x_2107_; 
lean_inc(v___x_2101_);
v___x_2107_ = lean_array_push(v_b_2094_, v___x_2101_);
v___y_2096_ = v___x_2107_;
goto v___jp_2095_;
}
}
}
else
{
return v_b_2094_;
}
v___jp_2095_:
{
size_t v___x_2097_; size_t v___x_2098_; 
v___x_2097_ = ((size_t)1ULL);
v___x_2098_ = lean_usize_add(v_i_2092_, v___x_2097_);
v_i_2092_ = v___x_2098_;
v_b_2094_ = v___y_2096_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object* v_as_2114_, lean_object* v_i_2115_, lean_object* v_stop_2116_, lean_object* v_b_2117_){
_start:
{
size_t v_i_boxed_2118_; size_t v_stop_boxed_2119_; lean_object* v_res_2120_; 
v_i_boxed_2118_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_stop_boxed_2119_ = lean_unbox_usize(v_stop_2116_);
lean_dec(v_stop_2116_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v_as_2114_, v_i_boxed_2118_, v_stop_boxed_2119_, v_b_2117_);
lean_dec_ref(v_as_2114_);
return v_res_2120_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v_as_2123_, size_t v_i_2124_, size_t v_stop_2125_){
_start:
{
uint8_t v___x_2126_; 
v___x_2126_ = lean_usize_dec_eq(v_i_2124_, v_stop_2125_);
if (v___x_2126_ == 0)
{
uint8_t v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = 1;
v___x_2128_ = lean_array_uget_borrowed(v_as_2123_, v_i_2124_);
v___x_2129_ = lean_nat_dec_le(v___x_2121_, v___x_2128_);
if (v___x_2129_ == 0)
{
return v___x_2127_;
}
else
{
uint8_t v___x_2130_; 
v___x_2130_ = lean_nat_dec_le(v___x_2121_, v___x_2122_);
if (v___x_2130_ == 0)
{
size_t v___x_2131_; size_t v___x_2132_; 
v___x_2131_ = ((size_t)1ULL);
v___x_2132_ = lean_usize_add(v_i_2124_, v___x_2131_);
v_i_2124_ = v___x_2132_;
goto _start;
}
else
{
return v___x_2127_;
}
}
}
else
{
uint8_t v___x_2134_; 
v___x_2134_ = 0;
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object* v___x_2135_, lean_object* v___x_2136_, lean_object* v_as_2137_, lean_object* v_i_2138_, lean_object* v_stop_2139_){
_start:
{
size_t v_i_boxed_2140_; size_t v_stop_boxed_2141_; uint8_t v_res_2142_; lean_object* v_r_2143_; 
v_i_boxed_2140_ = lean_unbox_usize(v_i_2138_);
lean_dec(v_i_2138_);
v_stop_boxed_2141_ = lean_unbox_usize(v_stop_2139_);
lean_dec(v_stop_2139_);
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2135_, v___x_2136_, v_as_2137_, v_i_boxed_2140_, v_stop_boxed_2141_);
lean_dec_ref(v_as_2137_);
lean_dec(v___x_2136_);
lean_dec(v___x_2135_);
v_r_2143_ = lean_box(v_res_2142_);
return v_r_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_bs_2146_){
_start:
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_usize_dec_lt(v_i_2145_, v_sz_2144_);
if (v___x_2147_ == 0)
{
return v_bs_2146_;
}
else
{
lean_object* v_v_2148_; lean_object* v_indentation_2149_; lean_object* v___x_2150_; lean_object* v_bs_x27_2151_; size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v_v_2148_ = lean_array_uget_borrowed(v_bs_2146_, v_i_2145_);
v_indentation_2149_ = lean_ctor_get(v_v_2148_, 1);
lean_inc(v_indentation_2149_);
v___x_2150_ = lean_unsigned_to_nat(0u);
v_bs_x27_2151_ = lean_array_uset(v_bs_2146_, v_i_2145_, v___x_2150_);
v___x_2152_ = ((size_t)1ULL);
v___x_2153_ = lean_usize_add(v_i_2145_, v___x_2152_);
v___x_2154_ = lean_array_uset(v_bs_x27_2151_, v_i_2145_, v_indentation_2149_);
v_i_2145_ = v___x_2153_;
v_bs_2146_ = v___x_2154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object* v_sz_2156_, lean_object* v_i_2157_, lean_object* v_bs_2158_){
_start:
{
size_t v_sz_boxed_2159_; size_t v_i_boxed_2160_; lean_object* v_res_2161_; 
v_sz_boxed_2159_ = lean_unbox_usize(v_sz_2156_);
lean_dec(v_sz_2156_);
v_i_boxed_2160_ = lean_unbox_usize(v_i_2157_);
lean_dec(v_i_2157_);
v_res_2161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_boxed_2159_, v_i_boxed_2160_, v_bs_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object* v_as_2162_, size_t v_i_2163_, size_t v_stop_2164_, lean_object* v_b_2165_){
_start:
{
lean_object* v___y_2167_; uint8_t v___x_2171_; 
v___x_2171_ = lean_usize_dec_eq(v_i_2163_, v_stop_2164_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_array_uget_borrowed(v_as_2162_, v_i_2163_);
v___x_2173_ = lean_nat_dec_le(v_b_2165_, v___x_2172_);
if (v___x_2173_ == 0)
{
v___y_2167_ = v___x_2172_;
goto v___jp_2166_;
}
else
{
v___y_2167_ = v_b_2165_;
goto v___jp_2166_;
}
}
else
{
lean_inc(v_b_2165_);
return v_b_2165_;
}
v___jp_2166_:
{
size_t v___x_2168_; size_t v___x_2169_; 
v___x_2168_ = ((size_t)1ULL);
v___x_2169_ = lean_usize_add(v_i_2163_, v___x_2168_);
v_i_2163_ = v___x_2169_;
v_b_2165_ = v___y_2167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object* v_as_2174_, lean_object* v_i_2175_, lean_object* v_stop_2176_, lean_object* v_b_2177_){
_start:
{
size_t v_i_boxed_2178_; size_t v_stop_boxed_2179_; lean_object* v_res_2180_; 
v_i_boxed_2178_ = lean_unbox_usize(v_i_2175_);
lean_dec(v_i_2175_);
v_stop_boxed_2179_ = lean_unbox_usize(v_stop_2176_);
lean_dec(v_stop_2176_);
v_res_2180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_as_2174_, v_i_boxed_2178_, v_stop_boxed_2179_, v_b_2177_);
lean_dec(v_b_2177_);
lean_dec_ref(v_as_2174_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object* v_arr_2181_){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2182_ = lean_unsigned_to_nat(0u);
v___x_2183_ = lean_array_fget_borrowed(v_arr_2181_, v___x_2182_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_array_get_size(v_arr_2181_);
v___x_2186_ = lean_nat_dec_lt(v___x_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_inc(v___x_2183_);
return v___x_2183_;
}
else
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((size_t)1ULL);
v___x_2188_ = lean_usize_of_nat(v___x_2185_);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_arr_2181_, v___x_2187_, v___x_2188_, v___x_2183_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object* v_arr_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2190_);
lean_dec_ref(v_arr_2190_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object* v_arr_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2193_ = lean_array_get_size(v_arr_2192_);
v___x_2194_ = lean_unsigned_to_nat(0u);
v___x_2195_ = lean_nat_dec_eq(v___x_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2192_);
v___x_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_box(0);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object* v_arr_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v_arr_2199_);
lean_dec_ref(v_arr_2199_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t v_isFallback_2201_, lean_object* v_stx_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v_rawDoc_2206_; lean_object* v___y_2207_; lean_object* v___y_2220_; lean_object* v___y_2221_; uint8_t v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = 0;
v___x_2226_ = l_Lean_Syntax_getPos_x3f(v_stx_2202_, v___x_2225_);
if (lean_obj_tag(v___x_2226_) == 1)
{
lean_object* v_val_2227_; lean_object* v___x_2228_; 
v_val_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_val_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2202_, v___x_2225_);
if (lean_obj_tag(v___x_2228_) == 1)
{
lean_object* v_val_2229_; lean_object* v___x_2230_; 
v_val_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_n(v_val_2229_, 2);
lean_dec_ref_known(v___x_2228_, 1);
lean_inc(v_val_2227_);
v___x_2230_ = l_Lean_Fmt_getLineInfos(v_val_2227_, v_val_2229_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v_a_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_indentation_2236_; lean_object* v_line_2237_; lean_object* v_startPos_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___y_2242_; size_t v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2256_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
v_a_2232_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2230_, 2);
v___x_2233_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_array_get_borrowed(v___x_2233_, v_a_2231_, v___x_2234_);
v_indentation_2236_ = lean_ctor_get(v___x_2235_, 1);
lean_inc(v_indentation_2236_);
v_line_2237_ = lean_ctor_get(v___x_2235_, 2);
v_startPos_2238_ = lean_ctor_get(v___x_2235_, 4);
v___x_2239_ = lean_nat_sub(v_val_2227_, v_startPos_2238_);
v___x_2240_ = l_String_Pos_Raw_offsetOfPosAux(v_line_2237_, v___x_2239_, v___x_2234_, v___x_2234_);
lean_dec(v___x_2239_);
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = lean_array_get_size(v_a_2231_);
v___x_2270_ = l_Array_toSubarray___redArg(v_a_2231_, v___x_2268_, v___x_2269_);
v___x_2271_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_2272_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_2270_, v___x_2271_);
v___x_2273_ = lean_array_get_size(v___x_2272_);
v___x_2274_ = lean_nat_dec_lt(v___x_2234_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v___x_2272_);
v___y_2256_ = v___x_2271_;
goto v___jp_2255_;
}
else
{
size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = lean_usize_of_nat(v___x_2273_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2272_, v___x_2275_, v___x_2276_, v___x_2271_);
lean_dec_ref(v___x_2272_);
v___y_2256_ = v___x_2277_;
goto v___jp_2255_;
}
v___jp_2241_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2245_, 0, v___y_2244_);
lean_ctor_set(v___x_2245_, 1, v_val_2227_);
lean_ctor_set(v___x_2245_, 2, v_val_2229_);
lean_inc(v_stx_2202_);
v___x_2246_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2202_, v___x_2245_, v_a_2203_, v_a_2232_);
lean_dec_ref_known(v___x_2245_, 3);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v_a_2248_; uint8_t v___x_2249_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
v_a_2248_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2246_, 2);
v___x_2249_ = lean_nat_dec_le(v___x_2240_, v_indentation_2236_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; uint8_t v___x_2251_; 
v___x_2250_ = lean_array_get_size(v___y_2242_);
v___x_2251_ = lean_nat_dec_lt(v___x_2234_, v___x_2250_);
if (v___x_2251_ == 0)
{
lean_dec_ref(v___y_2242_);
lean_dec(v___x_2240_);
lean_dec(v_indentation_2236_);
v___y_2220_ = v_a_2248_;
v___y_2221_ = v_a_2247_;
goto v___jp_2219_;
}
else
{
if (v___x_2251_ == 0)
{
lean_dec_ref(v___y_2242_);
lean_dec(v___x_2240_);
lean_dec(v_indentation_2236_);
v___y_2220_ = v_a_2248_;
v___y_2221_ = v_a_2247_;
goto v___jp_2219_;
}
else
{
size_t v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = lean_usize_of_nat(v___x_2250_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2240_, v_indentation_2236_, v___y_2242_, v___y_2243_, v___x_2252_);
lean_dec_ref(v___y_2242_);
lean_dec(v_indentation_2236_);
lean_dec(v___x_2240_);
if (v___x_2253_ == 0)
{
v___y_2220_ = v_a_2248_;
v___y_2221_ = v_a_2247_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Fmt_TaggedDoc_nested(v_a_2247_);
v_rawDoc_2206_ = v___x_2254_;
v___y_2207_ = v_a_2248_;
goto v___jp_2205_;
}
}
}
}
else
{
lean_dec_ref(v___y_2242_);
lean_dec(v___x_2240_);
lean_dec(v_indentation_2236_);
v___y_2220_ = v_a_2248_;
v___y_2221_ = v_a_2247_;
goto v___jp_2219_;
}
}
else
{
lean_dec_ref(v___y_2242_);
lean_dec(v___x_2240_);
lean_dec(v_indentation_2236_);
lean_dec(v_stx_2202_);
return v___x_2246_;
}
}
v___jp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; size_t v_sz_2260_; size_t v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_mk_empty_array_with_capacity(v___x_2257_);
lean_inc(v___x_2240_);
v___x_2259_ = lean_array_push(v___x_2258_, v___x_2240_);
v_sz_2260_ = lean_array_size(v___y_2256_);
v___x_2261_ = ((size_t)0ULL);
v___x_2262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_2260_, v___x_2261_, v___y_2256_);
v___x_2263_ = l_Array_append___redArg(v___x_2259_, v___x_2262_);
v___x_2264_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v___x_2263_);
lean_dec_ref(v___x_2263_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_2266_ = l_panic___at___00Lean_Fmt_fmtRaw_spec__4(v___x_2265_);
v___y_2242_ = v___x_2262_;
v___y_2243_ = v___x_2261_;
v___y_2244_ = v___x_2266_;
goto v___jp_2241_;
}
else
{
lean_object* v_val_2267_; 
v_val_2267_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v___x_2264_, 1);
v___y_2242_ = v___x_2262_;
v___y_2243_ = v___x_2261_;
v___y_2244_ = v_val_2267_;
goto v___jp_2241_;
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec(v_val_2229_);
lean_dec(v_val_2227_);
lean_dec(v_stx_2202_);
v_a_2278_ = lean_ctor_get(v___x_2230_, 0);
v_a_2279_ = lean_ctor_get(v___x_2230_, 1);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2230_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_inc(v_a_2278_);
lean_dec(v___x_2230_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2278_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec(v___x_2228_);
lean_dec(v_val_2227_);
v___x_2287_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2288_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2287_, v_stx_2202_, v_a_2204_);
lean_dec(v_stx_2202_);
return v___x_2288_;
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec(v___x_2226_);
v___x_2289_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2290_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2289_, v_stx_2202_, v_a_2204_);
lean_dec(v_stx_2202_);
return v___x_2290_;
}
v___jp_2205_:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_rawDoc_2206_, v_stx_2202_, v___y_2207_);
lean_dec(v_stx_2202_);
if (lean_obj_tag(v___x_2208_) == 0)
{
if (v_isFallback_2201_ == 0)
{
return v___x_2208_;
}
else
{
lean_object* v_a_2209_; lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2218_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_a_2210_ = lean_ctor_get(v___x_2208_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2212_ = v___x_2208_;
v_isShared_2213_ = v_isSharedCheck_2218_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2218_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_2209_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2214_);
v___x_2216_ = v___x_2212_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_a_2210_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
else
{
return v___x_2208_;
}
}
v___jp_2219_:
{
lean_object* v_doc_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_doc_2222_ = lean_ctor_get(v___y_2221_, 0);
lean_inc(v_doc_2222_);
lean_dec_ref(v___y_2221_);
v___x_2223_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_2222_);
v___x_2224_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2223_);
v_rawDoc_2206_ = v___x_2224_;
v___y_2207_ = v___y_2220_;
goto v___jp_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object* v_isFallback_2291_, lean_object* v_stx_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
uint8_t v_isFallback_boxed_2295_; lean_object* v_res_2296_; 
v_isFallback_boxed_2295_ = lean_unbox(v_isFallback_2291_);
v_res_2296_ = l_Lean_Fmt_fmtRaw(v_isFallback_boxed_2295_, v_stx_2292_, v_a_2293_, v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object* v_arr_2297_, lean_object* v_h_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object* v_arr_2300_, lean_object* v_h_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(v_arr_2300_, v_h_2301_);
lean_dec_ref(v_arr_2300_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object* v_a_2303_, lean_object* v_____r_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v_a_2303_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v___y_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object* v_a_2309_, lean_object* v_____r_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2309_, v_____r_2310_, v___y_2311_, v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object* v_a_2314_, lean_object* v_b_2315_, lean_object* v_x_2316_){
_start:
{
if (lean_obj_tag(v_x_2316_) == 0)
{
lean_dec(v_b_2315_);
lean_dec_ref(v_a_2314_);
return v_x_2316_;
}
else
{
lean_object* v_key_2317_; lean_object* v_value_2318_; lean_object* v_tail_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2331_; 
v_key_2317_ = lean_ctor_get(v_x_2316_, 0);
v_value_2318_ = lean_ctor_get(v_x_2316_, 1);
v_tail_2319_ = lean_ctor_get(v_x_2316_, 2);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_x_2316_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2321_ = v_x_2316_;
v_isShared_2322_ = v_isSharedCheck_2331_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_tail_2319_);
lean_inc(v_value_2318_);
lean_inc(v_key_2317_);
lean_dec(v_x_2316_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2331_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint8_t v___x_2323_; 
v___x_2323_ = l_Lean_Syntax_instBEqRange_beq(v_key_2317_, v_a_2314_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2314_, v_b_2315_, v_tail_2319_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 2, v___x_2324_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_key_2317_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_value_2318_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
else
{
lean_object* v___x_2329_; 
lean_dec(v_value_2318_);
lean_dec(v_key_2317_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v_b_2315_);
lean_ctor_set(v___x_2321_, 0, v_a_2314_);
v___x_2329_ = v___x_2321_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2314_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_b_2315_);
lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_tail_2319_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
if (lean_obj_tag(v_x_2333_) == 0)
{
return v_x_2332_;
}
else
{
lean_object* v_key_2334_; lean_object* v_value_2335_; lean_object* v_tail_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2359_; 
v_key_2334_ = lean_ctor_get(v_x_2333_, 0);
v_value_2335_ = lean_ctor_get(v_x_2333_, 1);
v_tail_2336_ = lean_ctor_get(v_x_2333_, 2);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_x_2333_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2338_ = v_x_2333_;
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_tail_2336_);
lean_inc(v_value_2335_);
lean_inc(v_key_2334_);
lean_dec(v_x_2333_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2359_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; uint64_t v___x_2341_; uint64_t v___x_2342_; uint64_t v___x_2343_; uint64_t v_fold_2344_; uint64_t v___x_2345_; uint64_t v___x_2346_; uint64_t v___x_2347_; size_t v___x_2348_; size_t v___x_2349_; size_t v___x_2350_; size_t v___x_2351_; size_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2340_ = lean_array_get_size(v_x_2332_);
v___x_2341_ = l_Lean_Syntax_instHashableRange_hash(v_key_2334_);
v___x_2342_ = 32ULL;
v___x_2343_ = lean_uint64_shift_right(v___x_2341_, v___x_2342_);
v_fold_2344_ = lean_uint64_xor(v___x_2341_, v___x_2343_);
v___x_2345_ = 16ULL;
v___x_2346_ = lean_uint64_shift_right(v_fold_2344_, v___x_2345_);
v___x_2347_ = lean_uint64_xor(v_fold_2344_, v___x_2346_);
v___x_2348_ = lean_uint64_to_usize(v___x_2347_);
v___x_2349_ = lean_usize_of_nat(v___x_2340_);
v___x_2350_ = ((size_t)1ULL);
v___x_2351_ = lean_usize_sub(v___x_2349_, v___x_2350_);
v___x_2352_ = lean_usize_land(v___x_2348_, v___x_2351_);
v___x_2353_ = lean_array_uget_borrowed(v_x_2332_, v___x_2352_);
lean_inc(v___x_2353_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 2, v___x_2353_);
v___x_2355_ = v___x_2338_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_key_2334_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_value_2335_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_array_uset(v_x_2332_, v___x_2352_, v___x_2355_);
v_x_2332_ = v___x_2356_;
v_x_2333_ = v_tail_2336_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2360_, lean_object* v_source_2361_, lean_object* v_target_2362_){
_start:
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = lean_array_get_size(v_source_2361_);
v___x_2364_ = lean_nat_dec_lt(v_i_2360_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_dec_ref(v_source_2361_);
lean_dec(v_i_2360_);
return v_target_2362_;
}
else
{
lean_object* v_es_2365_; lean_object* v___x_2366_; lean_object* v_source_2367_; lean_object* v_target_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_es_2365_ = lean_array_fget(v_source_2361_, v_i_2360_);
v___x_2366_ = lean_box(0);
v_source_2367_ = lean_array_fset(v_source_2361_, v_i_2360_, v___x_2366_);
v_target_2368_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2362_, v_es_2365_);
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_add(v_i_2360_, v___x_2369_);
lean_dec(v_i_2360_);
v_i_2360_ = v___x_2370_;
v_source_2361_ = v_source_2367_;
v_target_2362_ = v_target_2368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object* v_data_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_nbuckets_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2373_ = lean_array_get_size(v_data_2372_);
v___x_2374_ = lean_unsigned_to_nat(2u);
v_nbuckets_2375_ = lean_nat_mul(v___x_2373_, v___x_2374_);
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = lean_box(0);
v___x_2378_ = lean_mk_array(v_nbuckets_2375_, v___x_2377_);
v___x_2379_ = lean_array_propagate_mark(v_data_2372_, v___x_2378_);
v___x_2380_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v___x_2376_, v_data_2372_, v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object* v_a_2381_, lean_object* v_x_2382_){
_start:
{
if (lean_obj_tag(v_x_2382_) == 0)
{
uint8_t v___x_2383_; 
v___x_2383_ = 0;
return v___x_2383_;
}
else
{
lean_object* v_key_2384_; lean_object* v_tail_2385_; uint8_t v___x_2386_; 
v_key_2384_ = lean_ctor_get(v_x_2382_, 0);
v_tail_2385_ = lean_ctor_get(v_x_2382_, 2);
v___x_2386_ = l_Lean_Syntax_instBEqRange_beq(v_key_2384_, v_a_2381_);
if (v___x_2386_ == 0)
{
v_x_2382_ = v_tail_2385_;
goto _start;
}
else
{
return v___x_2386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object* v_a_2388_, lean_object* v_x_2389_){
_start:
{
uint8_t v_res_2390_; lean_object* v_r_2391_; 
v_res_2390_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2388_, v_x_2389_);
lean_dec(v_x_2389_);
lean_dec_ref(v_a_2388_);
v_r_2391_ = lean_box(v_res_2390_);
return v_r_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object* v_m_2392_, lean_object* v_a_2393_, lean_object* v_b_2394_){
_start:
{
lean_object* v_size_2395_; lean_object* v_buckets_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2439_; 
v_size_2395_ = lean_ctor_get(v_m_2392_, 0);
v_buckets_2396_ = lean_ctor_get(v_m_2392_, 1);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_m_2392_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2398_ = v_m_2392_;
v_isShared_2399_ = v_isSharedCheck_2439_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_buckets_2396_);
lean_inc(v_size_2395_);
lean_dec(v_m_2392_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2439_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; uint64_t v___x_2401_; uint64_t v___x_2402_; uint64_t v___x_2403_; uint64_t v_fold_2404_; uint64_t v___x_2405_; uint64_t v___x_2406_; uint64_t v___x_2407_; size_t v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; lean_object* v_bkt_2413_; uint8_t v___x_2414_; 
v___x_2400_ = lean_array_get_size(v_buckets_2396_);
v___x_2401_ = l_Lean_Syntax_instHashableRange_hash(v_a_2393_);
v___x_2402_ = 32ULL;
v___x_2403_ = lean_uint64_shift_right(v___x_2401_, v___x_2402_);
v_fold_2404_ = lean_uint64_xor(v___x_2401_, v___x_2403_);
v___x_2405_ = 16ULL;
v___x_2406_ = lean_uint64_shift_right(v_fold_2404_, v___x_2405_);
v___x_2407_ = lean_uint64_xor(v_fold_2404_, v___x_2406_);
v___x_2408_ = lean_uint64_to_usize(v___x_2407_);
v___x_2409_ = lean_usize_of_nat(v___x_2400_);
v___x_2410_ = ((size_t)1ULL);
v___x_2411_ = lean_usize_sub(v___x_2409_, v___x_2410_);
v___x_2412_ = lean_usize_land(v___x_2408_, v___x_2411_);
v_bkt_2413_ = lean_array_uget_borrowed(v_buckets_2396_, v___x_2412_);
v___x_2414_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2393_, v_bkt_2413_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v_size_x27_2416_; lean_object* v___x_2417_; lean_object* v_buckets_x27_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2415_ = lean_unsigned_to_nat(1u);
v_size_x27_2416_ = lean_nat_add(v_size_2395_, v___x_2415_);
lean_dec(v_size_2395_);
lean_inc(v_bkt_2413_);
v___x_2417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2417_, 0, v_a_2393_);
lean_ctor_set(v___x_2417_, 1, v_b_2394_);
lean_ctor_set(v___x_2417_, 2, v_bkt_2413_);
v_buckets_x27_2418_ = lean_array_uset(v_buckets_2396_, v___x_2412_, v___x_2417_);
v___x_2419_ = lean_unsigned_to_nat(4u);
v___x_2420_ = lean_nat_mul(v_size_x27_2416_, v___x_2419_);
v___x_2421_ = lean_unsigned_to_nat(3u);
v___x_2422_ = lean_nat_div(v___x_2420_, v___x_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_array_get_size(v_buckets_x27_2418_);
v___x_2424_ = lean_nat_dec_le(v___x_2422_, v___x_2423_);
lean_dec(v___x_2422_);
if (v___x_2424_ == 0)
{
lean_object* v_val_2425_; lean_object* v___x_2427_; 
v_val_2425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_buckets_x27_2418_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v_val_2425_);
lean_ctor_set(v___x_2398_, 0, v_size_x27_2416_);
v___x_2427_ = v___x_2398_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_size_x27_2416_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_val_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
else
{
lean_object* v___x_2430_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v_buckets_x27_2418_);
lean_ctor_set(v___x_2398_, 0, v_size_x27_2416_);
v___x_2430_ = v___x_2398_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_size_x27_2416_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v_buckets_x27_2418_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
else
{
lean_object* v___x_2432_; lean_object* v_buckets_x27_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_inc(v_bkt_2413_);
v___x_2432_ = lean_box(0);
v_buckets_x27_2433_ = lean_array_uset(v_buckets_2396_, v___x_2412_, v___x_2432_);
v___x_2434_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2393_, v_b_2394_, v_bkt_2413_);
v___x_2435_ = lean_array_uset(v_buckets_x27_2433_, v___x_2412_, v___x_2434_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v___x_2435_);
v___x_2437_ = v___x_2398_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_size_2395_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object* v_f_2440_, lean_object* v_formatterName_2441_, lean_object* v_stx_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v___y_2446_; lean_object* v_a_2458_; lean_object* v_a_2459_; lean_object* v___x_2494_; 
lean_inc_ref(v_a_2443_);
lean_inc(v_stx_2442_);
v___x_2494_ = lean_apply_3(v_f_2440_, v_stx_2442_, v_a_2443_, v_a_2444_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v_a_2496_; lean_object* v___x_2497_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
v_a_2496_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2494_, 2);
v___x_2497_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_a_2495_, v_stx_2442_, v_a_2496_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_stx_2442_);
lean_dec(v_formatterName_2441_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 1);
v_a_2499_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2522_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2498_);
lean_inc(v_a_2499_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2522_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_toBacktrackableState_2503_; lean_object* v_shareCommonState_2504_; lean_object* v_freshTagId_2505_; lean_object* v_missingFormatters_2506_; lean_object* v_partialFormatters_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2521_; 
v_toBacktrackableState_2503_ = lean_ctor_get(v_a_2498_, 0);
v_shareCommonState_2504_ = lean_ctor_get(v_a_2498_, 1);
v_freshTagId_2505_ = lean_ctor_get(v_a_2498_, 2);
v_missingFormatters_2506_ = lean_ctor_get(v_a_2498_, 3);
v_partialFormatters_2507_ = lean_ctor_get(v_a_2498_, 4);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_a_2498_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2509_ = v_a_2498_;
v_isShared_2510_ = v_isSharedCheck_2521_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_partialFormatters_2507_);
lean_inc(v_missingFormatters_2506_);
lean_inc(v_freshTagId_2505_);
lean_inc(v_shareCommonState_2504_);
lean_inc(v_toBacktrackableState_2503_);
lean_dec(v_a_2498_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2521_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_fst_2513_; lean_object* v_snd_2514_; lean_object* v___x_2516_; 
v___x_2511_ = l_Lean_ShareCommon_objectFactory;
v___x_2512_ = lean_state_sharecommon(v___x_2511_, v_shareCommonState_2504_, v_a_2499_);
v_fst_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_fst_2513_);
v_snd_2514_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_snd_2514_);
lean_dec_ref(v___x_2512_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 1, v_snd_2514_);
v___x_2516_ = v___x_2509_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_toBacktrackableState_2503_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_snd_2514_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_freshTagId_2505_);
lean_ctor_set(v_reuseFailAlloc_2520_, 3, v_missingFormatters_2506_);
lean_ctor_set(v_reuseFailAlloc_2520_, 4, v_partialFormatters_2507_);
v___x_2516_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2516_);
lean_ctor_set(v___x_2501_, 0, v_fst_2513_);
v___x_2518_ = v___x_2501_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_fst_2513_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v_a_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2523_);
v_a_2524_ = lean_ctor_get(v___x_2497_, 1);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2497_, 2);
v_a_2458_ = v_a_2523_;
v_a_2459_ = v_a_2524_;
goto v___jp_2457_;
}
}
else
{
lean_object* v_a_2525_; lean_object* v_a_2526_; 
v_a_2525_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2525_);
v_a_2526_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2494_, 2);
v_a_2458_ = v_a_2525_;
v_a_2459_ = v_a_2526_;
goto v___jp_2457_;
}
v___jp_2445_:
{
lean_object* v_a_2447_; lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2456_; 
v_a_2447_ = lean_ctor_get(v___y_2446_, 0);
v_a_2448_ = lean_ctor_get(v___y_2446_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___y_2446_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2450_ = v___y_2446_;
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_inc(v_a_2447_);
lean_dec(v___y_2446_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_a_2452_; lean_object* v___x_2454_; 
v_a_2452_ = lean_ctor_get(v_a_2447_, 0);
lean_inc(v_a_2452_);
lean_dec(v_a_2447_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_a_2452_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2452_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_a_2448_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
v___jp_2457_:
{
if (lean_obj_tag(v_a_2458_) == 0)
{
uint8_t v_err_2460_; 
v_err_2460_ = lean_ctor_get_uint8(v_a_2458_, 0);
if (v_err_2460_ == 0)
{
uint8_t v___x_2461_; lean_object* v___x_2462_; 
lean_dec_ref_known(v_a_2458_, 0);
v___x_2461_ = 1;
lean_inc(v_stx_2442_);
v___x_2462_ = l_Lean_Fmt_fmtRaw(v___x_2461_, v_stx_2442_, v_a_2443_, v_a_2459_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2491_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_a_2464_ = lean_ctor_get(v___x_2462_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2466_ = v___x_2462_;
v_isShared_2467_ = v_isSharedCheck_2491_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2491_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
uint8_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = 0;
v___x_2469_ = l_Lean_Syntax_getRange_x3f(v_stx_2442_, v___x_2468_);
if (lean_obj_tag(v___x_2469_) == 1)
{
lean_object* v_val_2470_; lean_object* v_toBacktrackableState_2471_; lean_object* v_shareCommonState_2472_; lean_object* v_freshTagId_2473_; lean_object* v_missingFormatters_2474_; lean_object* v_partialFormatters_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2488_; 
v_val_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v_toBacktrackableState_2471_ = lean_ctor_get(v_a_2464_, 0);
v_shareCommonState_2472_ = lean_ctor_get(v_a_2464_, 1);
v_freshTagId_2473_ = lean_ctor_get(v_a_2464_, 2);
v_missingFormatters_2474_ = lean_ctor_get(v_a_2464_, 3);
v_partialFormatters_2475_ = lean_ctor_get(v_a_2464_, 4);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2477_ = v_a_2464_;
v_isShared_2478_ = v_isSharedCheck_2488_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_partialFormatters_2475_);
lean_inc(v_missingFormatters_2474_);
lean_inc(v_freshTagId_2473_);
lean_inc(v_shareCommonState_2472_);
lean_inc(v_toBacktrackableState_2471_);
lean_dec(v_a_2464_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2488_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_box(0);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v_formatterName_2441_);
lean_ctor_set(v___x_2466_, 0, v_stx_2442_);
v___x_2481_ = v___x_2466_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_stx_2442_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_formatterName_2441_);
v___x_2481_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_partialFormatters_2475_, v_val_2470_, v___x_2481_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 4, v___x_2482_);
v___x_2484_ = v___x_2477_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_toBacktrackableState_2471_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_shareCommonState_2472_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_freshTagId_2473_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_missingFormatters_2474_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2463_, v___x_2479_, v_a_2443_, v___x_2484_);
v___y_2446_ = v___x_2485_;
goto v___jp_2445_;
}
}
}
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_dec(v___x_2469_);
lean_del_object(v___x_2466_);
lean_dec(v_stx_2442_);
lean_dec(v_formatterName_2441_);
v___x_2489_ = lean_box(0);
v___x_2490_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2463_, v___x_2489_, v_a_2443_, v_a_2464_);
v___y_2446_ = v___x_2490_;
goto v___jp_2445_;
}
}
}
else
{
lean_dec(v_stx_2442_);
lean_dec(v_formatterName_2441_);
return v___x_2462_;
}
}
else
{
lean_object* v___x_2492_; 
lean_dec(v_stx_2442_);
lean_dec(v_formatterName_2441_);
v___x_2492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2492_, 0, v_a_2458_);
lean_ctor_set(v___x_2492_, 1, v_a_2459_);
return v___x_2492_;
}
}
else
{
lean_object* v___x_2493_; 
lean_dec(v_stx_2442_);
lean_dec(v_formatterName_2441_);
v___x_2493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_a_2458_);
lean_ctor_set(v___x_2493_, 1, v_a_2459_);
return v___x_2493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object* v_f_2527_, lean_object* v_formatterName_2528_, lean_object* v_stx_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Fmt_fmtWith(v_f_2527_, v_formatterName_2528_, v_stx_2529_, v_a_2530_, v_a_2531_);
lean_dec_ref(v_a_2530_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object* v_00_u03b2_2533_, lean_object* v_m_2534_, lean_object* v_a_2535_, lean_object* v_b_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_m_2534_, v_a_2535_, v_b_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object* v_00_u03b2_2538_, lean_object* v_a_2539_, lean_object* v_x_2540_){
_start:
{
uint8_t v___x_2541_; 
v___x_2541_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2539_, v_x_2540_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2542_, lean_object* v_a_2543_, lean_object* v_x_2544_){
_start:
{
uint8_t v_res_2545_; lean_object* v_r_2546_; 
v_res_2545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(v_00_u03b2_2542_, v_a_2543_, v_x_2544_);
lean_dec(v_x_2544_);
lean_dec_ref(v_a_2543_);
v_r_2546_ = lean_box(v_res_2545_);
return v_r_2546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object* v_00_u03b2_2547_, lean_object* v_data_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_data_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object* v_00_u03b2_2550_, lean_object* v_a_2551_, lean_object* v_b_2552_, lean_object* v_x_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2551_, v_b_2552_, v_x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2555_, lean_object* v_i_2556_, lean_object* v_source_2557_, lean_object* v_target_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v_i_2556_, v_source_2557_, v_target_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2560_, lean_object* v_x_2561_, lean_object* v_x_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2561_, v_x_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object* v_a_2567_, lean_object* v_kind_2568_, lean_object* v_as_2569_, size_t v_sz_2570_, size_t v_i_2571_, lean_object* v_b_2572_){
_start:
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_usize_dec_lt(v_i_2571_, v_sz_2570_);
if (v___x_2573_ == 0)
{
lean_dec(v_kind_2568_);
lean_inc_ref(v_b_2572_);
return v_b_2572_;
}
else
{
lean_object* v_a_2574_; lean_object* v_provider_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2591_; 
v_a_2574_ = lean_array_uget(v_as_2569_, v_i_2571_);
v_provider_2575_ = lean_ctor_get(v_a_2574_, 1);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_a_2574_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; 
v_unused_2592_ = lean_ctor_get(v_a_2574_, 0);
lean_dec(v_unused_2592_);
v___x_2577_ = v_a_2574_;
v_isShared_2578_ = v_isSharedCheck_2591_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_provider_2575_);
lean_dec(v_a_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2591_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v_env_2579_; lean_object* v_opts_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v_env_2579_ = lean_ctor_get(v_a_2567_, 0);
v_opts_2580_ = lean_ctor_get(v_a_2567_, 3);
v___x_2581_ = lean_box(0);
lean_inc(v_kind_2568_);
lean_inc_ref(v_opts_2580_);
lean_inc_ref(v_env_2579_);
v___x_2582_ = lean_apply_3(v_provider_2575_, v_env_2579_, v_opts_2580_, v_kind_2568_);
if (lean_obj_tag(v___x_2582_) == 1)
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_dec(v_kind_2568_);
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 1, v___x_2581_);
lean_ctor_set(v___x_2577_, 0, v___x_2583_);
v___x_2585_ = v___x_2577_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v___x_2581_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
lean_object* v___x_2587_; size_t v___x_2588_; size_t v___x_2589_; 
lean_dec(v___x_2582_);
lean_del_object(v___x_2577_);
v___x_2587_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_add(v_i_2571_, v___x_2588_);
v_i_2571_ = v___x_2589_;
v_b_2572_ = v___x_2587_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object* v_a_2593_, lean_object* v_kind_2594_, lean_object* v_as_2595_, lean_object* v_sz_2596_, lean_object* v_i_2597_, lean_object* v_b_2598_){
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2596_);
lean_dec(v_sz_2596_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2593_, v_kind_2594_, v_as_2595_, v_sz_boxed_2599_, v_i_boxed_2600_, v_b_2598_);
lean_dec_ref(v_b_2598_);
lean_dec_ref(v_as_2595_);
lean_dec_ref(v_a_2593_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object* v_kind_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_env_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; size_t v_sz_2609_; size_t v___x_2610_; lean_object* v___x_2611_; lean_object* v_fst_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2623_; 
v_env_2605_ = lean_ctor_get(v_a_2603_, 0);
lean_inc_ref(v_env_2605_);
v___x_2606_ = l_Lean_Fmt_getFmtProviders(v_env_2605_);
v___x_2607_ = lean_box(0);
v___x_2608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v_sz_2609_ = lean_array_size(v___x_2606_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2603_, v_kind_2602_, v___x_2606_, v_sz_2609_, v___x_2610_, v___x_2608_);
lean_dec_ref(v___x_2606_);
v_fst_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; 
v_unused_2624_ = lean_ctor_get(v___x_2611_, 1);
lean_dec(v_unused_2624_);
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2623_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_fst_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2623_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
if (lean_obj_tag(v_fst_2612_) == 0)
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 1, v_a_2604_);
lean_ctor_set(v___x_2614_, 0, v___x_2607_);
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_a_2604_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
else
{
lean_object* v_val_2619_; lean_object* v___x_2621_; 
v_val_2619_ = lean_ctor_get(v_fst_2612_, 0);
lean_inc(v_val_2619_);
lean_dec_ref_known(v_fst_2612_, 1);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 1, v_a_2604_);
lean_ctor_set(v___x_2614_, 0, v_val_2619_);
v___x_2621_ = v___x_2614_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_val_2619_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_a_2604_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object* v_kind_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2625_, v_a_2626_, v_a_2627_);
lean_dec_ref(v_a_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object* v_stx_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
switch(lean_obj_tag(v_stx_2629_))
{
case 0:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v_a_2631_);
return v___x_2633_;
}
case 1:
{
lean_object* v_kind_2634_; lean_object* v___x_2635_; lean_object* v_a_2636_; 
lean_inc_ref(v_stx_2629_);
v_kind_2634_ = l_Lean_Syntax_getKind(v_stx_2629_);
lean_inc(v_kind_2634_);
v___x_2635_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2634_, v_a_2630_, v_a_2631_);
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
if (lean_obj_tag(v_a_2636_) == 1)
{
lean_object* v_val_2637_; lean_object* v_a_2638_; lean_object* v_fst_2639_; lean_object* v_snd_2640_; lean_object* v___x_2641_; 
lean_dec(v_kind_2634_);
v_val_2637_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_val_2637_);
v_a_2638_ = lean_ctor_get(v___x_2635_, 1);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2635_);
v_fst_2639_ = lean_ctor_get(v_val_2637_, 0);
lean_inc(v_fst_2639_);
v_snd_2640_ = lean_ctor_get(v_val_2637_, 1);
lean_inc(v_snd_2640_);
lean_dec(v_val_2637_);
v___x_2641_ = l_Lean_Fmt_fmtWith(v_snd_2640_, v_fst_2639_, v_stx_2629_, v_a_2630_, v_a_2638_);
return v___x_2641_;
}
else
{
lean_object* v_a_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; 
v_a_2642_ = lean_ctor_get(v___x_2635_, 1);
lean_inc(v_a_2642_);
lean_dec_ref(v___x_2635_);
v___x_2643_ = 1;
lean_inc_ref(v_stx_2629_);
v___x_2644_ = l_Lean_Fmt_fmtRaw(v___x_2643_, v_stx_2629_, v_a_2630_, v_a_2642_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v_a_2646_; uint8_t v___x_2647_; lean_object* v___x_2648_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
v_a_2646_ = lean_ctor_get(v___x_2644_, 1);
lean_inc(v_a_2646_);
v___x_2647_ = 0;
v___x_2648_ = l_Lean_Syntax_getRange_x3f(v_stx_2629_, v___x_2647_);
lean_dec_ref_known(v_stx_2629_, 3);
if (lean_obj_tag(v___x_2648_) == 1)
{
lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2669_; 
lean_inc(v_a_2645_);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; lean_object* v_unused_2671_; 
v_unused_2670_ = lean_ctor_get(v___x_2644_, 1);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v___x_2644_, 0);
lean_dec(v_unused_2671_);
v___x_2650_ = v___x_2644_;
v_isShared_2651_ = v_isSharedCheck_2669_;
goto v_resetjp_2649_;
}
else
{
lean_dec(v___x_2644_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2669_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v_val_2652_; lean_object* v_toBacktrackableState_2653_; lean_object* v_shareCommonState_2654_; lean_object* v_freshTagId_2655_; lean_object* v_missingFormatters_2656_; lean_object* v_partialFormatters_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2668_; 
v_val_2652_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_val_2652_);
lean_dec_ref_known(v___x_2648_, 1);
v_toBacktrackableState_2653_ = lean_ctor_get(v_a_2646_, 0);
v_shareCommonState_2654_ = lean_ctor_get(v_a_2646_, 1);
v_freshTagId_2655_ = lean_ctor_get(v_a_2646_, 2);
v_missingFormatters_2656_ = lean_ctor_get(v_a_2646_, 3);
v_partialFormatters_2657_ = lean_ctor_get(v_a_2646_, 4);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_a_2646_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2659_ = v_a_2646_;
v_isShared_2660_ = v_isSharedCheck_2668_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_partialFormatters_2657_);
lean_inc(v_missingFormatters_2656_);
lean_inc(v_freshTagId_2655_);
lean_inc(v_shareCommonState_2654_);
lean_inc(v_toBacktrackableState_2653_);
lean_dec(v_a_2646_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2668_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingFormatters_2656_, v_val_2652_, v_kind_2634_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 3, v___x_2661_);
v___x_2663_ = v___x_2659_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_toBacktrackableState_2653_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_shareCommonState_2654_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v_freshTagId_2655_);
lean_ctor_set(v_reuseFailAlloc_2667_, 3, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2667_, 4, v_partialFormatters_2657_);
v___x_2663_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v___x_2663_);
v___x_2665_ = v___x_2650_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2645_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
else
{
lean_dec(v___x_2648_);
lean_dec(v_a_2646_);
lean_dec(v_kind_2634_);
return v___x_2644_;
}
}
else
{
lean_dec_ref_known(v_stx_2629_, 3);
lean_dec(v_kind_2634_);
return v___x_2644_;
}
}
}
case 2:
{
lean_object* v_val_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v_valDocs_2678_; lean_object* v___x_2679_; lean_object* v_valDoc_2680_; lean_object* v___x_2681_; 
v_val_2672_ = lean_ctor_get(v_stx_2629_, 1);
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_string_utf8_byte_size(v_val_2672_);
lean_inc_ref_n(v_val_2672_, 2);
v___x_2675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2675_, 0, v_val_2672_);
lean_ctor_set(v___x_2675_, 1, v___x_2673_);
lean_ctor_set(v___x_2675_, 2, v___x_2674_);
v___x_2676_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_2677_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2678_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_val_2672_, v___x_2675_, v___x_2674_, v___x_2676_, v___x_2677_);
lean_dec_ref_known(v___x_2675_, 3);
v___x_2679_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2680_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2679_, v_valDocs_2678_);
v___x_2681_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2680_, v_stx_2629_, v_a_2631_);
lean_dec_ref_known(v_stx_2629_, 2);
return v___x_2681_;
}
default: 
{
lean_object* v_rawVal_2682_; lean_object* v_str_2683_; lean_object* v_startPos_2684_; lean_object* v_stopPos_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2701_; 
v_rawVal_2682_ = lean_ctor_get(v_stx_2629_, 1);
lean_inc_ref(v_rawVal_2682_);
v_str_2683_ = lean_ctor_get(v_rawVal_2682_, 0);
v_startPos_2684_ = lean_ctor_get(v_rawVal_2682_, 1);
v_stopPos_2685_ = lean_ctor_get(v_rawVal_2682_, 2);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_rawVal_2682_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2687_ = v_rawVal_2682_;
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_stopPos_2685_);
lean_inc(v_startPos_2684_);
lean_inc(v_str_2683_);
lean_dec(v_rawVal_2682_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2701_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2689_ = lean_string_utf8_extract(v_str_2683_, v_startPos_2684_, v_stopPos_2685_);
lean_dec(v_stopPos_2685_);
lean_dec(v_startPos_2684_);
lean_dec_ref(v_str_2683_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = lean_string_utf8_byte_size(v___x_2689_);
lean_inc_ref(v___x_2689_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 2, v___x_2691_);
lean_ctor_set(v___x_2687_, 1, v___x_2690_);
lean_ctor_set(v___x_2687_, 0, v___x_2689_);
v___x_2693_ = v___x_2687_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2700_, 2, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v_valDocs_2696_; lean_object* v___x_2697_; lean_object* v_valDoc_2698_; lean_object* v___x_2699_; 
v___x_2694_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_2695_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2696_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_2689_, v___x_2693_, v___x_2691_, v___x_2694_, v___x_2695_);
lean_dec_ref(v___x_2693_);
v___x_2697_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2698_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2697_, v_valDocs_2696_);
v___x_2699_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2698_, v_stx_2629_, v_a_2631_);
lean_dec_ref_known(v_stx_2629_, 4);
return v___x_2699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object* v_stx_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_Fmt_fmt(v_stx_2702_, v_a_2703_, v_a_2704_);
lean_dec_ref(v_a_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
uint8_t v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = 0;
v___x_2711_ = l_Lean_Syntax_getRange_x3f(v_a_2707_, v___x_2710_);
if (lean_obj_tag(v___x_2711_) == 1)
{
lean_object* v_val_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2777_; 
v_val_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2777_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_val_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2777_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_resolveChoiceNode_2716_; lean_object* v___x_2717_; 
v_resolveChoiceNode_2716_ = lean_ctor_get(v_a_2708_, 2);
lean_inc_ref(v_resolveChoiceNode_2716_);
v___x_2717_ = lean_apply_1(v_resolveChoiceNode_2716_, v_val_2712_);
if (lean_obj_tag(v___x_2717_) == 1)
{
lean_object* v_val_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2764_; 
lean_del_object(v___x_2714_);
v_val_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2764_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_val_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2764_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v_stx_2722_; lean_object* v_chosenAltIdx_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2763_; 
v_stx_2722_ = lean_ctor_get(v_val_2718_, 0);
v_chosenAltIdx_2723_ = lean_ctor_get(v_val_2718_, 1);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_val_2718_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2725_ = v_val_2718_;
v_isShared_2726_ = v_isSharedCheck_2763_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_chosenAltIdx_2723_);
lean_inc(v_stx_2722_);
lean_dec(v_val_2718_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2763_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2727_ = l_Lean_Syntax_getNumArgs(v_stx_2722_);
lean_dec(v_stx_2722_);
v___x_2728_ = l_Lean_Syntax_getNumArgs(v_a_2707_);
v___x_2729_ = lean_nat_dec_eq(v___x_2727_, v___x_2728_);
lean_dec(v___x_2728_);
lean_dec(v___x_2727_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_dec(v_chosenAltIdx_2723_);
v___x_2730_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2731_ = lean_box(0);
lean_inc(v_a_2707_);
v___x_2732_ = l_Lean_Syntax_formatStx(v_a_2707_, v___x_2731_, v___x_2729_);
v___x_2733_ = l_Std_Format_defWidth;
v___x_2734_ = lean_unsigned_to_nat(0u);
v___x_2735_ = l_Std_Format_pretty(v___x_2732_, v___x_2733_, v___x_2734_, v___x_2734_);
v___x_2736_ = lean_string_append(v___x_2730_, v___x_2735_);
lean_dec_ref(v___x_2735_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 1);
lean_ctor_set(v___x_2725_, 1, v___x_2736_);
lean_ctor_set(v___x_2725_, 0, v_a_2707_);
v___x_2738_ = v___x_2725_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2707_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2740_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 2);
lean_ctor_set(v___x_2720_, 0, v___x_2738_);
v___x_2740_ = v___x_2720_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_a_2709_);
return v___x_2741_;
}
}
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v___x_2744_ = l_Lean_Syntax_getArgs(v_a_2707_);
v___x_2745_ = lean_array_get_size(v___x_2744_);
v___x_2746_ = lean_nat_dec_lt(v_chosenAltIdx_2723_, v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec_ref(v___x_2744_);
lean_dec(v_chosenAltIdx_2723_);
v___x_2747_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2748_ = lean_box(0);
lean_inc(v_a_2707_);
v___x_2749_ = l_Lean_Syntax_formatStx(v_a_2707_, v___x_2748_, v___x_2746_);
v___x_2750_ = l_Std_Format_defWidth;
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = l_Std_Format_pretty(v___x_2749_, v___x_2750_, v___x_2751_, v___x_2751_);
v___x_2753_ = lean_string_append(v___x_2747_, v___x_2752_);
lean_dec_ref(v___x_2752_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set_tag(v___x_2725_, 1);
lean_ctor_set(v___x_2725_, 1, v___x_2753_);
lean_ctor_set(v___x_2725_, 0, v_a_2707_);
v___x_2755_ = v___x_2725_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2707_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2757_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set_tag(v___x_2720_, 2);
lean_ctor_set(v___x_2720_, 0, v___x_2755_);
v___x_2757_ = v___x_2720_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v_a_2709_);
return v___x_2758_;
}
}
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_del_object(v___x_2725_);
lean_del_object(v___x_2720_);
lean_dec(v_a_2707_);
v___x_2761_ = lean_array_fget(v___x_2744_, v_chosenAltIdx_2723_);
lean_dec(v_chosenAltIdx_2723_);
lean_dec_ref(v___x_2744_);
v___x_2762_ = l_Lean_Fmt_fmt(v___x_2761_, v_a_2708_, v_a_2709_);
return v___x_2762_;
}
}
}
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v___x_2717_);
v___x_2765_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2766_ = lean_box(0);
lean_inc(v_a_2707_);
v___x_2767_ = l_Lean_Syntax_formatStx(v_a_2707_, v___x_2766_, v___x_2710_);
v___x_2768_ = l_Std_Format_defWidth;
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = l_Std_Format_pretty(v___x_2767_, v___x_2768_, v___x_2769_, v___x_2769_);
v___x_2771_ = lean_string_append(v___x_2765_, v___x_2770_);
lean_dec_ref(v___x_2770_);
v___x_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_a_2707_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 2);
lean_ctor_set(v___x_2714_, 0, v___x_2772_);
v___x_2774_ = v___x_2714_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_a_2709_);
return v___x_2775_;
}
}
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v___x_2711_);
v___x_2778_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2779_ = lean_box(0);
lean_inc(v_a_2707_);
v___x_2780_ = l_Lean_Syntax_formatStx(v_a_2707_, v___x_2779_, v___x_2710_);
v___x_2781_ = l_Std_Format_defWidth;
v___x_2782_ = lean_unsigned_to_nat(0u);
v___x_2783_ = l_Std_Format_pretty(v___x_2780_, v___x_2781_, v___x_2782_, v___x_2782_);
v___x_2784_ = lean_string_append(v___x_2778_, v___x_2783_);
lean_dec_ref(v___x_2783_);
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_a_2707_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v_a_2709_);
return v___x_2787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___boxed(lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec_ref(v_a_2789_);
return v_res_2791_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = l_Lean_Fmt_instInhabitedState_default;
v___x_2793_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v___x_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object* v_msg_2795_){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_obj_once(&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0, &l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0);
v___x_2797_ = lean_panic_fn_borrowed(v___x_2796_, v_msg_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2798_){
_start:
{
lean_object* v_aPtr_2799_; lean_object* v_bPtr_2800_; size_t v_ptr_2801_; size_t v_ptr_2802_; uint64_t v___x_2803_; uint64_t v___x_2804_; uint64_t v___x_2805_; uint64_t v___x_2806_; uint64_t v___x_2807_; 
v_aPtr_2799_ = lean_ctor_get(v_x_2798_, 0);
v_bPtr_2800_ = lean_ctor_get(v_x_2798_, 1);
v_ptr_2801_ = lean_ctor_get_usize(v_aPtr_2799_, 1);
v_ptr_2802_ = lean_ctor_get_usize(v_bPtr_2800_, 1);
v___x_2803_ = 0ULL;
v___x_2804_ = lean_usize_to_uint64(v_ptr_2801_);
v___x_2805_ = lean_uint64_mix_hash(v___x_2803_, v___x_2804_);
v___x_2806_ = lean_usize_to_uint64(v_ptr_2802_);
v___x_2807_ = lean_uint64_mix_hash(v___x_2805_, v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2808_){
_start:
{
uint64_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_x_2808_);
lean_dec_ref(v_x_2808_);
v_r_2810_ = lean_box_uint64(v_res_2809_);
return v_r_2810_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_x_2811_, lean_object* v_x_2812_){
_start:
{
lean_object* v_aPtr_2813_; lean_object* v_aPtr_2814_; lean_object* v_bPtr_2815_; lean_object* v_bPtr_2816_; size_t v_ptr_2817_; size_t v_ptr_2818_; uint8_t v___x_2819_; 
v_aPtr_2813_ = lean_ctor_get(v_x_2811_, 0);
v_aPtr_2814_ = lean_ctor_get(v_x_2812_, 0);
v_bPtr_2815_ = lean_ctor_get(v_x_2811_, 1);
v_bPtr_2816_ = lean_ctor_get(v_x_2812_, 1);
v_ptr_2817_ = lean_ctor_get_usize(v_aPtr_2813_, 1);
v_ptr_2818_ = lean_ctor_get_usize(v_aPtr_2814_, 1);
v___x_2819_ = lean_usize_dec_eq(v_ptr_2817_, v_ptr_2818_);
if (v___x_2819_ == 0)
{
return v___x_2819_;
}
else
{
size_t v_ptr_2820_; size_t v_ptr_2821_; uint8_t v___x_2822_; 
v_ptr_2820_ = lean_ctor_get_usize(v_bPtr_2815_, 1);
v_ptr_2821_ = lean_ctor_get_usize(v_bPtr_2816_, 1);
v___x_2822_ = lean_usize_dec_eq(v_ptr_2820_, v_ptr_2821_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_x_2823_, lean_object* v_x_2824_){
_start:
{
uint8_t v_res_2825_; lean_object* v_r_2826_; 
v_res_2825_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_x_2823_, v_x_2824_);
lean_dec_ref(v_x_2824_);
lean_dec_ref(v_x_2823_);
v_r_2826_ = lean_box(v_res_2825_);
return v_r_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2827_, lean_object* v_x_2828_){
_start:
{
if (lean_obj_tag(v_x_2828_) == 0)
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_box(0);
return v___x_2829_;
}
else
{
lean_object* v_key_2830_; lean_object* v_value_2831_; lean_object* v_tail_2832_; uint8_t v___x_2833_; 
v_key_2830_ = lean_ctor_get(v_x_2828_, 0);
v_value_2831_ = lean_ctor_get(v_x_2828_, 1);
v_tail_2832_ = lean_ctor_get(v_x_2828_, 2);
v___x_2833_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2830_, v_a_2827_);
if (v___x_2833_ == 0)
{
v_x_2828_ = v_tail_2832_;
goto _start;
}
else
{
lean_object* v___x_2835_; 
lean_inc(v_value_2831_);
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_value_2831_);
return v___x_2835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2836_, lean_object* v_x_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2836_, v_x_2837_);
lean_dec(v_x_2837_);
lean_dec_ref(v_a_2836_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(lean_object* v_m_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_buckets_2841_; lean_object* v___x_2842_; uint64_t v___x_2843_; uint64_t v___x_2844_; uint64_t v___x_2845_; uint64_t v_fold_2846_; uint64_t v___x_2847_; uint64_t v___x_2848_; uint64_t v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; size_t v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_buckets_2841_ = lean_ctor_get(v_m_2839_, 1);
v___x_2842_ = lean_array_get_size(v_buckets_2841_);
v___x_2843_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2840_);
v___x_2844_ = 32ULL;
v___x_2845_ = lean_uint64_shift_right(v___x_2843_, v___x_2844_);
v_fold_2846_ = lean_uint64_xor(v___x_2843_, v___x_2845_);
v___x_2847_ = 16ULL;
v___x_2848_ = lean_uint64_shift_right(v_fold_2846_, v___x_2847_);
v___x_2849_ = lean_uint64_xor(v_fold_2846_, v___x_2848_);
v___x_2850_ = lean_uint64_to_usize(v___x_2849_);
v___x_2851_ = lean_usize_of_nat(v___x_2842_);
v___x_2852_ = ((size_t)1ULL);
v___x_2853_ = lean_usize_sub(v___x_2851_, v___x_2852_);
v___x_2854_ = lean_usize_land(v___x_2850_, v___x_2853_);
v___x_2855_ = lean_array_uget_borrowed(v_buckets_2841_, v___x_2854_);
v___x_2856_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2840_, v___x_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_2857_, v_a_2858_);
lean_dec_ref(v_a_2858_);
lean_dec_ref(v_m_2857_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(lean_object* v_x_2860_, lean_object* v_x_2861_){
_start:
{
if (lean_obj_tag(v_x_2861_) == 0)
{
return v_x_2860_;
}
else
{
lean_object* v_key_2862_; lean_object* v_value_2863_; lean_object* v_tail_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2887_; 
v_key_2862_ = lean_ctor_get(v_x_2861_, 0);
v_value_2863_ = lean_ctor_get(v_x_2861_, 1);
v_tail_2864_ = lean_ctor_get(v_x_2861_, 2);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2861_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2866_ = v_x_2861_;
v_isShared_2867_ = v_isSharedCheck_2887_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_tail_2864_);
lean_inc(v_value_2863_);
lean_inc(v_key_2862_);
lean_dec(v_x_2861_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2887_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; uint64_t v___x_2869_; uint64_t v___x_2870_; uint64_t v___x_2871_; uint64_t v_fold_2872_; uint64_t v___x_2873_; uint64_t v___x_2874_; uint64_t v___x_2875_; size_t v___x_2876_; size_t v___x_2877_; size_t v___x_2878_; size_t v___x_2879_; size_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2868_ = lean_array_get_size(v_x_2860_);
v___x_2869_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_key_2862_);
v___x_2870_ = 32ULL;
v___x_2871_ = lean_uint64_shift_right(v___x_2869_, v___x_2870_);
v_fold_2872_ = lean_uint64_xor(v___x_2869_, v___x_2871_);
v___x_2873_ = 16ULL;
v___x_2874_ = lean_uint64_shift_right(v_fold_2872_, v___x_2873_);
v___x_2875_ = lean_uint64_xor(v_fold_2872_, v___x_2874_);
v___x_2876_ = lean_uint64_to_usize(v___x_2875_);
v___x_2877_ = lean_usize_of_nat(v___x_2868_);
v___x_2878_ = ((size_t)1ULL);
v___x_2879_ = lean_usize_sub(v___x_2877_, v___x_2878_);
v___x_2880_ = lean_usize_land(v___x_2876_, v___x_2879_);
v___x_2881_ = lean_array_uget_borrowed(v_x_2860_, v___x_2880_);
lean_inc(v___x_2881_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 2, v___x_2881_);
v___x_2883_ = v___x_2866_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_key_2862_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_value_2863_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; 
v___x_2884_ = lean_array_uset(v_x_2860_, v___x_2880_, v___x_2883_);
v_x_2860_ = v___x_2884_;
v_x_2861_ = v_tail_2864_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(lean_object* v_i_2888_, lean_object* v_source_2889_, lean_object* v_target_2890_){
_start:
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = lean_array_get_size(v_source_2889_);
v___x_2892_ = lean_nat_dec_lt(v_i_2888_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_dec_ref(v_source_2889_);
lean_dec(v_i_2888_);
return v_target_2890_;
}
else
{
lean_object* v_es_2893_; lean_object* v___x_2894_; lean_object* v_source_2895_; lean_object* v_target_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_es_2893_ = lean_array_fget(v_source_2889_, v_i_2888_);
v___x_2894_ = lean_box(0);
v_source_2895_ = lean_array_fset(v_source_2889_, v_i_2888_, v___x_2894_);
v_target_2896_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_target_2890_, v_es_2893_);
v___x_2897_ = lean_unsigned_to_nat(1u);
v___x_2898_ = lean_nat_add(v_i_2888_, v___x_2897_);
lean_dec(v_i_2888_);
v_i_2888_ = v___x_2898_;
v_source_2889_ = v_source_2895_;
v_target_2890_ = v_target_2896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(lean_object* v_data_2900_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_nbuckets_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2901_ = lean_array_get_size(v_data_2900_);
v___x_2902_ = lean_unsigned_to_nat(2u);
v_nbuckets_2903_ = lean_nat_mul(v___x_2901_, v___x_2902_);
v___x_2904_ = lean_unsigned_to_nat(0u);
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_mk_array(v_nbuckets_2903_, v___x_2905_);
v___x_2907_ = lean_array_propagate_mark(v_data_2900_, v___x_2906_);
v___x_2908_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v___x_2904_, v_data_2900_, v___x_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(lean_object* v_a_2909_, lean_object* v_x_2910_){
_start:
{
if (lean_obj_tag(v_x_2910_) == 0)
{
uint8_t v___x_2911_; 
v___x_2911_ = 0;
return v___x_2911_;
}
else
{
lean_object* v_key_2912_; lean_object* v_tail_2913_; uint8_t v___x_2914_; 
v_key_2912_ = lean_ctor_get(v_x_2910_, 0);
v_tail_2913_ = lean_ctor_get(v_x_2910_, 2);
v___x_2914_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2912_, v_a_2909_);
if (v___x_2914_ == 0)
{
v_x_2910_ = v_tail_2913_;
goto _start;
}
else
{
return v___x_2914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_a_2916_, lean_object* v_x_2917_){
_start:
{
uint8_t v_res_2918_; lean_object* v_r_2919_; 
v_res_2918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2916_, v_x_2917_);
lean_dec(v_x_2917_);
lean_dec_ref(v_a_2916_);
v_r_2919_ = lean_box(v_res_2918_);
return v_r_2919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_a_2920_, lean_object* v_b_2921_, lean_object* v_x_2922_){
_start:
{
if (lean_obj_tag(v_x_2922_) == 0)
{
lean_dec(v_b_2921_);
lean_dec_ref(v_a_2920_);
return v_x_2922_;
}
else
{
lean_object* v_key_2923_; lean_object* v_value_2924_; lean_object* v_tail_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2937_; 
v_key_2923_ = lean_ctor_get(v_x_2922_, 0);
v_value_2924_ = lean_ctor_get(v_x_2922_, 1);
v_tail_2925_ = lean_ctor_get(v_x_2922_, 2);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_x_2922_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2927_ = v_x_2922_;
v_isShared_2928_ = v_isSharedCheck_2937_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_tail_2925_);
lean_inc(v_value_2924_);
lean_inc(v_key_2923_);
lean_dec(v_x_2922_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2937_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
uint8_t v___x_2929_; 
v___x_2929_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2923_, v_a_2920_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2920_, v_b_2921_, v_tail_2925_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 2, v___x_2930_);
v___x_2932_ = v___x_2927_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_key_2923_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_value_2924_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
else
{
lean_object* v___x_2935_; 
lean_dec(v_value_2924_);
lean_dec(v_key_2923_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 1, v_b_2921_);
lean_ctor_set(v___x_2927_, 0, v_a_2920_);
v___x_2935_ = v___x_2927_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2920_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_b_2921_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_tail_2925_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(lean_object* v_m_2938_, lean_object* v_a_2939_, lean_object* v_b_2940_){
_start:
{
lean_object* v_size_2941_; lean_object* v_buckets_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2985_; 
v_size_2941_ = lean_ctor_get(v_m_2938_, 0);
v_buckets_2942_ = lean_ctor_get(v_m_2938_, 1);
v_isSharedCheck_2985_ = !lean_is_exclusive(v_m_2938_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2944_ = v_m_2938_;
v_isShared_2945_ = v_isSharedCheck_2985_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_buckets_2942_);
lean_inc(v_size_2941_);
lean_dec(v_m_2938_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2985_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; uint64_t v___x_2947_; uint64_t v___x_2948_; uint64_t v___x_2949_; uint64_t v_fold_2950_; uint64_t v___x_2951_; uint64_t v___x_2952_; uint64_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; lean_object* v_bkt_2959_; uint8_t v___x_2960_; 
v___x_2946_ = lean_array_get_size(v_buckets_2942_);
v___x_2947_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2939_);
v___x_2948_ = 32ULL;
v___x_2949_ = lean_uint64_shift_right(v___x_2947_, v___x_2948_);
v_fold_2950_ = lean_uint64_xor(v___x_2947_, v___x_2949_);
v___x_2951_ = 16ULL;
v___x_2952_ = lean_uint64_shift_right(v_fold_2950_, v___x_2951_);
v___x_2953_ = lean_uint64_xor(v_fold_2950_, v___x_2952_);
v___x_2954_ = lean_uint64_to_usize(v___x_2953_);
v___x_2955_ = lean_usize_of_nat(v___x_2946_);
v___x_2956_ = ((size_t)1ULL);
v___x_2957_ = lean_usize_sub(v___x_2955_, v___x_2956_);
v___x_2958_ = lean_usize_land(v___x_2954_, v___x_2957_);
v_bkt_2959_ = lean_array_uget_borrowed(v_buckets_2942_, v___x_2958_);
v___x_2960_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2939_, v_bkt_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v_size_x27_2962_; lean_object* v___x_2963_; lean_object* v_buckets_x27_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v___x_2961_ = lean_unsigned_to_nat(1u);
v_size_x27_2962_ = lean_nat_add(v_size_2941_, v___x_2961_);
lean_dec(v_size_2941_);
lean_inc(v_bkt_2959_);
v___x_2963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2963_, 0, v_a_2939_);
lean_ctor_set(v___x_2963_, 1, v_b_2940_);
lean_ctor_set(v___x_2963_, 2, v_bkt_2959_);
v_buckets_x27_2964_ = lean_array_uset(v_buckets_2942_, v___x_2958_, v___x_2963_);
v___x_2965_ = lean_unsigned_to_nat(4u);
v___x_2966_ = lean_nat_mul(v_size_x27_2962_, v___x_2965_);
v___x_2967_ = lean_unsigned_to_nat(3u);
v___x_2968_ = lean_nat_div(v___x_2966_, v___x_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_array_get_size(v_buckets_x27_2964_);
v___x_2970_ = lean_nat_dec_le(v___x_2968_, v___x_2969_);
lean_dec(v___x_2968_);
if (v___x_2970_ == 0)
{
lean_object* v_val_2971_; lean_object* v___x_2973_; 
v_val_2971_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_buckets_x27_2964_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_val_2971_);
lean_ctor_set(v___x_2944_, 0, v_size_x27_2962_);
v___x_2973_ = v___x_2944_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_size_x27_2962_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_val_2971_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
else
{
lean_object* v___x_2976_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_buckets_x27_2964_);
lean_ctor_set(v___x_2944_, 0, v_size_x27_2962_);
v___x_2976_ = v___x_2944_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_size_x27_2962_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_buckets_x27_2964_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
else
{
lean_object* v___x_2978_; lean_object* v_buckets_x27_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_inc(v_bkt_2959_);
v___x_2978_ = lean_box(0);
v_buckets_x27_2979_ = lean_array_uset(v_buckets_2942_, v___x_2958_, v___x_2978_);
v___x_2980_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2939_, v_b_2940_, v_bkt_2959_);
v___x_2981_ = lean_array_uset(v_buckets_x27_2979_, v___x_2958_, v___x_2980_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v___x_2981_);
v___x_2983_ = v___x_2944_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_size_2941_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object* v_a_2986_, lean_object* v_b_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___y_2990_; lean_object* v_da1_2995_; lean_object* v_da2_2996_; lean_object* v_db1_2997_; lean_object* v_db2_2998_; lean_object* v___y_2999_; lean_object* v_sa_3006_; lean_object* v_sb_3007_; lean_object* v___y_3008_; 
switch(lean_obj_tag(v_a_2986_))
{
case 0:
{
if (lean_obj_tag(v_b_2987_) == 0)
{
uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = 1;
v___x_3017_ = lean_box(v___x_3016_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v_a_2988_);
return v___x_3018_;
}
else
{
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 1:
{
if (lean_obj_tag(v_b_2987_) == 1)
{
lean_object* v_f_3019_; lean_object* v_f_3020_; 
v_f_3019_ = lean_ctor_get(v_a_2986_, 1);
lean_inc_ref(v_f_3019_);
lean_dec_ref_known(v_a_2986_, 2);
v_f_3020_ = lean_ctor_get(v_b_2987_, 1);
lean_inc_ref(v_f_3020_);
lean_dec_ref_known(v_b_2987_, 2);
v_sa_3006_ = v_f_3019_;
v_sb_3007_ = v_f_3020_;
v___y_3008_ = v_a_2988_;
goto v___jp_3005_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 2:
{
if (lean_obj_tag(v_b_2987_) == 2)
{
lean_object* v_s_3021_; lean_object* v_s_3022_; 
v_s_3021_ = lean_ctor_get(v_a_2986_, 1);
lean_inc_ref(v_s_3021_);
lean_dec_ref_known(v_a_2986_, 2);
v_s_3022_ = lean_ctor_get(v_b_2987_, 1);
lean_inc_ref(v_s_3022_);
lean_dec_ref_known(v_b_2987_, 2);
v_sa_3006_ = v_s_3021_;
v_sb_3007_ = v_s_3022_;
v___y_3008_ = v_a_2988_;
goto v___jp_3005_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 3:
{
if (lean_obj_tag(v_b_2987_) == 3)
{
lean_object* v_id_3023_; lean_object* v_d_3024_; lean_object* v_id_3025_; lean_object* v_d_3026_; uint8_t v___x_3027_; 
v_id_3023_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_id_3023_);
v_d_3024_ = lean_ctor_get(v_a_2986_, 2);
lean_inc(v_d_3024_);
lean_dec_ref_known(v_a_2986_, 3);
v_id_3025_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_id_3025_);
v_d_3026_ = lean_ctor_get(v_b_2987_, 2);
lean_inc(v_d_3026_);
lean_dec_ref_known(v_b_2987_, 3);
v___x_3027_ = lean_nat_dec_eq(v_id_3023_, v_id_3025_);
lean_dec(v_id_3025_);
lean_dec(v_id_3023_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec(v_d_3026_);
lean_dec(v_d_3024_);
v___x_3028_ = lean_box(v___x_3027_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v_a_2988_);
return v___x_3029_;
}
else
{
lean_object* v___x_3030_; 
v___x_3030_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3024_, v_d_3026_, v_a_2988_);
return v___x_3030_;
}
}
else
{
lean_dec_ref_known(v_a_2986_, 3);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 4:
{
if (lean_obj_tag(v_b_2987_) == 4)
{
lean_object* v_d_3031_; lean_object* v_d_3032_; lean_object* v___x_3033_; 
v_d_3031_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3031_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3032_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3032_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3033_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3031_, v_d_3032_, v_a_2988_);
return v___x_3033_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 5:
{
if (lean_obj_tag(v_b_2987_) == 5)
{
lean_object* v_d_3034_; lean_object* v_d_3035_; lean_object* v___x_3036_; 
v_d_3034_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3034_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3035_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3035_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3036_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3034_, v_d_3035_, v_a_2988_);
return v___x_3036_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 6:
{
if (lean_obj_tag(v_b_2987_) == 6)
{
lean_object* v_n_3037_; uint8_t v_isCumulative_3038_; lean_object* v_d_3039_; lean_object* v_n_3040_; uint8_t v_isCumulative_3041_; lean_object* v_d_3042_; uint8_t v___x_3043_; 
v_n_3037_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_n_3037_);
v_isCumulative_3038_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*3 + 7);
v_d_3039_ = lean_ctor_get(v_a_2986_, 2);
lean_inc(v_d_3039_);
lean_dec_ref_known(v_a_2986_, 3);
v_n_3040_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_n_3040_);
v_isCumulative_3041_ = lean_ctor_get_uint8(v_b_2987_, sizeof(void*)*3 + 7);
v_d_3042_ = lean_ctor_get(v_b_2987_, 2);
lean_inc(v_d_3042_);
lean_dec_ref_known(v_b_2987_, 3);
v___x_3043_ = lean_nat_dec_eq(v_n_3037_, v_n_3040_);
lean_dec(v_n_3040_);
lean_dec(v_n_3037_);
if (v___x_3043_ == 0)
{
lean_dec(v_d_3042_);
lean_dec(v_d_3039_);
goto v___jp_3012_;
}
else
{
if (v_isCumulative_3041_ == 0)
{
if (v_isCumulative_3038_ == 0)
{
lean_object* v___x_3044_; 
v___x_3044_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3039_, v_d_3042_, v_a_2988_);
return v___x_3044_;
}
else
{
lean_dec(v_d_3042_);
lean_dec(v_d_3039_);
goto v___jp_3012_;
}
}
else
{
if (v_isCumulative_3038_ == 0)
{
lean_dec(v_d_3042_);
lean_dec(v_d_3039_);
goto v___jp_3012_;
}
else
{
lean_object* v___x_3045_; 
v___x_3045_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3039_, v_d_3042_, v_a_2988_);
return v___x_3045_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2986_, 3);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 7:
{
if (lean_obj_tag(v_b_2987_) == 7)
{
lean_object* v_d_3046_; lean_object* v_d_3047_; lean_object* v___x_3048_; 
v_d_3046_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3046_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3047_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3047_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3048_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3046_, v_d_3047_, v_a_2988_);
return v___x_3048_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 8:
{
if (lean_obj_tag(v_b_2987_) == 8)
{
uint8_t v_onlyNonCumulative_3049_; 
v_onlyNonCumulative_3049_ = lean_ctor_get_uint8(v_b_2987_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_3049_ == 0)
{
uint8_t v_onlyNonCumulative_3050_; 
v_onlyNonCumulative_3050_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_3050_ == 0)
{
lean_object* v_d_3051_; lean_object* v_d_3052_; lean_object* v___x_3053_; 
v_d_3051_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3051_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3052_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3052_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3053_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3051_, v_d_3052_, v_a_2988_);
return v___x_3053_;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref_known(v_b_2987_, 2);
lean_dec_ref_known(v_a_2986_, 2);
v___x_3054_ = lean_box(v_onlyNonCumulative_3049_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v_a_2988_);
return v___x_3055_;
}
}
else
{
uint8_t v_onlyNonCumulative_3056_; 
v_onlyNonCumulative_3056_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref_known(v_b_2987_, 2);
lean_dec_ref_known(v_a_2986_, 2);
v___x_3057_ = lean_box(v_onlyNonCumulative_3056_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v_a_2988_);
return v___x_3058_;
}
else
{
lean_object* v_d_3059_; lean_object* v_d_3060_; lean_object* v___x_3061_; 
v_d_3059_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3059_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3060_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3060_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3061_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3059_, v_d_3060_, v_a_2988_);
return v___x_3061_;
}
}
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 9:
{
if (lean_obj_tag(v_b_2987_) == 9)
{
lean_object* v_d_3062_; lean_object* v_d_3063_; lean_object* v___x_3064_; 
v_d_3062_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3062_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3063_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3063_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3064_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3062_, v_d_3063_, v_a_2988_);
return v___x_3064_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 10:
{
if (lean_obj_tag(v_b_2987_) == 10)
{
lean_object* v_d_3065_; lean_object* v_d_3066_; lean_object* v___x_3067_; 
v_d_3065_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3065_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3066_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3066_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3067_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3065_, v_d_3066_, v_a_2988_);
return v___x_3067_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 11:
{
if (lean_obj_tag(v_b_2987_) == 11)
{
lean_object* v_d_3068_; lean_object* v_d_3069_; lean_object* v___x_3070_; 
v_d_3068_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_d_3068_);
lean_dec_ref_known(v_a_2986_, 2);
v_d_3069_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_d_3069_);
lean_dec_ref_known(v_b_2987_, 2);
v___x_3070_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3068_, v_d_3069_, v_a_2988_);
return v___x_3070_;
}
else
{
lean_dec_ref_known(v_a_2986_, 2);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 12:
{
if (lean_obj_tag(v_b_2987_) == 12)
{
lean_object* v_p_3071_; lean_object* v_p_3072_; lean_object* v_d_3073_; lean_object* v_d_3074_; lean_object* v_id_3075_; lean_object* v_id_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3086_; 
v_p_3071_ = lean_ctor_get(v_a_2986_, 1);
lean_inc_ref(v_p_3071_);
v_p_3072_ = lean_ctor_get(v_b_2987_, 1);
lean_inc_ref(v_p_3072_);
v_d_3073_ = lean_ctor_get(v_a_2986_, 2);
lean_inc(v_d_3073_);
lean_dec_ref_known(v_a_2986_, 3);
v_d_3074_ = lean_ctor_get(v_b_2987_, 2);
lean_inc(v_d_3074_);
lean_dec_ref_known(v_b_2987_, 3);
v_id_3075_ = lean_ctor_get(v_p_3071_, 1);
lean_inc(v_id_3075_);
lean_dec_ref(v_p_3071_);
v_id_3076_ = lean_ctor_get(v_p_3072_, 1);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_p_3072_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v_p_3072_, 0);
lean_dec(v_unused_3087_);
v___x_3078_ = v_p_3072_;
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_id_3076_);
lean_dec(v_p_3072_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3086_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
uint8_t v___x_3080_; 
v___x_3080_ = lean_name_eq(v_id_3075_, v_id_3076_);
lean_dec(v_id_3076_);
lean_dec(v_id_3075_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3083_; 
lean_dec(v_d_3074_);
lean_dec(v_d_3073_);
v___x_3081_ = lean_box(v___x_3080_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v_a_2988_);
lean_ctor_set(v___x_3078_, 0, v___x_3081_);
v___x_3083_ = v___x_3078_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_a_2988_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
else
{
lean_object* v___x_3085_; 
lean_del_object(v___x_3078_);
v___x_3085_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3073_, v_d_3074_, v_a_2988_);
return v___x_3085_;
}
}
}
else
{
lean_dec_ref_known(v_a_2986_, 3);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 13:
{
if (lean_obj_tag(v_b_2987_) == 13)
{
lean_object* v_cost_3088_; lean_object* v_d_3089_; lean_object* v_cost_3090_; lean_object* v_d_3091_; uint8_t v___x_3092_; 
v_cost_3088_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_cost_3088_);
v_d_3089_ = lean_ctor_get(v_a_2986_, 2);
lean_inc(v_d_3089_);
lean_dec_ref_known(v_a_2986_, 3);
v_cost_3090_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_cost_3090_);
v_d_3091_ = lean_ctor_get(v_b_2987_, 2);
lean_inc(v_d_3091_);
lean_dec_ref_known(v_b_2987_, 3);
v___x_3092_ = l_Lean_Fmt_instBEqDefaultCost_beq___redArg(v_cost_3088_, v_cost_3090_);
lean_dec(v_cost_3090_);
lean_dec(v_cost_3088_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec(v_d_3091_);
lean_dec(v_d_3089_);
v___x_3093_ = lean_box(v___x_3092_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_a_2988_);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3089_, v_d_3091_, v_a_2988_);
return v___x_3095_;
}
}
else
{
lean_dec_ref_known(v_a_2986_, 3);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
case 14:
{
if (lean_obj_tag(v_b_2987_) == 14)
{
lean_object* v_a_3096_; lean_object* v_b_3097_; lean_object* v_a_3098_; lean_object* v_b_3099_; 
v_a_3096_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_a_3096_);
v_b_3097_ = lean_ctor_get(v_a_2986_, 2);
lean_inc(v_b_3097_);
lean_dec_ref_known(v_a_2986_, 3);
v_a_3098_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_a_3098_);
v_b_3099_ = lean_ctor_get(v_b_2987_, 2);
lean_inc(v_b_3099_);
lean_dec_ref_known(v_b_2987_, 3);
v_da1_2995_ = v_a_3096_;
v_da2_2996_ = v_b_3097_;
v_db1_2997_ = v_a_3098_;
v_db2_2998_ = v_b_3099_;
v___y_2999_ = v_a_2988_;
goto v___jp_2994_;
}
else
{
lean_dec_ref_known(v_a_2986_, 3);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
default: 
{
if (lean_obj_tag(v_b_2987_) == 15)
{
lean_object* v_a_3100_; lean_object* v_b_3101_; lean_object* v_a_3102_; lean_object* v_b_3103_; 
v_a_3100_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_a_3100_);
v_b_3101_ = lean_ctor_get(v_a_2986_, 2);
lean_inc(v_b_3101_);
lean_dec_ref_known(v_a_2986_, 3);
v_a_3102_ = lean_ctor_get(v_b_2987_, 1);
lean_inc(v_a_3102_);
v_b_3103_ = lean_ctor_get(v_b_2987_, 2);
lean_inc(v_b_3103_);
lean_dec_ref_known(v_b_2987_, 3);
v_da1_2995_ = v_a_3100_;
v_da2_2996_ = v_b_3101_;
v_db1_2997_ = v_a_3102_;
v_db2_2998_ = v_b_3103_;
v___y_2999_ = v_a_2988_;
goto v___jp_2994_;
}
else
{
lean_dec_ref_known(v_a_2986_, 3);
lean_dec(v_b_2987_);
v___y_2990_ = v_a_2988_;
goto v___jp_2989_;
}
}
}
v___jp_2989_:
{
uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2991_ = 0;
v___x_2992_ = lean_box(v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v___y_2990_);
return v___x_2993_;
}
v___jp_2994_:
{
lean_object* v___x_3000_; lean_object* v_fst_3001_; uint8_t v___x_3002_; 
v___x_3000_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da1_2995_, v_db1_2997_, v___y_2999_);
v_fst_3001_ = lean_ctor_get(v___x_3000_, 0);
v___x_3002_ = lean_unbox(v_fst_3001_);
if (v___x_3002_ == 0)
{
lean_dec(v_db2_2998_);
lean_dec(v_da2_2996_);
return v___x_3000_;
}
else
{
lean_object* v_snd_3003_; lean_object* v___x_3004_; 
v_snd_3003_ = lean_ctor_get(v___x_3000_, 1);
lean_inc(v_snd_3003_);
lean_dec_ref(v___x_3000_);
v___x_3004_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da2_2996_, v_db2_2998_, v_snd_3003_);
return v___x_3004_;
}
}
v___jp_3005_:
{
uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_string_dec_eq(v_sa_3006_, v_sb_3007_);
lean_dec_ref(v_sb_3007_);
lean_dec_ref(v_sa_3006_);
v___x_3010_ = lean_box(v___x_3009_);
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___y_3008_);
return v___x_3011_;
}
v___jp_3012_:
{
uint8_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = 0;
v___x_3014_ = lean_box(v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v_a_2988_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object* v_a_3104_, lean_object* v_b_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_cacheKey_3109_; lean_object* v___x_3110_; 
lean_inc(v_a_3104_);
v___x_3107_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3104_);
lean_inc(v_b_3105_);
v___x_3108_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3105_);
v_cacheKey_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3109_, 0, v___x_3107_);
lean_ctor_set(v_cacheKey_3109_, 1, v___x_3108_);
v___x_3110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_a_3106_, v_cacheKey_3109_);
if (lean_obj_tag(v___x_3110_) == 1)
{
lean_object* v_val_3111_; lean_object* v___x_3112_; 
lean_dec_ref_known(v_cacheKey_3109_, 2);
lean_dec(v_b_3105_);
lean_dec(v_a_3104_);
v_val_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_val_3111_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_val_3111_);
lean_ctor_set(v___x_3112_, 1, v_a_3106_);
return v___x_3112_;
}
else
{
lean_object* v___x_3113_; lean_object* v_fst_3114_; lean_object* v_snd_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v___x_3110_);
v___x_3113_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(v_a_3104_, v_b_3105_, v_a_3106_);
v_fst_3114_ = lean_ctor_get(v___x_3113_, 0);
v_snd_3115_ = lean_ctor_get(v___x_3113_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3117_ = v___x_3113_;
v_isShared_3118_ = v_isSharedCheck_3123_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_snd_3115_);
lean_inc(v_fst_3114_);
lean_dec(v___x_3113_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3123_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
lean_inc(v_fst_3114_);
v___x_3119_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_snd_3115_, v_cacheKey_3109_, v_fst_3114_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3119_);
v___x_3121_ = v___x_3117_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_fst_3114_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = lean_box(0);
v___x_3125_ = lean_unsigned_to_nat(16u);
v___x_3126_ = lean_mk_array(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0);
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
lean_ctor_set(v___x_3129_, 1, v___x_3127_);
return v___x_3129_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object* v_a_3130_, lean_object* v_b_3131_){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v_fst_3134_; uint8_t v___x_3135_; 
v___x_3132_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1);
v___x_3133_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_a_3130_, v_b_3131_, v___x_3132_);
v_fst_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_fst_3134_);
lean_dec_ref(v___x_3133_);
v___x_3135_ = lean_unbox(v_fst_3134_);
lean_dec(v_fst_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object* v_a_3136_, lean_object* v_b_3137_){
_start:
{
uint8_t v_res_3138_; lean_object* v_r_3139_; 
v_res_3138_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_a_3136_, v_b_3137_);
v_r_3139_ = lean_box(v_res_3138_);
return v_r_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object* v_a_3140_, lean_object* v_choiceStx_3141_, lean_object* v_as_3142_, size_t v_sz_3143_, size_t v_i_3144_, lean_object* v_b_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_a_3149_; lean_object* v_a_3150_; uint8_t v___x_3154_; 
v___x_3154_ = lean_usize_dec_lt(v_i_3144_, v_sz_3143_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; 
lean_dec(v_choiceStx_3141_);
lean_dec_ref(v_a_3140_);
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_b_3145_);
lean_ctor_set(v___x_3155_, 1, v___y_3147_);
return v___x_3155_;
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3157_; 
lean_dec_ref(v___y_3147_);
v_a_3156_ = lean_array_uget_borrowed(v_as_3142_, v_i_3144_);
lean_inc_ref(v_a_3140_);
lean_inc(v_a_3156_);
v___x_3157_ = l_Lean_Fmt_fmt(v_a_3156_, v___y_3146_, v_a_3140_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_snd_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3234_; 
v_snd_3158_ = lean_ctor_get(v_b_3145_, 1);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_b_3145_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v_b_3145_, 0);
lean_dec(v_unused_3235_);
v___x_3160_ = v_b_3145_;
v_isShared_3161_ = v_isSharedCheck_3234_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snd_3158_);
lean_dec(v_b_3145_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3234_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_a_3162_; lean_object* v_a_3163_; lean_object* v_fst_3164_; lean_object* v_snd_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3233_; 
v_a_3162_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3162_);
v_a_3163_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3157_, 2);
v_fst_3164_ = lean_ctor_get(v_snd_3158_, 0);
v_snd_3165_ = lean_ctor_get(v_snd_3158_, 1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_snd_3158_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3167_ = v_snd_3158_;
v_isShared_3168_ = v_isSharedCheck_3233_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_snd_3165_);
lean_inc(v_fst_3164_);
lean_dec(v_snd_3158_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3233_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v_first_x3f_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; 
v___x_3169_ = lean_box(0);
if (lean_obj_tag(v_fst_3164_) == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_inc(v_a_3163_);
lean_inc(v_a_3162_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_a_3162_);
lean_ctor_set(v___x_3231_, 1, v_a_3163_);
v___x_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
v_first_x3f_3171_ = v___x_3232_;
v___y_3172_ = v___y_3146_;
v___y_3173_ = v_a_3163_;
goto v___jp_3170_;
}
else
{
v_first_x3f_3171_ = v_fst_3164_;
v___y_3172_ = v___y_3146_;
v___y_3173_ = v_a_3163_;
goto v___jp_3170_;
}
v___jp_3170_:
{
uint8_t v___x_3174_; 
lean_inc(v_a_3162_);
v___x_3174_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_a_3162_);
if (v___x_3174_ == 0)
{
if (lean_obj_tag(v_snd_3165_) == 1)
{
lean_object* v_val_3175_; lean_object* v_fst_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3215_; 
lean_del_object(v___x_3160_);
v_val_3175_ = lean_ctor_get(v_snd_3165_, 0);
lean_inc(v_val_3175_);
v_fst_3176_ = lean_ctor_get(v_val_3175_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_val_3175_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v_val_3175_, 1);
lean_dec(v_unused_3216_);
v___x_3178_ = v_val_3175_;
v_isShared_3179_ = v_isSharedCheck_3215_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_fst_3176_);
lean_dec(v_val_3175_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3215_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v_doc_3180_; lean_object* v_doc_3181_; uint8_t v___x_3182_; 
v_doc_3180_ = lean_ctor_get(v_a_3162_, 0);
lean_inc(v_doc_3180_);
lean_dec(v_a_3162_);
v_doc_3181_ = lean_ctor_get(v_fst_3176_, 0);
lean_inc(v_doc_3181_);
lean_dec(v_fst_3176_);
v___x_3182_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_doc_3180_, v_doc_3181_);
if (v___x_3182_ == 0)
{
lean_object* v___x_3183_; 
lean_dec_ref(v___y_3173_);
v___x_3183_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_choiceStx_3141_, v___y_3172_, v_a_3140_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3199_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_a_3185_ = lean_ctor_get(v___x_3183_, 1);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3187_ = v___x_3183_;
v_isShared_3188_ = v_isSharedCheck_3199_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3199_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_a_3184_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v_snd_3165_);
lean_ctor_set(v___x_3178_, 0, v_first_x3f_3171_);
v___x_3191_ = v___x_3178_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_first_x3f_3171_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_snd_3165_);
v___x_3191_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3193_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___x_3191_);
lean_ctor_set(v___x_3167_, 0, v___x_3189_);
v___x_3193_ = v___x_3167_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3193_);
v___x_3195_ = v___x_3187_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_a_3185_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3178_);
lean_dec_ref_known(v_snd_3165_, 1);
lean_dec(v_first_x3f_3171_);
lean_del_object(v___x_3167_);
v_a_3200_ = lean_ctor_get(v___x_3183_, 0);
v_a_3201_ = lean_ctor_get(v___x_3183_, 1);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3183_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_inc(v_a_3200_);
lean_dec(v___x_3183_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3200_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v___x_3210_; 
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v_snd_3165_);
lean_ctor_set(v___x_3178_, 0, v_first_x3f_3171_);
v___x_3210_ = v___x_3178_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_first_x3f_3171_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_snd_3165_);
v___x_3210_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3212_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___x_3210_);
lean_ctor_set(v___x_3167_, 0, v___x_3169_);
v___x_3212_ = v___x_3167_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
v_a_3149_ = v___x_3212_;
v_a_3150_ = v___y_3173_;
goto v___jp_3148_;
}
}
}
}
}
else
{
lean_object* v___x_3218_; 
lean_dec(v_snd_3165_);
lean_inc_ref(v___y_3173_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___y_3173_);
lean_ctor_set(v___x_3167_, 0, v_a_3162_);
v___x_3218_ = v___x_3167_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3162_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___y_3173_);
v___x_3218_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3221_; 
v___x_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3219_);
lean_ctor_set(v___x_3160_, 0, v_first_x3f_3171_);
v___x_3221_ = v___x_3160_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_first_x3f_3171_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___x_3219_);
v___x_3221_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3169_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v_a_3149_ = v___x_3222_;
v_a_3150_ = v___y_3173_;
goto v___jp_3148_;
}
}
}
}
else
{
lean_object* v___x_3226_; 
lean_dec(v_a_3162_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v_first_x3f_3171_);
v___x_3226_ = v___x_3167_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_first_x3f_3171_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_snd_3165_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3228_; 
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 1, v___x_3226_);
lean_ctor_set(v___x_3160_, 0, v___x_3169_);
v___x_3228_ = v___x_3160_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
v_a_3149_ = v___x_3228_;
v_a_3150_ = v___y_3173_;
goto v___jp_3148_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3236_; lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec_ref(v_b_3145_);
lean_dec(v_choiceStx_3141_);
lean_dec_ref(v_a_3140_);
v_a_3236_ = lean_ctor_get(v___x_3157_, 0);
v_a_3237_ = lean_ctor_get(v___x_3157_, 1);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_3157_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_inc(v_a_3236_);
lean_dec(v___x_3157_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3236_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
v___jp_3148_:
{
size_t v___x_3151_; size_t v___x_3152_; 
v___x_3151_ = ((size_t)1ULL);
v___x_3152_ = lean_usize_add(v_i_3144_, v___x_3151_);
v_i_3144_ = v___x_3152_;
v_b_3145_ = v_a_3149_;
v___y_3147_ = v_a_3150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1___boxed(lean_object* v_a_3245_, lean_object* v_choiceStx_3246_, lean_object* v_as_3247_, lean_object* v_sz_3248_, lean_object* v_i_3249_, lean_object* v_b_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
size_t v_sz_boxed_3253_; size_t v_i_boxed_3254_; lean_object* v_res_3255_; 
v_sz_boxed_3253_ = lean_unbox_usize(v_sz_3248_);
lean_dec(v_sz_3248_);
v_i_boxed_3254_ = lean_unbox_usize(v_i_3249_);
lean_dec(v_i_3249_);
v_res_3255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3245_, v_choiceStx_3246_, v_as_3247_, v_sz_boxed_3253_, v_i_boxed_3254_, v_b_3250_, v___y_3251_, v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v_as_3247_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object* v_choiceStx_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v___y_3265_; lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3275_ = l_Lean_Syntax_getNumArgs(v_choiceStx_3261_);
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = lean_nat_dec_eq(v___x_3275_, v___x_3276_);
lean_dec(v___x_3275_);
if (v___x_3277_ == 0)
{
lean_object* v___x_3278_; lean_object* v___x_3279_; size_t v_sz_3280_; size_t v___x_3281_; lean_object* v___x_3282_; 
v___x_3278_ = l_Lean_Syntax_getArgs(v_choiceStx_3261_);
v___x_3279_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1));
v_sz_3280_ = lean_array_size(v___x_3278_);
v___x_3281_ = ((size_t)0ULL);
lean_inc_ref(v_a_3263_);
v___x_3282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3263_, v_choiceStx_3261_, v___x_3278_, v_sz_3280_, v___x_3281_, v___x_3279_, v_a_3262_, v_a_3263_);
lean_dec_ref(v___x_3278_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v_fst_3284_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
v_fst_3284_ = lean_ctor_get(v_a_3283_, 0);
if (lean_obj_tag(v_fst_3284_) == 0)
{
lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3300_; 
lean_inc(v_a_3283_);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; lean_object* v_unused_3302_; 
v_unused_3301_ = lean_ctor_get(v___x_3282_, 1);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v___x_3282_, 0);
lean_dec(v_unused_3302_);
v___x_3286_ = v___x_3282_;
v_isShared_3287_ = v_isSharedCheck_3300_;
goto v_resetjp_3285_;
}
else
{
lean_dec(v___x_3282_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3300_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v_snd_3288_; lean_object* v_snd_3289_; 
v_snd_3288_ = lean_ctor_get(v_a_3283_, 1);
lean_inc(v_snd_3288_);
lean_dec(v_a_3283_);
v_snd_3289_ = lean_ctor_get(v_snd_3288_, 1);
if (lean_obj_tag(v_snd_3289_) == 1)
{
lean_object* v_val_3290_; lean_object* v_fst_3291_; lean_object* v_snd_3292_; lean_object* v___x_3294_; 
lean_inc_ref(v_snd_3289_);
lean_dec(v_snd_3288_);
v_val_3290_ = lean_ctor_get(v_snd_3289_, 0);
lean_inc(v_val_3290_);
lean_dec_ref_known(v_snd_3289_, 1);
v_fst_3291_ = lean_ctor_get(v_val_3290_, 0);
lean_inc(v_fst_3291_);
v_snd_3292_ = lean_ctor_get(v_val_3290_, 1);
lean_inc(v_snd_3292_);
lean_dec(v_val_3290_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 1, v_snd_3292_);
lean_ctor_set(v___x_3286_, 0, v_fst_3291_);
v___x_3294_ = v___x_3286_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_fst_3291_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_snd_3292_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
else
{
lean_object* v_fst_3296_; 
lean_del_object(v___x_3286_);
v_fst_3296_ = lean_ctor_get(v_snd_3288_, 0);
lean_inc(v_fst_3296_);
lean_dec(v_snd_3288_);
if (lean_obj_tag(v_fst_3296_) == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3298_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v___x_3297_);
v___y_3265_ = v___x_3298_;
goto v___jp_3264_;
}
else
{
lean_object* v_val_3299_; 
v_val_3299_ = lean_ctor_get(v_fst_3296_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v_fst_3296_, 1);
v___y_3265_ = v_val_3299_;
goto v___jp_3264_;
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3311_; 
lean_inc_ref(v_fst_3284_);
v_a_3303_ = lean_ctor_get(v___x_3282_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3311_ == 0)
{
lean_object* v_unused_3312_; 
v_unused_3312_ = lean_ctor_get(v___x_3282_, 0);
lean_dec(v_unused_3312_);
v___x_3305_ = v___x_3282_;
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3282_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v_val_3307_; lean_object* v___x_3309_; 
v_val_3307_ = lean_ctor_get(v_fst_3284_, 0);
lean_inc(v_val_3307_);
lean_dec_ref_known(v_fst_3284_, 1);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v_val_3307_);
v___x_3309_ = v___x_3305_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_val_3307_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_a_3303_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
v_a_3313_ = lean_ctor_get(v___x_3282_, 0);
v_a_3314_ = lean_ctor_get(v___x_3282_, 1);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3282_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_inc(v_a_3313_);
lean_dec(v___x_3282_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3313_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3323_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_3322_, v_choiceStx_3261_, v_a_3263_);
lean_dec(v_choiceStx_3261_);
return v___x_3323_;
}
v___jp_3264_:
{
lean_object* v_fst_3266_; lean_object* v_snd_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
v_fst_3266_ = lean_ctor_get(v___y_3265_, 0);
v_snd_3267_ = lean_ctor_get(v___y_3265_, 1);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___y_3265_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___y_3265_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_snd_3267_);
lean_inc(v_fst_3266_);
lean_dec(v___y_3265_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3272_; 
if (v_isShared_3270_ == 0)
{
v___x_3272_ = v___x_3269_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_fst_3266_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_snd_3267_);
v___x_3272_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
return v___x_3272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object* v_choiceStx_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(v_choiceStx_3324_, v_a_3325_, v_a_3326_);
lean_dec_ref(v_a_3325_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3328_, lean_object* v_m_3329_, lean_object* v_a_3330_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_3329_, v_a_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3332_, lean_object* v_m_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(v_00_u03b2_3332_, v_m_3333_, v_a_3334_);
lean_dec_ref(v_a_3334_);
lean_dec_ref(v_m_3333_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3336_, lean_object* v_m_3337_, lean_object* v_a_3338_, lean_object* v_b_3339_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_m_3337_, v_a_3338_, v_b_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3341_, lean_object* v_a_3342_, lean_object* v_x_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_3342_, v_x_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3345_, lean_object* v_a_3346_, lean_object* v_x_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_3345_, v_a_3346_, v_x_3347_);
lean_dec(v_x_3347_);
lean_dec_ref(v_a_3346_);
return v_res_3348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_3349_, lean_object* v_a_3350_, lean_object* v_x_3351_){
_start:
{
uint8_t v___x_3352_; 
v___x_3352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_3350_, v_x_3351_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3353_, lean_object* v_a_3354_, lean_object* v_x_3355_){
_start:
{
uint8_t v_res_3356_; lean_object* v_r_3357_; 
v_res_3356_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(v_00_u03b2_3353_, v_a_3354_, v_x_3355_);
lean_dec(v_x_3355_);
lean_dec_ref(v_a_3354_);
v_r_3357_ = lean_box(v_res_3356_);
return v_r_3357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9(lean_object* v_00_u03b2_3358_, lean_object* v_data_3359_){
_start:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_data_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b2_3361_, lean_object* v_a_3362_, lean_object* v_b_3363_, lean_object* v_x_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_3362_, v_b_3363_, v_x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11(lean_object* v_00_u03b2_3366_, lean_object* v_i_3367_, lean_object* v_source_3368_, lean_object* v_target_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v_i_3367_, v_source_3368_, v_target_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12(lean_object* v_00_u03b2_3371_, lean_object* v_x_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_x_3372_, v_x_3373_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(size_t v_sz_3375_, size_t v_i_3376_, lean_object* v_bs_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_lt(v_i_3376_, v_sz_3375_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; 
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v_bs_3377_);
lean_ctor_set(v___x_3381_, 1, v___y_3379_);
return v___x_3381_;
}
else
{
lean_object* v_v_3382_; lean_object* v___x_3383_; 
v_v_3382_ = lean_array_uget_borrowed(v_bs_3377_, v_i_3376_);
lean_inc(v_v_3382_);
v___x_3383_ = l_Lean_Fmt_fmt(v_v_3382_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v_a_3385_; lean_object* v___x_3386_; lean_object* v_bs_x27_3387_; size_t v___x_3388_; size_t v___x_3389_; lean_object* v___x_3390_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
v_a_3385_ = lean_ctor_get(v___x_3383_, 1);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3383_, 2);
v___x_3386_ = lean_unsigned_to_nat(0u);
v_bs_x27_3387_ = lean_array_uset(v_bs_3377_, v_i_3376_, v___x_3386_);
v___x_3388_ = ((size_t)1ULL);
v___x_3389_ = lean_usize_add(v_i_3376_, v___x_3388_);
v___x_3390_ = lean_array_uset(v_bs_x27_3387_, v_i_3376_, v_a_3384_);
v_i_3376_ = v___x_3389_;
v_bs_3377_ = v___x_3390_;
v___y_3379_ = v_a_3385_;
goto _start;
}
else
{
lean_object* v_a_3392_; lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v_bs_3377_);
v_a_3392_ = lean_ctor_get(v___x_3383_, 0);
v_a_3393_ = lean_ctor_get(v___x_3383_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3383_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_inc(v_a_3392_);
lean_dec(v___x_3383_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3392_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1___boxed(lean_object* v_sz_3401_, lean_object* v_i_3402_, lean_object* v_bs_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
size_t v_sz_boxed_3406_; size_t v_i_boxed_3407_; lean_object* v_res_3408_; 
v_sz_boxed_3406_ = lean_unbox_usize(v_sz_3401_);
lean_dec(v_sz_3401_);
v_i_boxed_3407_ = lean_unbox_usize(v_i_3402_);
lean_dec(v_i_3402_);
v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_boxed_3406_, v_i_boxed_3407_, v_bs_3403_, v___y_3404_, v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3409_, lean_object* v_x_3410_){
_start:
{
if (lean_obj_tag(v_x_3410_) == 0)
{
return v_x_3409_;
}
else
{
lean_object* v_key_3411_; lean_object* v_value_3412_; lean_object* v_tail_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3439_; 
v_key_3411_ = lean_ctor_get(v_x_3410_, 0);
v_value_3412_ = lean_ctor_get(v_x_3410_, 1);
v_tail_3413_ = lean_ctor_get(v_x_3410_, 2);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_x_3410_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3415_ = v_x_3410_;
v_isShared_3416_ = v_isSharedCheck_3439_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_tail_3413_);
lean_inc(v_value_3412_);
lean_inc(v_key_3411_);
lean_dec(v_x_3410_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3439_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3417_; uint64_t v___y_3419_; 
v___x_3417_ = lean_array_get_size(v_x_3409_);
if (lean_obj_tag(v_key_3411_) == 0)
{
uint64_t v___x_3437_; 
v___x_3437_ = 1723ULL;
v___y_3419_ = v___x_3437_;
goto v___jp_3418_;
}
else
{
uint64_t v_hash_3438_; 
v_hash_3438_ = lean_ctor_get_uint64(v_key_3411_, sizeof(void*)*2);
v___y_3419_ = v_hash_3438_;
goto v___jp_3418_;
}
v___jp_3418_:
{
uint64_t v___x_3420_; uint64_t v___x_3421_; uint64_t v_fold_3422_; uint64_t v___x_3423_; uint64_t v___x_3424_; uint64_t v___x_3425_; size_t v___x_3426_; size_t v___x_3427_; size_t v___x_3428_; size_t v___x_3429_; size_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3420_ = 32ULL;
v___x_3421_ = lean_uint64_shift_right(v___y_3419_, v___x_3420_);
v_fold_3422_ = lean_uint64_xor(v___y_3419_, v___x_3421_);
v___x_3423_ = 16ULL;
v___x_3424_ = lean_uint64_shift_right(v_fold_3422_, v___x_3423_);
v___x_3425_ = lean_uint64_xor(v_fold_3422_, v___x_3424_);
v___x_3426_ = lean_uint64_to_usize(v___x_3425_);
v___x_3427_ = lean_usize_of_nat(v___x_3417_);
v___x_3428_ = ((size_t)1ULL);
v___x_3429_ = lean_usize_sub(v___x_3427_, v___x_3428_);
v___x_3430_ = lean_usize_land(v___x_3426_, v___x_3429_);
v___x_3431_ = lean_array_uget_borrowed(v_x_3409_, v___x_3430_);
lean_inc(v___x_3431_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 2, v___x_3431_);
v___x_3433_ = v___x_3415_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_key_3411_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_value_3412_);
lean_ctor_set(v_reuseFailAlloc_3436_, 2, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_array_uset(v_x_3409_, v___x_3430_, v___x_3433_);
v_x_3409_ = v___x_3434_;
v_x_3410_ = v_tail_3413_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(lean_object* v_i_3440_, lean_object* v_source_3441_, lean_object* v_target_3442_){
_start:
{
lean_object* v___x_3443_; uint8_t v___x_3444_; 
v___x_3443_ = lean_array_get_size(v_source_3441_);
v___x_3444_ = lean_nat_dec_lt(v_i_3440_, v___x_3443_);
if (v___x_3444_ == 0)
{
lean_dec_ref(v_source_3441_);
lean_dec(v_i_3440_);
return v_target_3442_;
}
else
{
lean_object* v_es_3445_; lean_object* v___x_3446_; lean_object* v_source_3447_; lean_object* v_target_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_es_3445_ = lean_array_fget(v_source_3441_, v_i_3440_);
v___x_3446_ = lean_box(0);
v_source_3447_ = lean_array_fset(v_source_3441_, v_i_3440_, v___x_3446_);
v_target_3448_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_target_3442_, v_es_3445_);
v___x_3449_ = lean_unsigned_to_nat(1u);
v___x_3450_ = lean_nat_add(v_i_3440_, v___x_3449_);
lean_dec(v_i_3440_);
v_i_3440_ = v___x_3450_;
v_source_3441_ = v_source_3447_;
v_target_3442_ = v_target_3448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(lean_object* v_data_3452_){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v_nbuckets_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3453_ = lean_array_get_size(v_data_3452_);
v___x_3454_ = lean_unsigned_to_nat(2u);
v_nbuckets_3455_ = lean_nat_mul(v___x_3453_, v___x_3454_);
v___x_3456_ = lean_unsigned_to_nat(0u);
v___x_3457_ = lean_box(0);
v___x_3458_ = lean_mk_array(v_nbuckets_3455_, v___x_3457_);
v___x_3459_ = lean_array_propagate_mark(v_data_3452_, v___x_3458_);
v___x_3460_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v___x_3456_, v_data_3452_, v___x_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(lean_object* v_m_3461_, lean_object* v_a_3462_, lean_object* v_b_3463_){
_start:
{
lean_object* v_size_3464_; lean_object* v_buckets_3465_; lean_object* v___x_3466_; uint64_t v___y_3468_; 
v_size_3464_ = lean_ctor_get(v_m_3461_, 0);
v_buckets_3465_ = lean_ctor_get(v_m_3461_, 1);
v___x_3466_ = lean_array_get_size(v_buckets_3465_);
if (lean_obj_tag(v_a_3462_) == 0)
{
uint64_t v___x_3505_; 
v___x_3505_ = 1723ULL;
v___y_3468_ = v___x_3505_;
goto v___jp_3467_;
}
else
{
uint64_t v_hash_3506_; 
v_hash_3506_ = lean_ctor_get_uint64(v_a_3462_, sizeof(void*)*2);
v___y_3468_ = v_hash_3506_;
goto v___jp_3467_;
}
v___jp_3467_:
{
uint64_t v___x_3469_; uint64_t v___x_3470_; uint64_t v_fold_3471_; uint64_t v___x_3472_; uint64_t v___x_3473_; uint64_t v___x_3474_; size_t v___x_3475_; size_t v___x_3476_; size_t v___x_3477_; size_t v___x_3478_; size_t v___x_3479_; lean_object* v_bkt_3480_; uint8_t v___x_3481_; 
v___x_3469_ = 32ULL;
v___x_3470_ = lean_uint64_shift_right(v___y_3468_, v___x_3469_);
v_fold_3471_ = lean_uint64_xor(v___y_3468_, v___x_3470_);
v___x_3472_ = 16ULL;
v___x_3473_ = lean_uint64_shift_right(v_fold_3471_, v___x_3472_);
v___x_3474_ = lean_uint64_xor(v_fold_3471_, v___x_3473_);
v___x_3475_ = lean_uint64_to_usize(v___x_3474_);
v___x_3476_ = lean_usize_of_nat(v___x_3466_);
v___x_3477_ = ((size_t)1ULL);
v___x_3478_ = lean_usize_sub(v___x_3476_, v___x_3477_);
v___x_3479_ = lean_usize_land(v___x_3475_, v___x_3478_);
v_bkt_3480_ = lean_array_uget_borrowed(v_buckets_3465_, v___x_3479_);
v___x_3481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_3462_, v_bkt_3480_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3502_; 
lean_inc_ref(v_buckets_3465_);
lean_inc(v_size_3464_);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_m_3461_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; lean_object* v_unused_3504_; 
v_unused_3503_ = lean_ctor_get(v_m_3461_, 1);
lean_dec(v_unused_3503_);
v_unused_3504_ = lean_ctor_get(v_m_3461_, 0);
lean_dec(v_unused_3504_);
v___x_3483_ = v_m_3461_;
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
else
{
lean_dec(v_m_3461_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3502_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v_size_x27_3486_; lean_object* v___x_3487_; lean_object* v_buckets_x27_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3485_ = lean_unsigned_to_nat(1u);
v_size_x27_3486_ = lean_nat_add(v_size_3464_, v___x_3485_);
lean_dec(v_size_3464_);
lean_inc(v_bkt_3480_);
v___x_3487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3462_);
lean_ctor_set(v___x_3487_, 1, v_b_3463_);
lean_ctor_set(v___x_3487_, 2, v_bkt_3480_);
v_buckets_x27_3488_ = lean_array_uset(v_buckets_3465_, v___x_3479_, v___x_3487_);
v___x_3489_ = lean_unsigned_to_nat(4u);
v___x_3490_ = lean_nat_mul(v_size_x27_3486_, v___x_3489_);
v___x_3491_ = lean_unsigned_to_nat(3u);
v___x_3492_ = lean_nat_div(v___x_3490_, v___x_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_array_get_size(v_buckets_x27_3488_);
v___x_3494_ = lean_nat_dec_le(v___x_3492_, v___x_3493_);
lean_dec(v___x_3492_);
if (v___x_3494_ == 0)
{
lean_object* v_val_3495_; lean_object* v___x_3497_; 
v_val_3495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_buckets_x27_3488_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 1, v_val_3495_);
lean_ctor_set(v___x_3483_, 0, v_size_x27_3486_);
v___x_3497_ = v___x_3483_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_size_x27_3486_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_val_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
else
{
lean_object* v___x_3500_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 1, v_buckets_x27_3488_);
lean_ctor_set(v___x_3483_, 0, v_size_x27_3486_);
v___x_3500_ = v___x_3483_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_size_x27_3486_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_buckets_x27_3488_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_dec(v_b_3463_);
lean_dec(v_a_3462_);
return v_m_3461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object* v_op_3507_, lean_object* v_stx_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
uint8_t v_sparse_3511_; uint8_t v_separateFinalOperand_3512_; lean_object* v_precs_x3f_3513_; lean_object* v_extendedChainKinds_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3555_; 
v_sparse_3511_ = lean_ctor_get_uint8(v_op_3507_, sizeof(void*)*2);
v_separateFinalOperand_3512_ = lean_ctor_get_uint8(v_op_3507_, sizeof(void*)*2 + 1);
v_precs_x3f_3513_ = lean_ctor_get(v_op_3507_, 0);
v_extendedChainKinds_3514_ = lean_ctor_get(v_op_3507_, 1);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_op_3507_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3516_ = v_op_3507_;
v_isShared_3517_ = v_isSharedCheck_3555_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_extendedChainKinds_3514_);
lean_inc(v_precs_x3f_3513_);
lean_dec(v_op_3507_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3555_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_env_3518_; lean_object* v_opts_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3524_; 
v_env_3518_ = lean_ctor_get(v_a_3509_, 0);
v_opts_3519_ = lean_ctor_get(v_a_3509_, 3);
lean_inc(v_stx_3508_);
v___x_3520_ = l_Lean_Syntax_getKind(v_stx_3508_);
v___x_3521_ = lean_box(0);
v___x_3522_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_extendedChainKinds_3514_, v___x_3520_, v___x_3521_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v___x_3522_);
v___x_3524_ = v___x_3516_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_precs_x3f_3513_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3522_);
lean_ctor_set_uint8(v_reuseFailAlloc_3554_, sizeof(void*)*2, v_sparse_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3554_, sizeof(void*)*2 + 1, v_separateFinalOperand_3512_);
v___x_3524_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3525_; size_t v_sz_3526_; size_t v___x_3527_; lean_object* v___x_3528_; 
lean_inc_ref(v_env_3518_);
v___x_3525_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_3518_, v_opts_3519_, v___x_3524_, v_stx_3508_);
lean_dec_ref(v___x_3524_);
v_sz_3526_ = lean_array_size(v___x_3525_);
v___x_3527_ = ((size_t)0ULL);
v___x_3528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_3526_, v___x_3527_, v___x_3525_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3544_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_a_3530_ = lean_ctor_get(v___x_3528_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3532_ = v___x_3528_;
v_isShared_3533_ = v_isSharedCheck_3544_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3544_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___y_3535_; uint8_t v___x_3540_; 
v___x_3540_ = 1;
if (v_sparse_3511_ == 0)
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3541_, 0, v___x_3540_);
lean_ctor_set_uint8(v___x_3541_, 1, v_sparse_3511_);
lean_ctor_set_uint8(v___x_3541_, 2, v___x_3540_);
lean_ctor_set_uint8(v___x_3541_, 3, v___x_3540_);
v___y_3535_ = v___x_3541_;
goto v___jp_3534_;
}
else
{
uint8_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = 0;
v___x_3543_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_3543_, 0, v___x_3540_);
lean_ctor_set_uint8(v___x_3543_, 1, v___x_3542_);
lean_ctor_set_uint8(v___x_3543_, 2, v___x_3540_);
lean_ctor_set_uint8(v___x_3543_, 3, v___x_3542_);
lean_ctor_set_uint8(v___x_3543_, 4, v_separateFinalOperand_3512_);
v___y_3535_ = v___x_3543_;
goto v___jp_3534_;
}
v___jp_3534_:
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3536_ = l_Lean_Fmt_Layouts_infixOperator(v_a_3529_, v___y_3535_);
lean_dec_ref(v___y_3535_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3536_);
v___x_3538_ = v___x_3532_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_a_3530_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
v_a_3545_ = lean_ctor_get(v___x_3528_, 0);
v_a_3546_ = lean_ctor_get(v___x_3528_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3528_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_inc(v_a_3545_);
lean_dec(v___x_3528_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3545_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3546_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object* v_op_3556_, lean_object* v_stx_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Fmt_fmtInfixOperator(v_op_3556_, v_stx_3557_, v_a_3558_, v_a_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0(lean_object* v_00_u03b2_3561_, lean_object* v_m_3562_, lean_object* v_a_3563_, lean_object* v_b_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_m_3562_, v_a_3563_, v_b_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0(lean_object* v_00_u03b2_3566_, lean_object* v_data_3567_){
_start:
{
lean_object* v___x_3568_; 
v___x_3568_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_data_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3569_, lean_object* v_i_3570_, lean_object* v_source_3571_, lean_object* v_target_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v_i_3570_, v_source_3571_, v_target_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3575_, v_x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
if (lean_obj_tag(v_x_3578_) == 0)
{
if (lean_obj_tag(v_x_3579_) == 0)
{
uint8_t v___x_3580_; 
v___x_3580_ = 1;
return v___x_3580_;
}
else
{
uint8_t v___x_3581_; 
v___x_3581_ = 0;
return v___x_3581_;
}
}
else
{
if (lean_obj_tag(v_x_3579_) == 0)
{
uint8_t v___x_3582_; 
v___x_3582_ = 0;
return v___x_3582_;
}
else
{
lean_object* v_val_3583_; lean_object* v_val_3584_; uint8_t v___x_3585_; 
v_val_3583_ = lean_ctor_get(v_x_3578_, 0);
v_val_3584_ = lean_ctor_get(v_x_3579_, 0);
v___x_3585_ = lean_string_dec_eq(v_val_3583_, v_val_3584_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0___boxed(lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
uint8_t v_res_3588_; lean_object* v_r_3589_; 
v_res_3588_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v_x_3586_, v_x_3587_);
lean_dec(v_x_3587_);
lean_dec(v_x_3586_);
v_r_3589_ = lean_box(v_res_3588_);
return v_r_3589_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(lean_object* v_msg_3590_){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = l_String_instInhabitedSlice;
v___x_3592_ = lean_panic_fn_borrowed(v___x_3591_, v_msg_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(lean_object* v_s_3593_, lean_object* v_a_3594_, uint8_t v_b_3595_){
_start:
{
lean_object* v_str_3596_; lean_object* v_startInclusive_3597_; lean_object* v_endExclusive_3598_; lean_object* v___x_3599_; uint8_t v_decide_3600_; 
v_str_3596_ = lean_ctor_get(v_s_3593_, 0);
v_startInclusive_3597_ = lean_ctor_get(v_s_3593_, 1);
v_endExclusive_3598_ = lean_ctor_get(v_s_3593_, 2);
v___x_3599_ = lean_nat_sub(v_endExclusive_3598_, v_startInclusive_3597_);
v_decide_3600_ = lean_nat_dec_eq(v_a_3594_, v___x_3599_);
lean_dec(v___x_3599_);
if (v_decide_3600_ == 0)
{
lean_object* v___x_3601_; uint32_t v___x_3602_; uint32_t v___x_3603_; uint8_t v___x_3604_; 
v___x_3601_ = lean_nat_add(v_startInclusive_3597_, v_a_3594_);
lean_dec(v_a_3594_);
v___x_3602_ = lean_string_utf8_get_fast(v_str_3596_, v___x_3601_);
v___x_3603_ = l_Lean_idEndEscape;
v___x_3604_ = lean_uint32_dec_eq(v___x_3602_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = lean_string_utf8_next_fast(v_str_3596_, v___x_3601_);
lean_dec(v___x_3601_);
v___x_3606_ = lean_nat_sub(v___x_3605_, v_startInclusive_3597_);
v_a_3594_ = v___x_3606_;
v_b_3595_ = v___x_3604_;
goto _start;
}
else
{
lean_dec(v___x_3601_);
return v___x_3604_;
}
}
else
{
lean_dec(v_a_3594_);
return v_b_3595_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg___boxed(lean_object* v_s_3608_, lean_object* v_a_3609_, lean_object* v_b_3610_){
_start:
{
uint8_t v_b_boxed_3611_; uint8_t v_res_3612_; lean_object* v_r_3613_; 
v_b_boxed_3611_ = lean_unbox(v_b_3610_);
v_res_3612_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3608_, v_a_3609_, v_b_boxed_3611_);
lean_dec_ref(v_s_3608_);
v_r_3613_ = lean_box(v_res_3612_);
return v_r_3613_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(lean_object* v_s_3614_){
_start:
{
lean_object* v_searcher_3615_; uint8_t v___x_3616_; uint8_t v___x_3617_; 
v_searcher_3615_ = lean_unsigned_to_nat(0u);
v___x_3616_ = 0;
v___x_3617_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3614_, v_searcher_3615_, v___x_3616_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1___boxed(lean_object* v_s_3618_){
_start:
{
uint8_t v_res_3619_; lean_object* v_r_3620_; 
v_res_3619_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v_s_3618_);
lean_dec_ref(v_s_3618_);
v_r_3620_ = lean_box(v_res_3619_);
return v_r_3620_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(lean_object* v_s_3621_, lean_object* v_pos_3622_){
_start:
{
lean_object* v_str_3623_; lean_object* v_startInclusive_3624_; lean_object* v_endExclusive_3625_; lean_object* v___x_3626_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v_decide_3637_; 
v_str_3623_ = lean_ctor_get(v_s_3621_, 0);
v_startInclusive_3624_ = lean_ctor_get(v_s_3621_, 1);
v_endExclusive_3625_ = lean_ctor_get(v_s_3621_, 2);
v___x_3626_ = lean_nat_add(v_startInclusive_3624_, v_pos_3622_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_nat_sub(v_endExclusive_3625_, v___x_3626_);
v_decide_3637_ = lean_nat_dec_eq(v___x_3635_, v___x_3636_);
lean_dec(v___x_3636_);
if (v_decide_3637_ == 0)
{
uint32_t v___x_3638_; uint32_t v___x_3660_; uint8_t v___x_3661_; 
v___x_3638_ = lean_string_utf8_get_fast(v_str_3623_, v___x_3626_);
v___x_3660_ = 65;
v___x_3661_ = lean_uint32_dec_le(v___x_3660_, v___x_3638_);
if (v___x_3661_ == 0)
{
goto v___jp_3655_;
}
else
{
uint32_t v___x_3662_; uint8_t v___x_3663_; 
v___x_3662_ = 90;
v___x_3663_ = lean_uint32_dec_le(v___x_3638_, v___x_3662_);
if (v___x_3663_ == 0)
{
goto v___jp_3655_;
}
else
{
goto v___jp_3627_;
}
}
v___jp_3639_:
{
uint32_t v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = 95;
v___x_3641_ = lean_uint32_dec_eq(v___x_3638_, v___x_3640_);
if (v___x_3641_ == 0)
{
uint32_t v___x_3642_; uint8_t v___x_3643_; 
v___x_3642_ = 39;
v___x_3643_ = lean_uint32_dec_eq(v___x_3638_, v___x_3642_);
if (v___x_3643_ == 0)
{
uint32_t v___x_3644_; uint8_t v___x_3645_; 
v___x_3644_ = 33;
v___x_3645_ = lean_uint32_dec_eq(v___x_3638_, v___x_3644_);
if (v___x_3645_ == 0)
{
uint32_t v___x_3646_; uint8_t v___x_3647_; 
v___x_3646_ = 63;
v___x_3647_ = lean_uint32_dec_eq(v___x_3638_, v___x_3646_);
if (v___x_3647_ == 0)
{
uint8_t v___x_3648_; 
v___x_3648_ = l_Lean_isLetterLike(v___x_3638_);
if (v___x_3648_ == 0)
{
uint8_t v___x_3649_; 
v___x_3649_ = l_Lean_isSubScriptAlnum(v___x_3638_);
if (v___x_3649_ == 0)
{
lean_dec(v___x_3626_);
return v_pos_3622_;
}
else
{
goto v___jp_3627_;
}
}
else
{
goto v___jp_3627_;
}
}
else
{
goto v___jp_3627_;
}
}
else
{
goto v___jp_3627_;
}
}
else
{
goto v___jp_3627_;
}
}
else
{
goto v___jp_3627_;
}
}
v___jp_3650_:
{
uint32_t v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = 48;
v___x_3652_ = lean_uint32_dec_le(v___x_3651_, v___x_3638_);
if (v___x_3652_ == 0)
{
goto v___jp_3639_;
}
else
{
uint32_t v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = 57;
v___x_3654_ = lean_uint32_dec_le(v___x_3638_, v___x_3653_);
if (v___x_3654_ == 0)
{
goto v___jp_3639_;
}
else
{
goto v___jp_3627_;
}
}
}
v___jp_3655_:
{
uint32_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3656_ = 97;
v___x_3657_ = lean_uint32_dec_le(v___x_3656_, v___x_3638_);
if (v___x_3657_ == 0)
{
goto v___jp_3650_;
}
else
{
uint32_t v___x_3658_; uint8_t v___x_3659_; 
v___x_3658_ = 122;
v___x_3659_ = lean_uint32_dec_le(v___x_3638_, v___x_3658_);
if (v___x_3659_ == 0)
{
goto v___jp_3650_;
}
else
{
goto v___jp_3627_;
}
}
}
}
else
{
lean_dec(v___x_3626_);
return v_pos_3622_;
}
v___jp_3627_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3628_ = lean_string_utf8_next_fast(v_str_3623_, v___x_3626_);
v___x_3629_ = lean_nat_sub(v___x_3628_, v___x_3626_);
lean_dec(v___x_3626_);
v___x_3630_ = lean_nat_add(v_pos_3622_, v___x_3629_);
lean_dec(v___x_3629_);
v___x_3631_ = lean_unsigned_to_nat(1u);
v___x_3632_ = lean_nat_add(v_pos_3622_, v___x_3631_);
v___x_3633_ = lean_nat_dec_le(v___x_3632_, v___x_3630_);
lean_dec(v___x_3632_);
if (v___x_3633_ == 0)
{
lean_dec(v___x_3630_);
return v_pos_3622_;
}
else
{
lean_dec(v_pos_3622_);
v_pos_3622_ = v___x_3630_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2___boxed(lean_object* v_s_3664_, lean_object* v_pos_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v_s_3664_, v_pos_3665_);
lean_dec_ref(v_s_3664_);
return v_res_3666_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__0(void){
_start:
{
uint32_t v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = l_Lean_idBeginEscape;
v___x_3668_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3669_ = lean_string_push(v___x_3668_, v___x_3667_);
return v___x_3669_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__1(void){
_start:
{
uint32_t v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3670_ = l_Lean_idEndEscape;
v___x_3671_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3672_ = lean_string_push(v___x_3671_, v___x_3670_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object* v_stx_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; uint8_t v___y_3680_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v___x_3683_ = l_Lean_Syntax_getNumArgs(v_stx_3673_);
v___x_3684_ = lean_unsigned_to_nat(2u);
v___x_3685_ = lean_nat_dec_eq(v___x_3683_, v___x_3684_);
lean_dec(v___x_3683_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
lean_ctor_set(v___x_3687_, 1, v_a_3675_);
return v___x_3687_;
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_unsigned_to_nat(0u);
v___x_3689_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3673_, v___x_3688_, v_a_3675_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; lean_object* v_a_3691_; lean_object* v___x_3692_; lean_object* v___y_3694_; lean_object* v___y_3729_; lean_object* v_startInclusive_3730_; lean_object* v_endExclusive_3731_; uint32_t v___y_3751_; uint32_t v___y_3756_; uint32_t v___y_3762_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
v_a_3691_ = lean_ctor_get(v___x_3689_, 1);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3689_, 2);
v___x_3692_ = l_Lean_Syntax_getAtomVal(v_a_3690_);
v___x_3778_ = lean_string_utf8_byte_size(v___x_3692_);
v___x_3779_ = lean_nat_dec_lt(v___x_3688_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3780_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3781_ = lean_string_append(v___x_3780_, v___x_3692_);
v___x_3782_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3783_ = lean_string_append(v___x_3781_, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
v___y_3694_ = v___x_3784_;
goto v___jp_3693_;
}
else
{
uint8_t v_c_3785_; uint8_t v___x_3794_; uint8_t v___x_3795_; 
v_c_3785_ = lean_string_get_byte_fast(v___x_3692_, v___x_3688_);
v___x_3794_ = 97;
v___x_3795_ = lean_uint8_dec_le(v___x_3794_, v_c_3785_);
if (v___x_3795_ == 0)
{
goto v___jp_3789_;
}
else
{
uint8_t v___x_3796_; uint8_t v___x_3797_; 
v___x_3796_ = 122;
v___x_3797_ = lean_uint8_dec_le(v_c_3785_, v___x_3796_);
if (v___x_3797_ == 0)
{
goto v___jp_3789_;
}
else
{
goto v___jp_3774_;
}
}
v___jp_3786_:
{
uint8_t v___x_3787_; uint8_t v___x_3788_; 
v___x_3787_ = 95;
v___x_3788_ = lean_uint8_dec_eq(v_c_3785_, v___x_3787_);
if (v___x_3788_ == 0)
{
goto v___jp_3767_;
}
else
{
goto v___jp_3774_;
}
}
v___jp_3789_:
{
uint8_t v___x_3790_; uint8_t v___x_3791_; 
v___x_3790_ = 65;
v___x_3791_ = lean_uint8_dec_le(v___x_3790_, v_c_3785_);
if (v___x_3791_ == 0)
{
goto v___jp_3786_;
}
else
{
uint8_t v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = 90;
v___x_3793_ = lean_uint8_dec_le(v_c_3785_, v___x_3792_);
if (v___x_3793_ == 0)
{
goto v___jp_3786_;
}
else
{
goto v___jp_3774_;
}
}
}
}
v___jp_3693_:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Fmt_fmt(v_a_3690_, v_a_3674_, v_a_3691_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v_a_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
v_a_3697_ = lean_ctor_get(v___x_3695_, 1);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3695_, 2);
v___x_3698_ = lean_unsigned_to_nat(1u);
v___x_3699_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3673_, v___x_3698_, v_a_3697_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v_a_3701_; lean_object* v___x_3702_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
v_a_3701_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3699_, 2);
v___x_3702_ = l_Lean_Fmt_fmt(v_a_3700_, v_a_3674_, v_a_3701_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v_a_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
v_a_3704_ = lean_ctor_get(v___x_3702_, 1);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3702_, 2);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3692_);
v___x_3706_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3694_, v___x_3705_);
lean_dec_ref_known(v___x_3705_, 1);
lean_dec(v___y_3694_);
if (v___x_3706_ == 0)
{
uint8_t v___x_3707_; 
v___x_3707_ = 1;
v___y_3677_ = v_a_3704_;
v___y_3678_ = v_a_3696_;
v___y_3679_ = v_a_3703_;
v___y_3680_ = v___x_3707_;
goto v___jp_3676_;
}
else
{
uint8_t v___x_3708_; 
v___x_3708_ = 2;
v___y_3677_ = v_a_3704_;
v___y_3678_ = v_a_3696_;
v___y_3679_ = v_a_3703_;
v___y_3680_ = v___x_3708_;
goto v___jp_3676_;
}
}
else
{
lean_dec(v_a_3696_);
lean_dec(v___y_3694_);
lean_dec_ref(v___x_3692_);
return v___x_3702_;
}
}
else
{
lean_object* v_a_3709_; lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec(v_a_3696_);
lean_dec(v___y_3694_);
lean_dec_ref(v___x_3692_);
v_a_3709_ = lean_ctor_get(v___x_3699_, 0);
v_a_3710_ = lean_ctor_get(v___x_3699_, 1);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3699_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_inc(v_a_3709_);
lean_dec(v___x_3699_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3709_);
lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_a_3710_);
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
else
{
lean_dec(v___y_3694_);
lean_dec_ref(v___x_3692_);
return v___x_3695_;
}
}
v___jp_3718_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v___x_3719_ = lean_string_utf8_byte_size(v___x_3692_);
lean_inc_ref(v___x_3692_);
v___x_3720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3692_);
lean_ctor_set(v___x_3720_, 1, v___x_3688_);
lean_ctor_set(v___x_3720_, 2, v___x_3719_);
v___x_3721_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3720_);
lean_dec_ref_known(v___x_3720_, 3);
if (v___x_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3722_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3723_ = lean_string_append(v___x_3722_, v___x_3692_);
v___x_3724_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3725_ = lean_string_append(v___x_3723_, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
v___y_3694_ = v___x_3726_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_box(0);
v___y_3694_ = v___x_3727_;
goto v___jp_3693_;
}
}
v___jp_3728_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v_decide_3734_; 
v___x_3732_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3729_, v___x_3688_);
lean_dec_ref(v___y_3729_);
v___x_3733_ = lean_nat_sub(v_endExclusive_3731_, v_startInclusive_3730_);
lean_dec(v_startInclusive_3730_);
lean_dec(v_endExclusive_3731_);
v_decide_3734_ = lean_nat_dec_eq(v___x_3732_, v___x_3733_);
lean_dec(v___x_3733_);
lean_dec(v___x_3732_);
if (v_decide_3734_ == 0)
{
goto v___jp_3718_;
}
else
{
lean_object* v___x_3735_; 
lean_inc_ref(v___x_3692_);
v___x_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3692_);
v___y_3694_ = v___x_3735_;
goto v___jp_3693_;
}
}
v___jp_3736_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v_startInclusive_3739_; lean_object* v_endExclusive_3740_; 
v___x_3737_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3738_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3737_);
v_startInclusive_3739_ = lean_ctor_get(v___x_3738_, 1);
lean_inc(v_startInclusive_3739_);
v_endExclusive_3740_ = lean_ctor_get(v___x_3738_, 2);
lean_inc(v_endExclusive_3740_);
v___y_3729_ = v___x_3738_;
v_startInclusive_3730_ = v_startInclusive_3739_;
v_endExclusive_3731_ = v_endExclusive_3740_;
goto v___jp_3728_;
}
v___jp_3741_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v___x_3742_ = lean_string_utf8_byte_size(v___x_3692_);
lean_inc_ref(v___x_3692_);
v___x_3743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3692_);
lean_ctor_set(v___x_3743_, 1, v___x_3688_);
lean_ctor_set(v___x_3743_, 2, v___x_3742_);
v___x_3744_ = lean_unsigned_to_nat(1u);
v___x_3745_ = l_Substring_Raw_nextn(v___x_3743_, v___x_3744_, v___x_3688_);
lean_dec_ref_known(v___x_3743_, 3);
v___x_3746_ = lean_string_is_valid_pos(v___x_3692_, v___x_3745_);
if (v___x_3746_ == 0)
{
lean_dec(v___x_3745_);
goto v___jp_3736_;
}
else
{
uint8_t v___x_3747_; 
v___x_3747_ = lean_string_is_valid_pos(v___x_3692_, v___x_3742_);
if (v___x_3747_ == 0)
{
lean_dec(v___x_3745_);
goto v___jp_3736_;
}
else
{
uint8_t v___x_3748_; 
v___x_3748_ = lean_nat_dec_le(v___x_3745_, v___x_3742_);
if (v___x_3748_ == 0)
{
lean_dec(v___x_3745_);
goto v___jp_3736_;
}
else
{
lean_object* v___x_3749_; 
lean_inc(v___x_3745_);
lean_inc_ref(v___x_3692_);
v___x_3749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3692_);
lean_ctor_set(v___x_3749_, 1, v___x_3745_);
lean_ctor_set(v___x_3749_, 2, v___x_3742_);
v___y_3729_ = v___x_3749_;
v_startInclusive_3730_ = v___x_3745_;
v_endExclusive_3731_ = v___x_3742_;
goto v___jp_3728_;
}
}
}
}
v___jp_3750_:
{
uint32_t v___x_3752_; uint8_t v___x_3753_; 
v___x_3752_ = 95;
v___x_3753_ = lean_uint32_dec_eq(v___y_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
uint8_t v___x_3754_; 
v___x_3754_ = l_Lean_isLetterLike(v___y_3751_);
if (v___x_3754_ == 0)
{
goto v___jp_3718_;
}
else
{
goto v___jp_3741_;
}
}
else
{
goto v___jp_3741_;
}
}
v___jp_3755_:
{
uint32_t v___x_3757_; uint8_t v___x_3758_; 
v___x_3757_ = 97;
v___x_3758_ = lean_uint32_dec_le(v___x_3757_, v___y_3756_);
if (v___x_3758_ == 0)
{
v___y_3751_ = v___y_3756_;
goto v___jp_3750_;
}
else
{
uint32_t v___x_3759_; uint8_t v___x_3760_; 
v___x_3759_ = 122;
v___x_3760_ = lean_uint32_dec_le(v___y_3756_, v___x_3759_);
if (v___x_3760_ == 0)
{
v___y_3751_ = v___y_3756_;
goto v___jp_3750_;
}
else
{
goto v___jp_3741_;
}
}
}
v___jp_3761_:
{
uint32_t v___x_3763_; uint8_t v___x_3764_; 
v___x_3763_ = 65;
v___x_3764_ = lean_uint32_dec_le(v___x_3763_, v___y_3762_);
if (v___x_3764_ == 0)
{
v___y_3756_ = v___y_3762_;
goto v___jp_3755_;
}
else
{
uint32_t v___x_3765_; uint8_t v___x_3766_; 
v___x_3765_ = 90;
v___x_3766_ = lean_uint32_dec_le(v___y_3762_, v___x_3765_);
if (v___x_3766_ == 0)
{
v___y_3756_ = v___y_3762_;
goto v___jp_3755_;
}
else
{
goto v___jp_3741_;
}
}
}
v___jp_3767_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_string_utf8_byte_size(v___x_3692_);
lean_inc_ref(v___x_3692_);
v___x_3769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3692_);
lean_ctor_set(v___x_3769_, 1, v___x_3688_);
lean_ctor_set(v___x_3769_, 2, v___x_3768_);
v___x_3770_ = l_String_Slice_Pos_get_x3f(v___x_3769_, v___x_3688_);
lean_dec_ref_known(v___x_3769_, 3);
if (lean_obj_tag(v___x_3770_) == 0)
{
uint32_t v___x_3771_; 
v___x_3771_ = 65;
v___y_3762_ = v___x_3771_;
goto v___jp_3761_;
}
else
{
lean_object* v_val_3772_; uint32_t v___x_3773_; 
v_val_3772_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3773_ = lean_unbox_uint32(v_val_3772_);
lean_dec(v_val_3772_);
v___y_3762_ = v___x_3773_;
goto v___jp_3761_;
}
}
v___jp_3774_:
{
lean_object* v___x_3775_; uint8_t v___x_3776_; 
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3692_, v___x_3775_);
if (v___x_3776_ == 0)
{
goto v___jp_3767_;
}
else
{
lean_object* v___x_3777_; 
lean_inc_ref(v___x_3692_);
v___x_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3692_);
v___y_3694_ = v___x_3777_;
goto v___jp_3693_;
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
v_a_3798_ = lean_ctor_get(v___x_3689_, 0);
v_a_3799_ = lean_ctor_get(v___x_3689_, 1);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3689_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_inc(v_a_3798_);
lean_dec(v___x_3689_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3798_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
v___jp_3676_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_3678_, v___y_3679_, v___y_3680_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v___y_3677_);
return v___x_3682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object* v_stx_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_Lean_Fmt_fmtPrefixOperator(v_stx_3807_, v_a_3808_, v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_stx_3807_);
return v_res_3810_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(lean_object* v_s_3811_, lean_object* v_inst_3812_, lean_object* v_R_3813_, lean_object* v_a_3814_, uint8_t v_b_3815_, lean_object* v_c_3816_){
_start:
{
uint8_t v___x_3817_; 
v___x_3817_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3811_, v_a_3814_, v_b_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___boxed(lean_object* v_s_3818_, lean_object* v_inst_3819_, lean_object* v_R_3820_, lean_object* v_a_3821_, lean_object* v_b_3822_, lean_object* v_c_3823_){
_start:
{
uint8_t v_b_boxed_3824_; uint8_t v_res_3825_; lean_object* v_r_3826_; 
v_b_boxed_3824_ = lean_unbox(v_b_3822_);
v_res_3825_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(v_s_3818_, v_inst_3819_, v_R_3820_, v_a_3821_, v_b_boxed_3824_, v_c_3823_);
lean_dec_ref(v_s_3818_);
v_r_3826_ = lean_box(v_res_3825_);
return v_r_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object* v_stx_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3830_ = l_Lean_Syntax_getNumArgs(v_stx_3827_);
v___x_3831_ = lean_unsigned_to_nat(2u);
v___x_3832_ = lean_nat_dec_eq(v___x_3830_, v___x_3831_);
lean_dec(v___x_3830_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set(v___x_3834_, 1, v_a_3829_);
return v___x_3834_;
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = lean_unsigned_to_nat(0u);
v___x_3836_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3827_, v___x_3835_, v_a_3829_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v_a_3838_; lean_object* v___x_3839_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
v_a_3838_ = lean_ctor_get(v___x_3836_, 1);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3836_, 2);
v___x_3839_ = l_Lean_Fmt_fmt(v_a_3837_, v_a_3828_, v_a_3838_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3954_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_a_3841_ = lean_ctor_get(v___x_3839_, 1);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3843_ = v___x_3839_;
v_isShared_3844_ = v_isSharedCheck_3954_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3954_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___y_3846_; lean_object* v___y_3847_; uint8_t v___y_3848_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_unsigned_to_nat(1u);
v___x_3854_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3827_, v___x_3853_, v_a_3841_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v_a_3856_; lean_object* v___x_3857_; lean_object* v___y_3859_; lean_object* v___y_3878_; lean_object* v_startInclusive_3879_; lean_object* v_endExclusive_3880_; uint32_t v___y_3899_; uint32_t v___y_3904_; uint32_t v___y_3910_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
v_a_3856_ = lean_ctor_get(v___x_3854_, 1);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3854_, 2);
v___x_3857_ = l_Lean_Syntax_getAtomVal(v_a_3855_);
v___x_3925_ = lean_string_utf8_byte_size(v___x_3857_);
v___x_3926_ = lean_nat_dec_lt(v___x_3835_, v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3927_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3928_ = lean_string_append(v___x_3927_, v___x_3857_);
v___x_3929_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3930_ = lean_string_append(v___x_3928_, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
v___y_3859_ = v___x_3931_;
goto v___jp_3858_;
}
else
{
uint8_t v_c_3932_; uint8_t v___x_3941_; uint8_t v___x_3942_; 
v_c_3932_ = lean_string_get_byte_fast(v___x_3857_, v___x_3835_);
v___x_3941_ = 97;
v___x_3942_ = lean_uint8_dec_le(v___x_3941_, v_c_3932_);
if (v___x_3942_ == 0)
{
goto v___jp_3936_;
}
else
{
uint8_t v___x_3943_; uint8_t v___x_3944_; 
v___x_3943_ = 122;
v___x_3944_ = lean_uint8_dec_le(v_c_3932_, v___x_3943_);
if (v___x_3944_ == 0)
{
goto v___jp_3936_;
}
else
{
goto v___jp_3922_;
}
}
v___jp_3933_:
{
uint8_t v___x_3934_; uint8_t v___x_3935_; 
v___x_3934_ = 95;
v___x_3935_ = lean_uint8_dec_eq(v_c_3932_, v___x_3934_);
if (v___x_3935_ == 0)
{
goto v___jp_3915_;
}
else
{
goto v___jp_3922_;
}
}
v___jp_3936_:
{
uint8_t v___x_3937_; uint8_t v___x_3938_; 
v___x_3937_ = 65;
v___x_3938_ = lean_uint8_dec_le(v___x_3937_, v_c_3932_);
if (v___x_3938_ == 0)
{
goto v___jp_3933_;
}
else
{
uint8_t v___x_3939_; uint8_t v___x_3940_; 
v___x_3939_ = 90;
v___x_3940_ = lean_uint8_dec_le(v_c_3932_, v___x_3939_);
if (v___x_3940_ == 0)
{
goto v___jp_3933_;
}
else
{
goto v___jp_3922_;
}
}
}
}
v___jp_3858_:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_Fmt_fmt(v_a_3855_, v_a_3828_, v_a_3856_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v_a_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
v_a_3862_ = lean_ctor_get(v___x_3860_, 1);
lean_inc(v_a_3862_);
lean_dec_ref_known(v___x_3860_, 2);
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3857_);
v___x_3864_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3859_, v___x_3863_);
lean_dec_ref_known(v___x_3863_, 1);
lean_dec(v___y_3859_);
if (v___x_3864_ == 0)
{
uint8_t v___x_3865_; 
v___x_3865_ = 0;
v___y_3846_ = v_a_3861_;
v___y_3847_ = v_a_3862_;
v___y_3848_ = v___x_3865_;
goto v___jp_3845_;
}
else
{
uint8_t v___x_3866_; 
v___x_3866_ = 1;
v___y_3846_ = v_a_3861_;
v___y_3847_ = v_a_3862_;
v___y_3848_ = v___x_3866_;
goto v___jp_3845_;
}
}
else
{
lean_dec(v___y_3859_);
lean_dec_ref(v___x_3857_);
lean_del_object(v___x_3843_);
lean_dec(v_a_3840_);
return v___x_3860_;
}
}
v___jp_3867_:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3868_ = lean_string_utf8_byte_size(v___x_3857_);
lean_inc_ref(v___x_3857_);
v___x_3869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3857_);
lean_ctor_set(v___x_3869_, 1, v___x_3835_);
lean_ctor_set(v___x_3869_, 2, v___x_3868_);
v___x_3870_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3869_);
lean_dec_ref_known(v___x_3869_, 3);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3871_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3872_ = lean_string_append(v___x_3871_, v___x_3857_);
v___x_3873_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3874_ = lean_string_append(v___x_3872_, v___x_3873_);
v___x_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
v___y_3859_ = v___x_3875_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3876_; 
v___x_3876_ = lean_box(0);
v___y_3859_ = v___x_3876_;
goto v___jp_3858_;
}
}
v___jp_3877_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v_decide_3883_; 
v___x_3881_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3878_, v___x_3835_);
lean_dec_ref(v___y_3878_);
v___x_3882_ = lean_nat_sub(v_endExclusive_3880_, v_startInclusive_3879_);
lean_dec(v_startInclusive_3879_);
lean_dec(v_endExclusive_3880_);
v_decide_3883_ = lean_nat_dec_eq(v___x_3881_, v___x_3882_);
lean_dec(v___x_3882_);
lean_dec(v___x_3881_);
if (v_decide_3883_ == 0)
{
goto v___jp_3867_;
}
else
{
lean_object* v___x_3884_; 
lean_inc_ref(v___x_3857_);
v___x_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3857_);
v___y_3859_ = v___x_3884_;
goto v___jp_3858_;
}
}
v___jp_3885_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v_startInclusive_3888_; lean_object* v_endExclusive_3889_; 
v___x_3886_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3887_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3886_);
v_startInclusive_3888_ = lean_ctor_get(v___x_3887_, 1);
lean_inc(v_startInclusive_3888_);
v_endExclusive_3889_ = lean_ctor_get(v___x_3887_, 2);
lean_inc(v_endExclusive_3889_);
v___y_3878_ = v___x_3887_;
v_startInclusive_3879_ = v_startInclusive_3888_;
v_endExclusive_3880_ = v_endExclusive_3889_;
goto v___jp_3877_;
}
v___jp_3890_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3891_ = lean_string_utf8_byte_size(v___x_3857_);
lean_inc_ref(v___x_3857_);
v___x_3892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3857_);
lean_ctor_set(v___x_3892_, 1, v___x_3835_);
lean_ctor_set(v___x_3892_, 2, v___x_3891_);
v___x_3893_ = l_Substring_Raw_nextn(v___x_3892_, v___x_3853_, v___x_3835_);
lean_dec_ref_known(v___x_3892_, 3);
v___x_3894_ = lean_string_is_valid_pos(v___x_3857_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_dec(v___x_3893_);
goto v___jp_3885_;
}
else
{
uint8_t v___x_3895_; 
v___x_3895_ = lean_string_is_valid_pos(v___x_3857_, v___x_3891_);
if (v___x_3895_ == 0)
{
lean_dec(v___x_3893_);
goto v___jp_3885_;
}
else
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_nat_dec_le(v___x_3893_, v___x_3891_);
if (v___x_3896_ == 0)
{
lean_dec(v___x_3893_);
goto v___jp_3885_;
}
else
{
lean_object* v___x_3897_; 
lean_inc(v___x_3893_);
lean_inc_ref(v___x_3857_);
v___x_3897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3857_);
lean_ctor_set(v___x_3897_, 1, v___x_3893_);
lean_ctor_set(v___x_3897_, 2, v___x_3891_);
v___y_3878_ = v___x_3897_;
v_startInclusive_3879_ = v___x_3893_;
v_endExclusive_3880_ = v___x_3891_;
goto v___jp_3877_;
}
}
}
}
v___jp_3898_:
{
uint32_t v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = 95;
v___x_3901_ = lean_uint32_dec_eq(v___y_3899_, v___x_3900_);
if (v___x_3901_ == 0)
{
uint8_t v___x_3902_; 
v___x_3902_ = l_Lean_isLetterLike(v___y_3899_);
if (v___x_3902_ == 0)
{
goto v___jp_3867_;
}
else
{
goto v___jp_3890_;
}
}
else
{
goto v___jp_3890_;
}
}
v___jp_3903_:
{
uint32_t v___x_3905_; uint8_t v___x_3906_; 
v___x_3905_ = 97;
v___x_3906_ = lean_uint32_dec_le(v___x_3905_, v___y_3904_);
if (v___x_3906_ == 0)
{
v___y_3899_ = v___y_3904_;
goto v___jp_3898_;
}
else
{
uint32_t v___x_3907_; uint8_t v___x_3908_; 
v___x_3907_ = 122;
v___x_3908_ = lean_uint32_dec_le(v___y_3904_, v___x_3907_);
if (v___x_3908_ == 0)
{
v___y_3899_ = v___y_3904_;
goto v___jp_3898_;
}
else
{
goto v___jp_3890_;
}
}
}
v___jp_3909_:
{
uint32_t v___x_3911_; uint8_t v___x_3912_; 
v___x_3911_ = 65;
v___x_3912_ = lean_uint32_dec_le(v___x_3911_, v___y_3910_);
if (v___x_3912_ == 0)
{
v___y_3904_ = v___y_3910_;
goto v___jp_3903_;
}
else
{
uint32_t v___x_3913_; uint8_t v___x_3914_; 
v___x_3913_ = 90;
v___x_3914_ = lean_uint32_dec_le(v___y_3910_, v___x_3913_);
if (v___x_3914_ == 0)
{
v___y_3904_ = v___y_3910_;
goto v___jp_3903_;
}
else
{
goto v___jp_3890_;
}
}
}
v___jp_3915_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_string_utf8_byte_size(v___x_3857_);
lean_inc_ref(v___x_3857_);
v___x_3917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3857_);
lean_ctor_set(v___x_3917_, 1, v___x_3835_);
lean_ctor_set(v___x_3917_, 2, v___x_3916_);
v___x_3918_ = l_String_Slice_Pos_get_x3f(v___x_3917_, v___x_3835_);
lean_dec_ref_known(v___x_3917_, 3);
if (lean_obj_tag(v___x_3918_) == 0)
{
uint32_t v___x_3919_; 
v___x_3919_ = 65;
v___y_3910_ = v___x_3919_;
goto v___jp_3909_;
}
else
{
lean_object* v_val_3920_; uint32_t v___x_3921_; 
v_val_3920_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_val_3920_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3921_ = lean_unbox_uint32(v_val_3920_);
lean_dec(v_val_3920_);
v___y_3910_ = v___x_3921_;
goto v___jp_3909_;
}
}
v___jp_3922_:
{
uint8_t v___x_3923_; 
v___x_3923_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3857_, v___x_3853_);
if (v___x_3923_ == 0)
{
goto v___jp_3915_;
}
else
{
lean_object* v___x_3924_; 
lean_inc_ref(v___x_3857_);
v___x_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3857_);
v___y_3859_ = v___x_3924_;
goto v___jp_3858_;
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_del_object(v___x_3843_);
lean_dec(v_a_3840_);
v_a_3945_ = lean_ctor_get(v___x_3854_, 0);
v_a_3946_ = lean_ctor_get(v___x_3854_, 1);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3854_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_inc(v_a_3945_);
lean_dec(v___x_3854_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3945_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
v___jp_3845_:
{
lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3849_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_3840_, v___y_3846_, v___y_3848_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 1, v___y_3847_);
lean_ctor_set(v___x_3843_, 0, v___x_3849_);
v___x_3851_ = v___x_3843_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3852_, 1, v___y_3847_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
else
{
return v___x_3839_;
}
}
else
{
lean_object* v_a_3955_; lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
v_a_3955_ = lean_ctor_get(v___x_3836_, 0);
v_a_3956_ = lean_ctor_get(v___x_3836_, 1);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3836_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_inc(v_a_3955_);
lean_dec(v___x_3836_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3955_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object* v_stx_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_Fmt_fmtPostfixOperator(v_stx_3964_, v_a_3965_, v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_stx_3964_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t v_sz_3968_, size_t v_i_3969_, lean_object* v_bs_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
uint8_t v___x_3973_; 
v___x_3973_ = lean_usize_dec_lt(v_i_3969_, v_sz_3968_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3974_, 0, v_bs_3970_);
lean_ctor_set(v___x_3974_, 1, v___y_3972_);
return v___x_3974_;
}
else
{
lean_object* v_v_3975_; lean_object* v_elseTk_3976_; lean_object* v_ifTk_3977_; lean_object* v_cond_3978_; lean_object* v_thenTk_3979_; lean_object* v_body_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4041_; 
v_v_3975_ = lean_array_uget(v_bs_3970_, v_i_3969_);
v_elseTk_3976_ = lean_ctor_get(v_v_3975_, 0);
v_ifTk_3977_ = lean_ctor_get(v_v_3975_, 1);
v_cond_3978_ = lean_ctor_get(v_v_3975_, 2);
v_thenTk_3979_ = lean_ctor_get(v_v_3975_, 3);
v_body_3980_ = lean_ctor_get(v_v_3975_, 4);
v_isSharedCheck_4041_ = !lean_is_exclusive(v_v_3975_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_3982_ = v_v_3975_;
v_isShared_3983_ = v_isSharedCheck_4041_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_body_3980_);
lean_inc(v_thenTk_3979_);
lean_inc(v_cond_3978_);
lean_inc(v_ifTk_3977_);
lean_inc(v_elseTk_3976_);
lean_dec(v_v_3975_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4041_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Fmt_fmt(v_elseTk_3976_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v_a_3986_; lean_object* v___x_3987_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
v_a_3986_ = lean_ctor_get(v___x_3984_, 1);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3984_, 2);
v___x_3987_ = l_Lean_Fmt_fmt(v_ifTk_3977_, v___y_3971_, v_a_3986_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v_a_3989_; lean_object* v___x_3990_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
v_a_3989_ = lean_ctor_get(v___x_3987_, 1);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3987_, 2);
v___x_3990_ = l_Lean_Fmt_fmt(v_thenTk_3979_, v___y_3971_, v_a_3989_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v_a_3992_; lean_object* v___x_3993_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
v_a_3992_ = lean_ctor_get(v___x_3990_, 1);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___x_3990_, 2);
v___x_3993_ = l_Lean_Fmt_fmt(v_body_3980_, v___y_3971_, v_a_3992_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v_a_3995_; lean_object* v___x_3996_; lean_object* v_bs_x27_3997_; lean_object* v___x_3999_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
v_a_3995_ = lean_ctor_get(v___x_3993_, 1);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3993_, 2);
v___x_3996_ = lean_unsigned_to_nat(0u);
v_bs_x27_3997_ = lean_array_uset(v_bs_3970_, v_i_3969_, v___x_3996_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 4, v_a_3994_);
lean_ctor_set(v___x_3982_, 3, v_a_3991_);
lean_ctor_set(v___x_3982_, 1, v_a_3988_);
lean_ctor_set(v___x_3982_, 0, v_a_3985_);
v___x_3999_ = v___x_3982_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3985_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_a_3988_);
lean_ctor_set(v_reuseFailAlloc_4004_, 2, v_cond_3978_);
lean_ctor_set(v_reuseFailAlloc_4004_, 3, v_a_3991_);
lean_ctor_set(v_reuseFailAlloc_4004_, 4, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
size_t v___x_4000_; size_t v___x_4001_; lean_object* v___x_4002_; 
v___x_4000_ = ((size_t)1ULL);
v___x_4001_ = lean_usize_add(v_i_3969_, v___x_4000_);
v___x_4002_ = lean_array_uset(v_bs_x27_3997_, v_i_3969_, v___x_3999_);
v_i_3969_ = v___x_4001_;
v_bs_3970_ = v___x_4002_;
v___y_3972_ = v_a_3995_;
goto _start;
}
}
else
{
lean_object* v_a_4005_; lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec(v_a_3991_);
lean_dec(v_a_3988_);
lean_dec(v_a_3985_);
lean_del_object(v___x_3982_);
lean_dec_ref(v_cond_3978_);
lean_dec_ref(v_bs_3970_);
v_a_4005_ = lean_ctor_get(v___x_3993_, 0);
v_a_4006_ = lean_ctor_get(v___x_3993_, 1);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3993_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_inc(v_a_4005_);
lean_dec(v___x_3993_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4005_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v_a_3988_);
lean_dec(v_a_3985_);
lean_del_object(v___x_3982_);
lean_dec(v_body_3980_);
lean_dec_ref(v_cond_3978_);
lean_dec_ref(v_bs_3970_);
v_a_4014_ = lean_ctor_get(v___x_3990_, 0);
v_a_4015_ = lean_ctor_get(v___x_3990_, 1);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3990_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_inc(v_a_4014_);
lean_dec(v___x_3990_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4014_);
lean_ctor_set(v_reuseFailAlloc_4021_, 1, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec(v_a_3985_);
lean_del_object(v___x_3982_);
lean_dec(v_body_3980_);
lean_dec(v_thenTk_3979_);
lean_dec_ref(v_cond_3978_);
lean_dec_ref(v_bs_3970_);
v_a_4023_ = lean_ctor_get(v___x_3987_, 0);
v_a_4024_ = lean_ctor_get(v___x_3987_, 1);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_3987_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_inc(v_a_4023_);
lean_dec(v___x_3987_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4023_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_del_object(v___x_3982_);
lean_dec(v_body_3980_);
lean_dec(v_thenTk_3979_);
lean_dec_ref(v_cond_3978_);
lean_dec(v_ifTk_3977_);
lean_dec_ref(v_bs_3970_);
v_a_4032_ = lean_ctor_get(v___x_3984_, 0);
v_a_4033_ = lean_ctor_get(v___x_3984_, 1);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_3984_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_inc(v_a_4032_);
lean_dec(v___x_3984_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4032_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object* v_sz_4042_, lean_object* v_i_4043_, lean_object* v_bs_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
size_t v_sz_boxed_4047_; size_t v_i_boxed_4048_; lean_object* v_res_4049_; 
v_sz_boxed_4047_ = lean_unbox_usize(v_sz_4042_);
lean_dec(v_sz_4042_);
v_i_boxed_4048_ = lean_unbox_usize(v_i_4043_);
lean_dec(v_i_4043_);
v_res_4049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_boxed_4047_, v_i_boxed_4048_, v_bs_4044_, v___y_4045_, v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object* v_a_4050_, lean_object* v_x_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v_a_4050_);
v___x_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
lean_ctor_set(v___x_4055_, 1, v___y_4053_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object* v_a_4056_, lean_object* v_x_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4056_, v_x_4057_, v___y_4058_, v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec_ref(v_x_4057_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object* v___x_4061_, lean_object* v_val_4062_, lean_object* v_elseIfs_4063_, lean_object* v_ifTk_4064_, lean_object* v_cond_4065_, lean_object* v_thenTk_4066_, lean_object* v_thenBody_4067_, lean_object* v_a_4068_, lean_object* v_____r_4069_, lean_object* v_elseBody_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
lean_inc(v_elseBody_4070_);
v___x_4073_ = l_Lean_Syntax_getKind(v_elseBody_4070_);
v___x_4074_ = l_Lean_Fmt_getConditionalFormatter_x3f(v___x_4061_, v___x_4073_);
lean_dec(v___x_4073_);
if (lean_obj_tag(v___x_4074_) == 1)
{
lean_object* v_val_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4135_; 
v_val_4075_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4077_ = v___x_4074_;
v_isShared_4078_ = v_isSharedCheck_4135_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_val_4075_);
lean_dec(v___x_4074_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4135_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4079_; 
lean_inc_ref(v___y_4071_);
v___x_4079_ = lean_apply_3(v_val_4075_, v_elseBody_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
if (lean_obj_tag(v_a_4080_) == 1)
{
lean_object* v_val_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4113_; 
lean_del_object(v___x_4077_);
lean_dec_ref(v_a_4068_);
v_val_4081_ = lean_ctor_get(v_a_4080_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v_a_4080_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4083_ = v_a_4080_;
v_isShared_4084_ = v_isSharedCheck_4113_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_val_4081_);
lean_dec(v_a_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4113_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4111_; 
v_a_4085_ = lean_ctor_get(v___x_4079_, 1);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4111_ == 0)
{
lean_object* v_unused_4112_; 
v_unused_4112_ = lean_ctor_get(v___x_4079_, 0);
lean_dec(v_unused_4112_);
v___x_4087_ = v___x_4079_;
v_isShared_4088_ = v_isSharedCheck_4111_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4079_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4111_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v_ifTk_4089_; lean_object* v_cond_4090_; lean_object* v_thenTk_4091_; lean_object* v_thenBody_4092_; lean_object* v_elseTk_x3f_4093_; lean_object* v_elseBody_x3f_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4109_; 
v_ifTk_4089_ = lean_ctor_get(v_val_4081_, 0);
v_cond_4090_ = lean_ctor_get(v_val_4081_, 1);
v_thenTk_4091_ = lean_ctor_get(v_val_4081_, 2);
v_thenBody_4092_ = lean_ctor_get(v_val_4081_, 3);
v_elseTk_x3f_4093_ = lean_ctor_get(v_val_4081_, 5);
v_elseBody_x3f_4094_ = lean_ctor_get(v_val_4081_, 6);
v_isSharedCheck_4109_ = !lean_is_exclusive(v_val_4081_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; 
v_unused_4110_ = lean_ctor_get(v_val_4081_, 4);
lean_dec(v_unused_4110_);
v___x_4096_ = v_val_4081_;
v_isShared_4097_ = v_isSharedCheck_4109_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_elseBody_x3f_4094_);
lean_inc(v_elseTk_x3f_4093_);
lean_inc(v_thenBody_4092_);
lean_inc(v_thenTk_4091_);
lean_inc(v_cond_4090_);
lean_inc(v_ifTk_4089_);
lean_dec(v_val_4081_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4109_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4098_, 0, v_val_4062_);
lean_ctor_set(v___x_4098_, 1, v_ifTk_4089_);
lean_ctor_set(v___x_4098_, 2, v_cond_4090_);
lean_ctor_set(v___x_4098_, 3, v_thenTk_4091_);
lean_ctor_set(v___x_4098_, 4, v_thenBody_4092_);
v___x_4099_ = lean_array_push(v_elseIfs_4063_, v___x_4098_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 4, v___x_4099_);
lean_ctor_set(v___x_4096_, 3, v_thenBody_4067_);
lean_ctor_set(v___x_4096_, 2, v_thenTk_4066_);
lean_ctor_set(v___x_4096_, 1, v_cond_4065_);
lean_ctor_set(v___x_4096_, 0, v_ifTk_4064_);
v___x_4101_ = v___x_4096_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_ifTk_4064_);
lean_ctor_set(v_reuseFailAlloc_4108_, 1, v_cond_4065_);
lean_ctor_set(v_reuseFailAlloc_4108_, 2, v_thenTk_4066_);
lean_ctor_set(v_reuseFailAlloc_4108_, 3, v_thenBody_4067_);
lean_ctor_set(v_reuseFailAlloc_4108_, 4, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4108_, 5, v_elseTk_x3f_4093_);
lean_ctor_set(v_reuseFailAlloc_4108_, 6, v_elseBody_x3f_4094_);
v___x_4101_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4103_; 
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 0, v___x_4101_);
v___x_4103_ = v___x_4083_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
lean_object* v___x_4105_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 0, v___x_4103_);
v___x_4105_ = v___x_4087_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_a_4085_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4124_; 
lean_dec(v_a_4080_);
lean_dec(v_thenBody_4067_);
lean_dec(v_thenTk_4066_);
lean_dec_ref(v_cond_4065_);
lean_dec(v_ifTk_4064_);
lean_dec_ref(v_elseIfs_4063_);
lean_dec(v_val_4062_);
v_a_4114_ = lean_ctor_get(v___x_4079_, 1);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4124_ == 0)
{
lean_object* v_unused_4125_; 
v_unused_4125_ = lean_ctor_get(v___x_4079_, 0);
lean_dec(v_unused_4125_);
v___x_4116_ = v___x_4079_;
v_isShared_4117_ = v_isSharedCheck_4124_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4079_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4124_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4078_ == 0)
{
lean_ctor_set_tag(v___x_4077_, 0);
lean_ctor_set(v___x_4077_, 0, v_a_4068_);
v___x_4119_ = v___x_4077_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4068_);
v___x_4119_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
lean_object* v___x_4121_; 
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4119_);
v___x_4121_ = v___x_4116_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4119_);
lean_ctor_set(v_reuseFailAlloc_4122_, 1, v_a_4114_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_del_object(v___x_4077_);
lean_dec_ref(v_a_4068_);
lean_dec(v_thenBody_4067_);
lean_dec(v_thenTk_4066_);
lean_dec_ref(v_cond_4065_);
lean_dec(v_ifTk_4064_);
lean_dec_ref(v_elseIfs_4063_);
lean_dec(v_val_4062_);
v_a_4126_ = lean_ctor_get(v___x_4079_, 0);
v_a_4127_ = lean_ctor_get(v___x_4079_, 1);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4079_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_inc(v_a_4126_);
lean_dec(v___x_4079_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4126_);
lean_ctor_set(v_reuseFailAlloc_4133_, 1, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_dec(v___x_4074_);
lean_dec(v_elseBody_4070_);
lean_dec(v_thenBody_4067_);
lean_dec(v_thenTk_4066_);
lean_dec_ref(v_cond_4065_);
lean_dec(v_ifTk_4064_);
lean_dec_ref(v_elseIfs_4063_);
lean_dec(v_val_4062_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_a_4068_);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
lean_ctor_set(v___x_4137_, 1, v___y_4072_);
return v___x_4137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object* v___x_4138_, lean_object* v_val_4139_, lean_object* v_elseIfs_4140_, lean_object* v_ifTk_4141_, lean_object* v_cond_4142_, lean_object* v_thenTk_4143_, lean_object* v_thenBody_4144_, lean_object* v_a_4145_, lean_object* v_____r_4146_, lean_object* v_elseBody_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4138_, v_val_4139_, v_elseIfs_4140_, v_ifTk_4141_, v_cond_4142_, v_thenTk_4143_, v_thenBody_4144_, v_a_4145_, v_____r_4146_, v_elseBody_4147_, v___y_4148_, v___y_4149_);
lean_dec_ref(v___y_4148_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object* v___x_4165_, lean_object* v_a_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
lean_object* v___y_4170_; lean_object* v_elseTk_x3f_4194_; 
v_elseTk_x3f_4194_ = lean_ctor_get(v_a_4166_, 5);
if (lean_obj_tag(v_elseTk_x3f_4194_) == 1)
{
lean_object* v_elseBody_x3f_4195_; 
v_elseBody_x3f_4195_ = lean_ctor_get(v_a_4166_, 6);
if (lean_obj_tag(v_elseBody_x3f_4195_) == 1)
{
lean_object* v_ifTk_4196_; lean_object* v_cond_4197_; lean_object* v_thenTk_4198_; lean_object* v_thenBody_4199_; lean_object* v_elseIfs_4200_; lean_object* v_val_4201_; lean_object* v_val_4202_; lean_object* v___x_4203_; uint8_t v___x_4204_; 
v_ifTk_4196_ = lean_ctor_get(v_a_4166_, 0);
lean_inc(v_ifTk_4196_);
v_cond_4197_ = lean_ctor_get(v_a_4166_, 1);
lean_inc_ref(v_cond_4197_);
v_thenTk_4198_ = lean_ctor_get(v_a_4166_, 2);
lean_inc(v_thenTk_4198_);
v_thenBody_4199_ = lean_ctor_get(v_a_4166_, 3);
lean_inc(v_thenBody_4199_);
v_elseIfs_4200_ = lean_ctor_get(v_a_4166_, 4);
lean_inc_ref(v_elseIfs_4200_);
v_val_4201_ = lean_ctor_get(v_elseTk_x3f_4194_, 0);
lean_inc(v_val_4201_);
v_val_4202_ = lean_ctor_get(v_elseBody_x3f_4195_, 0);
v___x_4203_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3));
lean_inc(v_val_4202_);
v___x_4204_ = l_Lean_Syntax_isOfKind(v_val_4202_, v___x_4203_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_inc(v_val_4202_);
v___x_4205_ = lean_box(0);
lean_inc_ref(v___x_4165_);
v___x_4206_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4165_, v_val_4201_, v_elseIfs_4200_, v_ifTk_4196_, v_cond_4197_, v_thenTk_4198_, v_thenBody_4199_, v_a_4166_, v___x_4205_, v_val_4202_, v___y_4167_, v___y_4168_);
v___y_4170_ = v___x_4206_;
goto v___jp_4169_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4207_ = lean_unsigned_to_nat(0u);
v___x_4208_ = l_Lean_Syntax_getArg(v_val_4202_, v___x_4207_);
v___x_4209_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5));
lean_inc(v___x_4208_);
v___x_4210_ = l_Lean_Syntax_isOfKind(v___x_4208_, v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_inc(v_val_4202_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
lean_inc_ref(v___x_4165_);
v___x_4212_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4165_, v_val_4201_, v_elseIfs_4200_, v_ifTk_4196_, v_cond_4197_, v_thenTk_4198_, v_thenBody_4199_, v_a_4166_, v___x_4211_, v_val_4202_, v___y_4167_, v___y_4168_);
v___y_4170_ = v___x_4212_;
goto v___jp_4169_;
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; 
v___x_4213_ = l_Lean_Syntax_getArg(v___x_4208_, v___x_4207_);
lean_dec(v___x_4208_);
v___x_4214_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4213_);
v___x_4215_ = l_Lean_Syntax_matchesNull(v___x_4213_, v___x_4214_);
if (v___x_4215_ == 0)
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_inc(v_val_4202_);
lean_dec(v___x_4213_);
v___x_4216_ = lean_box(0);
lean_inc_ref(v___x_4165_);
v___x_4217_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4165_, v_val_4201_, v_elseIfs_4200_, v_ifTk_4196_, v_cond_4197_, v_thenTk_4198_, v_thenBody_4199_, v_a_4166_, v___x_4216_, v_val_4202_, v___y_4167_, v___y_4168_);
v___y_4170_ = v___x_4217_;
goto v___jp_4169_;
}
else
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4218_ = l_Lean_Syntax_getArg(v___x_4213_, v___x_4207_);
lean_dec(v___x_4213_);
v___x_4219_ = lean_box(0);
lean_inc_ref(v___x_4165_);
v___x_4220_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4165_, v_val_4201_, v_elseIfs_4200_, v_ifTk_4196_, v_cond_4197_, v_thenTk_4198_, v_thenBody_4199_, v_a_4166_, v___x_4219_, v___x_4218_, v___y_4167_, v___y_4168_);
v___y_4170_ = v___x_4220_;
goto v___jp_4169_;
}
}
}
}
else
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_inc(v_elseBody_x3f_4195_);
lean_inc_ref(v_elseTk_x3f_4194_);
v___x_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4221_, 0, v_elseTk_x3f_4194_);
lean_ctor_set(v___x_4221_, 1, v_elseBody_x3f_4195_);
v___x_4222_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4166_, v___x_4221_, v___y_4167_, v___y_4168_);
lean_dec_ref_known(v___x_4221_, 2);
v___y_4170_ = v___x_4222_;
goto v___jp_4169_;
}
}
else
{
lean_object* v_elseBody_x3f_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_elseBody_x3f_4223_ = lean_ctor_get(v_a_4166_, 6);
lean_inc(v_elseBody_x3f_4223_);
lean_inc(v_elseTk_x3f_4194_);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v_elseTk_x3f_4194_);
lean_ctor_set(v___x_4224_, 1, v_elseBody_x3f_4223_);
v___x_4225_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4166_, v___x_4224_, v___y_4167_, v___y_4168_);
lean_dec_ref_known(v___x_4224_, 2);
v___y_4170_ = v___x_4225_;
goto v___jp_4169_;
}
v___jp_4169_:
{
if (lean_obj_tag(v___y_4170_) == 0)
{
lean_object* v_a_4171_; 
v_a_4171_ = lean_ctor_get(v___y_4170_, 0);
lean_inc(v_a_4171_);
if (lean_obj_tag(v_a_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4180_; 
lean_dec_ref(v___x_4165_);
v_a_4172_ = lean_ctor_get(v___y_4170_, 1);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___y_4170_);
if (v_isSharedCheck_4180_ == 0)
{
lean_object* v_unused_4181_; 
v_unused_4181_ = lean_ctor_get(v___y_4170_, 0);
lean_dec(v_unused_4181_);
v___x_4174_ = v___y_4170_;
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___y_4170_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4180_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v_a_4176_; lean_object* v___x_4178_; 
v_a_4176_ = lean_ctor_get(v_a_4171_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v_a_4171_, 1);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v_a_4176_);
v___x_4178_ = v___x_4174_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4176_);
lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_a_4172_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v_a_4183_; 
v_a_4182_ = lean_ctor_get(v___y_4170_, 1);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___y_4170_, 2);
v_a_4183_ = lean_ctor_get(v_a_4171_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v_a_4171_, 1);
v_a_4166_ = v_a_4183_;
v___y_4168_ = v_a_4182_;
goto _start;
}
}
else
{
lean_object* v_a_4185_; lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec_ref(v___x_4165_);
v_a_4185_ = lean_ctor_get(v___y_4170_, 0);
v_a_4186_ = lean_ctor_get(v___y_4170_, 1);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___y_4170_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___y_4170_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_inc(v_a_4185_);
lean_dec(v___y_4170_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4185_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object* v___x_4226_, lean_object* v_a_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4226_, v_a_4227_, v___y_4228_, v___y_4229_);
lean_dec_ref(v___y_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object* v_initialFmt_4231_, lean_object* v_stx_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v___y_4236_; lean_object* v___y_4237_; uint8_t v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v_env_4262_; lean_object* v___x_4263_; 
v_env_4262_ = lean_ctor_get(v_a_4233_, 0);
lean_inc_ref(v_a_4233_);
lean_inc(v_stx_4232_);
v___x_4263_ = lean_apply_3(v_initialFmt_4231_, v_stx_4232_, v_a_4233_, v_a_4234_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v_a_4264_; 
v_a_4264_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_a_4264_);
if (lean_obj_tag(v_a_4264_) == 1)
{
lean_object* v_a_4265_; lean_object* v_val_4266_; lean_object* v___x_4267_; 
v_a_4265_ = lean_ctor_get(v___x_4263_, 1);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4263_, 2);
v_val_4266_ = lean_ctor_get(v_a_4264_, 0);
lean_inc(v_val_4266_);
lean_dec_ref_known(v_a_4264_, 1);
v___x_4267_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_4232_, v_a_4233_, v_a_4265_);
lean_dec(v_stx_4232_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v_a_4269_; uint8_t v___y_4271_; uint8_t v___x_4321_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
v_a_4269_ = lean_ctor_get(v___x_4267_, 1);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4267_, 2);
v___x_4321_ = lean_unbox(v_a_4268_);
lean_dec(v_a_4268_);
if (v___x_4321_ == 0)
{
uint8_t v___x_4322_; 
v___x_4322_ = 1;
v___y_4271_ = v___x_4322_;
goto v___jp_4270_;
}
else
{
uint8_t v___x_4323_; 
v___x_4323_ = 0;
v___y_4271_ = v___x_4323_;
goto v___jp_4270_;
}
v___jp_4270_:
{
lean_object* v___x_4272_; 
lean_inc_ref(v_env_4262_);
v___x_4272_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v_env_4262_, v_val_4266_, v_a_4233_, v_a_4269_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v_a_4274_; lean_object* v_ifTk_4275_; lean_object* v_cond_4276_; lean_object* v_thenTk_4277_; lean_object* v_thenBody_4278_; lean_object* v_elseIfs_4279_; lean_object* v_elseTk_x3f_4280_; lean_object* v_elseBody_x3f_4281_; lean_object* v___x_4282_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
v_a_4274_ = lean_ctor_get(v___x_4272_, 1);
lean_inc(v_a_4274_);
lean_dec_ref_known(v___x_4272_, 2);
v_ifTk_4275_ = lean_ctor_get(v_a_4273_, 0);
lean_inc(v_ifTk_4275_);
v_cond_4276_ = lean_ctor_get(v_a_4273_, 1);
lean_inc_ref(v_cond_4276_);
v_thenTk_4277_ = lean_ctor_get(v_a_4273_, 2);
lean_inc(v_thenTk_4277_);
v_thenBody_4278_ = lean_ctor_get(v_a_4273_, 3);
lean_inc(v_thenBody_4278_);
v_elseIfs_4279_ = lean_ctor_get(v_a_4273_, 4);
lean_inc_ref(v_elseIfs_4279_);
v_elseTk_x3f_4280_ = lean_ctor_get(v_a_4273_, 5);
lean_inc(v_elseTk_x3f_4280_);
v_elseBody_x3f_4281_ = lean_ctor_get(v_a_4273_, 6);
lean_inc(v_elseBody_x3f_4281_);
lean_dec(v_a_4273_);
v___x_4282_ = l_Lean_Fmt_fmt(v_ifTk_4275_, v_a_4233_, v_a_4274_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v_a_4284_; lean_object* v___x_4285_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
v_a_4284_ = lean_ctor_get(v___x_4282_, 1);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4282_, 2);
v___x_4285_ = l_Lean_Fmt_fmt(v_thenTk_4277_, v_a_4233_, v_a_4284_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v_a_4287_; lean_object* v___x_4288_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
v_a_4287_ = lean_ctor_get(v___x_4285_, 1);
lean_inc(v_a_4287_);
lean_dec_ref_known(v___x_4285_, 2);
v___x_4288_ = l_Lean_Fmt_fmt(v_thenBody_4278_, v_a_4233_, v_a_4287_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v_a_4290_; size_t v_sz_4291_; size_t v___x_4292_; lean_object* v___x_4293_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
v_a_4290_ = lean_ctor_get(v___x_4288_, 1);
lean_inc(v_a_4290_);
lean_dec_ref_known(v___x_4288_, 2);
v_sz_4291_ = lean_array_size(v_elseIfs_4279_);
v___x_4292_ = ((size_t)0ULL);
v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_4291_, v___x_4292_, v_elseIfs_4279_, v_a_4233_, v_a_4290_);
if (lean_obj_tag(v___x_4293_) == 0)
{
if (lean_obj_tag(v_elseTk_x3f_4280_) == 0)
{
lean_object* v_a_4294_; lean_object* v_a_4295_; lean_object* v___x_4296_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
v_a_4295_ = lean_ctor_get(v___x_4293_, 1);
lean_inc(v_a_4295_);
lean_dec_ref_known(v___x_4293_, 2);
v___x_4296_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4248_ = v_a_4294_;
v___y_4249_ = v_cond_4276_;
v___y_4250_ = v___y_4271_;
v___y_4251_ = v_a_4295_;
v___y_4252_ = v_elseBody_x3f_4281_;
v___y_4253_ = v_a_4289_;
v___y_4254_ = v_a_4283_;
v___y_4255_ = v_a_4286_;
v___y_4256_ = v___x_4296_;
goto v___jp_4247_;
}
else
{
lean_object* v_a_4297_; lean_object* v_a_4298_; lean_object* v_val_4299_; lean_object* v___x_4300_; 
v_a_4297_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4297_);
v_a_4298_ = lean_ctor_get(v___x_4293_, 1);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4293_, 2);
v_val_4299_ = lean_ctor_get(v_elseTk_x3f_4280_, 0);
lean_inc(v_val_4299_);
lean_dec_ref_known(v_elseTk_x3f_4280_, 1);
v___x_4300_ = l_Lean_Fmt_fmt(v_val_4299_, v_a_4233_, v_a_4298_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v_a_4302_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
v_a_4302_ = lean_ctor_get(v___x_4300_, 1);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4300_, 2);
v___y_4248_ = v_a_4297_;
v___y_4249_ = v_cond_4276_;
v___y_4250_ = v___y_4271_;
v___y_4251_ = v_a_4302_;
v___y_4252_ = v_elseBody_x3f_4281_;
v___y_4253_ = v_a_4289_;
v___y_4254_ = v_a_4283_;
v___y_4255_ = v_a_4286_;
v___y_4256_ = v_a_4301_;
goto v___jp_4247_;
}
else
{
lean_dec(v_a_4297_);
lean_dec(v_a_4289_);
lean_dec(v_a_4286_);
lean_dec(v_a_4283_);
lean_dec(v_elseBody_x3f_4281_);
lean_dec_ref(v_cond_4276_);
return v___x_4300_;
}
}
}
else
{
lean_object* v_a_4303_; lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec(v_a_4289_);
lean_dec(v_a_4286_);
lean_dec(v_a_4283_);
lean_dec(v_elseBody_x3f_4281_);
lean_dec(v_elseTk_x3f_4280_);
lean_dec_ref(v_cond_4276_);
v_a_4303_ = lean_ctor_get(v___x_4293_, 0);
v_a_4304_ = lean_ctor_get(v___x_4293_, 1);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4293_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_inc(v_a_4303_);
lean_dec(v___x_4293_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4303_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
else
{
lean_dec(v_a_4286_);
lean_dec(v_a_4283_);
lean_dec(v_elseBody_x3f_4281_);
lean_dec(v_elseTk_x3f_4280_);
lean_dec_ref(v_elseIfs_4279_);
lean_dec_ref(v_cond_4276_);
return v___x_4288_;
}
}
else
{
lean_dec(v_a_4283_);
lean_dec(v_elseBody_x3f_4281_);
lean_dec(v_elseTk_x3f_4280_);
lean_dec_ref(v_elseIfs_4279_);
lean_dec(v_thenBody_4278_);
lean_dec_ref(v_cond_4276_);
return v___x_4285_;
}
}
else
{
lean_dec(v_elseBody_x3f_4281_);
lean_dec(v_elseTk_x3f_4280_);
lean_dec_ref(v_elseIfs_4279_);
lean_dec(v_thenBody_4278_);
lean_dec(v_thenTk_4277_);
lean_dec_ref(v_cond_4276_);
return v___x_4282_;
}
}
else
{
lean_object* v_a_4312_; lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
v_a_4312_ = lean_ctor_get(v___x_4272_, 0);
v_a_4313_ = lean_ctor_get(v___x_4272_, 1);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4272_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_inc(v_a_4312_);
lean_dec(v___x_4272_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4312_);
lean_ctor_set(v_reuseFailAlloc_4319_, 1, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec(v_val_4266_);
v_a_4324_ = lean_ctor_get(v___x_4267_, 0);
v_a_4325_ = lean_ctor_get(v___x_4267_, 1);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4267_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4267_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_inc(v_a_4324_);
lean_dec(v___x_4267_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4324_);
lean_ctor_set(v_reuseFailAlloc_4331_, 1, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4341_; 
lean_dec(v_a_4264_);
lean_dec(v_stx_4232_);
v_a_4333_ = lean_ctor_get(v___x_4263_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4341_ == 0)
{
lean_object* v_unused_4342_; 
v_unused_4342_ = lean_ctor_get(v___x_4263_, 0);
lean_dec(v_unused_4342_);
v___x_4335_ = v___x_4263_;
v_isShared_4336_ = v_isSharedCheck_4341_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4263_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4341_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v___x_4339_; 
v___x_4337_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4336_ == 0)
{
lean_ctor_set_tag(v___x_4335_, 1);
lean_ctor_set(v___x_4335_, 0, v___x_4337_);
v___x_4339_ = v___x_4335_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_a_4333_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_stx_4232_);
v_a_4343_ = lean_ctor_get(v___x_4263_, 0);
v_a_4344_ = lean_ctor_get(v___x_4263_, 1);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4263_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_inc(v_a_4343_);
lean_dec(v___x_4263_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4343_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
v___jp_4235_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = l_Lean_Fmt_Layouts_conditional(v___y_4242_, v___y_4237_, v___y_4243_, v___y_4241_, v___y_4236_, v___y_4240_, v___y_4244_, v___y_4238_);
lean_dec_ref(v___y_4236_);
v___x_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
lean_ctor_set(v___x_4246_, 1, v___y_4239_);
return v___x_4246_;
}
v___jp_4247_:
{
if (lean_obj_tag(v___y_4252_) == 0)
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4236_ = v___y_4248_;
v___y_4237_ = v___y_4249_;
v___y_4238_ = v___y_4250_;
v___y_4239_ = v___y_4251_;
v___y_4240_ = v___y_4256_;
v___y_4241_ = v___y_4253_;
v___y_4242_ = v___y_4254_;
v___y_4243_ = v___y_4255_;
v___y_4244_ = v___x_4257_;
goto v___jp_4235_;
}
else
{
lean_object* v_val_4258_; lean_object* v___x_4259_; 
v_val_4258_ = lean_ctor_get(v___y_4252_, 0);
lean_inc(v_val_4258_);
lean_dec_ref_known(v___y_4252_, 1);
v___x_4259_ = l_Lean_Fmt_fmt(v_val_4258_, v_a_4233_, v___y_4251_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v_a_4261_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
v_a_4261_ = lean_ctor_get(v___x_4259_, 1);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4259_, 2);
v___y_4236_ = v___y_4248_;
v___y_4237_ = v___y_4249_;
v___y_4238_ = v___y_4250_;
v___y_4239_ = v_a_4261_;
v___y_4240_ = v___y_4256_;
v___y_4241_ = v___y_4253_;
v___y_4242_ = v___y_4254_;
v___y_4243_ = v___y_4255_;
v___y_4244_ = v_a_4260_;
goto v___jp_4235_;
}
else
{
lean_dec_ref(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v___y_4249_);
lean_dec_ref(v___y_4248_);
return v___x_4259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object* v_initialFmt_4352_, lean_object* v_stx_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_Fmt_fmtConditional(v_initialFmt_4352_, v_stx_4353_, v_a_4354_, v_a_4355_);
lean_dec_ref(v_a_4354_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object* v___x_4357_, lean_object* v_inst_4358_, lean_object* v_a_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4357_, v_a_4359_, v___y_4360_, v___y_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object* v___x_4363_, lean_object* v_inst_4364_, lean_object* v_a_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(v___x_4363_, v_inst_4364_, v_a_4365_, v___y_4366_, v___y_4367_);
lean_dec_ref(v___y_4366_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t v_sz_4369_, size_t v_i_4370_, lean_object* v_bs_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
uint8_t v___x_4374_; 
v___x_4374_ = lean_usize_dec_lt(v_i_4370_, v_sz_4369_);
if (v___x_4374_ == 0)
{
lean_object* v___x_4375_; 
v___x_4375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4375_, 0, v_bs_4371_);
lean_ctor_set(v___x_4375_, 1, v___y_4373_);
return v___x_4375_;
}
else
{
lean_object* v_v_4376_; size_t v_sz_4377_; size_t v___x_4378_; lean_object* v___x_4379_; 
v_v_4376_ = lean_array_uget_borrowed(v_bs_4371_, v_i_4370_);
v_sz_4377_ = lean_array_size(v_v_4376_);
v___x_4378_ = ((size_t)0ULL);
lean_inc(v_v_4376_);
v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_4377_, v___x_4378_, v_v_4376_, v___y_4372_, v___y_4373_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v_a_4381_; lean_object* v___x_4382_; lean_object* v_bs_x27_4383_; size_t v___x_4384_; size_t v___x_4385_; lean_object* v___x_4386_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
v_a_4381_ = lean_ctor_get(v___x_4379_, 1);
lean_inc(v_a_4381_);
lean_dec_ref_known(v___x_4379_, 2);
v___x_4382_ = lean_unsigned_to_nat(0u);
v_bs_x27_4383_ = lean_array_uset(v_bs_4371_, v_i_4370_, v___x_4382_);
v___x_4384_ = ((size_t)1ULL);
v___x_4385_ = lean_usize_add(v_i_4370_, v___x_4384_);
v___x_4386_ = lean_array_uset(v_bs_x27_4383_, v_i_4370_, v_a_4380_);
v_i_4370_ = v___x_4385_;
v_bs_4371_ = v___x_4386_;
v___y_4373_ = v_a_4381_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4371_);
return v___x_4379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object* v_sz_4388_, lean_object* v_i_4389_, lean_object* v_bs_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
size_t v_sz_boxed_4393_; size_t v_i_boxed_4394_; lean_object* v_res_4395_; 
v_sz_boxed_4393_ = lean_unbox_usize(v_sz_4388_);
lean_dec(v_sz_4388_);
v_i_boxed_4394_ = lean_unbox_usize(v_i_4389_);
lean_dec(v_i_4389_);
v_res_4395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_boxed_4393_, v_i_boxed_4394_, v_bs_4390_, v___y_4391_, v___y_4392_);
lean_dec_ref(v___y_4391_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(size_t v_sz_4396_, size_t v_i_4397_, lean_object* v_bs_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
uint8_t v___x_4401_; 
v___x_4401_ = lean_usize_dec_lt(v_i_4397_, v_sz_4396_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v_bs_4398_);
lean_ctor_set(v___x_4402_, 1, v___y_4400_);
return v___x_4402_;
}
else
{
lean_object* v_v_4403_; size_t v_sz_4404_; size_t v___x_4405_; lean_object* v___x_4406_; 
v_v_4403_ = lean_array_uget_borrowed(v_bs_4398_, v_i_4397_);
v_sz_4404_ = lean_array_size(v_v_4403_);
v___x_4405_ = ((size_t)0ULL);
lean_inc(v_v_4403_);
v___x_4406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_4404_, v___x_4405_, v_v_4403_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v_a_4408_; lean_object* v___x_4409_; lean_object* v_bs_x27_4410_; size_t v___x_4411_; size_t v___x_4412_; lean_object* v___x_4413_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
v_a_4408_ = lean_ctor_get(v___x_4406_, 1);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4406_, 2);
v___x_4409_ = lean_unsigned_to_nat(0u);
v_bs_x27_4410_ = lean_array_uset(v_bs_4398_, v_i_4397_, v___x_4409_);
v___x_4411_ = ((size_t)1ULL);
v___x_4412_ = lean_usize_add(v_i_4397_, v___x_4411_);
v___x_4413_ = lean_array_uset(v_bs_x27_4410_, v_i_4397_, v_a_4407_);
v_i_4397_ = v___x_4412_;
v_bs_4398_ = v___x_4413_;
v___y_4400_ = v_a_4408_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4398_);
return v___x_4406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1___boxed(lean_object* v_sz_4415_, lean_object* v_i_4416_, lean_object* v_bs_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
size_t v_sz_boxed_4420_; size_t v_i_boxed_4421_; lean_object* v_res_4422_; 
v_sz_boxed_4420_ = lean_unbox_usize(v_sz_4415_);
lean_dec(v_sz_4415_);
v_i_boxed_4421_ = lean_unbox_usize(v_i_4416_);
lean_dec(v_i_4416_);
v_res_4422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_boxed_4420_, v_i_boxed_4421_, v_bs_4417_, v___y_4418_, v___y_4419_);
lean_dec_ref(v___y_4418_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object* v_bgs_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
size_t v_sz_4426_; size_t v___x_4427_; lean_object* v___x_4428_; 
v_sz_4426_ = lean_array_size(v_bgs_4423_);
v___x_4427_ = ((size_t)0ULL);
v___x_4428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_4426_, v___x_4427_, v_bgs_4423_, v_a_4424_, v_a_4425_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object* v_bgs_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Lean_Fmt_fmtBinderGroups(v_bgs_4429_, v_a_4430_, v_a_4431_);
lean_dec_ref(v_a_4430_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object* v_lhs_4433_, lean_object* v_rhs_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_){
_start:
{
lean_object* v___x_4437_; 
v___x_4437_ = l_Lean_Fmt_fmt(v_lhs_4433_, v_a_4435_, v_a_4436_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v_a_4439_; lean_object* v___x_4440_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
lean_inc(v_a_4438_);
v_a_4439_ = lean_ctor_get(v___x_4437_, 1);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4437_, 2);
v___x_4440_ = l_Lean_Fmt_fmt(v_rhs_4434_, v_a_4435_, v_a_4439_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4456_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
v_a_4442_ = lean_ctor_get(v___x_4440_, 1);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4444_ = v___x_4440_;
v_isShared_4445_ = v_isSharedCheck_4456_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_inc(v_a_4441_);
lean_dec(v___x_4440_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4456_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; uint8_t v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4454_; 
v___x_4446_ = lean_unsigned_to_nat(2u);
v___x_4447_ = lean_mk_empty_array_with_capacity(v___x_4446_);
v___x_4448_ = lean_array_push(v___x_4447_, v_a_4438_);
v___x_4449_ = lean_array_push(v___x_4448_, v_a_4441_);
v___x_4450_ = 1;
v___x_4451_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4449_, v___x_4450_);
lean_dec_ref(v___x_4449_);
v___x_4452_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4451_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4452_);
v___x_4454_ = v___x_4444_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v___x_4452_);
lean_ctor_set(v_reuseFailAlloc_4455_, 1, v_a_4442_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
else
{
lean_dec(v_a_4438_);
return v___x_4440_;
}
}
else
{
lean_dec(v_rhs_4434_);
return v___x_4437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object* v_lhs_4457_, lean_object* v_rhs_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4457_, v_rhs_4458_, v_a_4459_, v_a_4460_);
lean_dec_ref(v_a_4459_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object* v_head_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_quantifier_4465_; lean_object* v_binders_4466_; lean_object* v_typeAscriptionTk_x3f_4467_; lean_object* v_type_x3f_4468_; lean_object* v_commaTk_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4582_; 
v_quantifier_4465_ = lean_ctor_get(v_head_4462_, 0);
v_binders_4466_ = lean_ctor_get(v_head_4462_, 1);
v_typeAscriptionTk_x3f_4467_ = lean_ctor_get(v_head_4462_, 2);
v_type_x3f_4468_ = lean_ctor_get(v_head_4462_, 3);
v_commaTk_4469_ = lean_ctor_get(v_head_4462_, 4);
v_isSharedCheck_4582_ = !lean_is_exclusive(v_head_4462_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4471_ = v_head_4462_;
v_isShared_4472_ = v_isSharedCheck_4582_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_commaTk_4469_);
lean_inc(v_type_x3f_4468_);
lean_inc(v_typeAscriptionTk_x3f_4467_);
lean_inc(v_binders_4466_);
lean_inc(v_quantifier_4465_);
lean_dec(v_head_4462_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4582_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; 
v___x_4473_ = l_Lean_Fmt_fmt(v_quantifier_4465_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v_a_4475_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; lean_object* v___y_4481_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v_binderGroups_4524_; lean_object* v___y_4525_; lean_object* v___y_4526_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
v_a_4475_ = lean_ctor_get(v___x_4473_, 1);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4473_, 2);
if (lean_obj_tag(v_binders_4466_) == 0)
{
lean_object* v_group_4541_; lean_object* v___x_4542_; 
v_group_4541_ = lean_ctor_get(v_binders_4466_, 0);
lean_inc_ref(v_group_4541_);
lean_dec_ref_known(v_binders_4466_, 1);
v___x_4542_ = l_Lean_Fmt_fmtBinderGroups(v_group_4541_, v_a_4463_, v_a_4475_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v_a_4544_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
v_a_4544_ = lean_ctor_get(v___x_4542_, 1);
lean_inc(v_a_4544_);
lean_dec_ref_known(v___x_4542_, 2);
v_binderGroups_4524_ = v_a_4543_;
v___y_4525_ = v_a_4463_;
v___y_4526_ = v_a_4544_;
goto v___jp_4523_;
}
else
{
lean_object* v_a_4545_; lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
lean_dec(v_a_4474_);
lean_del_object(v___x_4471_);
lean_dec(v_commaTk_4469_);
lean_dec(v_type_x3f_4468_);
lean_dec(v_typeAscriptionTk_x3f_4467_);
v_a_4545_ = lean_ctor_get(v___x_4542_, 0);
v_a_4546_ = lean_ctor_get(v___x_4542_, 1);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4542_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_inc(v_a_4545_);
lean_dec(v___x_4542_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4545_);
lean_ctor_set(v_reuseFailAlloc_4552_, 1, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
else
{
lean_object* v_lhs_4554_; lean_object* v_rhs_4555_; lean_object* v___x_4556_; 
v_lhs_4554_ = lean_ctor_get(v_binders_4466_, 0);
lean_inc(v_lhs_4554_);
v_rhs_4555_ = lean_ctor_get(v_binders_4466_, 1);
lean_inc(v_rhs_4555_);
lean_dec_ref_known(v_binders_4466_, 2);
v___x_4556_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4554_, v_rhs_4555_, v_a_4463_, v_a_4475_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v_a_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_a_4557_);
v_a_4558_ = lean_ctor_get(v___x_4556_, 1);
lean_inc(v_a_4558_);
lean_dec_ref_known(v___x_4556_, 2);
v___x_4559_ = lean_unsigned_to_nat(1u);
v___x_4560_ = lean_mk_empty_array_with_capacity(v___x_4559_);
lean_inc_ref_n(v___x_4560_, 2);
v___x_4561_ = lean_array_push(v___x_4560_, v_a_4557_);
v___x_4562_ = lean_array_push(v___x_4560_, v___x_4561_);
v___x_4563_ = lean_array_push(v___x_4560_, v___x_4562_);
v_binderGroups_4524_ = v___x_4563_;
v___y_4525_ = v_a_4463_;
v___y_4526_ = v_a_4558_;
goto v___jp_4523_;
}
else
{
lean_object* v_a_4564_; lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
lean_dec(v_a_4474_);
lean_del_object(v___x_4471_);
lean_dec(v_commaTk_4469_);
lean_dec(v_type_x3f_4468_);
lean_dec(v_typeAscriptionTk_x3f_4467_);
v_a_4564_ = lean_ctor_get(v___x_4556_, 0);
v_a_4565_ = lean_ctor_get(v___x_4556_, 1);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4556_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_inc(v_a_4564_);
lean_dec(v___x_4556_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4564_);
lean_ctor_set(v_reuseFailAlloc_4571_, 1, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
v___jp_4476_:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_Fmt_fmt(v_commaTk_4469_, v___y_4479_, v___y_4477_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4494_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
v_a_4484_ = lean_ctor_get(v___x_4482_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4486_ = v___x_4482_;
v_isShared_4487_ = v_isSharedCheck_4494_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_inc(v_a_4483_);
lean_dec(v___x_4482_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4494_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 4, v_a_4483_);
lean_ctor_set(v___x_4471_, 3, v___y_4481_);
lean_ctor_set(v___x_4471_, 2, v___y_4480_);
lean_ctor_set(v___x_4471_, 1, v___y_4478_);
lean_ctor_set(v___x_4471_, 0, v_a_4474_);
v___x_4489_ = v___x_4471_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4474_);
lean_ctor_set(v_reuseFailAlloc_4493_, 1, v___y_4478_);
lean_ctor_set(v_reuseFailAlloc_4493_, 2, v___y_4480_);
lean_ctor_set(v_reuseFailAlloc_4493_, 3, v___y_4481_);
lean_ctor_set(v_reuseFailAlloc_4493_, 4, v_a_4483_);
v___x_4489_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4491_; 
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 0, v___x_4489_);
v___x_4491_ = v___x_4486_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4492_, 1, v_a_4484_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
lean_dec_ref(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec_ref(v___y_4478_);
lean_dec(v_a_4474_);
lean_del_object(v___x_4471_);
v_a_4495_ = lean_ctor_get(v___x_4482_, 0);
v_a_4496_ = lean_ctor_get(v___x_4482_, 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4482_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_inc(v_a_4495_);
lean_dec(v___x_4482_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4495_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
v___jp_4504_:
{
if (lean_obj_tag(v_type_x3f_4468_) == 0)
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4477_ = v___y_4505_;
v___y_4478_ = v___y_4506_;
v___y_4479_ = v___y_4507_;
v___y_4480_ = v___y_4508_;
v___y_4481_ = v___x_4509_;
goto v___jp_4476_;
}
else
{
lean_object* v_val_4510_; lean_object* v___x_4511_; 
v_val_4510_ = lean_ctor_get(v_type_x3f_4468_, 0);
lean_inc(v_val_4510_);
lean_dec_ref_known(v_type_x3f_4468_, 1);
v___x_4511_ = l_Lean_Fmt_fmt(v_val_4510_, v___y_4507_, v___y_4505_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v_a_4513_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
v_a_4513_ = lean_ctor_get(v___x_4511_, 1);
lean_inc(v_a_4513_);
lean_dec_ref_known(v___x_4511_, 2);
v___y_4477_ = v_a_4513_;
v___y_4478_ = v___y_4506_;
v___y_4479_ = v___y_4507_;
v___y_4480_ = v___y_4508_;
v___y_4481_ = v_a_4512_;
goto v___jp_4476_;
}
else
{
lean_object* v_a_4514_; lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec_ref(v___y_4508_);
lean_dec_ref(v___y_4506_);
lean_dec(v_a_4474_);
lean_del_object(v___x_4471_);
lean_dec(v_commaTk_4469_);
v_a_4514_ = lean_ctor_get(v___x_4511_, 0);
v_a_4515_ = lean_ctor_get(v___x_4511_, 1);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4511_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_inc(v_a_4514_);
lean_dec(v___x_4511_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4514_);
lean_ctor_set(v_reuseFailAlloc_4521_, 1, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
v___jp_4523_:
{
if (lean_obj_tag(v_typeAscriptionTk_x3f_4467_) == 0)
{
lean_object* v___x_4527_; 
v___x_4527_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4505_ = v___y_4526_;
v___y_4506_ = v_binderGroups_4524_;
v___y_4507_ = v___y_4525_;
v___y_4508_ = v___x_4527_;
goto v___jp_4504_;
}
else
{
lean_object* v_val_4528_; lean_object* v___x_4529_; 
v_val_4528_ = lean_ctor_get(v_typeAscriptionTk_x3f_4467_, 0);
lean_inc(v_val_4528_);
lean_dec_ref_known(v_typeAscriptionTk_x3f_4467_, 1);
v___x_4529_ = l_Lean_Fmt_fmt(v_val_4528_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v_a_4531_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
v_a_4531_ = lean_ctor_get(v___x_4529_, 1);
lean_inc(v_a_4531_);
lean_dec_ref_known(v___x_4529_, 2);
v___y_4505_ = v_a_4531_;
v___y_4506_ = v_binderGroups_4524_;
v___y_4507_ = v___y_4525_;
v___y_4508_ = v_a_4530_;
goto v___jp_4504_;
}
else
{
lean_object* v_a_4532_; lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec_ref(v_binderGroups_4524_);
lean_dec(v_a_4474_);
lean_del_object(v___x_4471_);
lean_dec(v_commaTk_4469_);
lean_dec(v_type_x3f_4468_);
v_a_4532_ = lean_ctor_get(v___x_4529_, 0);
v_a_4533_ = lean_ctor_get(v___x_4529_, 1);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4529_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_inc(v_a_4532_);
lean_dec(v___x_4529_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4532_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
}
}
else
{
lean_object* v_a_4573_; lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_del_object(v___x_4471_);
lean_dec(v_commaTk_4469_);
lean_dec(v_type_x3f_4468_);
lean_dec(v_typeAscriptionTk_x3f_4467_);
lean_dec_ref(v_binders_4466_);
v_a_4573_ = lean_ctor_get(v___x_4473_, 0);
v_a_4574_ = lean_ctor_get(v___x_4473_, 1);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4473_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_inc(v_a_4573_);
lean_dec(v___x_4473_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4573_);
lean_ctor_set(v_reuseFailAlloc_4580_, 1, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object* v_head_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_Fmt_fmtQuantifierHead(v_head_4583_, v_a_4584_, v_a_4585_);
lean_dec_ref(v_a_4584_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t v_sz_4587_, size_t v_i_4588_, lean_object* v_bs_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v___x_4592_; 
v___x_4592_ = lean_usize_dec_lt(v_i_4588_, v_sz_4587_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; 
v___x_4593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4593_, 0, v_bs_4589_);
lean_ctor_set(v___x_4593_, 1, v___y_4591_);
return v___x_4593_;
}
else
{
lean_object* v_v_4594_; lean_object* v___x_4595_; 
v_v_4594_ = lean_array_uget_borrowed(v_bs_4589_, v_i_4588_);
lean_inc(v_v_4594_);
v___x_4595_ = l_Lean_Fmt_fmtQuantifierHead(v_v_4594_, v___y_4590_, v___y_4591_);
if (lean_obj_tag(v___x_4595_) == 0)
{
lean_object* v_a_4596_; lean_object* v_a_4597_; lean_object* v___x_4598_; lean_object* v_bs_x27_4599_; size_t v___x_4600_; size_t v___x_4601_; lean_object* v___x_4602_; 
v_a_4596_ = lean_ctor_get(v___x_4595_, 0);
lean_inc(v_a_4596_);
v_a_4597_ = lean_ctor_get(v___x_4595_, 1);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4595_, 2);
v___x_4598_ = lean_unsigned_to_nat(0u);
v_bs_x27_4599_ = lean_array_uset(v_bs_4589_, v_i_4588_, v___x_4598_);
v___x_4600_ = ((size_t)1ULL);
v___x_4601_ = lean_usize_add(v_i_4588_, v___x_4600_);
v___x_4602_ = lean_array_uset(v_bs_x27_4599_, v_i_4588_, v_a_4596_);
v_i_4588_ = v___x_4601_;
v_bs_4589_ = v___x_4602_;
v___y_4591_ = v_a_4597_;
goto _start;
}
else
{
lean_object* v_a_4604_; lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec_ref(v_bs_4589_);
v_a_4604_ = lean_ctor_get(v___x_4595_, 0);
v_a_4605_ = lean_ctor_get(v___x_4595_, 1);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4595_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4595_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_inc(v_a_4604_);
lean_dec(v___x_4595_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4604_);
lean_ctor_set(v_reuseFailAlloc_4611_, 1, v_a_4605_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object* v_sz_4613_, lean_object* v_i_4614_, lean_object* v_bs_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
size_t v_sz_boxed_4618_; size_t v_i_boxed_4619_; lean_object* v_res_4620_; 
v_sz_boxed_4618_ = lean_unbox_usize(v_sz_4613_);
lean_dec(v_sz_4613_);
v_i_boxed_4619_ = lean_unbox_usize(v_i_4614_);
lean_dec(v_i_4614_);
v_res_4620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_boxed_4618_, v_i_boxed_4619_, v_bs_4615_, v___y_4616_, v___y_4617_);
lean_dec_ref(v___y_4616_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object* v_deconstructQuantifier_x3f_4621_, lean_object* v_stx_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_env_4625_; lean_object* v___x_4626_; lean_object* v_quantifiers_4627_; lean_object* v_body_4628_; lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4664_; 
v_env_4625_ = lean_ctor_get(v_a_4623_, 0);
lean_inc_ref(v_env_4625_);
v___x_4626_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(v_env_4625_, v_deconstructQuantifier_x3f_4621_, v_stx_4622_);
v_quantifiers_4627_ = lean_ctor_get(v___x_4626_, 0);
v_body_4628_ = lean_ctor_get(v___x_4626_, 1);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4630_ = v___x_4626_;
v_isShared_4631_ = v_isSharedCheck_4664_;
goto v_resetjp_4629_;
}
else
{
lean_inc(v_body_4628_);
lean_inc(v_quantifiers_4627_);
lean_dec(v___x_4626_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4664_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4632_ = lean_array_get_size(v_quantifiers_4627_);
v___x_4633_ = lean_unsigned_to_nat(0u);
v___x_4634_ = lean_nat_dec_eq(v___x_4632_, v___x_4633_);
if (v___x_4634_ == 0)
{
size_t v_sz_4635_; size_t v___x_4636_; lean_object* v___x_4637_; 
lean_del_object(v___x_4630_);
v_sz_4635_ = lean_array_size(v_quantifiers_4627_);
v___x_4636_ = ((size_t)0ULL);
v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_4635_, v___x_4636_, v_quantifiers_4627_, v_a_4623_, v_a_4624_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v_a_4639_; lean_object* v___x_4640_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
v_a_4639_ = lean_ctor_get(v___x_4637_, 1);
lean_inc(v_a_4639_);
lean_dec_ref_known(v___x_4637_, 2);
v___x_4640_ = l_Lean_Fmt_fmt(v_body_4628_, v_a_4623_, v_a_4639_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4650_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
v_a_4642_ = lean_ctor_get(v___x_4640_, 1);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4644_ = v___x_4640_;
v_isShared_4645_ = v_isSharedCheck_4650_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_inc(v_a_4641_);
lean_dec(v___x_4640_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4650_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4646_; lean_object* v___x_4648_; 
v___x_4646_ = l_Lean_Fmt_Layouts_quantified(v_a_4638_, v_a_4641_);
if (v_isShared_4645_ == 0)
{
lean_ctor_set(v___x_4644_, 0, v___x_4646_);
v___x_4648_ = v___x_4644_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4646_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_a_4642_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
return v___x_4648_;
}
}
}
else
{
lean_dec(v_a_4638_);
return v___x_4640_;
}
}
else
{
lean_object* v_a_4651_; lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec(v_body_4628_);
v_a_4651_ = lean_ctor_get(v___x_4637_, 0);
v_a_4652_ = lean_ctor_get(v___x_4637_, 1);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4637_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_inc(v_a_4651_);
lean_dec(v___x_4637_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4651_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v_a_4652_);
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
else
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
lean_dec(v_body_4628_);
lean_dec_ref(v_quantifiers_4627_);
v___x_4660_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4631_ == 0)
{
lean_ctor_set_tag(v___x_4630_, 1);
lean_ctor_set(v___x_4630_, 1, v_a_4624_);
lean_ctor_set(v___x_4630_, 0, v___x_4660_);
v___x_4662_ = v___x_4630_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_a_4624_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object* v_deconstructQuantifier_x3f_4665_, lean_object* v_stx_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v_res_4669_; 
v_res_4669_ = l_Lean_Fmt_fmtQuantifier(v_deconstructQuantifier_x3f_4665_, v_stx_4666_, v_a_4667_, v_a_4668_);
lean_dec_ref(v_a_4667_);
return v_res_4669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_){
_start:
{
uint8_t v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = 0;
v___x_4674_ = l_Lean_Fmt_fmtRaw(v___x_4673_, v_a_4670_, v_a_4671_, v_a_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_){
_start:
{
lean_object* v_res_4678_; 
v_res_4678_ = l_Lean_Fmt_fmtAtomic(v_a_4675_, v_a_4676_, v_a_4677_);
lean_dec_ref(v_a_4676_);
return v_res_4678_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed), 3, 0);
v___x_4686_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2));
v___x_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
lean_ctor_set(v___x_4687_, 1, v___x_4685_);
return v___x_4687_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4(void){
_start:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3);
v___x_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
return v___x_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object* v_kind_4690_){
_start:
{
lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4691_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_4692_ = lean_name_eq(v_kind_4690_, v___x_4691_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; 
v___x_4693_ = lean_box(0);
return v___x_4693_;
}
else
{
lean_object* v___x_4694_; 
v___x_4694_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4);
return v___x_4694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object* v_kind_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4695_);
lean_dec(v_kind_4695_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object* v_x_4697_, lean_object* v_x_4698_, lean_object* v_kind_4699_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4699_);
return v___x_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object* v_x_4701_, lean_object* v_x_4702_, lean_object* v_kind_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(v_x_4701_, v_x_4702_, v_kind_4703_);
lean_dec(v_kind_4703_);
lean_dec_ref(v_x_4702_);
lean_dec_ref(v_x_4701_);
return v_res_4704_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object* v_x_4710_){
_start:
{
if (lean_obj_tag(v_x_4710_) == 1)
{
lean_object* v_pre_4711_; lean_object* v_str_4712_; lean_object* v___x_4713_; uint8_t v___x_4714_; 
v_pre_4711_ = lean_ctor_get(v_x_4710_, 0);
v_str_4712_ = lean_ctor_get(v_x_4710_, 1);
v___x_4713_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0));
v___x_4714_ = lean_string_dec_eq(v_str_4712_, v___x_4713_);
if (v___x_4714_ == 0)
{
lean_object* v___x_4715_; uint8_t v___x_4716_; 
v___x_4715_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1));
v___x_4716_ = lean_string_dec_eq(v_str_4712_, v___x_4715_);
if (v___x_4716_ == 0)
{
lean_object* v___x_4717_; uint8_t v___x_4718_; 
v___x_4717_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2));
v___x_4718_ = lean_string_dec_eq(v_str_4712_, v___x_4717_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4719_; uint8_t v___x_4720_; 
v___x_4719_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3));
v___x_4720_ = lean_string_dec_eq(v_str_4712_, v___x_4719_);
if (v___x_4720_ == 0)
{
lean_object* v___x_4721_; uint8_t v___x_4722_; 
v___x_4721_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4));
v___x_4722_ = lean_string_dec_eq(v_str_4712_, v___x_4721_);
if (v___x_4722_ == 0)
{
return v___x_4722_;
}
else
{
if (lean_obj_tag(v_pre_4711_) == 0)
{
return v___x_4722_;
}
else
{
return v___x_4720_;
}
}
}
else
{
return v___x_4720_;
}
}
else
{
return v___x_4718_;
}
}
else
{
return v___x_4716_;
}
}
else
{
return v___x_4714_;
}
}
else
{
uint8_t v___x_4723_; 
v___x_4723_ = 0;
return v___x_4723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object* v_x_4724_){
_start:
{
uint8_t v_res_4725_; lean_object* v_r_4726_; 
v_res_4725_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_x_4724_);
lean_dec(v_x_4724_);
v_r_4726_ = lean_box(v_res_4725_);
return v_r_4726_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
v___x_4732_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAtomic___boxed), 3, 0);
v___x_4733_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1));
v___x_4734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4733_);
lean_ctor_set(v___x_4734_, 1, v___x_4732_);
return v___x_4734_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4735_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2);
v___x_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4735_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object* v_kind_4737_){
_start:
{
uint8_t v___x_4738_; 
v___x_4738_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_kind_4737_);
if (v___x_4738_ == 0)
{
lean_object* v___x_4739_; 
v___x_4739_ = lean_box(0);
return v___x_4739_;
}
else
{
lean_object* v___x_4740_; 
v___x_4740_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object* v_kind_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4741_);
lean_dec(v_kind_4741_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object* v_x_4743_, lean_object* v_x_4744_, lean_object* v_kind_4745_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object* v_x_4747_, lean_object* v_x_4748_, lean_object* v_kind_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(v_x_4747_, v_x_4748_, v_kind_4749_);
lean_dec(v_kind_4749_);
lean_dec_ref(v_x_4748_);
lean_dec_ref(v_x_4747_);
return v_res_4750_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4(void){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4761_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostfixOperator___boxed), 3, 0);
v___x_4762_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3));
v___x_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
lean_ctor_set(v___x_4763_, 1, v___x_4761_);
return v___x_4763_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5(void){
_start:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4);
v___x_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4764_);
return v___x_4765_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8(void){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4771_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrefixOperator___boxed), 3, 0);
v___x_4772_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7));
v___x_4773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
lean_ctor_set(v___x_4773_, 1, v___x_4771_);
return v___x_4773_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9(void){
_start:
{
lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4774_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8);
v___x_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
return v___x_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object* v_env_4776_, lean_object* v_opts_4777_, lean_object* v_kind_4778_){
_start:
{
lean_object* v___x_4779_; 
lean_inc(v_kind_4778_);
lean_inc_ref(v_env_4776_);
v___x_4779_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_4776_, v_opts_4777_, v_kind_4778_);
if (lean_obj_tag(v___x_4779_) == 1)
{
lean_object* v_val_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4790_; 
lean_dec(v_kind_4778_);
lean_dec_ref(v_env_4776_);
v_val_4780_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4782_ = v___x_4779_;
v_isShared_4783_ = v_isSharedCheck_4790_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_val_4780_);
lean_dec(v___x_4779_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4790_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4784_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1));
v___x_4785_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInfixOperator___boxed), 4, 1);
lean_closure_set(v___x_4785_, 0, v_val_4780_);
v___x_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4784_);
lean_ctor_set(v___x_4786_, 1, v___x_4785_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4786_);
v___x_4788_ = v___x_4782_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
else
{
uint8_t v___x_4791_; 
lean_dec(v___x_4779_);
lean_inc(v_kind_4778_);
lean_inc_ref(v_env_4776_);
v___x_4791_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_4776_, v_opts_4777_, v_kind_4778_);
if (v___x_4791_ == 0)
{
uint8_t v___x_4792_; 
v___x_4792_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_4776_, v_opts_4777_, v_kind_4778_);
if (v___x_4792_ == 0)
{
lean_object* v___x_4793_; 
v___x_4793_ = lean_box(0);
return v___x_4793_;
}
else
{
lean_object* v___x_4794_; 
v___x_4794_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5);
return v___x_4794_;
}
}
else
{
lean_object* v___x_4795_; 
lean_dec(v_kind_4778_);
lean_dec_ref(v_env_4776_);
v___x_4795_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9);
return v___x_4795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object* v_env_4796_, lean_object* v_opts_4797_, lean_object* v_kind_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(v_env_4796_, v_opts_4797_, v_kind_4798_);
lean_dec_ref(v_opts_4797_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object* v_env_4800_, lean_object* v_opts_4801_, lean_object* v_kind_4802_){
_start:
{
uint8_t v___x_4803_; 
v___x_4803_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_4800_, v_opts_4801_, v_kind_4802_);
if (v___x_4803_ == 0)
{
lean_object* v___x_4804_; 
v___x_4804_ = lean_box(0);
return v___x_4804_;
}
else
{
lean_object* v___x_4805_; 
v___x_4805_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object* v_env_4806_, lean_object* v_opts_4807_, lean_object* v_kind_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(v_env_4806_, v_opts_4807_, v_kind_4808_);
lean_dec_ref(v_opts_4807_);
return v_res_4809_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(lean_object* v_x_4810_, lean_object* v_x_4811_){
_start:
{
if (lean_obj_tag(v_x_4810_) == 0)
{
if (lean_obj_tag(v_x_4811_) == 0)
{
uint8_t v___x_4812_; 
v___x_4812_ = 1;
return v___x_4812_;
}
else
{
uint8_t v___x_4813_; 
v___x_4813_ = 0;
return v___x_4813_;
}
}
else
{
if (lean_obj_tag(v_x_4811_) == 0)
{
uint8_t v___x_4814_; 
v___x_4814_ = 0;
return v___x_4814_;
}
else
{
lean_object* v_val_4815_; lean_object* v_val_4816_; uint8_t v___x_4817_; 
v_val_4815_ = lean_ctor_get(v_x_4810_, 0);
v_val_4816_ = lean_ctor_get(v_x_4811_, 0);
v___x_4817_ = lean_nat_dec_eq(v_val_4815_, v_val_4816_);
return v___x_4817_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0___boxed(lean_object* v_x_4818_, lean_object* v_x_4819_){
_start:
{
uint8_t v_res_4820_; lean_object* v_r_4821_; 
v_res_4820_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v_x_4818_, v_x_4819_);
lean_dec(v_x_4819_);
lean_dec(v_x_4818_);
v_r_4821_ = lean_box(v_res_4820_);
return v_r_4821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(lean_object* v_lineInfos_4822_, lean_object* v___f_4823_, lean_object* v___f_4824_, lean_object* v_pos_4825_){
_start:
{
lean_object* v___x_4826_; 
v___x_4826_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_4822_, v_pos_4825_, v___f_4823_, v___f_4824_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v___x_4827_; 
v___x_4827_ = lean_box(0);
return v___x_4827_;
}
else
{
lean_object* v_val_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4836_; 
v_val_4828_ = lean_ctor_get(v___x_4826_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4826_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4830_ = v___x_4826_;
v_isShared_4831_ = v_isSharedCheck_4836_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_val_4828_);
lean_dec(v___x_4826_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4836_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v_fst_4832_; lean_object* v___x_4834_; 
v_fst_4832_ = lean_ctor_get(v_val_4828_, 0);
lean_inc(v_fst_4832_);
lean_dec(v_val_4828_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 0, v_fst_4832_);
v___x_4834_ = v___x_4830_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_fst_4832_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2___boxed(lean_object* v_lineInfos_4837_, lean_object* v___f_4838_, lean_object* v___f_4839_, lean_object* v_pos_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4837_, v___f_4838_, v___f_4839_, v_pos_4840_);
lean_dec_ref(v_lineInfos_4837_);
return v_res_4841_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(lean_object* v_lineInfos_4842_, lean_object* v_a_4843_, lean_object* v_b_4844_){
_start:
{
lean_object* v___f_4845_; lean_object* v___f_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; uint8_t v___x_4849_; 
v___f_4845_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_4846_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_4847_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4842_, v___f_4845_, v___f_4846_, v_a_4843_);
v___x_4848_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4842_, v___f_4845_, v___f_4846_, v_b_4844_);
v___x_4849_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v___x_4847_, v___x_4848_);
lean_dec(v___x_4848_);
lean_dec(v___x_4847_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___boxed(lean_object* v_lineInfos_4850_, lean_object* v_a_4851_, lean_object* v_b_4852_){
_start:
{
uint8_t v_res_4853_; lean_object* v_r_4854_; 
v_res_4853_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4850_, v_a_4851_, v_b_4852_);
lean_dec_ref(v_lineInfos_4850_);
v_r_4854_ = lean_box(v_res_4853_);
return v_r_4854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(lean_object* v_val_4855_, uint8_t v_opOnRhsLine_4856_, lean_object* v_val_4857_, lean_object* v_val_4858_, lean_object* v___x_4859_, uint8_t v_opOnLhsLine_4860_, lean_object* v___x_4861_, lean_object* v_as_4862_, size_t v_sz_4863_, size_t v_i_4864_, lean_object* v_b_4865_){
_start:
{
lean_object* v_a_4867_; uint8_t v___x_4871_; 
v___x_4871_ = lean_usize_dec_lt(v_i_4864_, v_sz_4863_);
if (v___x_4871_ == 0)
{
lean_dec_ref(v_val_4858_);
lean_dec_ref(v_val_4857_);
lean_dec_ref(v_val_4855_);
return v_b_4865_;
}
else
{
lean_object* v_a_4872_; uint8_t v_kind_4873_; uint8_t v_placement_4874_; lean_object* v_originalTokenRange_4875_; lean_object* v_originalWhitespaceRange_4876_; uint8_t v_originalWhitespaceKind_4877_; lean_object* v_content_4878_; uint8_t v___y_4885_; uint8_t v___y_4886_; lean_object* v___x_4891_; uint8_t v___x_4892_; uint8_t v___y_4894_; 
v_a_4872_ = lean_array_uget_borrowed(v_as_4862_, v_i_4864_);
v_kind_4873_ = lean_ctor_get_uint8(v_a_4872_, sizeof(void*)*3);
v_placement_4874_ = lean_ctor_get_uint8(v_a_4872_, sizeof(void*)*3 + 1);
v_originalTokenRange_4875_ = lean_ctor_get(v_a_4872_, 0);
v_originalWhitespaceRange_4876_ = lean_ctor_get(v_a_4872_, 1);
v_originalWhitespaceKind_4877_ = lean_ctor_get_uint8(v_a_4872_, sizeof(void*)*3 + 2);
v_content_4878_ = lean_ctor_get(v_a_4872_, 2);
v___x_4891_ = lean_unsigned_to_nat(0u);
v___x_4892_ = lean_nat_dec_eq(v___x_4859_, v___x_4891_);
if (v_placement_4874_ == 0)
{
lean_object* v___x_4895_; uint8_t v___x_4896_; 
v___x_4895_ = lean_unsigned_to_nat(3u);
v___x_4896_ = lean_nat_dec_eq(v___x_4861_, v___x_4895_);
v___y_4894_ = v___x_4896_;
goto v___jp_4893_;
}
else
{
v___y_4894_ = v___x_4892_;
goto v___jp_4893_;
}
v___jp_4879_:
{
uint8_t v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4880_ = 1;
lean_inc_ref(v_content_4878_);
lean_inc_ref(v_originalWhitespaceRange_4876_);
lean_inc_ref(v_originalTokenRange_4875_);
v___x_4881_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_4881_, 0, v_originalTokenRange_4875_);
lean_ctor_set(v___x_4881_, 1, v_originalWhitespaceRange_4876_);
lean_ctor_set(v___x_4881_, 2, v_content_4878_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*3, v_kind_4873_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*3 + 1, v___x_4880_);
lean_ctor_set_uint8(v___x_4881_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_4877_);
lean_inc_ref(v_val_4855_);
v___x_4882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4881_);
lean_ctor_set(v___x_4882_, 1, v_val_4855_);
v___x_4883_ = lean_array_push(v_b_4865_, v___x_4882_);
v_a_4867_ = v___x_4883_;
goto v___jp_4866_;
}
v___jp_4884_:
{
if (v___y_4886_ == 0)
{
if (v___y_4885_ == 0)
{
goto v___jp_4879_;
}
else
{
if (v_opOnRhsLine_4856_ == 0)
{
goto v___jp_4879_;
}
else
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
lean_inc_ref(v_val_4857_);
lean_inc(v_a_4872_);
v___x_4887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4887_, 0, v_a_4872_);
lean_ctor_set(v___x_4887_, 1, v_val_4857_);
v___x_4888_ = lean_array_push(v_b_4865_, v___x_4887_);
v_a_4867_ = v___x_4888_;
goto v___jp_4866_;
}
}
}
else
{
if (v_opOnRhsLine_4856_ == 0)
{
lean_object* v___x_4889_; lean_object* v___x_4890_; 
lean_inc_ref(v_val_4858_);
lean_inc(v_a_4872_);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v_a_4872_);
lean_ctor_set(v___x_4889_, 1, v_val_4858_);
v___x_4890_ = lean_array_push(v_b_4865_, v___x_4889_);
v_a_4867_ = v___x_4890_;
goto v___jp_4866_;
}
else
{
v_a_4867_ = v_b_4865_;
goto v___jp_4866_;
}
}
}
v___jp_4893_:
{
if (v___y_4894_ == 0)
{
v___y_4885_ = v___y_4894_;
v___y_4886_ = v___x_4892_;
goto v___jp_4884_;
}
else
{
v___y_4885_ = v___y_4894_;
v___y_4886_ = v_opOnLhsLine_4860_;
goto v___jp_4884_;
}
}
}
v___jp_4866_:
{
size_t v___x_4868_; size_t v___x_4869_; 
v___x_4868_ = ((size_t)1ULL);
v___x_4869_ = lean_usize_add(v_i_4864_, v___x_4868_);
v_i_4864_ = v___x_4869_;
v_b_4865_ = v_a_4867_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0___boxed(lean_object* v_val_4897_, lean_object* v_opOnRhsLine_4898_, lean_object* v_val_4899_, lean_object* v_val_4900_, lean_object* v___x_4901_, lean_object* v_opOnLhsLine_4902_, lean_object* v___x_4903_, lean_object* v_as_4904_, lean_object* v_sz_4905_, lean_object* v_i_4906_, lean_object* v_b_4907_){
_start:
{
uint8_t v_opOnRhsLine_boxed_4908_; uint8_t v_opOnLhsLine_boxed_4909_; size_t v_sz_boxed_4910_; size_t v_i_boxed_4911_; lean_object* v_res_4912_; 
v_opOnRhsLine_boxed_4908_ = lean_unbox(v_opOnRhsLine_4898_);
v_opOnLhsLine_boxed_4909_ = lean_unbox(v_opOnLhsLine_4902_);
v_sz_boxed_4910_ = lean_unbox_usize(v_sz_4905_);
lean_dec(v_sz_4905_);
v_i_boxed_4911_ = lean_unbox_usize(v_i_4906_);
lean_dec(v_i_4906_);
v_res_4912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_4897_, v_opOnRhsLine_boxed_4908_, v_val_4899_, v_val_4900_, v___x_4901_, v_opOnLhsLine_boxed_4909_, v___x_4903_, v_as_4904_, v_sz_boxed_4910_, v_i_boxed_4911_, v_b_4907_);
lean_dec_ref(v_as_4904_);
lean_dec(v___x_4903_);
lean_dec(v___x_4901_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector(lean_object* v_ctx_4915_, lean_object* v_stx_4916_){
_start:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; uint8_t v___x_4921_; 
v___x_4919_ = l_Lean_Syntax_getNumArgs(v_stx_4916_);
v___x_4920_ = lean_unsigned_to_nat(3u);
v___x_4921_ = lean_nat_dec_eq(v___x_4919_, v___x_4920_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; 
lean_dec(v___x_4919_);
lean_dec(v_stx_4916_);
lean_dec_ref(v_ctx_4915_);
v___x_4922_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4922_;
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4924_; uint8_t v___x_4925_; 
v___x_4923_ = lean_unsigned_to_nat(1u);
v___x_4924_ = l_Lean_Syntax_getArg(v_stx_4916_, v___x_4923_);
v___x_4925_ = l_Lean_Syntax_isAtom(v___x_4924_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; 
lean_dec(v___x_4924_);
lean_dec(v___x_4919_);
lean_dec(v_stx_4916_);
lean_dec_ref(v_ctx_4915_);
v___x_4926_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4926_;
}
else
{
lean_object* v_env_4927_; lean_object* v_opts_4928_; lean_object* v_lineInfos_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; 
v_env_4927_ = lean_ctor_get(v_ctx_4915_, 0);
v_opts_4928_ = lean_ctor_get(v_ctx_4915_, 1);
v_lineInfos_4929_ = lean_ctor_get(v_ctx_4915_, 2);
lean_inc_ref(v_lineInfos_4929_);
v___x_4930_ = lean_unsigned_to_nat(0u);
v___x_4931_ = l_Lean_Syntax_getArg(v_stx_4916_, v___x_4930_);
v___x_4932_ = lean_unsigned_to_nat(2u);
v___x_4933_ = l_Lean_Syntax_getArg(v_stx_4916_, v___x_4932_);
v___x_4934_ = l_Lean_Syntax_getKind(v_stx_4916_);
lean_inc_ref(v_env_4927_);
v___x_4935_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_4927_, v_opts_4928_, v___x_4934_);
if (lean_obj_tag(v___x_4935_) == 0)
{
lean_object* v___x_4936_; 
lean_dec(v___x_4933_);
lean_dec(v___x_4931_);
lean_dec_ref(v_lineInfos_4929_);
lean_dec(v___x_4924_);
lean_dec(v___x_4919_);
lean_dec_ref(v_ctx_4915_);
v___x_4936_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4936_;
}
else
{
lean_object* v_comments_4937_; lean_object* v___x_4938_; uint8_t v___x_4939_; 
lean_dec_ref_known(v___x_4935_, 1);
v_comments_4937_ = l_Lean_Fmt_CommentCollector_Context_trailingComments(v_ctx_4915_, v___x_4924_);
lean_dec_ref(v_ctx_4915_);
v___x_4938_ = lean_array_get_size(v_comments_4937_);
v___x_4939_ = lean_nat_dec_eq(v___x_4938_, v___x_4930_);
if (v___x_4939_ == 0)
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
v___x_4940_ = l_Lean_Syntax_getTailInfo(v___x_4931_);
lean_dec(v___x_4931_);
v___x_4941_ = l_Lean_SourceInfo_getRange_x3f(v___x_4939_, v___x_4940_);
lean_dec(v___x_4940_);
v___x_4942_ = l_Lean_Syntax_getRange_x3f(v___x_4924_, v___x_4939_);
lean_dec(v___x_4924_);
if (lean_obj_tag(v___x_4941_) == 1)
{
if (lean_obj_tag(v___x_4942_) == 1)
{
lean_object* v_val_4943_; lean_object* v_val_4944_; lean_object* v___x_4945_; 
v_val_4943_ = lean_ctor_get(v___x_4941_, 0);
lean_inc(v_val_4943_);
lean_dec_ref_known(v___x_4941_, 1);
v_val_4944_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_val_4944_);
lean_dec_ref_known(v___x_4942_, 1);
v___x_4945_ = l_Lean_Syntax_getPos_x3f(v___x_4933_, v___x_4939_);
if (lean_obj_tag(v___x_4945_) == 1)
{
lean_object* v_val_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v_val_4946_ = lean_ctor_get(v___x_4945_, 0);
lean_inc(v_val_4946_);
lean_dec_ref_known(v___x_4945_, 1);
v___x_4947_ = l_Lean_Syntax_getTailInfo(v___x_4933_);
lean_dec(v___x_4933_);
v___x_4948_ = l_Lean_SourceInfo_getRange_x3f(v___x_4939_, v___x_4947_);
lean_dec(v___x_4947_);
if (lean_obj_tag(v___x_4948_) == 1)
{
lean_object* v_val_4949_; lean_object* v_stop_4950_; lean_object* v_start_4951_; lean_object* v_stop_4952_; uint8_t v_opOnLhsLine_4953_; uint8_t v_opOnRhsLine_4954_; lean_object* v_r_4955_; size_t v_sz_4956_; size_t v___x_4957_; lean_object* v___x_4958_; 
v_val_4949_ = lean_ctor_get(v___x_4948_, 0);
lean_inc(v_val_4949_);
lean_dec_ref_known(v___x_4948_, 1);
v_stop_4950_ = lean_ctor_get(v_val_4943_, 1);
v_start_4951_ = lean_ctor_get(v_val_4944_, 0);
v_stop_4952_ = lean_ctor_get(v_val_4944_, 1);
lean_inc(v_start_4951_);
lean_inc(v_stop_4950_);
v_opOnLhsLine_4953_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4929_, v_stop_4950_, v_start_4951_);
lean_inc(v_stop_4952_);
v_opOnRhsLine_4954_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4929_, v_stop_4952_, v_val_4946_);
lean_dec_ref(v_lineInfos_4929_);
v_r_4955_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
v_sz_4956_ = lean_array_size(v_comments_4937_);
v___x_4957_ = ((size_t)0ULL);
v___x_4958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_4944_, v_opOnRhsLine_4954_, v_val_4949_, v_val_4943_, v___x_4938_, v_opOnLhsLine_4953_, v___x_4919_, v_comments_4937_, v_sz_4956_, v___x_4957_, v_r_4955_);
lean_dec_ref(v_comments_4937_);
lean_dec(v___x_4919_);
return v___x_4958_;
}
else
{
lean_dec(v___x_4948_);
lean_dec(v_val_4946_);
lean_dec(v_val_4944_);
lean_dec(v_val_4943_);
lean_dec_ref(v_comments_4937_);
lean_dec_ref(v_lineInfos_4929_);
lean_dec(v___x_4919_);
goto v___jp_4917_;
}
}
else
{
lean_dec(v___x_4945_);
lean_dec(v_val_4944_);
lean_dec(v_val_4943_);
lean_dec_ref(v_comments_4937_);
lean_dec(v___x_4933_);
lean_dec_ref(v_lineInfos_4929_);
lean_dec(v___x_4919_);
goto v___jp_4917_;
}
}
else
{
lean_dec_ref_known(v___x_4941_, 1);
lean_dec(v___x_4942_);
lean_dec_ref(v_comments_4937_);
lean_dec(v___x_4933_);
lean_dec_ref(v_lineInfos_4929_);
lean_dec(v___x_4919_);
goto v___jp_4917_;
}
}
else
{
lean_dec(v___x_4942_);
lean_dec(v___x_4941_);
lean_dec_ref(v_comments_4937_);
lean_dec(v___x_4933_);
lean_dec_ref(v_lineInfos_4929_);
lean_dec(v___x_4919_);
goto v___jp_4917_;
}
}
else
{
lean_object* v___x_4959_; 
lean_dec_ref(v_comments_4937_);
lean_dec(v___x_4933_);
lean_dec(v___x_4931_);
lean_dec_ref(v_lineInfos_4929_);
lean_dec(v___x_4924_);
lean_dec(v___x_4919_);
v___x_4959_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4959_;
}
}
}
}
v___jp_4917_:
{
lean_object* v___x_4918_; 
v___x_4918_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_){
_start:
{
lean_object* v___x_4964_; 
lean_inc_ref(v___y_4962_);
v___x_4964_ = lean_apply_3(v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
lean_dec_ref(v___y_4967_);
return v_res_4969_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___f_4972_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4973_ = l_Lean_Fmt_fmtAttribute;
v___x_4974_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4974_, 0, lean_box(0));
lean_closure_set(v___x_4974_, 1, v___x_4973_);
lean_closure_set(v___x_4974_, 2, v___f_4972_);
return v___x_4974_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___f_4975_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4976_ = l_Lean_Fmt_infixFmtAttribute;
v___x_4977_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4977_, 0, lean_box(0));
lean_closure_set(v___x_4977_, 1, v___x_4976_);
lean_closure_set(v___x_4977_, 2, v___f_4975_);
return v___x_4977_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___x_4979_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4980_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_4981_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4981_, 0, lean_box(0));
lean_closure_set(v___x_4981_, 1, v___x_4980_);
lean_closure_set(v___x_4981_, 2, v___x_4979_);
return v___x_4981_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4983_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4984_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_4985_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4985_, 0, lean_box(0));
lean_closure_set(v___x_4985_, 1, v___x_4984_);
lean_closure_set(v___x_4985_, 2, v___x_4983_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4987_ = lean_unsigned_to_nat(1100u);
v___x_4988_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed), 3, 0);
v___x_4989_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4987_, v___x_4988_);
if (lean_obj_tag(v___x_4989_) == 0)
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
lean_dec_ref_known(v___x_4989_, 1);
v___x_4990_ = lean_unsigned_to_nat(1000u);
v___x_4991_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_4992_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4990_, v___x_4991_);
if (lean_obj_tag(v___x_4992_) == 0)
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_dec_ref_known(v___x_4992_, 1);
v___x_4993_ = lean_unsigned_to_nat(900u);
v___x_4994_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed), 3, 0);
v___x_4995_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4993_, v___x_4994_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
lean_dec_ref_known(v___x_4995_, 1);
v___x_4996_ = lean_unsigned_to_nat(800u);
v___x_4997_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_4998_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4996_, v___x_4997_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_dec_ref_known(v___x_4998_, 1);
v___x_4999_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5000_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4996_, v___x_4999_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
lean_dec_ref_known(v___x_5000_, 1);
v___x_5001_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5002_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4996_, v___x_5001_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
lean_dec_ref_known(v___x_5002_, 1);
v___x_5003_ = lean_unsigned_to_nat(600u);
v___x_5004_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed), 3, 0);
v___x_5005_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5003_, v___x_5004_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
lean_dec_ref_known(v___x_5005_, 1);
v___x_5006_ = lean_unsigned_to_nat(400u);
v___x_5007_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed), 3, 0);
v___x_5008_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5006_, v___x_5007_);
return v___x_5008_;
}
else
{
return v___x_5005_;
}
}
else
{
return v___x_5002_;
}
}
else
{
return v___x_5000_;
}
}
else
{
return v___x_4998_;
}
}
else
{
return v___x_4995_;
}
}
else
{
return v___x_4992_;
}
}
else
{
return v___x_4989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v_a_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_();
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5012_ = lean_unsigned_to_nat(500u);
v___x_5013_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector), 2, 0);
v___x_5014_ = l_Lean_Fmt_addBuiltinCommentCollector(v___x_5012_, v___x_5013_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2____boxed(lean_object* v_a_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_();
return v_res_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object* v_stx_x3f_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5017_) == 1)
{
lean_object* v_val_5020_; lean_object* v___x_5021_; 
v_val_5020_ = lean_ctor_get(v_stx_x3f_5017_, 0);
lean_inc(v_val_5020_);
lean_dec_ref_known(v_stx_x3f_5017_, 1);
v___x_5021_ = l_Lean_Fmt_fmt(v_val_5020_, v_a_5018_, v_a_5019_);
return v___x_5021_;
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
lean_dec(v_stx_x3f_5017_);
v___x_5022_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5022_);
lean_ctor_set(v___x_5023_, 1, v_a_5019_);
return v___x_5023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object* v_stx_x3f_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l_Lean_Fmt_fmt_x3f(v_stx_x3f_5024_, v_a_5025_, v_a_5026_);
lean_dec_ref(v_a_5025_);
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object* v_f_5028_, lean_object* v_formatterName_5029_, lean_object* v_stx_x3f_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5030_) == 1)
{
lean_object* v_val_5033_; lean_object* v___x_5034_; 
v_val_5033_ = lean_ctor_get(v_stx_x3f_5030_, 0);
lean_inc(v_val_5033_);
lean_dec_ref_known(v_stx_x3f_5030_, 1);
v___x_5034_ = l_Lean_Fmt_fmtWith(v_f_5028_, v_formatterName_5029_, v_val_5033_, v_a_5031_, v_a_5032_);
return v___x_5034_;
}
else
{
lean_object* v___x_5035_; lean_object* v___x_5036_; 
lean_dec(v_stx_x3f_5030_);
lean_dec(v_formatterName_5029_);
lean_dec_ref(v_f_5028_);
v___x_5035_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5035_);
lean_ctor_set(v___x_5036_, 1, v_a_5032_);
return v___x_5036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object* v_f_5037_, lean_object* v_formatterName_5038_, lean_object* v_stx_x3f_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l_Lean_Fmt_fmtWith_x3f(v_f_5037_, v_formatterName_5038_, v_stx_x3f_5039_, v_a_5040_, v_a_5041_);
lean_dec_ref(v_a_5040_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object* v_array_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_){
_start:
{
size_t v_sz_5046_; size_t v___x_5047_; lean_object* v___x_5048_; 
v_sz_5046_ = lean_array_size(v_array_5043_);
v___x_5047_ = ((size_t)0ULL);
v___x_5048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5046_, v___x_5047_, v_array_5043_, v_a_5044_, v_a_5045_);
return v___x_5048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object* v_array_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l_Lean_Fmt_fmtArray___redArg(v_array_5049_, v_a_5050_, v_a_5051_);
lean_dec_ref(v_a_5050_);
return v_res_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object* v_ks_5053_, lean_object* v_array_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Fmt_fmtArray___redArg(v_array_5054_, v_a_5055_, v_a_5056_);
return v___x_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object* v_ks_5058_, lean_object* v_array_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Fmt_fmtArray(v_ks_5058_, v_array_5059_, v_a_5060_, v_a_5061_);
lean_dec_ref(v_a_5060_);
lean_dec(v_ks_5058_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object* v_f_5063_, lean_object* v_formatterName_5064_, size_t v_sz_5065_, size_t v_i_5066_, lean_object* v_bs_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
uint8_t v___x_5070_; 
v___x_5070_ = lean_usize_dec_lt(v_i_5066_, v_sz_5065_);
if (v___x_5070_ == 0)
{
lean_object* v___x_5071_; 
lean_dec(v_formatterName_5064_);
lean_dec_ref(v_f_5063_);
v___x_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5071_, 0, v_bs_5067_);
lean_ctor_set(v___x_5071_, 1, v___y_5069_);
return v___x_5071_;
}
else
{
lean_object* v_v_5072_; lean_object* v___x_5073_; 
v_v_5072_ = lean_array_uget_borrowed(v_bs_5067_, v_i_5066_);
lean_inc(v_v_5072_);
lean_inc(v_formatterName_5064_);
lean_inc_ref(v_f_5063_);
v___x_5073_ = l_Lean_Fmt_fmtWith(v_f_5063_, v_formatterName_5064_, v_v_5072_, v___y_5068_, v___y_5069_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_object* v_a_5074_; lean_object* v_a_5075_; lean_object* v___x_5076_; lean_object* v_bs_x27_5077_; size_t v___x_5078_; size_t v___x_5079_; lean_object* v___x_5080_; 
v_a_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_a_5074_);
v_a_5075_ = lean_ctor_get(v___x_5073_, 1);
lean_inc(v_a_5075_);
lean_dec_ref_known(v___x_5073_, 2);
v___x_5076_ = lean_unsigned_to_nat(0u);
v_bs_x27_5077_ = lean_array_uset(v_bs_5067_, v_i_5066_, v___x_5076_);
v___x_5078_ = ((size_t)1ULL);
v___x_5079_ = lean_usize_add(v_i_5066_, v___x_5078_);
v___x_5080_ = lean_array_uset(v_bs_x27_5077_, v_i_5066_, v_a_5074_);
v_i_5066_ = v___x_5079_;
v_bs_5067_ = v___x_5080_;
v___y_5069_ = v_a_5075_;
goto _start;
}
else
{
lean_object* v_a_5082_; lean_object* v_a_5083_; lean_object* v___x_5085_; uint8_t v_isShared_5086_; uint8_t v_isSharedCheck_5090_; 
lean_dec_ref(v_bs_5067_);
lean_dec(v_formatterName_5064_);
lean_dec_ref(v_f_5063_);
v_a_5082_ = lean_ctor_get(v___x_5073_, 0);
v_a_5083_ = lean_ctor_get(v___x_5073_, 1);
v_isSharedCheck_5090_ = !lean_is_exclusive(v___x_5073_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5085_ = v___x_5073_;
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
else
{
lean_inc(v_a_5083_);
lean_inc(v_a_5082_);
lean_dec(v___x_5073_);
v___x_5085_ = lean_box(0);
v_isShared_5086_ = v_isSharedCheck_5090_;
goto v_resetjp_5084_;
}
v_resetjp_5084_:
{
lean_object* v___x_5088_; 
if (v_isShared_5086_ == 0)
{
v___x_5088_ = v___x_5085_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v_a_5082_);
lean_ctor_set(v_reuseFailAlloc_5089_, 1, v_a_5083_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object* v_f_5091_, lean_object* v_formatterName_5092_, lean_object* v_sz_5093_, lean_object* v_i_5094_, lean_object* v_bs_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
size_t v_sz_boxed_5098_; size_t v_i_boxed_5099_; lean_object* v_res_5100_; 
v_sz_boxed_5098_ = lean_unbox_usize(v_sz_5093_);
lean_dec(v_sz_5093_);
v_i_boxed_5099_ = lean_unbox_usize(v_i_5094_);
lean_dec(v_i_5094_);
v_res_5100_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5091_, v_formatterName_5092_, v_sz_boxed_5098_, v_i_boxed_5099_, v_bs_5095_, v___y_5096_, v___y_5097_);
lean_dec_ref(v___y_5096_);
return v_res_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object* v_f_5101_, lean_object* v_formatterName_5102_, lean_object* v_array_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
size_t v_sz_5106_; size_t v___x_5107_; lean_object* v___x_5108_; 
v_sz_5106_ = lean_array_size(v_array_5103_);
v___x_5107_ = ((size_t)0ULL);
v___x_5108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5101_, v_formatterName_5102_, v_sz_5106_, v___x_5107_, v_array_5103_, v_a_5104_, v_a_5105_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object* v_f_5109_, lean_object* v_formatterName_5110_, lean_object* v_array_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5109_, v_formatterName_5110_, v_array_5111_, v_a_5112_, v_a_5113_);
lean_dec_ref(v_a_5112_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object* v_ks_5115_, lean_object* v_f_5116_, lean_object* v_formatterName_5117_, lean_object* v_array_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_){
_start:
{
lean_object* v___x_5121_; 
v___x_5121_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5116_, v_formatterName_5117_, v_array_5118_, v_a_5119_, v_a_5120_);
return v___x_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object* v_ks_5122_, lean_object* v_f_5123_, lean_object* v_formatterName_5124_, lean_object* v_array_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v_res_5128_; 
v_res_5128_ = l_Lean_Fmt_fmtArrayWith(v_ks_5122_, v_f_5123_, v_formatterName_5124_, v_array_5125_, v_a_5126_, v_a_5127_);
lean_dec_ref(v_a_5126_);
lean_dec(v_ks_5122_);
return v_res_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object* v_sepArray_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_){
_start:
{
size_t v_sz_5132_; size_t v___x_5133_; lean_object* v___x_5134_; 
v_sz_5132_ = lean_array_size(v_sepArray_5129_);
v___x_5133_ = ((size_t)0ULL);
v___x_5134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5132_, v___x_5133_, v_sepArray_5129_, v_a_5130_, v_a_5131_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
v_a_5136_ = lean_ctor_get(v___x_5134_, 1);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5134_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_inc(v_a_5135_);
lean_dec(v___x_5134_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5135_);
lean_ctor_set(v_reuseFailAlloc_5142_, 1, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
else
{
lean_object* v_a_5144_; lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
v_a_5144_ = lean_ctor_get(v___x_5134_, 0);
v_a_5145_ = lean_ctor_get(v___x_5134_, 1);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5134_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_inc(v_a_5144_);
lean_dec(v___x_5134_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5144_);
lean_ctor_set(v_reuseFailAlloc_5151_, 1, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object* v_sepArray_5153_, lean_object* v_a_5154_, lean_object* v_a_5155_){
_start:
{
lean_object* v_res_5156_; 
v_res_5156_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5153_, v_a_5154_, v_a_5155_);
lean_dec_ref(v_a_5154_);
return v_res_5156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object* v_sep_5157_, lean_object* v_sepArray_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_){
_start:
{
lean_object* v___x_5161_; 
v___x_5161_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5158_, v_a_5159_, v_a_5160_);
return v___x_5161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object* v_sep_5162_, lean_object* v_sepArray_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_){
_start:
{
lean_object* v_res_5166_; 
v_res_5166_ = l_Lean_Fmt_fmtSepArray(v_sep_5162_, v_sepArray_5163_, v_a_5164_, v_a_5165_);
lean_dec_ref(v_a_5164_);
lean_dec_ref(v_sep_5162_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object* v_f_5167_, lean_object* v_formatterName_5168_, size_t v_sz_5169_, size_t v_i_5170_, lean_object* v_bs_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_){
_start:
{
uint8_t v___x_5174_; 
v___x_5174_ = lean_usize_dec_lt(v_i_5170_, v_sz_5169_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; 
lean_dec(v_formatterName_5168_);
lean_dec_ref(v_f_5167_);
v___x_5175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5175_, 0, v_bs_5171_);
lean_ctor_set(v___x_5175_, 1, v___y_5173_);
return v___x_5175_;
}
else
{
lean_object* v_v_5176_; lean_object* v___x_5177_; lean_object* v_bs_x27_5178_; lean_object* v___y_5180_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; uint8_t v___x_5199_; 
v_v_5176_ = lean_array_uget(v_bs_5171_, v_i_5170_);
v___x_5177_ = lean_unsigned_to_nat(0u);
v_bs_x27_5178_ = lean_array_uset(v_bs_5171_, v_i_5170_, v___x_5177_);
v___x_5196_ = lean_usize_to_nat(v_i_5170_);
v___x_5197_ = lean_unsigned_to_nat(2u);
v___x_5198_ = lean_nat_mod(v___x_5196_, v___x_5197_);
lean_dec(v___x_5196_);
v___x_5199_ = lean_nat_dec_eq(v___x_5198_, v___x_5177_);
lean_dec(v___x_5198_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; 
v___x_5200_ = l_Lean_Fmt_fmt(v_v_5176_, v___y_5172_, v___y_5173_);
v___y_5180_ = v___x_5200_;
goto v___jp_5179_;
}
else
{
lean_object* v___x_5201_; 
lean_inc(v_formatterName_5168_);
lean_inc_ref(v_f_5167_);
v___x_5201_ = l_Lean_Fmt_fmtWith(v_f_5167_, v_formatterName_5168_, v_v_5176_, v___y_5172_, v___y_5173_);
v___y_5180_ = v___x_5201_;
goto v___jp_5179_;
}
v___jp_5179_:
{
if (lean_obj_tag(v___y_5180_) == 0)
{
lean_object* v_a_5181_; lean_object* v_a_5182_; size_t v___x_5183_; size_t v___x_5184_; lean_object* v___x_5185_; 
v_a_5181_ = lean_ctor_get(v___y_5180_, 0);
lean_inc(v_a_5181_);
v_a_5182_ = lean_ctor_get(v___y_5180_, 1);
lean_inc(v_a_5182_);
lean_dec_ref_known(v___y_5180_, 2);
v___x_5183_ = ((size_t)1ULL);
v___x_5184_ = lean_usize_add(v_i_5170_, v___x_5183_);
v___x_5185_ = lean_array_uset(v_bs_x27_5178_, v_i_5170_, v_a_5181_);
v_i_5170_ = v___x_5184_;
v_bs_5171_ = v___x_5185_;
v___y_5173_ = v_a_5182_;
goto _start;
}
else
{
lean_object* v_a_5187_; lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
lean_dec_ref(v_bs_x27_5178_);
lean_dec(v_formatterName_5168_);
lean_dec_ref(v_f_5167_);
v_a_5187_ = lean_ctor_get(v___y_5180_, 0);
v_a_5188_ = lean_ctor_get(v___y_5180_, 1);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___y_5180_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___y_5180_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_inc(v_a_5187_);
lean_dec(v___y_5180_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5187_);
lean_ctor_set(v_reuseFailAlloc_5194_, 1, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object* v_f_5202_, lean_object* v_formatterName_5203_, lean_object* v_sz_5204_, lean_object* v_i_5205_, lean_object* v_bs_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
size_t v_sz_boxed_5209_; size_t v_i_boxed_5210_; lean_object* v_res_5211_; 
v_sz_boxed_5209_ = lean_unbox_usize(v_sz_5204_);
lean_dec(v_sz_5204_);
v_i_boxed_5210_ = lean_unbox_usize(v_i_5205_);
lean_dec(v_i_5205_);
v_res_5211_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5202_, v_formatterName_5203_, v_sz_boxed_5209_, v_i_boxed_5210_, v_bs_5206_, v___y_5207_, v___y_5208_);
lean_dec_ref(v___y_5207_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object* v_f_5212_, lean_object* v_formatterName_5213_, lean_object* v_sepArray_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_){
_start:
{
size_t v_sz_5217_; size_t v___x_5218_; lean_object* v___x_5219_; 
v_sz_5217_ = lean_array_size(v_sepArray_5214_);
v___x_5218_ = ((size_t)0ULL);
v___x_5219_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5212_, v_formatterName_5213_, v_sz_5217_, v___x_5218_, v_sepArray_5214_, v_a_5215_, v_a_5216_);
if (lean_obj_tag(v___x_5219_) == 0)
{
lean_object* v_a_5220_; lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
v_a_5221_ = lean_ctor_get(v___x_5219_, 1);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5219_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_inc(v_a_5220_);
lean_dec(v___x_5219_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5220_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
else
{
lean_object* v_a_5229_; lean_object* v_a_5230_; lean_object* v___x_5232_; uint8_t v_isShared_5233_; uint8_t v_isSharedCheck_5237_; 
v_a_5229_ = lean_ctor_get(v___x_5219_, 0);
v_a_5230_ = lean_ctor_get(v___x_5219_, 1);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5232_ = v___x_5219_;
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
else
{
lean_inc(v_a_5230_);
lean_inc(v_a_5229_);
lean_dec(v___x_5219_);
v___x_5232_ = lean_box(0);
v_isShared_5233_ = v_isSharedCheck_5237_;
goto v_resetjp_5231_;
}
v_resetjp_5231_:
{
lean_object* v___x_5235_; 
if (v_isShared_5233_ == 0)
{
v___x_5235_ = v___x_5232_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5229_);
lean_ctor_set(v_reuseFailAlloc_5236_, 1, v_a_5230_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object* v_f_5238_, lean_object* v_formatterName_5239_, lean_object* v_sepArray_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_){
_start:
{
lean_object* v_res_5243_; 
v_res_5243_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5238_, v_formatterName_5239_, v_sepArray_5240_, v_a_5241_, v_a_5242_);
lean_dec_ref(v_a_5241_);
return v_res_5243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object* v_sep_5244_, lean_object* v_f_5245_, lean_object* v_formatterName_5246_, lean_object* v_sepArray_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v___x_5250_; 
v___x_5250_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5245_, v_formatterName_5246_, v_sepArray_5247_, v_a_5248_, v_a_5249_);
return v___x_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object* v_sep_5251_, lean_object* v_f_5252_, lean_object* v_formatterName_5253_, lean_object* v_sepArray_5254_, lean_object* v_a_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_Lean_Fmt_fmtSepArrayWith(v_sep_5251_, v_f_5252_, v_formatterName_5253_, v_sepArray_5254_, v_a_5255_, v_a_5256_);
lean_dec_ref(v_a_5255_);
lean_dec_ref(v_sep_5251_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object* v_f_5258_, lean_object* v_formatterName_5259_, lean_object* v_as_5260_, size_t v_sz_5261_, size_t v_i_5262_, lean_object* v_bs_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
lean_object* v___x_5266_; 
v___x_5266_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5258_, v_formatterName_5259_, v_sz_5261_, v_i_5262_, v_bs_5263_, v___y_5264_, v___y_5265_);
return v___x_5266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object* v_f_5267_, lean_object* v_formatterName_5268_, lean_object* v_as_5269_, lean_object* v_sz_5270_, lean_object* v_i_5271_, lean_object* v_bs_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
size_t v_sz_boxed_5275_; size_t v_i_boxed_5276_; lean_object* v_res_5277_; 
v_sz_boxed_5275_ = lean_unbox_usize(v_sz_5270_);
lean_dec(v_sz_5270_);
v_i_boxed_5276_ = lean_unbox_usize(v_i_5271_);
lean_dec(v_i_5271_);
v_res_5277_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(v_f_5267_, v_formatterName_5268_, v_as_5269_, v_sz_boxed_5275_, v_i_boxed_5276_, v_bs_5272_, v___y_5273_, v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec_ref(v_as_5269_);
return v_res_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object* v_sepArray_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
size_t v_sz_5281_; size_t v___x_5282_; lean_object* v___x_5283_; 
v_sz_5281_ = lean_array_size(v_sepArray_5278_);
v___x_5282_ = ((size_t)0ULL);
v___x_5283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5281_, v___x_5282_, v_sepArray_5278_, v_a_5279_, v_a_5280_);
if (lean_obj_tag(v___x_5283_) == 0)
{
lean_object* v_a_5284_; lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
v_a_5285_ = lean_ctor_get(v___x_5283_, 1);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5283_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_inc(v_a_5284_);
lean_dec(v___x_5283_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5284_);
lean_ctor_set(v_reuseFailAlloc_5291_, 1, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
else
{
lean_object* v_a_5293_; lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5301_; 
v_a_5293_ = lean_ctor_get(v___x_5283_, 0);
v_a_5294_ = lean_ctor_get(v___x_5283_, 1);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5283_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5296_ = v___x_5283_;
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_inc(v_a_5293_);
lean_dec(v___x_5283_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5299_; 
if (v_isShared_5297_ == 0)
{
v___x_5299_ = v___x_5296_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5293_);
lean_ctor_set(v_reuseFailAlloc_5300_, 1, v_a_5294_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object* v_sepArray_5302_, lean_object* v_a_5303_, lean_object* v_a_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5302_, v_a_5303_, v_a_5304_);
lean_dec_ref(v_a_5303_);
return v_res_5305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object* v_ks_5306_, lean_object* v_sep_5307_, lean_object* v_sepArray_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_){
_start:
{
lean_object* v___x_5311_; 
v___x_5311_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5308_, v_a_5309_, v_a_5310_);
return v___x_5311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object* v_ks_5312_, lean_object* v_sep_5313_, lean_object* v_sepArray_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_){
_start:
{
lean_object* v_res_5317_; 
v_res_5317_ = l_Lean_Fmt_fmtTSepArray(v_ks_5312_, v_sep_5313_, v_sepArray_5314_, v_a_5315_, v_a_5316_);
lean_dec_ref(v_a_5315_);
lean_dec_ref(v_sep_5313_);
lean_dec(v_ks_5312_);
return v_res_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object* v_f_5318_, lean_object* v_formatterName_5319_, lean_object* v_sepArray_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_){
_start:
{
size_t v_sz_5323_; size_t v___x_5324_; lean_object* v___x_5325_; 
v_sz_5323_ = lean_array_size(v_sepArray_5320_);
v___x_5324_ = ((size_t)0ULL);
v___x_5325_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5318_, v_formatterName_5319_, v_sz_5323_, v___x_5324_, v_sepArray_5320_, v_a_5321_, v_a_5322_);
if (lean_obj_tag(v___x_5325_) == 0)
{
lean_object* v_a_5326_; lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5334_; 
v_a_5326_ = lean_ctor_get(v___x_5325_, 0);
v_a_5327_ = lean_ctor_get(v___x_5325_, 1);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___x_5325_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_inc(v_a_5326_);
lean_dec(v___x_5325_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
if (v_isShared_5330_ == 0)
{
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5326_);
lean_ctor_set(v_reuseFailAlloc_5333_, 1, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
else
{
lean_object* v_a_5335_; lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
v_a_5335_ = lean_ctor_get(v___x_5325_, 0);
v_a_5336_ = lean_ctor_get(v___x_5325_, 1);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5325_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_inc(v_a_5335_);
lean_dec(v___x_5325_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5335_);
lean_ctor_set(v_reuseFailAlloc_5342_, 1, v_a_5336_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object* v_f_5344_, lean_object* v_formatterName_5345_, lean_object* v_sepArray_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_){
_start:
{
lean_object* v_res_5349_; 
v_res_5349_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5344_, v_formatterName_5345_, v_sepArray_5346_, v_a_5347_, v_a_5348_);
lean_dec_ref(v_a_5347_);
return v_res_5349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object* v_ks_5350_, lean_object* v_sep_5351_, lean_object* v_f_5352_, lean_object* v_formatterName_5353_, lean_object* v_sepArray_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_){
_start:
{
lean_object* v___x_5357_; 
v___x_5357_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5352_, v_formatterName_5353_, v_sepArray_5354_, v_a_5355_, v_a_5356_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object* v_ks_5358_, lean_object* v_sep_5359_, lean_object* v_f_5360_, lean_object* v_formatterName_5361_, lean_object* v_sepArray_5362_, lean_object* v_a_5363_, lean_object* v_a_5364_){
_start:
{
lean_object* v_res_5365_; 
v_res_5365_ = l_Lean_Fmt_fmtTSepArrayWith(v_ks_5358_, v_sep_5359_, v_f_5360_, v_formatterName_5361_, v_sepArray_5362_, v_a_5363_, v_a_5364_);
lean_dec_ref(v_a_5363_);
lean_dec_ref(v_sep_5359_);
lean_dec(v_ks_5358_);
return v_res_5365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(uint8_t v___x_5366_, lean_object* v___x_5367_, lean_object* v___x_5368_, lean_object* v___x_5369_, lean_object* v_a_5370_, lean_object* v_b_5371_){
_start:
{
lean_object* v___x_5372_; uint8_t v_decide_5373_; 
v___x_5372_ = lean_nat_sub(v___x_5367_, v___x_5368_);
v_decide_5373_ = lean_nat_dec_eq(v_a_5370_, v___x_5372_);
lean_dec(v___x_5372_);
if (v_decide_5373_ == 0)
{
uint32_t v___x_5374_; lean_object* v___x_5375_; uint32_t v___x_5376_; uint8_t v___x_5377_; 
v___x_5374_ = 10;
v___x_5375_ = lean_nat_add(v___x_5368_, v_a_5370_);
v___x_5376_ = lean_string_utf8_get_fast(v___x_5369_, v___x_5375_);
v___x_5377_ = lean_uint32_dec_eq(v___x_5376_, v___x_5374_);
if (v___x_5377_ == 0)
{
lean_object* v___x_5378_; lean_object* v___x_5379_; 
lean_dec(v_a_5370_);
v___x_5378_ = lean_string_utf8_next_fast(v___x_5369_, v___x_5375_);
lean_dec(v___x_5375_);
v___x_5379_ = lean_nat_sub(v___x_5378_, v___x_5368_);
v_a_5370_ = v___x_5379_;
goto _start;
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
v___x_5381_ = lean_string_utf8_next_fast(v___x_5369_, v___x_5375_);
v___x_5382_ = lean_nat_sub(v___x_5381_, v___x_5375_);
lean_dec(v___x_5375_);
v___x_5383_ = lean_nat_add(v_a_5370_, v___x_5382_);
lean_dec(v___x_5382_);
lean_dec(v_a_5370_);
if (v___x_5366_ == 0)
{
v_a_5370_ = v___x_5383_;
goto _start;
}
else
{
lean_object* v___x_5385_; lean_object* v___x_5386_; 
v___x_5385_ = lean_unsigned_to_nat(1u);
v___x_5386_ = lean_nat_add(v_b_5371_, v___x_5385_);
lean_dec(v_b_5371_);
v_a_5370_ = v___x_5383_;
v_b_5371_ = v___x_5386_;
goto _start;
}
}
}
else
{
lean_dec(v_a_5370_);
return v_b_5371_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___x_5388_, lean_object* v___x_5389_, lean_object* v___x_5390_, lean_object* v___x_5391_, lean_object* v_a_5392_, lean_object* v_b_5393_){
_start:
{
uint8_t v___x_2013__boxed_5394_; lean_object* v_res_5395_; 
v___x_2013__boxed_5394_ = lean_unbox(v___x_5388_);
v_res_5395_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_2013__boxed_5394_, v___x_5389_, v___x_5390_, v___x_5391_, v_a_5392_, v_b_5393_);
lean_dec_ref(v___x_5391_);
lean_dec(v___x_5390_);
lean_dec(v___x_5389_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5398_, lean_object* v_minNewlines_5399_, lean_object* v_leadingTk_5400_, lean_object* v_leading_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_){
_start:
{
lean_object* v___y_5411_; lean_object* v___y_5422_; lean_object* v_str_5424_; lean_object* v_startPos_5425_; lean_object* v_stopPos_5426_; uint8_t v___x_5427_; 
v_str_5424_ = lean_ctor_get(v_leading_5401_, 0);
v_startPos_5425_ = lean_ctor_get(v_leading_5401_, 1);
v_stopPos_5426_ = lean_ctor_get(v_leading_5401_, 2);
v___x_5427_ = lean_string_is_valid_pos(v_str_5424_, v_startPos_5425_);
if (v___x_5427_ == 0)
{
lean_dec(v_minNewlines_5399_);
lean_dec(v_maxNewlines_5398_);
goto v___jp_5404_;
}
else
{
uint8_t v___x_5428_; 
v___x_5428_ = lean_string_is_valid_pos(v_str_5424_, v_stopPos_5426_);
if (v___x_5428_ == 0)
{
lean_dec(v_minNewlines_5399_);
lean_dec(v_maxNewlines_5398_);
goto v___jp_5404_;
}
else
{
uint8_t v___x_5429_; 
v___x_5429_ = lean_nat_dec_le(v_startPos_5425_, v_stopPos_5426_);
if (v___x_5429_ == 0)
{
lean_dec(v_minNewlines_5399_);
lean_dec(v_maxNewlines_5398_);
goto v___jp_5404_;
}
else
{
lean_object* v_searcher_5430_; lean_object* v_numNewlines_5431_; uint8_t v___x_5432_; 
lean_dec(v_leadingTk_5400_);
v_searcher_5430_ = lean_unsigned_to_nat(0u);
v_numNewlines_5431_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5429_, v_stopPos_5426_, v_startPos_5425_, v_str_5424_, v_searcher_5430_, v_searcher_5430_);
v___x_5432_ = lean_nat_dec_le(v_numNewlines_5431_, v_minNewlines_5399_);
if (v___x_5432_ == 0)
{
lean_dec(v_minNewlines_5399_);
v___y_5422_ = v_numNewlines_5431_;
goto v___jp_5421_;
}
else
{
lean_dec(v_numNewlines_5431_);
v___y_5422_ = v_minNewlines_5399_;
goto v___jp_5421_;
}
}
}
}
v___jp_5404_:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; 
v___x_5405_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5406_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5407_, 0, v_leadingTk_5400_);
lean_ctor_set(v___x_5407_, 1, v___x_5405_);
lean_ctor_set(v___x_5407_, 2, v___x_5406_);
v___x_5408_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5408_, 0, v___x_5407_);
v___x_5409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5408_);
lean_ctor_set(v___x_5409_, 1, v___y_5403_);
return v___x_5409_;
}
v___jp_5410_:
{
lean_object* v___x_5412_; lean_object* v_nls_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5412_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5413_ = lean_mk_array(v___y_5411_, v___x_5412_);
v___x_5414_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5413_);
v___x_5415_ = lean_box(0);
v___x_5416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5416_, 0, v___x_5414_);
lean_ctor_set(v___x_5416_, 1, v___x_5415_);
v___x_5417_ = lean_unsigned_to_nat(1u);
v___x_5418_ = lean_mk_empty_array_with_capacity(v___x_5417_);
v___x_5419_ = lean_array_push(v___x_5418_, v___x_5416_);
v___x_5420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5419_);
lean_ctor_set(v___x_5420_, 1, v___y_5403_);
return v___x_5420_;
}
v___jp_5421_:
{
uint8_t v___x_5423_; 
v___x_5423_ = lean_nat_dec_le(v___y_5422_, v_maxNewlines_5398_);
if (v___x_5423_ == 0)
{
lean_dec(v___y_5422_);
v___y_5411_ = v_maxNewlines_5398_;
goto v___jp_5410_;
}
else
{
lean_dec(v_maxNewlines_5398_);
v___y_5411_ = v___y_5422_;
goto v___jp_5410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5433_, lean_object* v_minNewlines_5434_, lean_object* v_leadingTk_5435_, lean_object* v_leading_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(v_maxNewlines_5433_, v_minNewlines_5434_, v_leadingTk_5435_, v_leading_5436_, v___y_5437_, v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec_ref(v_leading_5436_);
return v_res_5439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object* v_stx_5440_, lean_object* v_minNewlines_5441_, lean_object* v_maxNewlines_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v___f_5445_; lean_object* v___x_5446_; 
v___f_5445_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5445_, 0, v_maxNewlines_5442_);
lean_closure_set(v___f_5445_, 1, v_minNewlines_5441_);
v___x_5446_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_5440_, v___f_5445_, v_a_5443_, v_a_5444_);
return v___x_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object* v_stx_5447_, lean_object* v_minNewlines_5448_, lean_object* v_maxNewlines_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_){
_start:
{
lean_object* v_res_5452_; 
v_res_5452_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines(v_stx_5447_, v_minNewlines_5448_, v_maxNewlines_5449_, v_a_5450_, v_a_5451_);
lean_dec_ref(v_a_5450_);
return v_res_5452_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(uint8_t v___x_5453_, lean_object* v___x_5454_, lean_object* v___x_5455_, lean_object* v___x_5456_, lean_object* v___x_5457_, lean_object* v_inst_5458_, lean_object* v_R_5459_, lean_object* v_a_5460_, lean_object* v_b_5461_, lean_object* v_c_5462_){
_start:
{
lean_object* v___x_5463_; 
v___x_5463_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5453_, v___x_5454_, v___x_5455_, v___x_5457_, v_a_5460_, v_b_5461_);
return v___x_5463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object* v___x_5464_, lean_object* v___x_5465_, lean_object* v___x_5466_, lean_object* v___x_5467_, lean_object* v___x_5468_, lean_object* v_inst_5469_, lean_object* v_R_5470_, lean_object* v_a_5471_, lean_object* v_b_5472_, lean_object* v_c_5473_){
_start:
{
uint8_t v___x_2122__boxed_5474_; lean_object* v_res_5475_; 
v___x_2122__boxed_5474_ = lean_unbox(v___x_5464_);
v_res_5475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(v___x_2122__boxed_5474_, v___x_5465_, v___x_5466_, v___x_5467_, v___x_5468_, v_inst_5469_, v_R_5470_, v_a_5471_, v_b_5472_, v_c_5473_);
lean_dec_ref(v___x_5468_);
lean_dec_ref(v___x_5467_);
lean_dec(v___x_5466_);
lean_dec(v___x_5465_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5476_, lean_object* v_minNewlines_5477_, lean_object* v_trailingTk_5478_, lean_object* v_trailing_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v___y_5489_; lean_object* v___y_5500_; lean_object* v_str_5502_; lean_object* v_startPos_5503_; lean_object* v_stopPos_5504_; uint8_t v___x_5505_; 
v_str_5502_ = lean_ctor_get(v_trailing_5479_, 0);
v_startPos_5503_ = lean_ctor_get(v_trailing_5479_, 1);
v_stopPos_5504_ = lean_ctor_get(v_trailing_5479_, 2);
v___x_5505_ = lean_string_is_valid_pos(v_str_5502_, v_startPos_5503_);
if (v___x_5505_ == 0)
{
lean_dec(v_minNewlines_5477_);
lean_dec(v_maxNewlines_5476_);
goto v___jp_5482_;
}
else
{
uint8_t v___x_5506_; 
v___x_5506_ = lean_string_is_valid_pos(v_str_5502_, v_stopPos_5504_);
if (v___x_5506_ == 0)
{
lean_dec(v_minNewlines_5477_);
lean_dec(v_maxNewlines_5476_);
goto v___jp_5482_;
}
else
{
uint8_t v___x_5507_; 
v___x_5507_ = lean_nat_dec_le(v_startPos_5503_, v_stopPos_5504_);
if (v___x_5507_ == 0)
{
lean_dec(v_minNewlines_5477_);
lean_dec(v_maxNewlines_5476_);
goto v___jp_5482_;
}
else
{
lean_object* v_searcher_5508_; lean_object* v_numNewlines_5509_; uint8_t v___x_5510_; 
lean_dec(v_trailingTk_5478_);
v_searcher_5508_ = lean_unsigned_to_nat(0u);
v_numNewlines_5509_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5507_, v_stopPos_5504_, v_startPos_5503_, v_str_5502_, v_searcher_5508_, v_searcher_5508_);
v___x_5510_ = lean_nat_dec_le(v_numNewlines_5509_, v_minNewlines_5477_);
if (v___x_5510_ == 0)
{
lean_dec(v_minNewlines_5477_);
v___y_5500_ = v_numNewlines_5509_;
goto v___jp_5499_;
}
else
{
lean_dec(v_numNewlines_5509_);
v___y_5500_ = v_minNewlines_5477_;
goto v___jp_5499_;
}
}
}
}
v___jp_5482_:
{
lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; 
v___x_5483_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5484_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5485_, 0, v_trailingTk_5478_);
lean_ctor_set(v___x_5485_, 1, v___x_5483_);
lean_ctor_set(v___x_5485_, 2, v___x_5484_);
v___x_5486_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5485_);
v___x_5487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5487_, 0, v___x_5486_);
lean_ctor_set(v___x_5487_, 1, v___y_5481_);
return v___x_5487_;
}
v___jp_5488_:
{
lean_object* v___x_5490_; lean_object* v_nls_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5490_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5491_ = lean_mk_array(v___y_5489_, v___x_5490_);
v___x_5492_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5491_);
v___x_5493_ = lean_box(0);
v___x_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5494_, 0, v___x_5492_);
lean_ctor_set(v___x_5494_, 1, v___x_5493_);
v___x_5495_ = lean_unsigned_to_nat(1u);
v___x_5496_ = lean_mk_empty_array_with_capacity(v___x_5495_);
v___x_5497_ = lean_array_push(v___x_5496_, v___x_5494_);
v___x_5498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5497_);
lean_ctor_set(v___x_5498_, 1, v___y_5481_);
return v___x_5498_;
}
v___jp_5499_:
{
uint8_t v___x_5501_; 
v___x_5501_ = lean_nat_dec_le(v___y_5500_, v_maxNewlines_5476_);
if (v___x_5501_ == 0)
{
lean_dec(v___y_5500_);
v___y_5489_ = v_maxNewlines_5476_;
goto v___jp_5488_;
}
else
{
lean_dec(v_maxNewlines_5476_);
v___y_5489_ = v___y_5500_;
goto v___jp_5488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5511_, lean_object* v_minNewlines_5512_, lean_object* v_trailingTk_5513_, lean_object* v_trailing_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_){
_start:
{
lean_object* v_res_5517_; 
v_res_5517_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(v_maxNewlines_5511_, v_minNewlines_5512_, v_trailingTk_5513_, v_trailing_5514_, v___y_5515_, v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec_ref(v_trailing_5514_);
return v_res_5517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object* v_stx_5518_, lean_object* v_minNewlines_5519_, lean_object* v_maxNewlines_5520_, lean_object* v_a_5521_, lean_object* v_a_5522_){
_start:
{
lean_object* v___f_5523_; lean_object* v___x_5524_; 
v___f_5523_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5523_, 0, v_maxNewlines_5520_);
lean_closure_set(v___f_5523_, 1, v_minNewlines_5519_);
v___x_5524_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_5518_, v___f_5523_, v_a_5521_, v_a_5522_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object* v_stx_5525_, lean_object* v_minNewlines_5526_, lean_object* v_maxNewlines_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_){
_start:
{
lean_object* v_res_5530_; 
v_res_5530_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v_stx_5525_, v_minNewlines_5526_, v_maxNewlines_5527_, v_a_5528_, v_a_5529_);
lean_dec_ref(v_a_5528_);
return v_res_5530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object* v_b_5531_, lean_object* v_a_5532_, lean_object* v_trailingDoc_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_){
_start:
{
lean_object* v___y_5537_; uint8_t v___x_5541_; 
v___x_5541_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_5532_);
if (v___x_5541_ == 0)
{
uint8_t v___x_5542_; 
v___x_5542_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_trailingDoc_5533_);
if (v___x_5542_ == 0)
{
lean_object* v_doc_5543_; lean_object* v_doc_5544_; uint8_t v___x_5545_; 
v_doc_5543_ = lean_ctor_get(v_a_5532_, 0);
lean_inc(v_doc_5543_);
lean_dec_ref(v_a_5532_);
v_doc_5544_ = lean_ctor_get(v_trailingDoc_5533_, 0);
lean_inc(v_doc_5544_);
lean_dec_ref(v_trailingDoc_5533_);
v___x_5545_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5543_);
if (v___x_5545_ == 0)
{
uint8_t v___x_5546_; 
v___x_5546_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5544_);
if (v___x_5546_ == 0)
{
lean_object* v___x_5547_; lean_object* v___x_5548_; 
v___x_5547_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_5543_, v_doc_5544_);
v___x_5548_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_5547_);
v___y_5537_ = v___x_5548_;
goto v___jp_5536_;
}
else
{
lean_object* v___x_5549_; 
lean_dec(v_doc_5544_);
v___x_5549_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5543_);
v___y_5537_ = v___x_5549_;
goto v___jp_5536_;
}
}
else
{
lean_object* v___x_5550_; 
lean_dec(v_doc_5543_);
v___x_5550_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5544_);
v___y_5537_ = v___x_5550_;
goto v___jp_5536_;
}
}
else
{
lean_dec_ref(v_trailingDoc_5533_);
v___y_5537_ = v_a_5532_;
goto v___jp_5536_;
}
}
else
{
lean_dec_ref(v_a_5532_);
v___y_5537_ = v_trailingDoc_5533_;
goto v___jp_5536_;
}
v___jp_5536_:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; 
v___x_5538_ = lean_array_push(v_b_5531_, v___y_5537_);
v___x_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5538_);
v___x_5540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5540_, 0, v___x_5539_);
lean_ctor_set(v___x_5540_, 1, v___y_5535_);
return v___x_5540_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object* v_b_5551_, lean_object* v_a_5552_, lean_object* v_trailingDoc_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
lean_object* v_res_5556_; 
v_res_5556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5551_, v_a_5552_, v_trailingDoc_5553_, v___y_5554_, v___y_5555_);
lean_dec_ref(v___y_5554_);
return v_res_5556_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object* v_upperBound_5557_, lean_object* v_stxs_5558_, lean_object* v___x_5559_, lean_object* v_a_5560_, lean_object* v_b_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_){
_start:
{
uint8_t v___x_5564_; 
v___x_5564_ = lean_nat_dec_lt(v_a_5560_, v_upperBound_5557_);
if (v___x_5564_ == 0)
{
lean_object* v___x_5565_; 
lean_dec(v_a_5560_);
v___x_5565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5565_, 0, v_b_5561_);
lean_ctor_set(v___x_5565_, 1, v___y_5563_);
return v___x_5565_;
}
else
{
lean_object* v___x_5566_; lean_object* v___x_5567_; 
v___x_5566_ = lean_array_fget_borrowed(v_stxs_5558_, v_a_5560_);
lean_inc(v___x_5566_);
v___x_5567_ = l_Lean_Fmt_fmt(v___x_5566_, v___y_5562_, v___y_5563_);
if (lean_obj_tag(v___x_5567_) == 0)
{
lean_object* v_a_5568_; lean_object* v_a_5569_; lean_object* v___x_5570_; lean_object* v___y_5572_; lean_object* v___x_5597_; uint8_t v___x_5598_; 
v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
lean_inc(v_a_5568_);
v_a_5569_ = lean_ctor_get(v___x_5567_, 1);
lean_inc(v_a_5569_);
lean_dec_ref_known(v___x_5567_, 2);
v___x_5570_ = lean_unsigned_to_nat(1u);
v___x_5597_ = lean_nat_sub(v___x_5559_, v___x_5570_);
v___x_5598_ = lean_nat_dec_lt(v_a_5560_, v___x_5597_);
lean_dec(v___x_5597_);
if (v___x_5598_ == 0)
{
lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5599_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5561_, v_a_5568_, v___x_5599_, v___y_5562_, v_a_5569_);
v___y_5572_ = v___x_5600_;
goto v___jp_5571_;
}
else
{
lean_object* v___x_5601_; lean_object* v___x_5602_; 
v___x_5601_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5566_);
v___x_5602_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v___x_5566_, v___x_5570_, v___x_5601_, v___y_5562_, v_a_5569_);
if (lean_obj_tag(v___x_5602_) == 0)
{
lean_object* v_a_5603_; lean_object* v_a_5604_; lean_object* v___x_5605_; 
v_a_5603_ = lean_ctor_get(v___x_5602_, 0);
lean_inc(v_a_5603_);
v_a_5604_ = lean_ctor_get(v___x_5602_, 1);
lean_inc(v_a_5604_);
lean_dec_ref_known(v___x_5602_, 2);
v___x_5605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5561_, v_a_5568_, v_a_5603_, v___y_5562_, v_a_5604_);
v___y_5572_ = v___x_5605_;
goto v___jp_5571_;
}
else
{
lean_object* v_a_5606_; lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5614_; 
lean_dec(v_a_5568_);
lean_dec_ref(v_b_5561_);
lean_dec(v_a_5560_);
v_a_5606_ = lean_ctor_get(v___x_5602_, 0);
v_a_5607_ = lean_ctor_get(v___x_5602_, 1);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5602_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5609_ = v___x_5602_;
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_inc(v_a_5606_);
lean_dec(v___x_5602_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5614_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
if (v_isShared_5610_ == 0)
{
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5606_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
v___jp_5571_:
{
if (lean_obj_tag(v___y_5572_) == 0)
{
lean_object* v_a_5573_; 
v_a_5573_ = lean_ctor_get(v___y_5572_, 0);
lean_inc(v_a_5573_);
if (lean_obj_tag(v_a_5573_) == 0)
{
lean_object* v_a_5574_; lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5582_; 
lean_dec(v_a_5560_);
v_a_5574_ = lean_ctor_get(v___y_5572_, 1);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___y_5572_);
if (v_isSharedCheck_5582_ == 0)
{
lean_object* v_unused_5583_; 
v_unused_5583_ = lean_ctor_get(v___y_5572_, 0);
lean_dec(v_unused_5583_);
v___x_5576_ = v___y_5572_;
v_isShared_5577_ = v_isSharedCheck_5582_;
goto v_resetjp_5575_;
}
else
{
lean_inc(v_a_5574_);
lean_dec(v___y_5572_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5582_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v_a_5578_; lean_object* v___x_5580_; 
v_a_5578_ = lean_ctor_get(v_a_5573_, 0);
lean_inc(v_a_5578_);
lean_dec_ref_known(v_a_5573_, 1);
if (v_isShared_5577_ == 0)
{
lean_ctor_set(v___x_5576_, 0, v_a_5578_);
v___x_5580_ = v___x_5576_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5578_);
lean_ctor_set(v_reuseFailAlloc_5581_, 1, v_a_5574_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
else
{
lean_object* v_a_5584_; lean_object* v_a_5585_; lean_object* v___x_5586_; 
v_a_5584_ = lean_ctor_get(v___y_5572_, 1);
lean_inc(v_a_5584_);
lean_dec_ref_known(v___y_5572_, 2);
v_a_5585_ = lean_ctor_get(v_a_5573_, 0);
lean_inc(v_a_5585_);
lean_dec_ref_known(v_a_5573_, 1);
v___x_5586_ = lean_nat_add(v_a_5560_, v___x_5570_);
lean_dec(v_a_5560_);
v_a_5560_ = v___x_5586_;
v_b_5561_ = v_a_5585_;
v___y_5563_ = v_a_5584_;
goto _start;
}
}
else
{
lean_object* v_a_5588_; lean_object* v_a_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5596_; 
lean_dec(v_a_5560_);
v_a_5588_ = lean_ctor_get(v___y_5572_, 0);
v_a_5589_ = lean_ctor_get(v___y_5572_, 1);
v_isSharedCheck_5596_ = !lean_is_exclusive(v___y_5572_);
if (v_isSharedCheck_5596_ == 0)
{
v___x_5591_ = v___y_5572_;
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_a_5589_);
lean_inc(v_a_5588_);
lean_dec(v___y_5572_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5596_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5594_; 
if (v_isShared_5592_ == 0)
{
v___x_5594_ = v___x_5591_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5588_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v_a_5589_);
v___x_5594_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
return v___x_5594_;
}
}
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec_ref(v_b_5561_);
lean_dec(v_a_5560_);
v_a_5615_ = lean_ctor_get(v___x_5567_, 0);
v_a_5616_ = lean_ctor_get(v___x_5567_, 1);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5567_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5567_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_inc(v_a_5615_);
lean_dec(v___x_5567_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5615_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object* v_upperBound_5624_, lean_object* v_stxs_5625_, lean_object* v___x_5626_, lean_object* v_a_5627_, lean_object* v_b_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_){
_start:
{
lean_object* v_res_5631_; 
v_res_5631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5624_, v_stxs_5625_, v___x_5626_, v_a_5627_, v_b_5628_, v___y_5629_, v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec(v___x_5626_);
lean_dec_ref(v_stxs_5625_);
lean_dec(v_upperBound_5624_);
return v_res_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object* v_stxs_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_){
_start:
{
lean_object* v___x_5637_; lean_object* v___x_5638_; uint8_t v___x_5639_; 
v___x_5637_ = lean_array_get_size(v_stxs_5634_);
v___x_5638_ = lean_unsigned_to_nat(1u);
v___x_5639_ = lean_nat_dec_eq(v___x_5637_, v___x_5638_);
if (v___x_5639_ == 0)
{
lean_object* v___x_5640_; lean_object* v_acc_5641_; lean_object* v___x_5642_; 
v___x_5640_ = lean_unsigned_to_nat(0u);
v_acc_5641_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_5642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v___x_5637_, v_stxs_5634_, v___x_5637_, v___x_5640_, v_acc_5641_, v_a_5635_, v_a_5636_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v_a_5643_; lean_object* v_a_5644_; lean_object* v___x_5646_; uint8_t v_isShared_5647_; uint8_t v_isSharedCheck_5652_; 
v_a_5643_ = lean_ctor_get(v___x_5642_, 0);
v_a_5644_ = lean_ctor_get(v___x_5642_, 1);
v_isSharedCheck_5652_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5652_ == 0)
{
v___x_5646_ = v___x_5642_;
v_isShared_5647_ = v_isSharedCheck_5652_;
goto v_resetjp_5645_;
}
else
{
lean_inc(v_a_5644_);
lean_inc(v_a_5643_);
lean_dec(v___x_5642_);
v___x_5646_ = lean_box(0);
v_isShared_5647_ = v_isSharedCheck_5652_;
goto v_resetjp_5645_;
}
v_resetjp_5645_:
{
lean_object* v___x_5648_; lean_object* v___x_5650_; 
v___x_5648_ = l_Lean_Fmt_TaggedDoc_join(v_a_5643_);
if (v_isShared_5647_ == 0)
{
lean_ctor_set(v___x_5646_, 0, v___x_5648_);
v___x_5650_ = v___x_5646_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v_a_5644_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
}
else
{
lean_object* v_a_5653_; lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5661_; 
v_a_5653_ = lean_ctor_get(v___x_5642_, 0);
v_a_5654_ = lean_ctor_get(v___x_5642_, 1);
v_isSharedCheck_5661_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5656_ = v___x_5642_;
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_inc(v_a_5653_);
lean_dec(v___x_5642_);
v___x_5656_ = lean_box(0);
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
v_resetjp_5655_:
{
lean_object* v___x_5659_; 
if (v_isShared_5657_ == 0)
{
v___x_5659_ = v___x_5656_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5653_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v_a_5654_);
v___x_5659_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
return v___x_5659_;
}
}
}
}
else
{
lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___x_5662_ = lean_box(0);
v___x_5663_ = lean_unsigned_to_nat(0u);
v___x_5664_ = lean_array_get_borrowed(v___x_5662_, v_stxs_5634_, v___x_5663_);
lean_inc(v___x_5664_);
v___x_5665_ = l_Lean_Fmt_fmt(v___x_5664_, v_a_5635_, v_a_5636_);
return v___x_5665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object* v_stxs_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_){
_start:
{
lean_object* v_res_5669_; 
v_res_5669_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(v_stxs_5666_, v_a_5667_, v_a_5668_);
lean_dec_ref(v_a_5667_);
lean_dec_ref(v_stxs_5666_);
return v_res_5669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object* v_upperBound_5670_, lean_object* v_stxs_5671_, lean_object* v___x_5672_, lean_object* v_inst_5673_, lean_object* v_R_5674_, lean_object* v_a_5675_, lean_object* v_b_5676_, lean_object* v_c_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_){
_start:
{
lean_object* v___x_5680_; 
v___x_5680_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5670_, v_stxs_5671_, v___x_5672_, v_a_5675_, v_b_5676_, v___y_5678_, v___y_5679_);
return v___x_5680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object* v_upperBound_5681_, lean_object* v_stxs_5682_, lean_object* v___x_5683_, lean_object* v_inst_5684_, lean_object* v_R_5685_, lean_object* v_a_5686_, lean_object* v_b_5687_, lean_object* v_c_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
lean_object* v_res_5691_; 
v_res_5691_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(v_upperBound_5681_, v_stxs_5682_, v___x_5683_, v_inst_5684_, v_R_5685_, v_a_5686_, v_b_5687_, v_c_5688_, v___y_5689_, v___y_5690_);
lean_dec_ref(v___y_5689_);
lean_dec(v___x_5683_);
lean_dec_ref(v_stxs_5682_);
lean_dec(v_upperBound_5681_);
return v_res_5691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object* v_comments_5692_, lean_object* v_out_5693_, lean_object* v_a_5694_){
_start:
{
lean_object* v___x_5695_; uint8_t v___x_5696_; 
v___x_5695_ = lean_array_get_size(v_comments_5692_);
v___x_5696_ = lean_nat_dec_lt(v_a_5694_, v___x_5695_);
if (v___x_5696_ == 0)
{
return v_a_5694_;
}
else
{
lean_object* v___x_5697_; lean_object* v_originalWhitespaceRange_5698_; lean_object* v_stop_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; uint8_t v___x_5702_; 
v___x_5697_ = lean_array_fget_borrowed(v_comments_5692_, v_a_5694_);
v_originalWhitespaceRange_5698_ = lean_ctor_get(v___x_5697_, 1);
v_stop_5699_ = lean_ctor_get(v_originalWhitespaceRange_5698_, 1);
v___x_5700_ = lean_unsigned_to_nat(1u);
v___x_5701_ = lean_nat_add(v_out_5693_, v___x_5700_);
v___x_5702_ = lean_nat_dec_le(v___x_5701_, v_stop_5699_);
lean_dec(v___x_5701_);
if (v___x_5702_ == 0)
{
lean_object* v___x_5703_; 
v___x_5703_ = lean_nat_add(v_a_5694_, v___x_5700_);
lean_dec(v_a_5694_);
v_a_5694_ = v___x_5703_;
goto _start;
}
else
{
return v_a_5694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object* v_comments_5705_, lean_object* v_out_5706_, lean_object* v_a_5707_){
_start:
{
lean_object* v_res_5708_; 
v_res_5708_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5705_, v_out_5706_, v_a_5707_);
lean_dec(v_out_5706_);
lean_dec_ref(v_comments_5705_);
return v_res_5708_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_5709_, lean_object* v_x_5710_){
_start:
{
if (lean_obj_tag(v_x_5710_) == 0)
{
return v_x_5709_;
}
else
{
lean_object* v_key_5711_; lean_object* v_value_5712_; lean_object* v_tail_5713_; lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5736_; 
v_key_5711_ = lean_ctor_get(v_x_5710_, 0);
v_value_5712_ = lean_ctor_get(v_x_5710_, 1);
v_tail_5713_ = lean_ctor_get(v_x_5710_, 2);
v_isSharedCheck_5736_ = !lean_is_exclusive(v_x_5710_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5715_ = v_x_5710_;
v_isShared_5716_ = v_isSharedCheck_5736_;
goto v_resetjp_5714_;
}
else
{
lean_inc(v_tail_5713_);
lean_inc(v_value_5712_);
lean_inc(v_key_5711_);
lean_dec(v_x_5710_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5736_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
lean_object* v___x_5717_; uint64_t v___x_5718_; uint64_t v___x_5719_; uint64_t v___x_5720_; uint64_t v_fold_5721_; uint64_t v___x_5722_; uint64_t v___x_5723_; uint64_t v___x_5724_; size_t v___x_5725_; size_t v___x_5726_; size_t v___x_5727_; size_t v___x_5728_; size_t v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5732_; 
v___x_5717_ = lean_array_get_size(v_x_5709_);
v___x_5718_ = lean_uint64_of_nat(v_key_5711_);
v___x_5719_ = 32ULL;
v___x_5720_ = lean_uint64_shift_right(v___x_5718_, v___x_5719_);
v_fold_5721_ = lean_uint64_xor(v___x_5718_, v___x_5720_);
v___x_5722_ = 16ULL;
v___x_5723_ = lean_uint64_shift_right(v_fold_5721_, v___x_5722_);
v___x_5724_ = lean_uint64_xor(v_fold_5721_, v___x_5723_);
v___x_5725_ = lean_uint64_to_usize(v___x_5724_);
v___x_5726_ = lean_usize_of_nat(v___x_5717_);
v___x_5727_ = ((size_t)1ULL);
v___x_5728_ = lean_usize_sub(v___x_5726_, v___x_5727_);
v___x_5729_ = lean_usize_land(v___x_5725_, v___x_5728_);
v___x_5730_ = lean_array_uget_borrowed(v_x_5709_, v___x_5729_);
lean_inc(v___x_5730_);
if (v_isShared_5716_ == 0)
{
lean_ctor_set(v___x_5715_, 2, v___x_5730_);
v___x_5732_ = v___x_5715_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_key_5711_);
lean_ctor_set(v_reuseFailAlloc_5735_, 1, v_value_5712_);
lean_ctor_set(v_reuseFailAlloc_5735_, 2, v___x_5730_);
v___x_5732_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
lean_object* v___x_5733_; 
v___x_5733_ = lean_array_uset(v_x_5709_, v___x_5729_, v___x_5732_);
v_x_5709_ = v___x_5733_;
v_x_5710_ = v_tail_5713_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object* v_i_5737_, lean_object* v_source_5738_, lean_object* v_target_5739_){
_start:
{
lean_object* v___x_5740_; uint8_t v___x_5741_; 
v___x_5740_ = lean_array_get_size(v_source_5738_);
v___x_5741_ = lean_nat_dec_lt(v_i_5737_, v___x_5740_);
if (v___x_5741_ == 0)
{
lean_dec_ref(v_source_5738_);
lean_dec(v_i_5737_);
return v_target_5739_;
}
else
{
lean_object* v_es_5742_; lean_object* v___x_5743_; lean_object* v_source_5744_; lean_object* v_target_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v_es_5742_ = lean_array_fget(v_source_5738_, v_i_5737_);
v___x_5743_ = lean_box(0);
v_source_5744_ = lean_array_fset(v_source_5738_, v_i_5737_, v___x_5743_);
v_target_5745_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_target_5739_, v_es_5742_);
v___x_5746_ = lean_unsigned_to_nat(1u);
v___x_5747_ = lean_nat_add(v_i_5737_, v___x_5746_);
lean_dec(v_i_5737_);
v_i_5737_ = v___x_5747_;
v_source_5738_ = v_source_5744_;
v_target_5739_ = v_target_5745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object* v_data_5749_){
_start:
{
lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v_nbuckets_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; 
v___x_5750_ = lean_array_get_size(v_data_5749_);
v___x_5751_ = lean_unsigned_to_nat(2u);
v_nbuckets_5752_ = lean_nat_mul(v___x_5750_, v___x_5751_);
v___x_5753_ = lean_unsigned_to_nat(0u);
v___x_5754_ = lean_box(0);
v___x_5755_ = lean_mk_array(v_nbuckets_5752_, v___x_5754_);
v___x_5756_ = lean_array_propagate_mark(v_data_5749_, v___x_5755_);
v___x_5757_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v___x_5753_, v_data_5749_, v___x_5756_);
return v___x_5757_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object* v_a_5758_, lean_object* v_x_5759_){
_start:
{
if (lean_obj_tag(v_x_5759_) == 0)
{
uint8_t v___x_5760_; 
v___x_5760_ = 0;
return v___x_5760_;
}
else
{
lean_object* v_key_5761_; lean_object* v_tail_5762_; uint8_t v___x_5763_; 
v_key_5761_ = lean_ctor_get(v_x_5759_, 0);
v_tail_5762_ = lean_ctor_get(v_x_5759_, 2);
v___x_5763_ = lean_nat_dec_eq(v_key_5761_, v_a_5758_);
if (v___x_5763_ == 0)
{
v_x_5759_ = v_tail_5762_;
goto _start;
}
else
{
return v___x_5763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object* v_a_5765_, lean_object* v_x_5766_){
_start:
{
uint8_t v_res_5767_; lean_object* v_r_5768_; 
v_res_5767_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5765_, v_x_5766_);
lean_dec(v_x_5766_);
lean_dec(v_a_5765_);
v_r_5768_ = lean_box(v_res_5767_);
return v_r_5768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object* v_x_5771_){
_start:
{
if (lean_obj_tag(v_x_5771_) == 0)
{
lean_object* v___x_5772_; 
v___x_5772_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0));
return v___x_5772_;
}
else
{
lean_object* v_val_5773_; lean_object* v___x_5775_; uint8_t v_isShared_5776_; uint8_t v_isSharedCheck_5782_; 
v_val_5773_ = lean_ctor_get(v_x_5771_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v_x_5771_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5775_ = v_x_5771_;
v_isShared_5776_ = v_isSharedCheck_5782_;
goto v_resetjp_5774_;
}
else
{
lean_inc(v_val_5773_);
lean_dec(v_x_5771_);
v___x_5775_ = lean_box(0);
v_isShared_5776_ = v_isSharedCheck_5782_;
goto v_resetjp_5774_;
}
v_resetjp_5774_:
{
lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5780_; 
v___x_5777_ = lean_unsigned_to_nat(1u);
v___x_5778_ = lean_nat_add(v_val_5773_, v___x_5777_);
lean_dec(v_val_5773_);
if (v_isShared_5776_ == 0)
{
lean_ctor_set(v___x_5775_, 0, v___x_5778_);
v___x_5780_ = v___x_5775_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v___x_5778_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5783_; lean_object* v___x_5784_; 
v___x_5783_ = lean_box(0);
v___x_5784_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5783_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object* v_a_5785_, lean_object* v_x_5786_){
_start:
{
if (lean_obj_tag(v_x_5786_) == 0)
{
lean_object* v___x_5787_; lean_object* v_val_5788_; lean_object* v___x_5789_; 
v___x_5787_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0);
v_val_5788_ = lean_ctor_get(v___x_5787_, 0);
lean_inc(v_val_5788_);
v___x_5789_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5789_, 0, v_a_5785_);
lean_ctor_set(v___x_5789_, 1, v_val_5788_);
lean_ctor_set(v___x_5789_, 2, v_x_5786_);
return v___x_5789_;
}
else
{
lean_object* v_key_5790_; lean_object* v_value_5791_; lean_object* v_tail_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5807_; 
v_key_5790_ = lean_ctor_get(v_x_5786_, 0);
v_value_5791_ = lean_ctor_get(v_x_5786_, 1);
v_tail_5792_ = lean_ctor_get(v_x_5786_, 2);
v_isSharedCheck_5807_ = !lean_is_exclusive(v_x_5786_);
if (v_isSharedCheck_5807_ == 0)
{
v___x_5794_ = v_x_5786_;
v_isShared_5795_ = v_isSharedCheck_5807_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_tail_5792_);
lean_inc(v_value_5791_);
lean_inc(v_key_5790_);
lean_dec(v_x_5786_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5807_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
uint8_t v___x_5796_; 
v___x_5796_ = lean_nat_dec_eq(v_key_5790_, v_a_5785_);
if (v___x_5796_ == 0)
{
lean_object* v_tail_5797_; lean_object* v___x_5799_; 
v_tail_5797_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5785_, v_tail_5792_);
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 2, v_tail_5797_);
v___x_5799_ = v___x_5794_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v_key_5790_);
lean_ctor_set(v_reuseFailAlloc_5800_, 1, v_value_5791_);
lean_ctor_set(v_reuseFailAlloc_5800_, 2, v_tail_5797_);
v___x_5799_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
return v___x_5799_;
}
}
else
{
lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v_val_5803_; lean_object* v___x_5805_; 
lean_dec(v_key_5790_);
v___x_5801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5801_, 0, v_value_5791_);
v___x_5802_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5801_);
v_val_5803_ = lean_ctor_get(v___x_5802_, 0);
lean_inc(v_val_5803_);
lean_dec(v___x_5802_);
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 1, v_val_5803_);
lean_ctor_set(v___x_5794_, 0, v_a_5785_);
v___x_5805_ = v___x_5794_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5785_);
lean_ctor_set(v_reuseFailAlloc_5806_, 1, v_val_5803_);
lean_ctor_set(v_reuseFailAlloc_5806_, 2, v_tail_5792_);
v___x_5805_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
return v___x_5805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object* v_m_5808_, lean_object* v_a_5809_){
_start:
{
lean_object* v_size_5810_; lean_object* v_buckets_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5859_; 
v_size_5810_ = lean_ctor_get(v_m_5808_, 0);
v_buckets_5811_ = lean_ctor_get(v_m_5808_, 1);
v_isSharedCheck_5859_ = !lean_is_exclusive(v_m_5808_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5813_ = v_m_5808_;
v_isShared_5814_ = v_isSharedCheck_5859_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_buckets_5811_);
lean_inc(v_size_5810_);
lean_dec(v_m_5808_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5859_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___x_5815_; uint64_t v___x_5816_; uint64_t v___x_5817_; uint64_t v___x_5818_; uint64_t v_fold_5819_; uint64_t v___x_5820_; uint64_t v___x_5821_; uint64_t v___x_5822_; size_t v___x_5823_; size_t v___x_5824_; size_t v___x_5825_; size_t v___x_5826_; size_t v___x_5827_; lean_object* v_bkt_5828_; uint8_t v___x_5829_; 
v___x_5815_ = lean_array_get_size(v_buckets_5811_);
v___x_5816_ = lean_uint64_of_nat(v_a_5809_);
v___x_5817_ = 32ULL;
v___x_5818_ = lean_uint64_shift_right(v___x_5816_, v___x_5817_);
v_fold_5819_ = lean_uint64_xor(v___x_5816_, v___x_5818_);
v___x_5820_ = 16ULL;
v___x_5821_ = lean_uint64_shift_right(v_fold_5819_, v___x_5820_);
v___x_5822_ = lean_uint64_xor(v_fold_5819_, v___x_5821_);
v___x_5823_ = lean_uint64_to_usize(v___x_5822_);
v___x_5824_ = lean_usize_of_nat(v___x_5815_);
v___x_5825_ = ((size_t)1ULL);
v___x_5826_ = lean_usize_sub(v___x_5824_, v___x_5825_);
v___x_5827_ = lean_usize_land(v___x_5823_, v___x_5826_);
v_bkt_5828_ = lean_array_uget_borrowed(v_buckets_5811_, v___x_5827_);
v___x_5829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5809_, v_bkt_5828_);
if (v___x_5829_ == 0)
{
lean_object* v___x_5830_; lean_object* v_size_x27_5831_; lean_object* v___x_5832_; lean_object* v_buckets_x27_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; uint8_t v___x_5839_; 
v___x_5830_ = lean_unsigned_to_nat(1u);
v_size_x27_5831_ = lean_nat_add(v_size_5810_, v___x_5830_);
lean_dec(v_size_5810_);
lean_inc(v_bkt_5828_);
v___x_5832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5832_, 0, v_a_5809_);
lean_ctor_set(v___x_5832_, 1, v___x_5830_);
lean_ctor_set(v___x_5832_, 2, v_bkt_5828_);
v_buckets_x27_5833_ = lean_array_uset(v_buckets_5811_, v___x_5827_, v___x_5832_);
v___x_5834_ = lean_unsigned_to_nat(4u);
v___x_5835_ = lean_nat_mul(v_size_x27_5831_, v___x_5834_);
v___x_5836_ = lean_unsigned_to_nat(3u);
v___x_5837_ = lean_nat_div(v___x_5835_, v___x_5836_);
lean_dec(v___x_5835_);
v___x_5838_ = lean_array_get_size(v_buckets_x27_5833_);
v___x_5839_ = lean_nat_dec_le(v___x_5837_, v___x_5838_);
lean_dec(v___x_5837_);
if (v___x_5839_ == 0)
{
lean_object* v_val_5840_; lean_object* v___x_5842_; 
v_val_5840_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_buckets_x27_5833_);
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 1, v_val_5840_);
lean_ctor_set(v___x_5813_, 0, v_size_x27_5831_);
v___x_5842_ = v___x_5813_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_size_x27_5831_);
lean_ctor_set(v_reuseFailAlloc_5843_, 1, v_val_5840_);
v___x_5842_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
return v___x_5842_;
}
}
else
{
lean_object* v___x_5845_; 
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 1, v_buckets_x27_5833_);
lean_ctor_set(v___x_5813_, 0, v_size_x27_5831_);
v___x_5845_ = v___x_5813_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_size_x27_5831_);
lean_ctor_set(v_reuseFailAlloc_5846_, 1, v_buckets_x27_5833_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
else
{
lean_object* v___x_5847_; lean_object* v_buckets_x27_5848_; lean_object* v_bkt_x27_5849_; lean_object* v___y_5851_; uint8_t v___x_5856_; 
lean_inc(v_bkt_5828_);
v___x_5847_ = lean_box(0);
v_buckets_x27_5848_ = lean_array_uset(v_buckets_5811_, v___x_5827_, v___x_5847_);
lean_inc(v_a_5809_);
v_bkt_x27_5849_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5809_, v_bkt_5828_);
v___x_5856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5809_, v_bkt_x27_5849_);
lean_dec(v_a_5809_);
if (v___x_5856_ == 0)
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = lean_unsigned_to_nat(1u);
v___x_5858_ = lean_nat_sub(v_size_5810_, v___x_5857_);
lean_dec(v_size_5810_);
v___y_5851_ = v___x_5858_;
goto v___jp_5850_;
}
else
{
v___y_5851_ = v_size_5810_;
goto v___jp_5850_;
}
v___jp_5850_:
{
lean_object* v___x_5852_; lean_object* v___x_5854_; 
v___x_5852_ = lean_array_uset(v_buckets_x27_5848_, v___x_5827_, v_bkt_x27_5849_);
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 1, v___x_5852_);
lean_ctor_set(v___x_5813_, 0, v___y_5851_);
v___x_5854_ = v___x_5813_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___y_5851_);
lean_ctor_set(v_reuseFailAlloc_5855_, 1, v___x_5852_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object* v_fst_5860_, lean_object* v___x_5861_, lean_object* v_____r_5862_){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; 
lean_inc(v___x_5861_);
v___x_5863_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(v_fst_5860_, v___x_5861_);
v___x_5864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5863_);
lean_ctor_set(v___x_5864_, 1, v___x_5861_);
v___x_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5865_, 0, v___x_5864_);
return v___x_5865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object* v_comments_5866_, lean_object* v_whitespace_5867_, lean_object* v_a_5868_, lean_object* v_b_5869_){
_start:
{
lean_object* v_str_5870_; lean_object* v_startInclusive_5871_; lean_object* v_endExclusive_5872_; lean_object* v___x_5873_; uint8_t v_decide_5874_; 
v_str_5870_ = lean_ctor_get(v_whitespace_5867_, 0);
v_startInclusive_5871_ = lean_ctor_get(v_whitespace_5867_, 1);
v_endExclusive_5872_ = lean_ctor_get(v_whitespace_5867_, 2);
v___x_5873_ = lean_nat_sub(v_endExclusive_5872_, v_startInclusive_5871_);
v_decide_5874_ = lean_nat_dec_eq(v_a_5868_, v___x_5873_);
lean_dec(v___x_5873_);
if (v_decide_5874_ == 0)
{
uint32_t v___x_5875_; lean_object* v___x_5876_; uint32_t v___x_5877_; uint8_t v___x_5878_; 
v___x_5875_ = 10;
v___x_5876_ = lean_nat_add(v_startInclusive_5871_, v_a_5868_);
v___x_5877_ = lean_string_utf8_get_fast(v_str_5870_, v___x_5876_);
v___x_5878_ = lean_uint32_dec_eq(v___x_5877_, v___x_5875_);
if (v___x_5878_ == 0)
{
lean_object* v___x_5879_; lean_object* v___x_5880_; 
lean_dec(v_a_5868_);
v___x_5879_ = lean_string_utf8_next_fast(v_str_5870_, v___x_5876_);
lean_dec(v___x_5876_);
v___x_5880_ = lean_nat_sub(v___x_5879_, v_startInclusive_5871_);
v_a_5868_ = v___x_5880_;
goto _start;
}
else
{
lean_object* v_fst_5882_; lean_object* v_snd_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5909_; 
v_fst_5882_ = lean_ctor_get(v_b_5869_, 0);
v_snd_5883_ = lean_ctor_get(v_b_5869_, 1);
v_isSharedCheck_5909_ = !lean_is_exclusive(v_b_5869_);
if (v_isSharedCheck_5909_ == 0)
{
v___x_5885_ = v_b_5869_;
v_isShared_5886_ = v_isSharedCheck_5909_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_snd_5883_);
lean_inc(v_fst_5882_);
lean_dec(v_b_5869_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5909_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v_val_5891_; lean_object* v___x_5895_; lean_object* v___x_5896_; uint8_t v___x_5897_; 
v___x_5887_ = lean_string_utf8_next_fast(v_str_5870_, v___x_5876_);
v___x_5888_ = lean_nat_sub(v___x_5887_, v___x_5876_);
v___x_5889_ = lean_nat_add(v_a_5868_, v___x_5888_);
lean_dec(v___x_5888_);
lean_dec(v_a_5868_);
v___x_5895_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5866_, v___x_5876_, v_snd_5883_);
v___x_5896_ = lean_array_get_size(v_comments_5866_);
v___x_5897_ = lean_nat_dec_lt(v___x_5895_, v___x_5896_);
if (v___x_5897_ == 0)
{
lean_object* v___x_5898_; lean_object* v___x_5899_; 
lean_del_object(v___x_5885_);
lean_dec(v___x_5876_);
v___x_5898_ = lean_box(0);
v___x_5899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5882_, v___x_5895_, v___x_5898_);
v_val_5891_ = v___x_5899_;
goto v___jp_5890_;
}
else
{
lean_object* v___x_5900_; lean_object* v_originalWhitespaceRange_5901_; uint8_t v___x_5902_; 
v___x_5900_ = lean_array_fget_borrowed(v_comments_5866_, v___x_5895_);
v_originalWhitespaceRange_5901_ = lean_ctor_get(v___x_5900_, 1);
v___x_5902_ = l_Lean_Syntax_Range_contains(v_originalWhitespaceRange_5901_, v___x_5876_, v_decide_5874_);
lean_dec(v___x_5876_);
if (v___x_5902_ == 0)
{
lean_object* v___x_5903_; lean_object* v___x_5904_; 
lean_del_object(v___x_5885_);
v___x_5903_ = lean_box(0);
v___x_5904_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5882_, v___x_5895_, v___x_5903_);
v_val_5891_ = v___x_5904_;
goto v___jp_5890_;
}
else
{
lean_object* v___x_5906_; 
if (v_isShared_5886_ == 0)
{
lean_ctor_set(v___x_5885_, 1, v___x_5895_);
v___x_5906_ = v___x_5885_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_fst_5882_);
lean_ctor_set(v_reuseFailAlloc_5908_, 1, v___x_5895_);
v___x_5906_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
v_a_5868_ = v___x_5889_;
v_b_5869_ = v___x_5906_;
goto _start;
}
}
}
v___jp_5890_:
{
if (lean_obj_tag(v_val_5891_) == 0)
{
lean_object* v_a_5892_; 
lean_dec(v___x_5889_);
v_a_5892_ = lean_ctor_get(v_val_5891_, 0);
lean_inc(v_a_5892_);
lean_dec_ref_known(v_val_5891_, 1);
return v_a_5892_;
}
else
{
lean_object* v_a_5893_; 
v_a_5893_ = lean_ctor_get(v_val_5891_, 0);
lean_inc(v_a_5893_);
lean_dec_ref_known(v_val_5891_, 1);
v_a_5868_ = v___x_5889_;
v_b_5869_ = v_a_5893_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_5868_);
return v_b_5869_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object* v_comments_5910_, lean_object* v_whitespace_5911_, lean_object* v_a_5912_, lean_object* v_b_5913_){
_start:
{
lean_object* v_res_5914_; 
v_res_5914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5910_, v_whitespace_5911_, v_a_5912_, v_b_5913_);
lean_dec_ref(v_whitespace_5911_);
lean_dec_ref(v_comments_5910_);
return v_res_5914_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0(void){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; 
v___x_5915_ = lean_box(0);
v___x_5916_ = lean_unsigned_to_nat(16u);
v___x_5917_ = lean_mk_array(v___x_5916_, v___x_5915_);
return v___x_5917_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1(void){
_start:
{
lean_object* v___x_5918_; lean_object* v_newlinePositions_5919_; lean_object* v_newlinesBeforeComment_5920_; 
v___x_5918_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0);
v_newlinePositions_5919_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_newlinesBeforeComment_5920_, 0, v_newlinePositions_5919_);
lean_ctor_set(v_newlinesBeforeComment_5920_, 1, v___x_5918_);
return v_newlinesBeforeComment_5920_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2(void){
_start:
{
lean_object* v_newlinePositions_5921_; lean_object* v_newlinesBeforeComment_5922_; lean_object* v___x_5923_; 
v_newlinePositions_5921_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5922_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1);
v___x_5923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5923_, 0, v_newlinesBeforeComment_5922_);
lean_ctor_set(v___x_5923_, 1, v_newlinePositions_5921_);
return v___x_5923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object* v_comments_5924_, lean_object* v_whitespace_5925_){
_start:
{
lean_object* v_newlinePositions_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v_fst_5929_; 
v_newlinePositions_5926_ = lean_unsigned_to_nat(0u);
v___x_5927_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2);
v___x_5928_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5924_, v_whitespace_5925_, v_newlinePositions_5926_, v___x_5927_);
v_fst_5929_ = lean_ctor_get(v___x_5928_, 0);
lean_inc(v_fst_5929_);
lean_dec_ref(v___x_5928_);
return v_fst_5929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object* v_comments_5930_, lean_object* v_whitespace_5931_){
_start:
{
lean_object* v_res_5932_; 
v_res_5932_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v_comments_5930_, v_whitespace_5931_);
lean_dec_ref(v_whitespace_5931_);
lean_dec_ref(v_comments_5930_);
return v_res_5932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object* v_comments_5933_, lean_object* v_out_5934_, lean_object* v_inst_5935_, lean_object* v_a_5936_){
_start:
{
lean_object* v___x_5937_; 
v___x_5937_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5933_, v_out_5934_, v_a_5936_);
return v___x_5937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object* v_comments_5938_, lean_object* v_out_5939_, lean_object* v_inst_5940_, lean_object* v_a_5941_){
_start:
{
lean_object* v_res_5942_; 
v_res_5942_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(v_comments_5938_, v_out_5939_, v_inst_5940_, v_a_5941_);
lean_dec(v_out_5939_);
lean_dec_ref(v_comments_5938_);
return v_res_5942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object* v_comments_5943_, lean_object* v_whitespace_5944_, lean_object* v_inst_5945_, lean_object* v_R_5946_, lean_object* v_a_5947_, lean_object* v_b_5948_, lean_object* v_c_5949_){
_start:
{
lean_object* v___x_5950_; 
v___x_5950_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5943_, v_whitespace_5944_, v_a_5947_, v_b_5948_);
return v___x_5950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object* v_comments_5951_, lean_object* v_whitespace_5952_, lean_object* v_inst_5953_, lean_object* v_R_5954_, lean_object* v_a_5955_, lean_object* v_b_5956_, lean_object* v_c_5957_){
_start:
{
lean_object* v_res_5958_; 
v_res_5958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(v_comments_5951_, v_whitespace_5952_, v_inst_5953_, v_R_5954_, v_a_5955_, v_b_5956_, v_c_5957_);
lean_dec_ref(v_whitespace_5952_);
lean_dec_ref(v_comments_5951_);
return v_res_5958_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object* v_00_u03b2_5959_, lean_object* v_a_5960_, lean_object* v_x_5961_){
_start:
{
uint8_t v___x_5962_; 
v___x_5962_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5960_, v_x_5961_);
return v___x_5962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5963_, lean_object* v_a_5964_, lean_object* v_x_5965_){
_start:
{
uint8_t v_res_5966_; lean_object* v_r_5967_; 
v_res_5966_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(v_00_u03b2_5963_, v_a_5964_, v_x_5965_);
lean_dec(v_x_5965_);
lean_dec(v_a_5964_);
v_r_5967_ = lean_box(v_res_5966_);
return v_r_5967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object* v_00_u03b2_5968_, lean_object* v_data_5969_){
_start:
{
lean_object* v___x_5970_; 
v___x_5970_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_data_5969_);
return v___x_5970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5971_, lean_object* v_i_5972_, lean_object* v_source_5973_, lean_object* v_target_5974_){
_start:
{
lean_object* v___x_5975_; 
v___x_5975_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v_i_5972_, v_source_5973_, v_target_5974_);
return v___x_5975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5976_, lean_object* v_x_5977_, lean_object* v_x_5978_){
_start:
{
lean_object* v___x_5979_; 
v___x_5979_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_x_5977_, v_x_5978_);
return v___x_5979_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_5983_; 
v___x_5983_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0));
return v___x_5983_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___dummy_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v_res_5985_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5986_; 
v___x_5986_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v___x_5986_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object* v_s_5987_){
_start:
{
lean_object* v___x_5988_; 
v___x_5988_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
return v___x_5988_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object* v_s_5989_){
_start:
{
lean_object* v_res_5990_; 
v_res_5990_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(v_s_5989_);
lean_dec_ref(v_s_5989_);
return v_res_5990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t v_sz_5991_, size_t v_i_5992_, lean_object* v_bs_5993_){
_start:
{
uint8_t v___x_5994_; 
v___x_5994_ = lean_usize_dec_lt(v_i_5992_, v_sz_5991_);
if (v___x_5994_ == 0)
{
return v_bs_5993_;
}
else
{
lean_object* v_v_5995_; lean_object* v_rendered_5996_; lean_object* v___x_5997_; lean_object* v_bs_x27_5998_; size_t v___x_5999_; size_t v___x_6000_; lean_object* v___x_6001_; 
v_v_5995_ = lean_array_uget_borrowed(v_bs_5993_, v_i_5992_);
v_rendered_5996_ = lean_ctor_get(v_v_5995_, 0);
lean_inc_ref(v_rendered_5996_);
v___x_5997_ = lean_unsigned_to_nat(0u);
v_bs_x27_5998_ = lean_array_uset(v_bs_5993_, v_i_5992_, v___x_5997_);
v___x_5999_ = ((size_t)1ULL);
v___x_6000_ = lean_usize_add(v_i_5992_, v___x_5999_);
v___x_6001_ = lean_array_uset(v_bs_x27_5998_, v_i_5992_, v_rendered_5996_);
v_i_5992_ = v___x_6000_;
v_bs_5993_ = v___x_6001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object* v_sz_6003_, lean_object* v_i_6004_, lean_object* v_bs_6005_){
_start:
{
size_t v_sz_boxed_6006_; size_t v_i_boxed_6007_; lean_object* v_res_6008_; 
v_sz_boxed_6006_ = lean_unbox_usize(v_sz_6003_);
lean_dec(v_sz_6003_);
v_i_boxed_6007_ = lean_unbox_usize(v_i_6004_);
lean_dec(v_i_6004_);
v_res_6008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_boxed_6006_, v_i_boxed_6007_, v_bs_6005_);
return v_res_6008_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; 
v___x_6009_ = lean_box(0);
v___x_6010_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6011_, 0, v___x_6010_);
lean_ctor_set(v___x_6011_, 1, v___x_6009_);
return v___x_6011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object* v_upperBound_6012_, lean_object* v_next_6013_, lean_object* v_upperBound_6014_, lean_object* v_a_6015_, lean_object* v_b_6016_){
_start:
{
uint8_t v___x_6017_; 
v___x_6017_ = lean_nat_dec_lt(v_a_6015_, v_upperBound_6012_);
if (v___x_6017_ == 0)
{
lean_dec(v_a_6015_);
return v_b_6016_;
}
else
{
lean_object* v_fst_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6032_; 
v_fst_6018_ = lean_ctor_get(v_b_6016_, 0);
v_isSharedCheck_6032_ = !lean_is_exclusive(v_b_6016_);
if (v_isSharedCheck_6032_ == 0)
{
lean_object* v_unused_6033_; 
v_unused_6033_ = lean_ctor_get(v_b_6016_, 1);
lean_dec(v_unused_6033_);
v___x_6020_ = v_b_6016_;
v_isShared_6021_ = v_isSharedCheck_6032_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_fst_6018_);
lean_dec(v_b_6016_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6032_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
uint8_t v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6027_; 
v___x_6022_ = lean_nat_dec_lt(v_next_6013_, v_upperBound_6014_);
v___x_6023_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6024_ = lean_array_push(v_fst_6018_, v___x_6023_);
v___x_6025_ = lean_box(v___x_6022_);
if (v_isShared_6021_ == 0)
{
lean_ctor_set(v___x_6020_, 1, v___x_6025_);
lean_ctor_set(v___x_6020_, 0, v___x_6024_);
v___x_6027_ = v___x_6020_;
goto v_reusejp_6026_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_6024_);
lean_ctor_set(v_reuseFailAlloc_6031_, 1, v___x_6025_);
v___x_6027_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6026_;
}
v_reusejp_6026_:
{
lean_object* v___x_6028_; lean_object* v___x_6029_; 
v___x_6028_ = lean_unsigned_to_nat(1u);
v___x_6029_ = lean_nat_add(v_a_6015_, v___x_6028_);
lean_dec(v_a_6015_);
v_a_6015_ = v___x_6029_;
v_b_6016_ = v___x_6027_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object* v_upperBound_6034_, lean_object* v_next_6035_, lean_object* v_upperBound_6036_, lean_object* v_a_6037_, lean_object* v_b_6038_){
_start:
{
lean_object* v_res_6039_; 
v_res_6039_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6034_, v_next_6035_, v_upperBound_6036_, v_a_6037_, v_b_6038_);
lean_dec(v_upperBound_6036_);
lean_dec(v_next_6035_);
lean_dec(v_upperBound_6034_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(lean_object* v_originalWhitespaceRange_6040_, lean_object* v_fst_6041_, lean_object* v_____r_6042_, uint8_t v_insertedAnyNewlines_6043_, lean_object* v_d_6044_){
_start:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; 
v___x_6045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6045_, 0, v_originalWhitespaceRange_6040_);
v___x_6046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6046_, 0, v_d_6044_);
lean_ctor_set(v___x_6046_, 1, v___x_6045_);
v___x_6047_ = lean_array_push(v_fst_6041_, v___x_6046_);
v___x_6048_ = lean_box(v_insertedAnyNewlines_6043_);
v___x_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6049_, 0, v___x_6047_);
lean_ctor_set(v___x_6049_, 1, v___x_6048_);
v___x_6050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6049_);
return v___x_6050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed(lean_object* v_originalWhitespaceRange_6051_, lean_object* v_fst_6052_, lean_object* v_____r_6053_, lean_object* v_insertedAnyNewlines_6054_, lean_object* v_d_6055_){
_start:
{
uint8_t v_insertedAnyNewlines_boxed_6056_; lean_object* v_res_6057_; 
v_insertedAnyNewlines_boxed_6056_ = lean_unbox(v_insertedAnyNewlines_6054_);
v_res_6057_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6051_, v_fst_6052_, v_____r_6053_, v_insertedAnyNewlines_boxed_6056_, v_d_6055_);
return v_res_6057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object* v_a_6058_, lean_object* v___x_6059_, lean_object* v___x_6060_, lean_object* v_a_6061_, lean_object* v_b_6062_){
_start:
{
lean_object* v_it_6064_; lean_object* v_startInclusive_6065_; lean_object* v_endExclusive_6066_; 
if (lean_obj_tag(v_a_6061_) == 0)
{
lean_object* v_currPos_6072_; lean_object* v_searcher_6073_; lean_object* v___x_6075_; uint8_t v_isShared_6076_; uint8_t v_isSharedCheck_6096_; 
v_currPos_6072_ = lean_ctor_get(v_a_6061_, 0);
v_searcher_6073_ = lean_ctor_get(v_a_6061_, 1);
v_isSharedCheck_6096_ = !lean_is_exclusive(v_a_6061_);
if (v_isSharedCheck_6096_ == 0)
{
v___x_6075_ = v_a_6061_;
v_isShared_6076_ = v_isSharedCheck_6096_;
goto v_resetjp_6074_;
}
else
{
lean_inc(v_searcher_6073_);
lean_inc(v_currPos_6072_);
lean_dec(v_a_6061_);
v___x_6075_ = lean_box(0);
v_isShared_6076_ = v_isSharedCheck_6096_;
goto v_resetjp_6074_;
}
v_resetjp_6074_:
{
uint8_t v_decide_6077_; 
v_decide_6077_ = lean_nat_dec_eq(v_searcher_6073_, v___x_6060_);
if (v_decide_6077_ == 0)
{
uint32_t v___x_6078_; uint32_t v___x_6079_; uint8_t v___x_6080_; 
v___x_6078_ = 10;
v___x_6079_ = lean_string_utf8_get_fast(v_a_6058_, v_searcher_6073_);
v___x_6080_ = lean_uint32_dec_eq(v___x_6079_, v___x_6078_);
if (v___x_6080_ == 0)
{
lean_object* v___x_6081_; lean_object* v___x_6083_; 
v___x_6081_ = lean_string_utf8_next_fast(v_a_6058_, v_searcher_6073_);
lean_dec(v_searcher_6073_);
if (v_isShared_6076_ == 0)
{
lean_ctor_set(v___x_6075_, 1, v___x_6081_);
v___x_6083_ = v___x_6075_;
goto v_reusejp_6082_;
}
else
{
lean_object* v_reuseFailAlloc_6085_; 
v_reuseFailAlloc_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_currPos_6072_);
lean_ctor_set(v_reuseFailAlloc_6085_, 1, v___x_6081_);
v___x_6083_ = v_reuseFailAlloc_6085_;
goto v_reusejp_6082_;
}
v_reusejp_6082_:
{
v_a_6061_ = v___x_6083_;
goto _start;
}
}
else
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v_slice_6089_; lean_object* v_nextIt_6091_; 
v___x_6086_ = lean_string_utf8_next_fast(v_a_6058_, v_searcher_6073_);
v___x_6087_ = lean_nat_sub(v___x_6086_, v_searcher_6073_);
v___x_6088_ = lean_nat_add(v_searcher_6073_, v___x_6087_);
lean_dec(v___x_6087_);
v_slice_6089_ = l_String_Slice_subslice_x21(v___x_6059_, v_currPos_6072_, v_searcher_6073_);
lean_inc(v___x_6088_);
if (v_isShared_6076_ == 0)
{
lean_ctor_set(v___x_6075_, 1, v___x_6088_);
lean_ctor_set(v___x_6075_, 0, v___x_6088_);
v_nextIt_6091_ = v___x_6075_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v___x_6088_);
lean_ctor_set(v_reuseFailAlloc_6094_, 1, v___x_6088_);
v_nextIt_6091_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
lean_object* v_startInclusive_6092_; lean_object* v_endExclusive_6093_; 
v_startInclusive_6092_ = lean_ctor_get(v_slice_6089_, 0);
lean_inc(v_startInclusive_6092_);
v_endExclusive_6093_ = lean_ctor_get(v_slice_6089_, 1);
lean_inc(v_endExclusive_6093_);
lean_dec_ref(v_slice_6089_);
v_it_6064_ = v_nextIt_6091_;
v_startInclusive_6065_ = v_startInclusive_6092_;
v_endExclusive_6066_ = v_endExclusive_6093_;
goto v___jp_6063_;
}
}
}
else
{
lean_object* v___x_6095_; 
lean_del_object(v___x_6075_);
lean_dec(v_searcher_6073_);
v___x_6095_ = lean_box(1);
lean_inc(v___x_6060_);
v_it_6064_ = v___x_6095_;
v_startInclusive_6065_ = v_currPos_6072_;
v_endExclusive_6066_ = v___x_6060_;
goto v___jp_6063_;
}
}
}
else
{
lean_dec(v___x_6060_);
lean_dec_ref(v_a_6058_);
return v_b_6062_;
}
v___jp_6063_:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
lean_inc_ref(v_a_6058_);
v___x_6067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6067_, 0, v_a_6058_);
lean_ctor_set(v___x_6067_, 1, v_startInclusive_6065_);
lean_ctor_set(v___x_6067_, 2, v_endExclusive_6066_);
v___x_6068_ = l_String_Slice_toString(v___x_6067_);
lean_dec_ref_known(v___x_6067_, 3);
v___x_6069_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_6068_);
v___x_6070_ = lean_array_push(v_b_6062_, v___x_6069_);
v_a_6061_ = v_it_6064_;
v_b_6062_ = v___x_6070_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object* v_a_6097_, lean_object* v___x_6098_, lean_object* v___x_6099_, lean_object* v_a_6100_, lean_object* v_b_6101_){
_start:
{
lean_object* v_res_6102_; 
v_res_6102_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6097_, v___x_6098_, v___x_6099_, v_a_6100_, v_b_6101_);
lean_dec_ref(v___x_6098_);
return v_res_6102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(size_t v_sz_6103_, size_t v_i_6104_, lean_object* v_bs_6105_){
_start:
{
uint8_t v___x_6106_; 
v___x_6106_ = lean_usize_dec_lt(v_i_6104_, v_sz_6103_);
if (v___x_6106_ == 0)
{
return v_bs_6105_;
}
else
{
lean_object* v_v_6107_; lean_object* v___x_6108_; lean_object* v_bs_x27_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; size_t v___x_6118_; size_t v___x_6119_; lean_object* v___x_6120_; 
v_v_6107_ = lean_array_uget(v_bs_6105_, v_i_6104_);
v___x_6108_ = lean_unsigned_to_nat(0u);
v_bs_x27_6109_ = lean_array_uset(v_bs_6105_, v_i_6104_, v___x_6108_);
v___x_6110_ = lean_string_utf8_byte_size(v_v_6107_);
lean_inc(v_v_6107_);
v___x_6111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6111_, 0, v_v_6107_);
lean_ctor_set(v___x_6111_, 1, v___x_6108_);
lean_ctor_set(v___x_6111_, 2, v___x_6110_);
v___x_6112_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
v___x_6113_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_6114_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_v_6107_, v___x_6111_, v___x_6110_, v___x_6112_, v___x_6113_);
lean_dec_ref_known(v___x_6111_, 3);
v___x_6115_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_6116_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_6115_, v___x_6114_);
v___x_6117_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6116_);
v___x_6118_ = ((size_t)1ULL);
v___x_6119_ = lean_usize_add(v_i_6104_, v___x_6118_);
v___x_6120_ = lean_array_uset(v_bs_x27_6109_, v_i_6104_, v___x_6117_);
v_i_6104_ = v___x_6119_;
v_bs_6105_ = v___x_6120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg___boxed(lean_object* v_sz_6122_, lean_object* v_i_6123_, lean_object* v_bs_6124_){
_start:
{
size_t v_sz_boxed_6125_; size_t v_i_boxed_6126_; lean_object* v_res_6127_; 
v_sz_boxed_6125_ = lean_unbox_usize(v_sz_6122_);
lean_dec(v_sz_6122_);
v_i_boxed_6126_ = lean_unbox_usize(v_i_6123_);
lean_dec(v_i_6123_);
v_res_6127_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_boxed_6125_, v_i_boxed_6126_, v_bs_6124_);
return v_res_6127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object* v_a_6128_, lean_object* v_x_6129_){
_start:
{
if (lean_obj_tag(v_x_6129_) == 0)
{
lean_object* v___x_6130_; 
v___x_6130_ = lean_box(0);
return v___x_6130_;
}
else
{
lean_object* v_key_6131_; lean_object* v_value_6132_; lean_object* v_tail_6133_; uint8_t v___x_6134_; 
v_key_6131_ = lean_ctor_get(v_x_6129_, 0);
v_value_6132_ = lean_ctor_get(v_x_6129_, 1);
v_tail_6133_ = lean_ctor_get(v_x_6129_, 2);
v___x_6134_ = lean_nat_dec_eq(v_key_6131_, v_a_6128_);
if (v___x_6134_ == 0)
{
v_x_6129_ = v_tail_6133_;
goto _start;
}
else
{
lean_object* v___x_6136_; 
lean_inc(v_value_6132_);
v___x_6136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6136_, 0, v_value_6132_);
return v___x_6136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object* v_a_6137_, lean_object* v_x_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6137_, v_x_6138_);
lean_dec(v_x_6138_);
lean_dec(v_a_6137_);
return v_res_6139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object* v_m_6140_, lean_object* v_a_6141_){
_start:
{
lean_object* v_buckets_6142_; lean_object* v___x_6143_; uint64_t v___x_6144_; uint64_t v___x_6145_; uint64_t v___x_6146_; uint64_t v_fold_6147_; uint64_t v___x_6148_; uint64_t v___x_6149_; uint64_t v___x_6150_; size_t v___x_6151_; size_t v___x_6152_; size_t v___x_6153_; size_t v___x_6154_; size_t v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; 
v_buckets_6142_ = lean_ctor_get(v_m_6140_, 1);
v___x_6143_ = lean_array_get_size(v_buckets_6142_);
v___x_6144_ = lean_uint64_of_nat(v_a_6141_);
v___x_6145_ = 32ULL;
v___x_6146_ = lean_uint64_shift_right(v___x_6144_, v___x_6145_);
v_fold_6147_ = lean_uint64_xor(v___x_6144_, v___x_6146_);
v___x_6148_ = 16ULL;
v___x_6149_ = lean_uint64_shift_right(v_fold_6147_, v___x_6148_);
v___x_6150_ = lean_uint64_xor(v_fold_6147_, v___x_6149_);
v___x_6151_ = lean_uint64_to_usize(v___x_6150_);
v___x_6152_ = lean_usize_of_nat(v___x_6143_);
v___x_6153_ = ((size_t)1ULL);
v___x_6154_ = lean_usize_sub(v___x_6152_, v___x_6153_);
v___x_6155_ = lean_usize_land(v___x_6151_, v___x_6154_);
v___x_6156_ = lean_array_uget_borrowed(v_buckets_6142_, v___x_6155_);
v___x_6157_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6141_, v___x_6156_);
return v___x_6157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object* v_m_6158_, lean_object* v_a_6159_){
_start:
{
lean_object* v_res_6160_; 
v_res_6160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6158_, v_a_6159_);
lean_dec(v_a_6159_);
lean_dec_ref(v_m_6158_);
return v_res_6160_;
}
}
static uint8_t _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_6161_; uint8_t v___x_6162_; 
v___x_6161_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6162_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6161_);
return v___x_6162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(lean_object* v_upperBound_6163_, lean_object* v_comments_6164_, lean_object* v_numNewlinesBeforeComments_6165_, lean_object* v_a_6166_, lean_object* v_b_6167_){
_start:
{
lean_object* v___y_6169_; uint8_t v___x_6175_; lean_object* v___y_6177_; lean_object* v___y_6178_; 
v___x_6175_ = lean_nat_dec_lt(v_a_6166_, v_upperBound_6163_);
if (v___x_6175_ == 0)
{
lean_dec(v_a_6166_);
return v_b_6167_;
}
else
{
lean_object* v_fst_6182_; lean_object* v_snd_6183_; lean_object* v___x_6185_; uint8_t v_isShared_6186_; uint8_t v_isSharedCheck_6249_; 
v_fst_6182_ = lean_ctor_get(v_b_6167_, 0);
v_snd_6183_ = lean_ctor_get(v_b_6167_, 1);
v_isSharedCheck_6249_ = !lean_is_exclusive(v_b_6167_);
if (v_isSharedCheck_6249_ == 0)
{
v___x_6185_ = v_b_6167_;
v_isShared_6186_ = v_isSharedCheck_6249_;
goto v_resetjp_6184_;
}
else
{
lean_inc(v_snd_6183_);
lean_inc(v_fst_6182_);
lean_dec(v_b_6167_);
v___x_6185_ = lean_box(0);
v_isShared_6186_ = v_isSharedCheck_6249_;
goto v_resetjp_6184_;
}
v_resetjp_6184_:
{
lean_object* v___x_6187_; lean_object* v___y_6189_; lean_object* v___y_6223_; lean_object* v___y_6224_; lean_object* v___y_6227_; uint8_t v___y_6230_; lean_object* v___y_6231_; uint8_t v___y_6235_; lean_object* v___y_6236_; uint8_t v___y_6240_; uint8_t v_insertedAnyNewlines_6243_; uint8_t v___x_6244_; 
v___x_6187_ = lean_unsigned_to_nat(0u);
v_insertedAnyNewlines_6243_ = 0;
v___x_6244_ = lean_nat_dec_eq(v_a_6166_, v___x_6187_);
if (v___x_6244_ == 0)
{
lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; uint8_t v_kind_6248_; 
v___x_6245_ = lean_unsigned_to_nat(1u);
v___x_6246_ = lean_nat_sub(v_a_6166_, v___x_6245_);
v___x_6247_ = lean_array_fget_borrowed(v_comments_6164_, v___x_6246_);
lean_dec(v___x_6246_);
v_kind_6248_ = lean_ctor_get_uint8(v___x_6247_, sizeof(void*)*3);
if (v_kind_6248_ == 1)
{
v___y_6240_ = v___x_6175_;
goto v___jp_6239_;
}
else
{
v___y_6240_ = v_insertedAnyNewlines_6243_;
goto v___jp_6239_;
}
}
else
{
v___y_6240_ = v_insertedAnyNewlines_6243_;
goto v___jp_6239_;
}
v___jp_6188_:
{
lean_object* v___x_6191_; 
if (v_isShared_6186_ == 0)
{
v___x_6191_ = v___x_6185_;
goto v_reusejp_6190_;
}
else
{
lean_object* v_reuseFailAlloc_6221_; 
v_reuseFailAlloc_6221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6221_, 0, v_fst_6182_);
lean_ctor_set(v_reuseFailAlloc_6221_, 1, v_snd_6183_);
v___x_6191_ = v_reuseFailAlloc_6221_;
goto v_reusejp_6190_;
}
v_reusejp_6190_:
{
lean_object* v___x_6192_; lean_object* v_fst_6193_; lean_object* v_snd_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; size_t v_sz_6197_; size_t v___x_6198_; lean_object* v___x_6199_; size_t v_sz_6200_; uint8_t v_kind_6201_; lean_object* v_originalWhitespaceRange_6202_; lean_object* v___x_6203_; lean_object* v___f_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; 
v___x_6192_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v___y_6189_, v_a_6166_, v_upperBound_6163_, v___x_6187_, v___x_6191_);
lean_dec(v___y_6189_);
v_fst_6193_ = lean_ctor_get(v___x_6192_, 0);
lean_inc_n(v_fst_6193_, 2);
v_snd_6194_ = lean_ctor_get(v___x_6192_, 1);
lean_inc(v_snd_6194_);
lean_dec_ref(v___x_6192_);
v___x_6195_ = lean_array_fget_borrowed(v_comments_6164_, v_a_6166_);
lean_inc(v___x_6195_);
v___x_6196_ = l_Lean_Fmt_Comment_render(v___x_6195_);
v_sz_6197_ = lean_array_size(v___x_6196_);
v___x_6198_ = ((size_t)0ULL);
v___x_6199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_6197_, v___x_6198_, v___x_6196_);
v_sz_6200_ = lean_array_size(v___x_6199_);
v_kind_6201_ = lean_ctor_get_uint8(v___x_6195_, sizeof(void*)*3);
v_originalWhitespaceRange_6202_ = lean_ctor_get(v___x_6195_, 1);
v___x_6203_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6200_, v___x_6198_, v___x_6199_);
lean_inc_ref(v_originalWhitespaceRange_6202_);
v___f_6204_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_6204_, 0, v_originalWhitespaceRange_6202_);
lean_closure_set(v___f_6204_, 1, v_fst_6193_);
v___x_6205_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_6203_);
v___x_6206_ = l_Lean_Fmt_TaggedDoc_free(v___x_6205_);
if (v_kind_6201_ == 0)
{
lean_object* v___x_6207_; uint8_t v___x_6208_; 
lean_dec(v_snd_6194_);
lean_dec(v_fst_6193_);
v___x_6207_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6208_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6206_);
if (v___x_6208_ == 0)
{
uint8_t v___x_6209_; 
v___x_6209_ = lean_uint8_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0);
if (v___x_6209_ == 0)
{
lean_object* v_doc_6210_; lean_object* v_doc_6211_; uint8_t v___x_6212_; 
v_doc_6210_ = lean_ctor_get(v___x_6206_, 0);
lean_inc(v_doc_6210_);
lean_dec_ref(v___x_6206_);
v_doc_6211_ = lean_ctor_get(v___x_6207_, 0);
v___x_6212_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6210_);
if (v___x_6212_ == 0)
{
uint8_t v___x_6213_; 
v___x_6213_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6211_);
if (v___x_6213_ == 0)
{
lean_object* v___x_6214_; lean_object* v___x_6215_; 
lean_inc(v_doc_6211_);
v___x_6214_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_6210_, v_doc_6211_);
v___x_6215_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6214_);
v___y_6177_ = v___f_6204_;
v___y_6178_ = v___x_6215_;
goto v___jp_6176_;
}
else
{
lean_object* v___x_6216_; 
v___x_6216_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6210_);
v___y_6177_ = v___f_6204_;
v___y_6178_ = v___x_6216_;
goto v___jp_6176_;
}
}
else
{
lean_object* v___x_6217_; 
lean_dec(v_doc_6210_);
lean_inc(v_doc_6211_);
v___x_6217_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6211_);
v___y_6177_ = v___f_6204_;
v___y_6178_ = v___x_6217_;
goto v___jp_6176_;
}
}
else
{
v___y_6177_ = v___f_6204_;
v___y_6178_ = v___x_6206_;
goto v___jp_6176_;
}
}
else
{
lean_dec_ref(v___x_6206_);
v___y_6177_ = v___f_6204_;
v___y_6178_ = v___x_6207_;
goto v___jp_6176_;
}
}
else
{
lean_object* v___x_6218_; uint8_t v___x_6219_; lean_object* v___x_6220_; 
lean_dec_ref(v___f_6204_);
v___x_6218_ = lean_box(0);
v___x_6219_ = lean_unbox(v_snd_6194_);
lean_dec(v_snd_6194_);
lean_inc_ref(v_originalWhitespaceRange_6202_);
v___x_6220_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6202_, v_fst_6193_, v___x_6218_, v___x_6219_, v___x_6206_);
v___y_6169_ = v___x_6220_;
goto v___jp_6168_;
}
}
}
v___jp_6222_:
{
uint8_t v___x_6225_; 
v___x_6225_ = lean_nat_dec_le(v___y_6223_, v___y_6224_);
if (v___x_6225_ == 0)
{
lean_dec(v___y_6223_);
v___y_6189_ = v___y_6224_;
goto v___jp_6188_;
}
else
{
lean_dec(v___y_6224_);
v___y_6189_ = v___y_6223_;
goto v___jp_6188_;
}
}
v___jp_6226_:
{
lean_object* v___x_6228_; 
v___x_6228_ = lean_unsigned_to_nat(2u);
v___y_6223_ = v___y_6227_;
v___y_6224_ = v___x_6228_;
goto v___jp_6222_;
}
v___jp_6229_:
{
uint8_t v___x_6232_; 
v___x_6232_ = lean_nat_dec_eq(v_a_6166_, v___x_6187_);
if (v___x_6232_ == 0)
{
if (v___y_6230_ == 0)
{
lean_object* v___x_6233_; 
v___x_6233_ = lean_unsigned_to_nat(1u);
v___y_6223_ = v___y_6231_;
v___y_6224_ = v___x_6233_;
goto v___jp_6222_;
}
else
{
v___y_6227_ = v___y_6231_;
goto v___jp_6226_;
}
}
else
{
v___y_6227_ = v___y_6231_;
goto v___jp_6226_;
}
}
v___jp_6234_:
{
if (v___y_6235_ == 0)
{
v___y_6230_ = v___y_6235_;
v___y_6231_ = v___y_6236_;
goto v___jp_6229_;
}
else
{
lean_object* v___x_6237_; uint8_t v___x_6238_; 
v___x_6237_ = lean_unsigned_to_nat(1u);
v___x_6238_ = lean_nat_dec_le(v___y_6236_, v___x_6237_);
if (v___x_6238_ == 0)
{
v___y_6230_ = v___y_6235_;
v___y_6231_ = v___y_6236_;
goto v___jp_6229_;
}
else
{
lean_dec(v___y_6236_);
v___y_6230_ = v___y_6235_;
v___y_6231_ = v___x_6237_;
goto v___jp_6229_;
}
}
}
v___jp_6239_:
{
lean_object* v___x_6241_; 
v___x_6241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_numNewlinesBeforeComments_6165_, v_a_6166_);
if (lean_obj_tag(v___x_6241_) == 0)
{
v___y_6235_ = v___y_6240_;
v___y_6236_ = v___x_6187_;
goto v___jp_6234_;
}
else
{
lean_object* v_val_6242_; 
v_val_6242_ = lean_ctor_get(v___x_6241_, 0);
lean_inc(v_val_6242_);
lean_dec_ref_known(v___x_6241_, 1);
v___y_6235_ = v___y_6240_;
v___y_6236_ = v_val_6242_;
goto v___jp_6234_;
}
}
}
}
v___jp_6168_:
{
if (lean_obj_tag(v___y_6169_) == 0)
{
lean_object* v_a_6170_; 
lean_dec(v_a_6166_);
v_a_6170_ = lean_ctor_get(v___y_6169_, 0);
lean_inc(v_a_6170_);
lean_dec_ref_known(v___y_6169_, 1);
return v_a_6170_;
}
else
{
lean_object* v_a_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v_a_6171_ = lean_ctor_get(v___y_6169_, 0);
lean_inc(v_a_6171_);
lean_dec_ref_known(v___y_6169_, 1);
v___x_6172_ = lean_unsigned_to_nat(1u);
v___x_6173_ = lean_nat_add(v_a_6166_, v___x_6172_);
lean_dec(v_a_6166_);
v_a_6166_ = v___x_6173_;
v_b_6167_ = v_a_6171_;
goto _start;
}
}
v___jp_6176_:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; 
v___x_6179_ = lean_box(0);
v___x_6180_ = lean_box(v___x_6175_);
v___x_6181_ = lean_apply_3(v___y_6177_, v___x_6179_, v___x_6180_, v___y_6178_);
v___y_6169_ = v___x_6181_;
goto v___jp_6168_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___boxed(lean_object* v_upperBound_6250_, lean_object* v_comments_6251_, lean_object* v_numNewlinesBeforeComments_6252_, lean_object* v_a_6253_, lean_object* v_b_6254_){
_start:
{
lean_object* v_res_6255_; 
v_res_6255_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6250_, v_comments_6251_, v_numNewlinesBeforeComments_6252_, v_a_6253_, v_b_6254_);
lean_dec_ref(v_numNewlinesBeforeComments_6252_);
lean_dec_ref(v_comments_6251_);
lean_dec(v_upperBound_6250_);
return v_res_6255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object* v_upperBound_6256_, lean_object* v_a_6257_, lean_object* v_b_6258_){
_start:
{
uint8_t v___x_6259_; 
v___x_6259_ = lean_nat_dec_lt(v_a_6257_, v_upperBound_6256_);
if (v___x_6259_ == 0)
{
lean_dec(v_a_6257_);
return v_b_6258_;
}
else
{
lean_object* v_fst_6260_; lean_object* v___x_6262_; uint8_t v_isShared_6263_; uint8_t v_isSharedCheck_6273_; 
v_fst_6260_ = lean_ctor_get(v_b_6258_, 0);
v_isSharedCheck_6273_ = !lean_is_exclusive(v_b_6258_);
if (v_isSharedCheck_6273_ == 0)
{
lean_object* v_unused_6274_; 
v_unused_6274_ = lean_ctor_get(v_b_6258_, 1);
lean_dec(v_unused_6274_);
v___x_6262_ = v_b_6258_;
v_isShared_6263_ = v_isSharedCheck_6273_;
goto v_resetjp_6261_;
}
else
{
lean_inc(v_fst_6260_);
lean_dec(v_b_6258_);
v___x_6262_ = lean_box(0);
v_isShared_6263_ = v_isSharedCheck_6273_;
goto v_resetjp_6261_;
}
v_resetjp_6261_:
{
lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; lean_object* v___x_6268_; 
v___x_6264_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6265_ = lean_array_push(v_fst_6260_, v___x_6264_);
v___x_6266_ = lean_box(v___x_6259_);
if (v_isShared_6263_ == 0)
{
lean_ctor_set(v___x_6262_, 1, v___x_6266_);
lean_ctor_set(v___x_6262_, 0, v___x_6265_);
v___x_6268_ = v___x_6262_;
goto v_reusejp_6267_;
}
else
{
lean_object* v_reuseFailAlloc_6272_; 
v_reuseFailAlloc_6272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6272_, 0, v___x_6265_);
lean_ctor_set(v_reuseFailAlloc_6272_, 1, v___x_6266_);
v___x_6268_ = v_reuseFailAlloc_6272_;
goto v_reusejp_6267_;
}
v_reusejp_6267_:
{
lean_object* v___x_6269_; lean_object* v___x_6270_; 
v___x_6269_ = lean_unsigned_to_nat(1u);
v___x_6270_ = lean_nat_add(v_a_6257_, v___x_6269_);
lean_dec(v_a_6257_);
v_a_6257_ = v___x_6270_;
v_b_6258_ = v___x_6268_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object* v_upperBound_6275_, lean_object* v_a_6276_, lean_object* v_b_6277_){
_start:
{
lean_object* v_res_6278_; 
v_res_6278_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6275_, v_a_6276_, v_b_6277_);
lean_dec(v_upperBound_6275_);
return v_res_6278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(lean_object* v_as_6279_, size_t v_i_6280_, size_t v_stop_6281_, lean_object* v_b_6282_){
_start:
{
lean_object* v___y_6284_; uint8_t v___x_6288_; 
v___x_6288_ = lean_usize_dec_eq(v_i_6280_, v_stop_6281_);
if (v___x_6288_ == 0)
{
lean_object* v___x_6289_; uint8_t v_placement_6290_; 
v___x_6289_ = lean_array_uget_borrowed(v_as_6279_, v_i_6280_);
v_placement_6290_ = lean_ctor_get_uint8(v___x_6289_, sizeof(void*)*3 + 1);
if (v_placement_6290_ == 0)
{
v___y_6284_ = v_b_6282_;
goto v___jp_6283_;
}
else
{
lean_object* v___x_6291_; 
lean_inc(v___x_6289_);
v___x_6291_ = lean_array_push(v_b_6282_, v___x_6289_);
v___y_6284_ = v___x_6291_;
goto v___jp_6283_;
}
}
else
{
return v_b_6282_;
}
v___jp_6283_:
{
size_t v___x_6285_; size_t v___x_6286_; 
v___x_6285_ = ((size_t)1ULL);
v___x_6286_ = lean_usize_add(v_i_6280_, v___x_6285_);
v_i_6280_ = v___x_6286_;
v_b_6282_ = v___y_6284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8___boxed(lean_object* v_as_6292_, lean_object* v_i_6293_, lean_object* v_stop_6294_, lean_object* v_b_6295_){
_start:
{
size_t v_i_boxed_6296_; size_t v_stop_boxed_6297_; lean_object* v_res_6298_; 
v_i_boxed_6296_ = lean_unbox_usize(v_i_6293_);
lean_dec(v_i_6293_);
v_stop_boxed_6297_ = lean_unbox_usize(v_stop_6294_);
lean_dec(v_stop_6294_);
v_res_6298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_as_6292_, v_i_boxed_6296_, v_stop_boxed_6297_, v_b_6295_);
lean_dec_ref(v_as_6292_);
return v_res_6298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object* v_comments_6305_, lean_object* v_whitespace_6306_, uint8_t v_isLeading_6307_){
_start:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___y_6311_; lean_object* v___y_6312_; lean_object* v___y_6313_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___x_6336_; lean_object* v___y_6338_; lean_object* v___y_6339_; uint8_t v___y_6340_; lean_object* v___y_6341_; lean_object* v___y_6347_; lean_object* v___y_6348_; uint8_t v___y_6349_; lean_object* v___y_6350_; lean_object* v___y_6354_; lean_object* v___y_6355_; lean_object* v___y_6356_; uint8_t v___y_6357_; lean_object* v___y_6361_; lean_object* v___x_6374_; uint8_t v___x_6375_; 
v___x_6308_ = l_Lean_Fmt_instInhabitedComment_default;
v___x_6309_ = lean_unsigned_to_nat(0u);
v___x_6336_ = lean_array_get_size(v_comments_6305_);
v___x_6374_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6375_ = lean_nat_dec_lt(v___x_6309_, v___x_6336_);
if (v___x_6375_ == 0)
{
v___y_6361_ = v___x_6374_;
goto v___jp_6360_;
}
else
{
size_t v___x_6376_; size_t v___x_6377_; lean_object* v___x_6378_; 
v___x_6376_ = ((size_t)0ULL);
v___x_6377_ = lean_usize_of_nat(v___x_6336_);
v___x_6378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_comments_6305_, v___x_6376_, v___x_6377_, v___x_6374_);
v___y_6361_ = v___x_6378_;
goto v___jp_6360_;
}
v___jp_6310_:
{
lean_object* v___x_6314_; lean_object* v___x_6315_; lean_object* v_fst_6316_; lean_object* v_snd_6317_; lean_object* v___x_6319_; uint8_t v_isShared_6320_; uint8_t v_isSharedCheck_6324_; 
v___x_6314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6314_, 0, v___y_6312_);
lean_ctor_set(v___x_6314_, 1, v___y_6311_);
v___x_6315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v___y_6313_, v___x_6309_, v___x_6314_);
lean_dec(v___y_6313_);
v_fst_6316_ = lean_ctor_get(v___x_6315_, 0);
v_snd_6317_ = lean_ctor_get(v___x_6315_, 1);
v_isSharedCheck_6324_ = !lean_is_exclusive(v___x_6315_);
if (v_isSharedCheck_6324_ == 0)
{
v___x_6319_ = v___x_6315_;
v_isShared_6320_ = v_isSharedCheck_6324_;
goto v_resetjp_6318_;
}
else
{
lean_inc(v_snd_6317_);
lean_inc(v_fst_6316_);
lean_dec(v___x_6315_);
v___x_6319_ = lean_box(0);
v_isShared_6320_ = v_isSharedCheck_6324_;
goto v_resetjp_6318_;
}
v_resetjp_6318_:
{
lean_object* v___x_6322_; 
if (v_isShared_6320_ == 0)
{
v___x_6322_ = v___x_6319_;
goto v_reusejp_6321_;
}
else
{
lean_object* v_reuseFailAlloc_6323_; 
v_reuseFailAlloc_6323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6323_, 0, v_fst_6316_);
lean_ctor_set(v_reuseFailAlloc_6323_, 1, v_snd_6317_);
v___x_6322_ = v_reuseFailAlloc_6323_;
goto v_reusejp_6321_;
}
v_reusejp_6321_:
{
return v___x_6322_;
}
}
}
v___jp_6325_:
{
uint8_t v___x_6330_; 
v___x_6330_ = lean_nat_dec_le(v___y_6328_, v___y_6329_);
if (v___x_6330_ == 0)
{
lean_dec(v___y_6328_);
v___y_6311_ = v___y_6326_;
v___y_6312_ = v___y_6327_;
v___y_6313_ = v___y_6329_;
goto v___jp_6310_;
}
else
{
lean_dec(v___y_6329_);
v___y_6311_ = v___y_6326_;
v___y_6312_ = v___y_6327_;
v___y_6313_ = v___y_6328_;
goto v___jp_6310_;
}
}
v___jp_6331_:
{
lean_object* v___x_6335_; 
v___x_6335_ = lean_unsigned_to_nat(2u);
v___y_6326_ = v___y_6332_;
v___y_6327_ = v___y_6333_;
v___y_6328_ = v___y_6334_;
v___y_6329_ = v___x_6335_;
goto v___jp_6325_;
}
v___jp_6337_:
{
if (v_isLeading_6307_ == 0)
{
uint8_t v___x_6342_; 
v___x_6342_ = lean_nat_dec_eq(v___x_6336_, v___x_6309_);
if (v___x_6342_ == 0)
{
if (v___y_6340_ == 0)
{
lean_object* v___x_6343_; 
v___x_6343_ = lean_unsigned_to_nat(1u);
v___y_6326_ = v___y_6338_;
v___y_6327_ = v___y_6339_;
v___y_6328_ = v___y_6341_;
v___y_6329_ = v___x_6343_;
goto v___jp_6325_;
}
else
{
v___y_6332_ = v___y_6338_;
v___y_6333_ = v___y_6339_;
v___y_6334_ = v___y_6341_;
goto v___jp_6331_;
}
}
else
{
v___y_6332_ = v___y_6338_;
v___y_6333_ = v___y_6339_;
v___y_6334_ = v___y_6341_;
goto v___jp_6331_;
}
}
else
{
uint8_t v___x_6344_; 
v___x_6344_ = lean_nat_dec_lt(v___x_6309_, v___x_6336_);
if (v___x_6344_ == 0)
{
v___y_6326_ = v___y_6338_;
v___y_6327_ = v___y_6339_;
v___y_6328_ = v___y_6341_;
v___y_6329_ = v___x_6309_;
goto v___jp_6325_;
}
else
{
lean_object* v___x_6345_; 
v___x_6345_ = lean_unsigned_to_nat(2u);
v___y_6326_ = v___y_6338_;
v___y_6327_ = v___y_6339_;
v___y_6328_ = v___y_6341_;
v___y_6329_ = v___x_6345_;
goto v___jp_6325_;
}
}
}
v___jp_6346_:
{
if (v___y_6349_ == 0)
{
v___y_6338_ = v___y_6347_;
v___y_6339_ = v___y_6348_;
v___y_6340_ = v___y_6349_;
v___y_6341_ = v___y_6350_;
goto v___jp_6337_;
}
else
{
lean_object* v___x_6351_; uint8_t v___x_6352_; 
v___x_6351_ = lean_unsigned_to_nat(1u);
v___x_6352_ = lean_nat_dec_le(v___y_6350_, v___x_6351_);
if (v___x_6352_ == 0)
{
v___y_6338_ = v___y_6347_;
v___y_6339_ = v___y_6348_;
v___y_6340_ = v___y_6349_;
v___y_6341_ = v___y_6350_;
goto v___jp_6337_;
}
else
{
lean_dec(v___y_6350_);
v___y_6338_ = v___y_6347_;
v___y_6339_ = v___y_6348_;
v___y_6340_ = v___y_6349_;
v___y_6341_ = v___x_6351_;
goto v___jp_6337_;
}
}
}
v___jp_6353_:
{
lean_object* v___x_6358_; 
v___x_6358_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v___y_6356_, v___x_6336_);
lean_dec_ref(v___y_6356_);
if (lean_obj_tag(v___x_6358_) == 0)
{
v___y_6347_ = v___y_6354_;
v___y_6348_ = v___y_6355_;
v___y_6349_ = v___y_6357_;
v___y_6350_ = v___x_6309_;
goto v___jp_6346_;
}
else
{
lean_object* v_val_6359_; 
v_val_6359_ = lean_ctor_get(v___x_6358_, 0);
lean_inc(v_val_6359_);
lean_dec_ref_known(v___x_6358_, 1);
v___y_6347_ = v___y_6354_;
v___y_6348_ = v___y_6355_;
v___y_6349_ = v___y_6357_;
v___y_6350_ = v_val_6359_;
goto v___jp_6346_;
}
}
v___jp_6360_:
{
lean_object* v_numNewlinesBeforeComments_6362_; uint8_t v_insertedAnyNewlines_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v_fst_6366_; lean_object* v_snd_6367_; uint8_t v___x_6368_; 
v_numNewlinesBeforeComments_6362_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v___y_6361_, v_whitespace_6306_);
lean_dec_ref(v___y_6361_);
v_insertedAnyNewlines_6363_ = 0;
v___x_6364_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0));
v___x_6365_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v___x_6336_, v_comments_6305_, v_numNewlinesBeforeComments_6362_, v___x_6309_, v___x_6364_);
v_fst_6366_ = lean_ctor_get(v___x_6365_, 0);
lean_inc(v_fst_6366_);
v_snd_6367_ = lean_ctor_get(v___x_6365_, 1);
lean_inc(v_snd_6367_);
lean_dec_ref(v___x_6365_);
v___x_6368_ = lean_nat_dec_eq(v___x_6336_, v___x_6309_);
if (v___x_6368_ == 0)
{
lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; uint8_t v_kind_6372_; 
v___x_6369_ = lean_unsigned_to_nat(1u);
v___x_6370_ = lean_nat_sub(v___x_6336_, v___x_6369_);
v___x_6371_ = lean_array_get_borrowed(v___x_6308_, v_comments_6305_, v___x_6370_);
lean_dec(v___x_6370_);
v_kind_6372_ = lean_ctor_get_uint8(v___x_6371_, sizeof(void*)*3);
if (v_kind_6372_ == 1)
{
uint8_t v___x_6373_; 
v___x_6373_ = 1;
v___y_6354_ = v_snd_6367_;
v___y_6355_ = v_fst_6366_;
v___y_6356_ = v_numNewlinesBeforeComments_6362_;
v___y_6357_ = v___x_6373_;
goto v___jp_6353_;
}
else
{
v___y_6354_ = v_snd_6367_;
v___y_6355_ = v_fst_6366_;
v___y_6356_ = v_numNewlinesBeforeComments_6362_;
v___y_6357_ = v_insertedAnyNewlines_6363_;
goto v___jp_6353_;
}
}
else
{
v___y_6354_ = v_snd_6367_;
v___y_6355_ = v_fst_6366_;
v___y_6356_ = v_numNewlinesBeforeComments_6362_;
v___y_6357_ = v_insertedAnyNewlines_6363_;
goto v___jp_6353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object* v_comments_6379_, lean_object* v_whitespace_6380_, lean_object* v_isLeading_6381_){
_start:
{
uint8_t v_isLeading_boxed_6382_; lean_object* v_res_6383_; 
v_isLeading_boxed_6382_ = lean_unbox(v_isLeading_6381_);
v_res_6383_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v_comments_6379_, v_whitespace_6380_, v_isLeading_boxed_6382_);
lean_dec_ref(v_whitespace_6380_);
lean_dec_ref(v_comments_6379_);
return v_res_6383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object* v_a_6384_, lean_object* v___x_6385_, lean_object* v___x_6386_, lean_object* v_inst_6387_, lean_object* v_R_6388_, lean_object* v_a_6389_, lean_object* v_b_6390_){
_start:
{
lean_object* v___x_6391_; 
v___x_6391_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6384_, v___x_6385_, v___x_6386_, v_a_6389_, v_b_6390_);
return v___x_6391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object* v_a_6392_, lean_object* v___x_6393_, lean_object* v___x_6394_, lean_object* v_inst_6395_, lean_object* v_R_6396_, lean_object* v_a_6397_, lean_object* v_b_6398_){
_start:
{
lean_object* v_res_6399_; 
v_res_6399_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(v_a_6392_, v___x_6393_, v___x_6394_, v_inst_6395_, v_R_6396_, v_a_6397_, v_b_6398_);
lean_dec_ref(v___x_6393_);
return v_res_6399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(lean_object* v_as_6400_, size_t v_sz_6401_, size_t v_i_6402_, lean_object* v_bs_6403_){
_start:
{
lean_object* v___x_6404_; 
v___x_6404_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6401_, v_i_6402_, v_bs_6403_);
return v___x_6404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object* v_as_6405_, lean_object* v_sz_6406_, lean_object* v_i_6407_, lean_object* v_bs_6408_){
_start:
{
size_t v_sz_boxed_6409_; size_t v_i_boxed_6410_; lean_object* v_res_6411_; 
v_sz_boxed_6409_ = lean_unbox_usize(v_sz_6406_);
lean_dec(v_sz_6406_);
v_i_boxed_6410_ = lean_unbox_usize(v_i_6407_);
lean_dec(v_i_6407_);
v_res_6411_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(v_as_6405_, v_sz_boxed_6409_, v_i_boxed_6410_, v_bs_6408_);
lean_dec_ref(v_as_6405_);
return v_res_6411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object* v_upperBound_6412_, lean_object* v_next_6413_, lean_object* v_upperBound_6414_, lean_object* v_inst_6415_, lean_object* v_R_6416_, lean_object* v_a_6417_, lean_object* v_b_6418_, lean_object* v_c_6419_){
_start:
{
lean_object* v___x_6420_; 
v___x_6420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6412_, v_next_6413_, v_upperBound_6414_, v_a_6417_, v_b_6418_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object* v_upperBound_6421_, lean_object* v_next_6422_, lean_object* v_upperBound_6423_, lean_object* v_inst_6424_, lean_object* v_R_6425_, lean_object* v_a_6426_, lean_object* v_b_6427_, lean_object* v_c_6428_){
_start:
{
lean_object* v_res_6429_; 
v_res_6429_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(v_upperBound_6421_, v_next_6422_, v_upperBound_6423_, v_inst_6424_, v_R_6425_, v_a_6426_, v_b_6427_, v_c_6428_);
lean_dec(v_upperBound_6423_);
lean_dec(v_next_6422_);
lean_dec(v_upperBound_6421_);
return v_res_6429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object* v_00_u03b2_6430_, lean_object* v_m_6431_, lean_object* v_a_6432_){
_start:
{
lean_object* v___x_6433_; 
v___x_6433_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6431_, v_a_6432_);
return v___x_6433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object* v_00_u03b2_6434_, lean_object* v_m_6435_, lean_object* v_a_6436_){
_start:
{
lean_object* v_res_6437_; 
v_res_6437_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(v_00_u03b2_6434_, v_m_6435_, v_a_6436_);
lean_dec(v_a_6436_);
lean_dec_ref(v_m_6435_);
return v_res_6437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object* v_upperBound_6438_, lean_object* v_inst_6439_, lean_object* v_R_6440_, lean_object* v_a_6441_, lean_object* v_b_6442_, lean_object* v_c_6443_){
_start:
{
lean_object* v___x_6444_; 
v___x_6444_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6438_, v_a_6441_, v_b_6442_);
return v___x_6444_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object* v_upperBound_6445_, lean_object* v_inst_6446_, lean_object* v_R_6447_, lean_object* v_a_6448_, lean_object* v_b_6449_, lean_object* v_c_6450_){
_start:
{
lean_object* v_res_6451_; 
v_res_6451_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(v_upperBound_6445_, v_inst_6446_, v_R_6447_, v_a_6448_, v_b_6449_, v_c_6450_);
lean_dec(v_upperBound_6445_);
return v_res_6451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object* v_upperBound_6452_, lean_object* v_comments_6453_, lean_object* v_numNewlinesBeforeComments_6454_, lean_object* v_inst_6455_, lean_object* v_R_6456_, lean_object* v_a_6457_, lean_object* v_b_6458_, lean_object* v_c_6459_){
_start:
{
lean_object* v___x_6460_; 
v___x_6460_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6452_, v_comments_6453_, v_numNewlinesBeforeComments_6454_, v_a_6457_, v_b_6458_);
return v___x_6460_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object* v_upperBound_6461_, lean_object* v_comments_6462_, lean_object* v_numNewlinesBeforeComments_6463_, lean_object* v_inst_6464_, lean_object* v_R_6465_, lean_object* v_a_6466_, lean_object* v_b_6467_, lean_object* v_c_6468_){
_start:
{
lean_object* v_res_6469_; 
v_res_6469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_upperBound_6461_, v_comments_6462_, v_numNewlinesBeforeComments_6463_, v_inst_6464_, v_R_6465_, v_a_6466_, v_b_6467_, v_c_6468_);
lean_dec_ref(v_numNewlinesBeforeComments_6463_);
lean_dec_ref(v_comments_6462_);
lean_dec(v_upperBound_6461_);
return v_res_6469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object* v_00_u03b2_6470_, lean_object* v_a_6471_, lean_object* v_x_6472_){
_start:
{
lean_object* v___x_6473_; 
v___x_6473_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6471_, v_x_6472_);
return v___x_6473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object* v_00_u03b2_6474_, lean_object* v_a_6475_, lean_object* v_x_6476_){
_start:
{
lean_object* v_res_6477_; 
v_res_6477_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(v_00_u03b2_6474_, v_a_6475_, v_x_6476_);
lean_dec(v_x_6476_);
lean_dec(v_a_6475_);
return v_res_6477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object* v_leadingTk_6480_, lean_object* v_leading_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_){
_start:
{
uint8_t v___x_6490_; lean_object* v___x_6491_; 
v___x_6490_ = 0;
v___x_6491_ = l_Lean_Syntax_getRange_x3f(v_leadingTk_6480_, v___x_6490_);
if (lean_obj_tag(v___x_6491_) == 1)
{
lean_object* v_val_6492_; lean_object* v_str_6493_; lean_object* v_startPos_6494_; lean_object* v_stopPos_6495_; lean_object* v___x_6497_; uint8_t v_isShared_6498_; uint8_t v_isSharedCheck_6518_; 
v_val_6492_ = lean_ctor_get(v___x_6491_, 0);
lean_inc(v_val_6492_);
lean_dec_ref_known(v___x_6491_, 1);
v_str_6493_ = lean_ctor_get(v_leading_6481_, 0);
v_startPos_6494_ = lean_ctor_get(v_leading_6481_, 1);
v_stopPos_6495_ = lean_ctor_get(v_leading_6481_, 2);
v_isSharedCheck_6518_ = !lean_is_exclusive(v_leading_6481_);
if (v_isSharedCheck_6518_ == 0)
{
v___x_6497_ = v_leading_6481_;
v_isShared_6498_ = v_isSharedCheck_6518_;
goto v_resetjp_6496_;
}
else
{
lean_inc(v_stopPos_6495_);
lean_inc(v_startPos_6494_);
lean_inc(v_str_6493_);
lean_dec(v_leading_6481_);
v___x_6497_ = lean_box(0);
v_isShared_6498_ = v_isSharedCheck_6518_;
goto v_resetjp_6496_;
}
v_resetjp_6496_:
{
uint8_t v___x_6499_; 
v___x_6499_ = lean_string_is_valid_pos(v_str_6493_, v_startPos_6494_);
if (v___x_6499_ == 0)
{
lean_del_object(v___x_6497_);
lean_dec(v_stopPos_6495_);
lean_dec(v_startPos_6494_);
lean_dec_ref(v_str_6493_);
lean_dec(v_val_6492_);
goto v___jp_6484_;
}
else
{
uint8_t v___x_6500_; 
v___x_6500_ = lean_string_is_valid_pos(v_str_6493_, v_stopPos_6495_);
if (v___x_6500_ == 0)
{
lean_del_object(v___x_6497_);
lean_dec(v_stopPos_6495_);
lean_dec(v_startPos_6494_);
lean_dec_ref(v_str_6493_);
lean_dec(v_val_6492_);
goto v___jp_6484_;
}
else
{
uint8_t v___x_6501_; 
v___x_6501_ = lean_nat_dec_le(v_startPos_6494_, v_stopPos_6495_);
if (v___x_6501_ == 0)
{
lean_del_object(v___x_6497_);
lean_dec(v_stopPos_6495_);
lean_dec(v_startPos_6494_);
lean_dec_ref(v_str_6493_);
lean_dec(v_val_6492_);
goto v___jp_6484_;
}
else
{
lean_object* v_lineInfos_6502_; lean_object* v___x_6504_; 
lean_dec(v_leadingTk_6480_);
v_lineInfos_6502_ = lean_ctor_get(v___y_6482_, 4);
if (v_isShared_6498_ == 0)
{
v___x_6504_ = v___x_6497_;
goto v_reusejp_6503_;
}
else
{
lean_object* v_reuseFailAlloc_6517_; 
v_reuseFailAlloc_6517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6517_, 0, v_str_6493_);
lean_ctor_set(v_reuseFailAlloc_6517_, 1, v_startPos_6494_);
lean_ctor_set(v_reuseFailAlloc_6517_, 2, v_stopPos_6495_);
v___x_6504_ = v_reuseFailAlloc_6517_;
goto v_reusejp_6503_;
}
v_reusejp_6503_:
{
uint8_t v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v_fst_6508_; lean_object* v___x_6510_; uint8_t v_isShared_6511_; uint8_t v_isSharedCheck_6515_; 
v___x_6505_ = 0;
lean_inc_ref(v___x_6504_);
v___x_6506_ = l_Lean_Fmt_parseComments(v_lineInfos_6502_, v_val_6492_, v___x_6505_, v___x_6504_);
v___x_6507_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___x_6506_, v___x_6504_, v___x_6501_);
lean_dec_ref(v___x_6504_);
lean_dec_ref(v___x_6506_);
v_fst_6508_ = lean_ctor_get(v___x_6507_, 0);
v_isSharedCheck_6515_ = !lean_is_exclusive(v___x_6507_);
if (v_isSharedCheck_6515_ == 0)
{
lean_object* v_unused_6516_; 
v_unused_6516_ = lean_ctor_get(v___x_6507_, 1);
lean_dec(v_unused_6516_);
v___x_6510_ = v___x_6507_;
v_isShared_6511_ = v_isSharedCheck_6515_;
goto v_resetjp_6509_;
}
else
{
lean_inc(v_fst_6508_);
lean_dec(v___x_6507_);
v___x_6510_ = lean_box(0);
v_isShared_6511_ = v_isSharedCheck_6515_;
goto v_resetjp_6509_;
}
v_resetjp_6509_:
{
lean_object* v___x_6513_; 
if (v_isShared_6511_ == 0)
{
lean_ctor_set(v___x_6510_, 1, v___y_6483_);
v___x_6513_ = v___x_6510_;
goto v_reusejp_6512_;
}
else
{
lean_object* v_reuseFailAlloc_6514_; 
v_reuseFailAlloc_6514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6514_, 0, v_fst_6508_);
lean_ctor_set(v_reuseFailAlloc_6514_, 1, v___y_6483_);
v___x_6513_ = v_reuseFailAlloc_6514_;
goto v_reusejp_6512_;
}
v_reusejp_6512_:
{
return v___x_6513_;
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
lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; 
lean_dec(v___x_6491_);
lean_dec_ref(v_leading_6481_);
v___x_6519_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6520_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6521_, 0, v_leadingTk_6480_);
lean_ctor_set(v___x_6521_, 1, v___x_6519_);
lean_ctor_set(v___x_6521_, 2, v___x_6520_);
v___x_6522_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6522_, 0, v___x_6521_);
v___x_6523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6523_, 0, v___x_6522_);
lean_ctor_set(v___x_6523_, 1, v___y_6483_);
return v___x_6523_;
}
v___jp_6484_:
{
lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; 
v___x_6485_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6486_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6487_, 0, v_leadingTk_6480_);
lean_ctor_set(v___x_6487_, 1, v___x_6485_);
lean_ctor_set(v___x_6487_, 2, v___x_6486_);
v___x_6488_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6488_, 0, v___x_6487_);
v___x_6489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6489_, 0, v___x_6488_);
lean_ctor_set(v___x_6489_, 1, v___y_6483_);
return v___x_6489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_leadingTk_6524_, lean_object* v_leading_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_){
_start:
{
lean_object* v_res_6528_; 
v_res_6528_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(v_leadingTk_6524_, v_leading_6525_, v___y_6526_, v___y_6527_);
lean_dec_ref(v___y_6526_);
return v_res_6528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object* v_stx_6530_, lean_object* v_a_6531_, lean_object* v_a_6532_){
_start:
{
lean_object* v___f_6533_; lean_object* v___x_6534_; 
v___f_6533_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0));
v___x_6534_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_6530_, v___f_6533_, v_a_6531_, v_a_6532_);
return v___x_6534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6535_, lean_object* v_a_6536_, lean_object* v_a_6537_){
_start:
{
lean_object* v_res_6538_; 
v_res_6538_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v_stx_6535_, v_a_6536_, v_a_6537_);
lean_dec_ref(v_a_6536_);
return v_res_6538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t v_atleastOneNewline_6539_, lean_object* v_trailingTk_6540_, lean_object* v_trailing_6541_, lean_object* v___y_6542_, lean_object* v___y_6543_){
_start:
{
uint8_t v___x_6550_; lean_object* v___x_6551_; 
v___x_6550_ = 0;
v___x_6551_ = l_Lean_Syntax_getRange_x3f(v_trailingTk_6540_, v___x_6550_);
if (lean_obj_tag(v___x_6551_) == 1)
{
lean_object* v_val_6552_; lean_object* v_str_6553_; lean_object* v_startPos_6554_; lean_object* v_stopPos_6555_; lean_object* v___x_6557_; uint8_t v_isShared_6558_; uint8_t v_isSharedCheck_6609_; 
v_val_6552_ = lean_ctor_get(v___x_6551_, 0);
lean_inc(v_val_6552_);
lean_dec_ref_known(v___x_6551_, 1);
v_str_6553_ = lean_ctor_get(v_trailing_6541_, 0);
v_startPos_6554_ = lean_ctor_get(v_trailing_6541_, 1);
v_stopPos_6555_ = lean_ctor_get(v_trailing_6541_, 2);
v_isSharedCheck_6609_ = !lean_is_exclusive(v_trailing_6541_);
if (v_isSharedCheck_6609_ == 0)
{
v___x_6557_ = v_trailing_6541_;
v_isShared_6558_ = v_isSharedCheck_6609_;
goto v_resetjp_6556_;
}
else
{
lean_inc(v_stopPos_6555_);
lean_inc(v_startPos_6554_);
lean_inc(v_str_6553_);
lean_dec(v_trailing_6541_);
v___x_6557_ = lean_box(0);
v_isShared_6558_ = v_isSharedCheck_6609_;
goto v_resetjp_6556_;
}
v_resetjp_6556_:
{
uint8_t v___x_6559_; 
v___x_6559_ = lean_string_is_valid_pos(v_str_6553_, v_startPos_6554_);
if (v___x_6559_ == 0)
{
lean_del_object(v___x_6557_);
lean_dec(v_stopPos_6555_);
lean_dec(v_startPos_6554_);
lean_dec_ref(v_str_6553_);
lean_dec(v_val_6552_);
goto v___jp_6544_;
}
else
{
uint8_t v___x_6560_; 
v___x_6560_ = lean_string_is_valid_pos(v_str_6553_, v_stopPos_6555_);
if (v___x_6560_ == 0)
{
lean_del_object(v___x_6557_);
lean_dec(v_stopPos_6555_);
lean_dec(v_startPos_6554_);
lean_dec_ref(v_str_6553_);
lean_dec(v_val_6552_);
goto v___jp_6544_;
}
else
{
uint8_t v___x_6561_; 
v___x_6561_ = lean_nat_dec_le(v_startPos_6554_, v_stopPos_6555_);
if (v___x_6561_ == 0)
{
lean_del_object(v___x_6557_);
lean_dec(v_stopPos_6555_);
lean_dec(v_startPos_6554_);
lean_dec_ref(v_str_6553_);
lean_dec(v_val_6552_);
goto v___jp_6544_;
}
else
{
lean_object* v_lineInfos_6562_; lean_object* v___x_6564_; 
lean_dec(v_trailingTk_6540_);
v_lineInfos_6562_ = lean_ctor_get(v___y_6542_, 4);
if (v_isShared_6558_ == 0)
{
v___x_6564_ = v___x_6557_;
goto v_reusejp_6563_;
}
else
{
lean_object* v_reuseFailAlloc_6608_; 
v_reuseFailAlloc_6608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6608_, 0, v_str_6553_);
lean_ctor_set(v_reuseFailAlloc_6608_, 1, v_startPos_6554_);
lean_ctor_set(v_reuseFailAlloc_6608_, 2, v_stopPos_6555_);
v___x_6564_ = v_reuseFailAlloc_6608_;
goto v_reusejp_6563_;
}
v_reusejp_6563_:
{
lean_object* v___y_6566_; uint8_t v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; uint8_t v___x_6604_; 
v___x_6599_ = 1;
lean_inc_ref(v___x_6564_);
v___x_6600_ = l_Lean_Fmt_parseComments(v_lineInfos_6562_, v_val_6552_, v___x_6599_, v___x_6564_);
v___x_6601_ = lean_unsigned_to_nat(0u);
v___x_6602_ = lean_array_get_size(v___x_6600_);
v___x_6603_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6604_ = lean_nat_dec_lt(v___x_6601_, v___x_6602_);
if (v___x_6604_ == 0)
{
lean_dec_ref(v___x_6600_);
v___y_6566_ = v___x_6603_;
goto v___jp_6565_;
}
else
{
size_t v___x_6605_; size_t v___x_6606_; lean_object* v___x_6607_; 
v___x_6605_ = ((size_t)0ULL);
v___x_6606_ = lean_usize_of_nat(v___x_6602_);
v___x_6607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v___x_6600_, v___x_6605_, v___x_6606_, v___x_6603_);
lean_dec_ref(v___x_6600_);
v___y_6566_ = v___x_6607_;
goto v___jp_6565_;
}
v___jp_6565_:
{
lean_object* v___x_6567_; lean_object* v_snd_6568_; uint8_t v___x_6569_; 
v___x_6567_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___y_6566_, v___x_6564_, v___x_6550_);
lean_dec_ref(v___x_6564_);
lean_dec_ref(v___y_6566_);
v_snd_6568_ = lean_ctor_get(v___x_6567_, 1);
v___x_6569_ = lean_unbox(v_snd_6568_);
if (v___x_6569_ == 0)
{
if (v_atleastOneNewline_6539_ == 0)
{
lean_object* v_fst_6570_; lean_object* v___x_6572_; uint8_t v_isShared_6573_; uint8_t v_isSharedCheck_6577_; 
v_fst_6570_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6577_ == 0)
{
lean_object* v_unused_6578_; 
v_unused_6578_ = lean_ctor_get(v___x_6567_, 1);
lean_dec(v_unused_6578_);
v___x_6572_ = v___x_6567_;
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
else
{
lean_inc(v_fst_6570_);
lean_dec(v___x_6567_);
v___x_6572_ = lean_box(0);
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
v_resetjp_6571_:
{
lean_object* v___x_6575_; 
if (v_isShared_6573_ == 0)
{
lean_ctor_set(v___x_6572_, 1, v___y_6543_);
v___x_6575_ = v___x_6572_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v_fst_6570_);
lean_ctor_set(v_reuseFailAlloc_6576_, 1, v___y_6543_);
v___x_6575_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
return v___x_6575_;
}
}
}
else
{
lean_object* v_fst_6579_; lean_object* v___x_6581_; uint8_t v_isShared_6582_; uint8_t v_isSharedCheck_6588_; 
v_fst_6579_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6588_ == 0)
{
lean_object* v_unused_6589_; 
v_unused_6589_ = lean_ctor_get(v___x_6567_, 1);
lean_dec(v_unused_6589_);
v___x_6581_ = v___x_6567_;
v_isShared_6582_ = v_isSharedCheck_6588_;
goto v_resetjp_6580_;
}
else
{
lean_inc(v_fst_6579_);
lean_dec(v___x_6567_);
v___x_6581_ = lean_box(0);
v_isShared_6582_ = v_isSharedCheck_6588_;
goto v_resetjp_6580_;
}
v_resetjp_6580_:
{
lean_object* v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6586_; 
v___x_6583_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6584_ = lean_array_push(v_fst_6579_, v___x_6583_);
if (v_isShared_6582_ == 0)
{
lean_ctor_set(v___x_6581_, 1, v___y_6543_);
lean_ctor_set(v___x_6581_, 0, v___x_6584_);
v___x_6586_ = v___x_6581_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v___x_6584_);
lean_ctor_set(v_reuseFailAlloc_6587_, 1, v___y_6543_);
v___x_6586_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
return v___x_6586_;
}
}
}
}
else
{
lean_object* v_fst_6590_; lean_object* v___x_6592_; uint8_t v_isShared_6593_; uint8_t v_isSharedCheck_6597_; 
v_fst_6590_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6597_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6597_ == 0)
{
lean_object* v_unused_6598_; 
v_unused_6598_ = lean_ctor_get(v___x_6567_, 1);
lean_dec(v_unused_6598_);
v___x_6592_ = v___x_6567_;
v_isShared_6593_ = v_isSharedCheck_6597_;
goto v_resetjp_6591_;
}
else
{
lean_inc(v_fst_6590_);
lean_dec(v___x_6567_);
v___x_6592_ = lean_box(0);
v_isShared_6593_ = v_isSharedCheck_6597_;
goto v_resetjp_6591_;
}
v_resetjp_6591_:
{
lean_object* v___x_6595_; 
if (v_isShared_6593_ == 0)
{
lean_ctor_set(v___x_6592_, 1, v___y_6543_);
v___x_6595_ = v___x_6592_;
goto v_reusejp_6594_;
}
else
{
lean_object* v_reuseFailAlloc_6596_; 
v_reuseFailAlloc_6596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6596_, 0, v_fst_6590_);
lean_ctor_set(v_reuseFailAlloc_6596_, 1, v___y_6543_);
v___x_6595_ = v_reuseFailAlloc_6596_;
goto v_reusejp_6594_;
}
v_reusejp_6594_:
{
return v___x_6595_;
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
lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; 
lean_dec(v___x_6551_);
lean_dec_ref(v_trailing_6541_);
v___x_6610_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6611_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6612_, 0, v_trailingTk_6540_);
lean_ctor_set(v___x_6612_, 1, v___x_6610_);
lean_ctor_set(v___x_6612_, 2, v___x_6611_);
v___x_6613_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6613_, 0, v___x_6612_);
v___x_6614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6614_, 0, v___x_6613_);
lean_ctor_set(v___x_6614_, 1, v___y_6543_);
return v___x_6614_;
}
v___jp_6544_:
{
lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; 
v___x_6545_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6546_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6547_, 0, v_trailingTk_6540_);
lean_ctor_set(v___x_6547_, 1, v___x_6545_);
lean_ctor_set(v___x_6547_, 2, v___x_6546_);
v___x_6548_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6548_, 0, v___x_6547_);
v___x_6549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6549_, 0, v___x_6548_);
lean_ctor_set(v___x_6549_, 1, v___y_6543_);
return v___x_6549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_atleastOneNewline_6615_, lean_object* v_trailingTk_6616_, lean_object* v_trailing_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6620_; lean_object* v_res_6621_; 
v_atleastOneNewline_boxed_6620_ = lean_unbox(v_atleastOneNewline_6615_);
v_res_6621_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(v_atleastOneNewline_boxed_6620_, v_trailingTk_6616_, v_trailing_6617_, v___y_6618_, v___y_6619_);
lean_dec_ref(v___y_6618_);
return v_res_6621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object* v_stx_6622_, uint8_t v_atleastOneNewline_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_){
_start:
{
lean_object* v___x_6626_; lean_object* v___f_6627_; lean_object* v___x_6628_; 
v___x_6626_ = lean_box(v_atleastOneNewline_6623_);
v___f_6627_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed), 5, 1);
lean_closure_set(v___f_6627_, 0, v___x_6626_);
v___x_6628_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_6622_, v___f_6627_, v_a_6624_, v_a_6625_);
return v___x_6628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6629_, lean_object* v_atleastOneNewline_6630_, lean_object* v_a_6631_, lean_object* v_a_6632_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6633_; lean_object* v_res_6634_; 
v_atleastOneNewline_boxed_6633_ = lean_unbox(v_atleastOneNewline_6630_);
v_res_6634_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_stx_6629_, v_atleastOneNewline_boxed_6633_, v_a_6631_, v_a_6632_);
lean_dec_ref(v_a_6631_);
return v_res_6634_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object* v_upperBound_6635_, lean_object* v_stxs_6636_, lean_object* v_f_6637_, lean_object* v___x_6638_, lean_object* v_a_6639_, lean_object* v_b_6640_, lean_object* v___y_6641_, lean_object* v___y_6642_){
_start:
{
uint8_t v___x_6643_; 
v___x_6643_ = lean_nat_dec_lt(v_a_6639_, v_upperBound_6635_);
if (v___x_6643_ == 0)
{
lean_object* v___x_6644_; 
lean_dec(v_a_6639_);
lean_dec_ref(v_f_6637_);
v___x_6644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6644_, 0, v_b_6640_);
lean_ctor_set(v___x_6644_, 1, v___y_6642_);
return v___x_6644_;
}
else
{
lean_object* v___x_6645_; lean_object* v___x_6646_; 
v___x_6645_ = lean_array_fget_borrowed(v_stxs_6636_, v_a_6639_);
lean_inc_ref(v_f_6637_);
lean_inc_ref(v___y_6641_);
lean_inc(v___x_6645_);
v___x_6646_ = lean_apply_3(v_f_6637_, v___x_6645_, v___y_6641_, v___y_6642_);
if (lean_obj_tag(v___x_6646_) == 0)
{
lean_object* v_a_6647_; lean_object* v_a_6648_; lean_object* v___x_6649_; lean_object* v___y_6651_; lean_object* v___x_6676_; uint8_t v___x_6677_; 
v_a_6647_ = lean_ctor_get(v___x_6646_, 0);
lean_inc(v_a_6647_);
v_a_6648_ = lean_ctor_get(v___x_6646_, 1);
lean_inc(v_a_6648_);
lean_dec_ref_known(v___x_6646_, 2);
v___x_6649_ = lean_unsigned_to_nat(1u);
v___x_6676_ = lean_nat_sub(v___x_6638_, v___x_6649_);
v___x_6677_ = lean_nat_dec_lt(v_a_6639_, v___x_6676_);
lean_dec(v___x_6676_);
if (v___x_6677_ == 0)
{
lean_object* v___x_6678_; lean_object* v___x_6679_; 
v___x_6678_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_6679_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6640_, v_a_6647_, v___x_6678_, v___y_6641_, v_a_6648_);
v___y_6651_ = v___x_6679_;
goto v___jp_6650_;
}
else
{
lean_object* v___x_6680_; 
lean_inc(v___x_6645_);
v___x_6680_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_6645_, v___x_6677_, v___y_6641_, v_a_6648_);
if (lean_obj_tag(v___x_6680_) == 0)
{
lean_object* v_a_6681_; lean_object* v_a_6682_; lean_object* v___x_6683_; 
v_a_6681_ = lean_ctor_get(v___x_6680_, 0);
lean_inc(v_a_6681_);
v_a_6682_ = lean_ctor_get(v___x_6680_, 1);
lean_inc(v_a_6682_);
lean_dec_ref_known(v___x_6680_, 2);
v___x_6683_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6640_, v_a_6647_, v_a_6681_, v___y_6641_, v_a_6682_);
v___y_6651_ = v___x_6683_;
goto v___jp_6650_;
}
else
{
lean_object* v_a_6684_; lean_object* v_a_6685_; lean_object* v___x_6687_; uint8_t v_isShared_6688_; uint8_t v_isSharedCheck_6692_; 
lean_dec(v_a_6647_);
lean_dec_ref(v_b_6640_);
lean_dec(v_a_6639_);
lean_dec_ref(v_f_6637_);
v_a_6684_ = lean_ctor_get(v___x_6680_, 0);
v_a_6685_ = lean_ctor_get(v___x_6680_, 1);
v_isSharedCheck_6692_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6692_ == 0)
{
v___x_6687_ = v___x_6680_;
v_isShared_6688_ = v_isSharedCheck_6692_;
goto v_resetjp_6686_;
}
else
{
lean_inc(v_a_6685_);
lean_inc(v_a_6684_);
lean_dec(v___x_6680_);
v___x_6687_ = lean_box(0);
v_isShared_6688_ = v_isSharedCheck_6692_;
goto v_resetjp_6686_;
}
v_resetjp_6686_:
{
lean_object* v___x_6690_; 
if (v_isShared_6688_ == 0)
{
v___x_6690_ = v___x_6687_;
goto v_reusejp_6689_;
}
else
{
lean_object* v_reuseFailAlloc_6691_; 
v_reuseFailAlloc_6691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6691_, 0, v_a_6684_);
lean_ctor_set(v_reuseFailAlloc_6691_, 1, v_a_6685_);
v___x_6690_ = v_reuseFailAlloc_6691_;
goto v_reusejp_6689_;
}
v_reusejp_6689_:
{
return v___x_6690_;
}
}
}
}
v___jp_6650_:
{
if (lean_obj_tag(v___y_6651_) == 0)
{
lean_object* v_a_6652_; 
v_a_6652_ = lean_ctor_get(v___y_6651_, 0);
lean_inc(v_a_6652_);
if (lean_obj_tag(v_a_6652_) == 0)
{
lean_object* v_a_6653_; lean_object* v___x_6655_; uint8_t v_isShared_6656_; uint8_t v_isSharedCheck_6661_; 
lean_dec(v_a_6639_);
lean_dec_ref(v_f_6637_);
v_a_6653_ = lean_ctor_get(v___y_6651_, 1);
v_isSharedCheck_6661_ = !lean_is_exclusive(v___y_6651_);
if (v_isSharedCheck_6661_ == 0)
{
lean_object* v_unused_6662_; 
v_unused_6662_ = lean_ctor_get(v___y_6651_, 0);
lean_dec(v_unused_6662_);
v___x_6655_ = v___y_6651_;
v_isShared_6656_ = v_isSharedCheck_6661_;
goto v_resetjp_6654_;
}
else
{
lean_inc(v_a_6653_);
lean_dec(v___y_6651_);
v___x_6655_ = lean_box(0);
v_isShared_6656_ = v_isSharedCheck_6661_;
goto v_resetjp_6654_;
}
v_resetjp_6654_:
{
lean_object* v_a_6657_; lean_object* v___x_6659_; 
v_a_6657_ = lean_ctor_get(v_a_6652_, 0);
lean_inc(v_a_6657_);
lean_dec_ref_known(v_a_6652_, 1);
if (v_isShared_6656_ == 0)
{
lean_ctor_set(v___x_6655_, 0, v_a_6657_);
v___x_6659_ = v___x_6655_;
goto v_reusejp_6658_;
}
else
{
lean_object* v_reuseFailAlloc_6660_; 
v_reuseFailAlloc_6660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6660_, 0, v_a_6657_);
lean_ctor_set(v_reuseFailAlloc_6660_, 1, v_a_6653_);
v___x_6659_ = v_reuseFailAlloc_6660_;
goto v_reusejp_6658_;
}
v_reusejp_6658_:
{
return v___x_6659_;
}
}
}
else
{
lean_object* v_a_6663_; lean_object* v_a_6664_; lean_object* v___x_6665_; 
v_a_6663_ = lean_ctor_get(v___y_6651_, 1);
lean_inc(v_a_6663_);
lean_dec_ref_known(v___y_6651_, 2);
v_a_6664_ = lean_ctor_get(v_a_6652_, 0);
lean_inc(v_a_6664_);
lean_dec_ref_known(v_a_6652_, 1);
v___x_6665_ = lean_nat_add(v_a_6639_, v___x_6649_);
lean_dec(v_a_6639_);
v_a_6639_ = v___x_6665_;
v_b_6640_ = v_a_6664_;
v___y_6642_ = v_a_6663_;
goto _start;
}
}
else
{
lean_object* v_a_6667_; lean_object* v_a_6668_; lean_object* v___x_6670_; uint8_t v_isShared_6671_; uint8_t v_isSharedCheck_6675_; 
lean_dec(v_a_6639_);
lean_dec_ref(v_f_6637_);
v_a_6667_ = lean_ctor_get(v___y_6651_, 0);
v_a_6668_ = lean_ctor_get(v___y_6651_, 1);
v_isSharedCheck_6675_ = !lean_is_exclusive(v___y_6651_);
if (v_isSharedCheck_6675_ == 0)
{
v___x_6670_ = v___y_6651_;
v_isShared_6671_ = v_isSharedCheck_6675_;
goto v_resetjp_6669_;
}
else
{
lean_inc(v_a_6668_);
lean_inc(v_a_6667_);
lean_dec(v___y_6651_);
v___x_6670_ = lean_box(0);
v_isShared_6671_ = v_isSharedCheck_6675_;
goto v_resetjp_6669_;
}
v_resetjp_6669_:
{
lean_object* v___x_6673_; 
if (v_isShared_6671_ == 0)
{
v___x_6673_ = v___x_6670_;
goto v_reusejp_6672_;
}
else
{
lean_object* v_reuseFailAlloc_6674_; 
v_reuseFailAlloc_6674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6674_, 0, v_a_6667_);
lean_ctor_set(v_reuseFailAlloc_6674_, 1, v_a_6668_);
v___x_6673_ = v_reuseFailAlloc_6674_;
goto v_reusejp_6672_;
}
v_reusejp_6672_:
{
return v___x_6673_;
}
}
}
}
}
else
{
lean_object* v_a_6693_; lean_object* v_a_6694_; lean_object* v___x_6696_; uint8_t v_isShared_6697_; uint8_t v_isSharedCheck_6701_; 
lean_dec_ref(v_b_6640_);
lean_dec(v_a_6639_);
lean_dec_ref(v_f_6637_);
v_a_6693_ = lean_ctor_get(v___x_6646_, 0);
v_a_6694_ = lean_ctor_get(v___x_6646_, 1);
v_isSharedCheck_6701_ = !lean_is_exclusive(v___x_6646_);
if (v_isSharedCheck_6701_ == 0)
{
v___x_6696_ = v___x_6646_;
v_isShared_6697_ = v_isSharedCheck_6701_;
goto v_resetjp_6695_;
}
else
{
lean_inc(v_a_6694_);
lean_inc(v_a_6693_);
lean_dec(v___x_6646_);
v___x_6696_ = lean_box(0);
v_isShared_6697_ = v_isSharedCheck_6701_;
goto v_resetjp_6695_;
}
v_resetjp_6695_:
{
lean_object* v___x_6699_; 
if (v_isShared_6697_ == 0)
{
v___x_6699_ = v___x_6696_;
goto v_reusejp_6698_;
}
else
{
lean_object* v_reuseFailAlloc_6700_; 
v_reuseFailAlloc_6700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6700_, 0, v_a_6693_);
lean_ctor_set(v_reuseFailAlloc_6700_, 1, v_a_6694_);
v___x_6699_ = v_reuseFailAlloc_6700_;
goto v_reusejp_6698_;
}
v_reusejp_6698_:
{
return v___x_6699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object* v_upperBound_6702_, lean_object* v_stxs_6703_, lean_object* v_f_6704_, lean_object* v___x_6705_, lean_object* v_a_6706_, lean_object* v_b_6707_, lean_object* v___y_6708_, lean_object* v___y_6709_){
_start:
{
lean_object* v_res_6710_; 
v_res_6710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6702_, v_stxs_6703_, v_f_6704_, v___x_6705_, v_a_6706_, v_b_6707_, v___y_6708_, v___y_6709_);
lean_dec_ref(v___y_6708_);
lean_dec(v___x_6705_);
lean_dec_ref(v_stxs_6703_);
lean_dec(v_upperBound_6702_);
return v_res_6710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object* v_f_6711_, lean_object* v_stxs_6712_, lean_object* v_a_6713_, lean_object* v_a_6714_){
_start:
{
lean_object* v___x_6715_; lean_object* v___x_6716_; uint8_t v___x_6717_; 
v___x_6715_ = lean_array_get_size(v_stxs_6712_);
v___x_6716_ = lean_unsigned_to_nat(1u);
v___x_6717_ = lean_nat_dec_eq(v___x_6715_, v___x_6716_);
if (v___x_6717_ == 0)
{
lean_object* v___x_6718_; lean_object* v_acc_6719_; lean_object* v___x_6720_; 
v___x_6718_ = lean_unsigned_to_nat(0u);
v_acc_6719_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_6720_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v___x_6715_, v_stxs_6712_, v_f_6711_, v___x_6715_, v___x_6718_, v_acc_6719_, v_a_6713_, v_a_6714_);
if (lean_obj_tag(v___x_6720_) == 0)
{
lean_object* v_a_6721_; lean_object* v_a_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6730_; 
v_a_6721_ = lean_ctor_get(v___x_6720_, 0);
v_a_6722_ = lean_ctor_get(v___x_6720_, 1);
v_isSharedCheck_6730_ = !lean_is_exclusive(v___x_6720_);
if (v_isSharedCheck_6730_ == 0)
{
v___x_6724_ = v___x_6720_;
v_isShared_6725_ = v_isSharedCheck_6730_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_a_6722_);
lean_inc(v_a_6721_);
lean_dec(v___x_6720_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6730_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6726_; lean_object* v___x_6728_; 
v___x_6726_ = l_Lean_Fmt_TaggedDoc_join(v_a_6721_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6726_);
v___x_6728_ = v___x_6724_;
goto v_reusejp_6727_;
}
else
{
lean_object* v_reuseFailAlloc_6729_; 
v_reuseFailAlloc_6729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6729_, 0, v___x_6726_);
lean_ctor_set(v_reuseFailAlloc_6729_, 1, v_a_6722_);
v___x_6728_ = v_reuseFailAlloc_6729_;
goto v_reusejp_6727_;
}
v_reusejp_6727_:
{
return v___x_6728_;
}
}
}
else
{
lean_object* v_a_6731_; lean_object* v_a_6732_; lean_object* v___x_6734_; uint8_t v_isShared_6735_; uint8_t v_isSharedCheck_6739_; 
v_a_6731_ = lean_ctor_get(v___x_6720_, 0);
v_a_6732_ = lean_ctor_get(v___x_6720_, 1);
v_isSharedCheck_6739_ = !lean_is_exclusive(v___x_6720_);
if (v_isSharedCheck_6739_ == 0)
{
v___x_6734_ = v___x_6720_;
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
else
{
lean_inc(v_a_6732_);
lean_inc(v_a_6731_);
lean_dec(v___x_6720_);
v___x_6734_ = lean_box(0);
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
v_resetjp_6733_:
{
lean_object* v___x_6737_; 
if (v_isShared_6735_ == 0)
{
v___x_6737_ = v___x_6734_;
goto v_reusejp_6736_;
}
else
{
lean_object* v_reuseFailAlloc_6738_; 
v_reuseFailAlloc_6738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6738_, 0, v_a_6731_);
lean_ctor_set(v_reuseFailAlloc_6738_, 1, v_a_6732_);
v___x_6737_ = v_reuseFailAlloc_6738_;
goto v_reusejp_6736_;
}
v_reusejp_6736_:
{
return v___x_6737_;
}
}
}
}
else
{
lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; lean_object* v___x_6743_; 
v___x_6740_ = lean_box(0);
v___x_6741_ = lean_unsigned_to_nat(0u);
v___x_6742_ = lean_array_get_borrowed(v___x_6740_, v_stxs_6712_, v___x_6741_);
lean_inc_ref(v_a_6713_);
lean_inc(v___x_6742_);
v___x_6743_ = lean_apply_3(v_f_6711_, v___x_6742_, v_a_6713_, v_a_6714_);
return v___x_6743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object* v_f_6744_, lean_object* v_stxs_6745_, lean_object* v_a_6746_, lean_object* v_a_6747_){
_start:
{
lean_object* v_res_6748_; 
v_res_6748_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v_f_6744_, v_stxs_6745_, v_a_6746_, v_a_6747_);
lean_dec_ref(v_a_6746_);
lean_dec_ref(v_stxs_6745_);
return v_res_6748_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object* v_upperBound_6749_, lean_object* v_stxs_6750_, lean_object* v_f_6751_, lean_object* v___x_6752_, lean_object* v_inst_6753_, lean_object* v_R_6754_, lean_object* v_a_6755_, lean_object* v_b_6756_, lean_object* v_c_6757_, lean_object* v___y_6758_, lean_object* v___y_6759_){
_start:
{
lean_object* v___x_6760_; 
v___x_6760_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6749_, v_stxs_6750_, v_f_6751_, v___x_6752_, v_a_6755_, v_b_6756_, v___y_6758_, v___y_6759_);
return v___x_6760_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object* v_upperBound_6761_, lean_object* v_stxs_6762_, lean_object* v_f_6763_, lean_object* v___x_6764_, lean_object* v_inst_6765_, lean_object* v_R_6766_, lean_object* v_a_6767_, lean_object* v_b_6768_, lean_object* v_c_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_){
_start:
{
lean_object* v_res_6772_; 
v_res_6772_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(v_upperBound_6761_, v_stxs_6762_, v_f_6763_, v___x_6764_, v_inst_6765_, v_R_6766_, v_a_6767_, v_b_6768_, v_c_6769_, v___y_6770_, v___y_6771_);
lean_dec_ref(v___y_6770_);
lean_dec(v___x_6764_);
lean_dec_ref(v_stxs_6762_);
lean_dec(v_upperBound_6761_);
return v_res_6772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_stxs_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_){
_start:
{
lean_object* v___x_6776_; lean_object* v___x_6777_; 
v___x_6776_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 0);
v___x_6777_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v___x_6776_, v_stxs_6773_, v_a_6774_, v_a_6775_);
return v___x_6777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_stxs_6778_, lean_object* v_a_6779_, lean_object* v_a_6780_){
_start:
{
lean_object* v_res_6781_; 
v_res_6781_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_stxs_6778_, v_a_6779_, v_a_6780_);
lean_dec_ref(v_a_6779_);
lean_dec_ref(v_stxs_6778_);
return v_res_6781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(lean_object* v_x_6782_){
_start:
{
lean_object* v___x_6783_; 
v___x_6783_ = lean_obj_tag_nat(v_x_6782_);
return v___x_6783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg___boxed(lean_object* v_x_6784_){
_start:
{
lean_object* v_res_6785_; 
v_res_6785_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(v_x_6784_);
lean_dec_ref(v_x_6784_);
return v_res_6785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl(lean_object* v_sep_6786_, lean_object* v_x_6787_){
_start:
{
lean_object* v___x_6788_; 
v___x_6788_ = lean_obj_tag_nat(v_x_6787_);
return v___x_6788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___boxed(lean_object* v_sep_6789_, lean_object* v_x_6790_){
_start:
{
lean_object* v_res_6791_; 
v_res_6791_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl(v_sep_6789_, v_x_6790_);
lean_dec_ref(v_x_6790_);
lean_dec_ref(v_sep_6789_);
return v_res_6791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object* v_t_6792_, lean_object* v_k_6793_){
_start:
{
lean_object* v_g_6794_; lean_object* v___x_6795_; 
v_g_6794_ = lean_ctor_get(v_t_6792_, 0);
lean_inc_ref(v_g_6794_);
lean_dec_ref(v_t_6792_);
v___x_6795_ = lean_apply_1(v_k_6793_, v_g_6794_);
return v___x_6795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim(lean_object* v_sep_6796_, lean_object* v_motive_6797_, lean_object* v_ctorIdx_6798_, lean_object* v_t_6799_, lean_object* v_h_6800_, lean_object* v_k_6801_){
_start:
{
lean_object* v___x_6802_; 
v___x_6802_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6799_, v_k_6801_);
return v___x_6802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object* v_sep_6803_, lean_object* v_motive_6804_, lean_object* v_ctorIdx_6805_, lean_object* v_t_6806_, lean_object* v_h_6807_, lean_object* v_k_6808_){
_start:
{
lean_object* v_res_6809_; 
v_res_6809_ = l_Lean_Fmt_TrailingGroup_ctorElim(v_sep_6803_, v_motive_6804_, v_ctorIdx_6805_, v_t_6806_, v_h_6807_, v_k_6808_);
lean_dec(v_ctorIdx_6805_);
lean_dec_ref(v_sep_6803_);
return v_res_6809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object* v_t_6810_, lean_object* v_group_6811_){
_start:
{
lean_object* v___x_6812_; 
v___x_6812_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6810_, v_group_6811_);
return v___x_6812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim(lean_object* v_sep_6813_, lean_object* v_motive_6814_, lean_object* v_t_6815_, lean_object* v_h_6816_, lean_object* v_group_6817_){
_start:
{
lean_object* v___x_6818_; 
v___x_6818_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6815_, v_group_6817_);
return v___x_6818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object* v_sep_6819_, lean_object* v_motive_6820_, lean_object* v_t_6821_, lean_object* v_h_6822_, lean_object* v_group_6823_){
_start:
{
lean_object* v_res_6824_; 
v_res_6824_ = l_Lean_Fmt_TrailingGroup_group_elim(v_sep_6819_, v_motive_6820_, v_t_6821_, v_h_6822_, v_group_6823_);
lean_dec_ref(v_sep_6819_);
return v_res_6824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object* v_t_6825_, lean_object* v_trailing_6826_){
_start:
{
lean_object* v___x_6827_; 
v___x_6827_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6825_, v_trailing_6826_);
return v___x_6827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim(lean_object* v_sep_6828_, lean_object* v_motive_6829_, lean_object* v_t_6830_, lean_object* v_h_6831_, lean_object* v_trailing_6832_){
_start:
{
lean_object* v___x_6833_; 
v___x_6833_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6830_, v_trailing_6832_);
return v___x_6833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object* v_sep_6834_, lean_object* v_motive_6835_, lean_object* v_t_6836_, lean_object* v_h_6837_, lean_object* v_trailing_6838_){
_start:
{
lean_object* v_res_6839_; 
v_res_6839_ = l_Lean_Fmt_TrailingGroup_trailing_elim(v_sep_6834_, v_motive_6835_, v_t_6836_, v_h_6837_, v_trailing_6838_);
lean_dec_ref(v_sep_6834_);
return v_res_6839_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_6840_; lean_object* v___x_6841_; 
v___x_6840_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_6841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6841_, 0, v___x_6840_);
return v___x_6841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg(){
_start:
{
lean_object* v___x_6843_; 
v___x_6843_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0);
return v___x_6843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___boxed(lean_object* v___dummy_6844_){
_start:
{
lean_object* v_res_6845_; 
v_res_6845_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v_res_6845_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0(void){
_start:
{
lean_object* v___x_6846_; 
v___x_6846_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v___x_6846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object* v_sep_6847_){
_start:
{
lean_object* v___x_6848_; 
v___x_6848_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object* v_sep_6849_){
_start:
{
lean_object* v_res_6850_; 
v_res_6850_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6849_);
lean_dec_ref(v_sep_6849_);
return v_res_6850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg(){
_start:
{
lean_object* v___x_6852_; 
v___x_6852_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg___boxed(lean_object* v___dummy_6853_){
_start:
{
lean_object* v_res_6854_; 
v_res_6854_ = l_Lean_Fmt_instInhabitedTrailingGroup___redArg();
return v_res_6854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup(lean_object* v_a_6855_){
_start:
{
lean_object* v___x_6856_; 
v___x_6856_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object* v_a_6857_){
_start:
{
lean_object* v_res_6858_; 
v_res_6858_ = l_Lean_Fmt_instInhabitedTrailingGroup(v_a_6857_);
lean_dec_ref(v_a_6857_);
return v_res_6858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object* v_upperBound_6859_, lean_object* v_elemsAndSeps_6860_, lean_object* v_pendingGroup_6861_, lean_object* v___x_6862_, lean_object* v_a_6863_, lean_object* v_b_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_){
_start:
{
lean_object* v_a_6868_; lean_object* v_a_6869_; uint8_t v___x_6873_; 
v___x_6873_ = lean_nat_dec_lt(v_a_6863_, v_upperBound_6859_);
if (v___x_6873_ == 0)
{
lean_object* v___x_6874_; 
lean_dec(v_a_6863_);
lean_dec_ref(v_pendingGroup_6861_);
v___x_6874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6874_, 0, v_b_6864_);
lean_ctor_set(v___x_6874_, 1, v___y_6866_);
return v___x_6874_;
}
else
{
lean_object* v___x_6875_; lean_object* v___x_6876_; 
v___x_6875_ = lean_array_fget_borrowed(v_elemsAndSeps_6860_, v_a_6863_);
lean_inc(v___x_6875_);
v___x_6876_ = l_Lean_Fmt_fmt(v___x_6875_, v___y_6865_, v___y_6866_);
if (lean_obj_tag(v___x_6876_) == 0)
{
lean_object* v_a_6877_; lean_object* v_a_6878_; lean_object* v_fst_6879_; lean_object* v_snd_6880_; lean_object* v___x_6882_; uint8_t v_isShared_6883_; uint8_t v_isSharedCheck_6927_; 
v_a_6877_ = lean_ctor_get(v___x_6876_, 0);
lean_inc(v_a_6877_);
v_a_6878_ = lean_ctor_get(v___x_6876_, 1);
lean_inc(v_a_6878_);
lean_dec_ref_known(v___x_6876_, 2);
v_fst_6879_ = lean_ctor_get(v_b_6864_, 0);
v_snd_6880_ = lean_ctor_get(v_b_6864_, 1);
v_isSharedCheck_6927_ = !lean_is_exclusive(v_b_6864_);
if (v_isSharedCheck_6927_ == 0)
{
v___x_6882_ = v_b_6864_;
v_isShared_6883_ = v_isSharedCheck_6927_;
goto v_resetjp_6881_;
}
else
{
lean_inc(v_snd_6880_);
lean_inc(v_fst_6879_);
lean_dec(v_b_6864_);
v___x_6882_ = lean_box(0);
v_isShared_6883_ = v_isSharedCheck_6927_;
goto v_resetjp_6881_;
}
v_resetjp_6881_:
{
lean_object* v___x_6884_; lean_object* v___x_6885_; lean_object* v___x_6886_; lean_object* v___y_6888_; uint8_t v___y_6916_; lean_object* v___x_6923_; lean_object* v___x_6924_; uint8_t v___x_6925_; 
v___x_6884_ = lean_unsigned_to_nat(0u);
v___x_6885_ = lean_box(0);
v___x_6886_ = lean_array_push(v_snd_6880_, v_a_6877_);
v___x_6923_ = lean_unsigned_to_nat(2u);
v___x_6924_ = lean_nat_mod(v_a_6863_, v___x_6923_);
v___x_6925_ = lean_nat_dec_eq(v___x_6924_, v___x_6884_);
lean_dec(v___x_6924_);
if (v___x_6925_ == 0)
{
v___y_6916_ = v___x_6873_;
goto v___jp_6915_;
}
else
{
uint8_t v___x_6926_; 
v___x_6926_ = 0;
v___y_6916_ = v___x_6926_;
goto v___jp_6915_;
}
v___jp_6887_:
{
uint8_t v___x_6889_; lean_object* v___x_6890_; 
v___x_6889_ = 0;
v___x_6890_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___y_6888_, v___x_6889_, v___y_6865_, v_a_6878_);
if (lean_obj_tag(v___x_6890_) == 0)
{
lean_object* v_a_6891_; lean_object* v_a_6892_; uint8_t v___x_6893_; 
v_a_6891_ = lean_ctor_get(v___x_6890_, 0);
lean_inc(v_a_6891_);
v_a_6892_ = lean_ctor_get(v___x_6890_, 1);
lean_inc(v_a_6892_);
lean_dec_ref_known(v___x_6890_, 2);
v___x_6893_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_6891_);
if (v___x_6893_ == 0)
{
lean_object* v___x_6894_; lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6897_; lean_object* v___x_6899_; 
v___x_6894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6894_, 0, v___x_6886_);
v___x_6895_ = lean_array_push(v_fst_6879_, v___x_6894_);
v___x_6896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6896_, 0, v_a_6891_);
v___x_6897_ = lean_array_push(v___x_6895_, v___x_6896_);
lean_inc_ref(v_pendingGroup_6861_);
if (v_isShared_6883_ == 0)
{
lean_ctor_set(v___x_6882_, 1, v_pendingGroup_6861_);
lean_ctor_set(v___x_6882_, 0, v___x_6897_);
v___x_6899_ = v___x_6882_;
goto v_reusejp_6898_;
}
else
{
lean_object* v_reuseFailAlloc_6900_; 
v_reuseFailAlloc_6900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6900_, 0, v___x_6897_);
lean_ctor_set(v_reuseFailAlloc_6900_, 1, v_pendingGroup_6861_);
v___x_6899_ = v_reuseFailAlloc_6900_;
goto v_reusejp_6898_;
}
v_reusejp_6898_:
{
v_a_6868_ = v___x_6899_;
v_a_6869_ = v_a_6892_;
goto v___jp_6867_;
}
}
else
{
lean_object* v___x_6902_; 
lean_dec(v_a_6891_);
if (v_isShared_6883_ == 0)
{
lean_ctor_set(v___x_6882_, 1, v___x_6886_);
v___x_6902_ = v___x_6882_;
goto v_reusejp_6901_;
}
else
{
lean_object* v_reuseFailAlloc_6903_; 
v_reuseFailAlloc_6903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_fst_6879_);
lean_ctor_set(v_reuseFailAlloc_6903_, 1, v___x_6886_);
v___x_6902_ = v_reuseFailAlloc_6903_;
goto v_reusejp_6901_;
}
v_reusejp_6901_:
{
v_a_6868_ = v___x_6902_;
v_a_6869_ = v_a_6892_;
goto v___jp_6867_;
}
}
}
else
{
lean_object* v_a_6904_; lean_object* v_a_6905_; lean_object* v___x_6907_; uint8_t v_isShared_6908_; uint8_t v_isSharedCheck_6912_; 
lean_dec_ref(v___x_6886_);
lean_del_object(v___x_6882_);
lean_dec(v_fst_6879_);
lean_dec(v_a_6863_);
lean_dec_ref(v_pendingGroup_6861_);
v_a_6904_ = lean_ctor_get(v___x_6890_, 0);
v_a_6905_ = lean_ctor_get(v___x_6890_, 1);
v_isSharedCheck_6912_ = !lean_is_exclusive(v___x_6890_);
if (v_isSharedCheck_6912_ == 0)
{
v___x_6907_ = v___x_6890_;
v_isShared_6908_ = v_isSharedCheck_6912_;
goto v_resetjp_6906_;
}
else
{
lean_inc(v_a_6905_);
lean_inc(v_a_6904_);
lean_dec(v___x_6890_);
v___x_6907_ = lean_box(0);
v_isShared_6908_ = v_isSharedCheck_6912_;
goto v_resetjp_6906_;
}
v_resetjp_6906_:
{
lean_object* v___x_6910_; 
if (v_isShared_6908_ == 0)
{
v___x_6910_ = v___x_6907_;
goto v_reusejp_6909_;
}
else
{
lean_object* v_reuseFailAlloc_6911_; 
v_reuseFailAlloc_6911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6911_, 0, v_a_6904_);
lean_ctor_set(v_reuseFailAlloc_6911_, 1, v_a_6905_);
v___x_6910_ = v_reuseFailAlloc_6911_;
goto v_reusejp_6909_;
}
v_reusejp_6909_:
{
return v___x_6910_;
}
}
}
}
v___jp_6913_:
{
lean_object* v___x_6914_; 
v___x_6914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6914_, 0, v_fst_6879_);
lean_ctor_set(v___x_6914_, 1, v___x_6886_);
v_a_6868_ = v___x_6914_;
v_a_6869_ = v_a_6878_;
goto v___jp_6867_;
}
v___jp_6915_:
{
lean_object* v___x_6917_; lean_object* v___x_6918_; uint8_t v___x_6919_; 
v___x_6917_ = lean_unsigned_to_nat(1u);
v___x_6918_ = lean_nat_sub(v___x_6862_, v___x_6917_);
v___x_6919_ = lean_nat_dec_lt(v_a_6863_, v___x_6918_);
lean_dec(v___x_6918_);
if (v___x_6919_ == 0)
{
lean_del_object(v___x_6882_);
goto v___jp_6913_;
}
else
{
if (v___y_6916_ == 0)
{
lean_del_object(v___x_6882_);
goto v___jp_6913_;
}
else
{
uint8_t v___x_6920_; 
lean_inc(v___x_6875_);
v___x_6920_ = l_Lean_Syntax_matchesNull(v___x_6875_, v___x_6884_);
if (v___x_6920_ == 0)
{
lean_inc(v___x_6875_);
v___y_6888_ = v___x_6875_;
goto v___jp_6887_;
}
else
{
lean_object* v___x_6921_; lean_object* v___x_6922_; 
v___x_6921_ = lean_nat_sub(v_a_6863_, v___x_6917_);
v___x_6922_ = lean_array_get_borrowed(v___x_6885_, v_elemsAndSeps_6860_, v___x_6921_);
lean_dec(v___x_6921_);
lean_inc(v___x_6922_);
v___y_6888_ = v___x_6922_;
goto v___jp_6887_;
}
}
}
}
}
}
else
{
lean_object* v_a_6928_; lean_object* v_a_6929_; lean_object* v___x_6931_; uint8_t v_isShared_6932_; uint8_t v_isSharedCheck_6936_; 
lean_dec_ref(v_b_6864_);
lean_dec(v_a_6863_);
lean_dec_ref(v_pendingGroup_6861_);
v_a_6928_ = lean_ctor_get(v___x_6876_, 0);
v_a_6929_ = lean_ctor_get(v___x_6876_, 1);
v_isSharedCheck_6936_ = !lean_is_exclusive(v___x_6876_);
if (v_isSharedCheck_6936_ == 0)
{
v___x_6931_ = v___x_6876_;
v_isShared_6932_ = v_isSharedCheck_6936_;
goto v_resetjp_6930_;
}
else
{
lean_inc(v_a_6929_);
lean_inc(v_a_6928_);
lean_dec(v___x_6876_);
v___x_6931_ = lean_box(0);
v_isShared_6932_ = v_isSharedCheck_6936_;
goto v_resetjp_6930_;
}
v_resetjp_6930_:
{
lean_object* v___x_6934_; 
if (v_isShared_6932_ == 0)
{
v___x_6934_ = v___x_6931_;
goto v_reusejp_6933_;
}
else
{
lean_object* v_reuseFailAlloc_6935_; 
v_reuseFailAlloc_6935_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6935_, 0, v_a_6928_);
lean_ctor_set(v_reuseFailAlloc_6935_, 1, v_a_6929_);
v___x_6934_ = v_reuseFailAlloc_6935_;
goto v_reusejp_6933_;
}
v_reusejp_6933_:
{
return v___x_6934_;
}
}
}
}
v___jp_6867_:
{
lean_object* v___x_6870_; lean_object* v___x_6871_; 
v___x_6870_ = lean_unsigned_to_nat(1u);
v___x_6871_ = lean_nat_add(v_a_6863_, v___x_6870_);
lean_dec(v_a_6863_);
v_a_6863_ = v___x_6871_;
v_b_6864_ = v_a_6868_;
v___y_6866_ = v_a_6869_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object* v_upperBound_6937_, lean_object* v_elemsAndSeps_6938_, lean_object* v_pendingGroup_6939_, lean_object* v___x_6940_, lean_object* v_a_6941_, lean_object* v_b_6942_, lean_object* v___y_6943_, lean_object* v___y_6944_){
_start:
{
lean_object* v_res_6945_; 
v_res_6945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_6937_, v_elemsAndSeps_6938_, v_pendingGroup_6939_, v___x_6940_, v_a_6941_, v_b_6942_, v___y_6943_, v___y_6944_);
lean_dec_ref(v___y_6943_);
lean_dec(v___x_6940_);
lean_dec_ref(v_elemsAndSeps_6938_);
lean_dec(v_upperBound_6937_);
return v_res_6945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object* v_sep_6950_, lean_object* v_stxs_6951_, lean_object* v_a_6952_, lean_object* v_a_6953_){
_start:
{
lean_object* v___x_6954_; lean_object* v___x_6955_; lean_object* v_acc_6956_; lean_object* v___x_6957_; lean_object* v___x_6958_; 
v___x_6954_ = lean_unsigned_to_nat(0u);
v___x_6955_ = lean_array_get_size(v_stxs_6951_);
v_acc_6956_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0));
v___x_6957_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1));
v___x_6958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v___x_6955_, v_stxs_6951_, v_acc_6956_, v___x_6955_, v___x_6954_, v___x_6957_, v_a_6952_, v_a_6953_);
if (lean_obj_tag(v___x_6958_) == 0)
{
lean_object* v_a_6959_; lean_object* v_a_6960_; lean_object* v___x_6962_; uint8_t v_isShared_6963_; uint8_t v_isSharedCheck_6976_; 
v_a_6959_ = lean_ctor_get(v___x_6958_, 0);
v_a_6960_ = lean_ctor_get(v___x_6958_, 1);
v_isSharedCheck_6976_ = !lean_is_exclusive(v___x_6958_);
if (v_isSharedCheck_6976_ == 0)
{
v___x_6962_ = v___x_6958_;
v_isShared_6963_ = v_isSharedCheck_6976_;
goto v_resetjp_6961_;
}
else
{
lean_inc(v_a_6960_);
lean_inc(v_a_6959_);
lean_dec(v___x_6958_);
v___x_6962_ = lean_box(0);
v_isShared_6963_ = v_isSharedCheck_6976_;
goto v_resetjp_6961_;
}
v_resetjp_6961_:
{
lean_object* v_fst_6964_; lean_object* v_snd_6965_; lean_object* v___x_6966_; uint8_t v___x_6967_; 
v_fst_6964_ = lean_ctor_get(v_a_6959_, 0);
lean_inc(v_fst_6964_);
v_snd_6965_ = lean_ctor_get(v_a_6959_, 1);
lean_inc(v_snd_6965_);
lean_dec(v_a_6959_);
v___x_6966_ = lean_array_get_size(v_snd_6965_);
v___x_6967_ = lean_nat_dec_eq(v___x_6966_, v___x_6954_);
if (v___x_6967_ == 0)
{
lean_object* v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6971_; 
v___x_6968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6968_, 0, v_snd_6965_);
v___x_6969_ = lean_array_push(v_fst_6964_, v___x_6968_);
if (v_isShared_6963_ == 0)
{
lean_ctor_set(v___x_6962_, 0, v___x_6969_);
v___x_6971_ = v___x_6962_;
goto v_reusejp_6970_;
}
else
{
lean_object* v_reuseFailAlloc_6972_; 
v_reuseFailAlloc_6972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6972_, 0, v___x_6969_);
lean_ctor_set(v_reuseFailAlloc_6972_, 1, v_a_6960_);
v___x_6971_ = v_reuseFailAlloc_6972_;
goto v_reusejp_6970_;
}
v_reusejp_6970_:
{
return v___x_6971_;
}
}
else
{
lean_object* v___x_6974_; 
lean_dec(v_snd_6965_);
if (v_isShared_6963_ == 0)
{
lean_ctor_set(v___x_6962_, 0, v_fst_6964_);
v___x_6974_ = v___x_6962_;
goto v_reusejp_6973_;
}
else
{
lean_object* v_reuseFailAlloc_6975_; 
v_reuseFailAlloc_6975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6975_, 0, v_fst_6964_);
lean_ctor_set(v_reuseFailAlloc_6975_, 1, v_a_6960_);
v___x_6974_ = v_reuseFailAlloc_6975_;
goto v_reusejp_6973_;
}
v_reusejp_6973_:
{
return v___x_6974_;
}
}
}
}
else
{
lean_object* v_a_6977_; lean_object* v_a_6978_; lean_object* v___x_6980_; uint8_t v_isShared_6981_; uint8_t v_isSharedCheck_6985_; 
v_a_6977_ = lean_ctor_get(v___x_6958_, 0);
v_a_6978_ = lean_ctor_get(v___x_6958_, 1);
v_isSharedCheck_6985_ = !lean_is_exclusive(v___x_6958_);
if (v_isSharedCheck_6985_ == 0)
{
v___x_6980_ = v___x_6958_;
v_isShared_6981_ = v_isSharedCheck_6985_;
goto v_resetjp_6979_;
}
else
{
lean_inc(v_a_6978_);
lean_inc(v_a_6977_);
lean_dec(v___x_6958_);
v___x_6980_ = lean_box(0);
v_isShared_6981_ = v_isSharedCheck_6985_;
goto v_resetjp_6979_;
}
v_resetjp_6979_:
{
lean_object* v___x_6983_; 
if (v_isShared_6981_ == 0)
{
v___x_6983_ = v___x_6980_;
goto v_reusejp_6982_;
}
else
{
lean_object* v_reuseFailAlloc_6984_; 
v_reuseFailAlloc_6984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6984_, 0, v_a_6977_);
lean_ctor_set(v_reuseFailAlloc_6984_, 1, v_a_6978_);
v___x_6983_ = v_reuseFailAlloc_6984_;
goto v_reusejp_6982_;
}
v_reusejp_6982_:
{
return v___x_6983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object* v_sep_6986_, lean_object* v_stxs_6987_, lean_object* v_a_6988_, lean_object* v_a_6989_){
_start:
{
lean_object* v_res_6990_; 
v_res_6990_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_6986_, v_stxs_6987_, v_a_6988_, v_a_6989_);
lean_dec_ref(v_a_6988_);
lean_dec_ref(v_stxs_6987_);
lean_dec_ref(v_sep_6986_);
return v_res_6990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object* v_ks_6991_, lean_object* v_sep_6992_, lean_object* v_stxs_6993_, lean_object* v_a_6994_, lean_object* v_a_6995_){
_start:
{
lean_object* v___x_6996_; 
v___x_6996_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_6992_, v_stxs_6993_, v_a_6994_, v_a_6995_);
return v___x_6996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object* v_ks_6997_, lean_object* v_sep_6998_, lean_object* v_stxs_6999_, lean_object* v_a_7000_, lean_object* v_a_7001_){
_start:
{
lean_object* v_res_7002_; 
v_res_7002_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups(v_ks_6997_, v_sep_6998_, v_stxs_6999_, v_a_7000_, v_a_7001_);
lean_dec_ref(v_a_7000_);
lean_dec_ref(v_stxs_6999_);
lean_dec_ref(v_sep_6998_);
lean_dec(v_ks_6997_);
return v_res_7002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object* v_upperBound_7003_, lean_object* v_elemsAndSeps_7004_, lean_object* v_sep_7005_, lean_object* v_pendingGroup_7006_, lean_object* v___x_7007_, lean_object* v_inst_7008_, lean_object* v_R_7009_, lean_object* v_a_7010_, lean_object* v_b_7011_, lean_object* v_c_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_){
_start:
{
lean_object* v___x_7015_; 
v___x_7015_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7003_, v_elemsAndSeps_7004_, v_pendingGroup_7006_, v___x_7007_, v_a_7010_, v_b_7011_, v___y_7013_, v___y_7014_);
return v___x_7015_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object* v_upperBound_7016_, lean_object* v_elemsAndSeps_7017_, lean_object* v_sep_7018_, lean_object* v_pendingGroup_7019_, lean_object* v___x_7020_, lean_object* v_inst_7021_, lean_object* v_R_7022_, lean_object* v_a_7023_, lean_object* v_b_7024_, lean_object* v_c_7025_, lean_object* v___y_7026_, lean_object* v___y_7027_){
_start:
{
lean_object* v_res_7028_; 
v_res_7028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(v_upperBound_7016_, v_elemsAndSeps_7017_, v_sep_7018_, v_pendingGroup_7019_, v___x_7020_, v_inst_7021_, v_R_7022_, v_a_7023_, v_b_7024_, v_c_7025_, v___y_7026_, v___y_7027_);
lean_dec_ref(v___y_7026_);
lean_dec(v___x_7020_);
lean_dec_ref(v_sep_7018_);
lean_dec_ref(v_elemsAndSeps_7017_);
lean_dec(v_upperBound_7016_);
return v_res_7028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object* v_sep_7032_, size_t v_sz_7033_, size_t v_i_7034_, lean_object* v_bs_7035_){
_start:
{
uint8_t v___x_7036_; 
v___x_7036_ = lean_usize_dec_lt(v_i_7034_, v_sz_7033_);
if (v___x_7036_ == 0)
{
lean_dec_ref(v_sep_7032_);
return v_bs_7035_;
}
else
{
lean_object* v_v_7037_; lean_object* v___x_7038_; lean_object* v_bs_x27_7039_; lean_object* v___y_7041_; 
v_v_7037_ = lean_array_uget(v_bs_7035_, v_i_7034_);
v___x_7038_ = lean_unsigned_to_nat(0u);
v_bs_x27_7039_ = lean_array_uset(v_bs_7035_, v_i_7034_, v___x_7038_);
if (lean_obj_tag(v_v_7037_) == 0)
{
lean_object* v_g_7046_; lean_object* v___x_7047_; lean_object* v___x_7048_; 
v_g_7046_ = lean_ctor_get(v_v_7037_, 0);
lean_inc_ref(v_g_7046_);
lean_dec_ref_known(v_v_7037_, 1);
v___x_7047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0));
lean_inc_ref(v_sep_7032_);
v___x_7048_ = l_Lean_Fmt_Layouts_sepArray(v_sep_7032_, v_g_7046_, v___x_7047_);
lean_dec_ref(v_g_7046_);
v___y_7041_ = v___x_7048_;
goto v___jp_7040_;
}
else
{
lean_object* v_t_7049_; 
v_t_7049_ = lean_ctor_get(v_v_7037_, 0);
lean_inc_ref(v_t_7049_);
lean_dec_ref_known(v_v_7037_, 1);
v___y_7041_ = v_t_7049_;
goto v___jp_7040_;
}
v___jp_7040_:
{
size_t v___x_7042_; size_t v___x_7043_; lean_object* v___x_7044_; 
v___x_7042_ = ((size_t)1ULL);
v___x_7043_ = lean_usize_add(v_i_7034_, v___x_7042_);
v___x_7044_ = lean_array_uset(v_bs_x27_7039_, v_i_7034_, v___y_7041_);
v_i_7034_ = v___x_7043_;
v_bs_7035_ = v___x_7044_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object* v_sep_7050_, lean_object* v_sz_7051_, lean_object* v_i_7052_, lean_object* v_bs_7053_){
_start:
{
size_t v_sz_boxed_7054_; size_t v_i_boxed_7055_; lean_object* v_res_7056_; 
v_sz_boxed_7054_ = lean_unbox_usize(v_sz_7051_);
lean_dec(v_sz_7051_);
v_i_boxed_7055_ = lean_unbox_usize(v_i_7052_);
lean_dec(v_i_7052_);
v_res_7056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7050_, v_sz_boxed_7054_, v_i_boxed_7055_, v_bs_7053_);
return v_res_7056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object* v_sep_7057_, lean_object* v_stxs_7058_, lean_object* v_a_7059_, lean_object* v_a_7060_){
_start:
{
lean_object* v___x_7061_; 
v___x_7061_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7057_, v_stxs_7058_, v_a_7059_, v_a_7060_);
if (lean_obj_tag(v___x_7061_) == 0)
{
lean_object* v_a_7062_; lean_object* v_a_7063_; lean_object* v___x_7065_; uint8_t v_isShared_7066_; uint8_t v_isSharedCheck_7074_; 
v_a_7062_ = lean_ctor_get(v___x_7061_, 0);
v_a_7063_ = lean_ctor_get(v___x_7061_, 1);
v_isSharedCheck_7074_ = !lean_is_exclusive(v___x_7061_);
if (v_isSharedCheck_7074_ == 0)
{
v___x_7065_ = v___x_7061_;
v_isShared_7066_ = v_isSharedCheck_7074_;
goto v_resetjp_7064_;
}
else
{
lean_inc(v_a_7063_);
lean_inc(v_a_7062_);
lean_dec(v___x_7061_);
v___x_7065_ = lean_box(0);
v_isShared_7066_ = v_isSharedCheck_7074_;
goto v_resetjp_7064_;
}
v_resetjp_7064_:
{
size_t v_sz_7067_; size_t v___x_7068_; lean_object* v___x_7069_; lean_object* v___x_7070_; lean_object* v___x_7072_; 
v_sz_7067_ = lean_array_size(v_a_7062_);
v___x_7068_ = ((size_t)0ULL);
v___x_7069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7057_, v_sz_7067_, v___x_7068_, v_a_7062_);
v___x_7070_ = l_Lean_Fmt_TaggedDoc_join(v___x_7069_);
if (v_isShared_7066_ == 0)
{
lean_ctor_set(v___x_7065_, 0, v___x_7070_);
v___x_7072_ = v___x_7065_;
goto v_reusejp_7071_;
}
else
{
lean_object* v_reuseFailAlloc_7073_; 
v_reuseFailAlloc_7073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7073_, 0, v___x_7070_);
lean_ctor_set(v_reuseFailAlloc_7073_, 1, v_a_7063_);
v___x_7072_ = v_reuseFailAlloc_7073_;
goto v_reusejp_7071_;
}
v_reusejp_7071_:
{
return v___x_7072_;
}
}
}
else
{
lean_object* v_a_7075_; lean_object* v_a_7076_; lean_object* v___x_7078_; uint8_t v_isShared_7079_; uint8_t v_isSharedCheck_7083_; 
lean_dec_ref(v_sep_7057_);
v_a_7075_ = lean_ctor_get(v___x_7061_, 0);
v_a_7076_ = lean_ctor_get(v___x_7061_, 1);
v_isSharedCheck_7083_ = !lean_is_exclusive(v___x_7061_);
if (v_isSharedCheck_7083_ == 0)
{
v___x_7078_ = v___x_7061_;
v_isShared_7079_ = v_isSharedCheck_7083_;
goto v_resetjp_7077_;
}
else
{
lean_inc(v_a_7076_);
lean_inc(v_a_7075_);
lean_dec(v___x_7061_);
v___x_7078_ = lean_box(0);
v_isShared_7079_ = v_isSharedCheck_7083_;
goto v_resetjp_7077_;
}
v_resetjp_7077_:
{
lean_object* v___x_7081_; 
if (v_isShared_7079_ == 0)
{
v___x_7081_ = v___x_7078_;
goto v_reusejp_7080_;
}
else
{
lean_object* v_reuseFailAlloc_7082_; 
v_reuseFailAlloc_7082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_a_7075_);
lean_ctor_set(v_reuseFailAlloc_7082_, 1, v_a_7076_);
v___x_7081_ = v_reuseFailAlloc_7082_;
goto v_reusejp_7080_;
}
v_reusejp_7080_:
{
return v___x_7081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object* v_sep_7084_, lean_object* v_stxs_7085_, lean_object* v_a_7086_, lean_object* v_a_7087_){
_start:
{
lean_object* v_res_7088_; 
v_res_7088_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7084_, v_stxs_7085_, v_a_7086_, v_a_7087_);
lean_dec_ref(v_a_7086_);
lean_dec_ref(v_stxs_7085_);
return v_res_7088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_ks_7089_, lean_object* v_sep_7090_, lean_object* v_stxs_7091_, lean_object* v_a_7092_, lean_object* v_a_7093_){
_start:
{
lean_object* v___x_7094_; 
v___x_7094_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7090_, v_stxs_7091_, v_a_7092_, v_a_7093_);
return v___x_7094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_ks_7095_, lean_object* v_sep_7096_, lean_object* v_stxs_7097_, lean_object* v_a_7098_, lean_object* v_a_7099_){
_start:
{
lean_object* v_res_7100_; 
v_res_7100_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(v_ks_7095_, v_sep_7096_, v_stxs_7097_, v_a_7098_, v_a_7099_);
lean_dec_ref(v_a_7098_);
lean_dec_ref(v_stxs_7097_);
lean_dec(v_ks_7095_);
return v_res_7100_;
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
