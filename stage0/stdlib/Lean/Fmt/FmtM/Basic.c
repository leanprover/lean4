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
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
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
uint8_t v___x_819_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; uint8_t v___y_825_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; uint8_t v___y_839_; uint8_t v___y_840_; lean_object* v___x_888_; 
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
v___x_827_ = lean_nat_add(v___y_821_, v___x_826_);
lean_dec(v___y_821_);
v___x_828_ = lean_nat_dec_eq(v___x_827_, v___y_824_);
lean_dec(v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v___y_824_);
lean_dec(v___y_823_);
lean_dec(v___y_822_);
v___x_829_ = lean_box(0);
return v___x_829_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = lean_nat_dec_eq(v___y_824_, v___y_822_);
lean_dec(v___y_822_);
lean_dec(v___y_824_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec(v___y_823_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_833_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_833_, 0, v___y_823_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*2, v___y_825_);
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
lean_inc(v___y_837_);
lean_inc(v___y_838_);
lean_inc(v___y_836_);
v___x_841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_841_, 0, v___y_836_);
lean_ctor_set(v___x_841_, 1, v___y_838_);
lean_ctor_set(v___x_841_, 2, v___y_837_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
if (v___y_840_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_eq(v___y_836_, v___y_837_);
if (v___x_843_ == 0)
{
v___y_821_ = v___y_836_;
v___y_822_ = v___y_837_;
v___y_823_ = v___x_842_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_839_;
goto v___jp_820_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_nat_add(v___y_837_, v___x_844_);
v___x_846_ = lean_nat_dec_eq(v___y_838_, v___x_845_);
lean_dec(v___x_845_);
if (v___x_846_ == 0)
{
v___y_821_ = v___y_836_;
v___y_822_ = v___y_837_;
v___y_823_ = v___x_842_;
v___y_824_ = v___y_838_;
v___y_825_ = v___y_839_;
goto v___jp_820_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
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
lean_dec(v___y_838_);
lean_dec(v___y_837_);
lean_dec(v___y_836_);
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
v___y_836_ = v_prec_861_;
v___y_837_ = v_rbp_871_;
v___y_838_ = v_lhsPrec_862_;
v___y_839_ = v___x_874_;
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
v___y_836_ = v_prec_861_;
v___y_837_ = v_rbp_871_;
v___y_838_ = v_lhsPrec_862_;
v___y_839_ = v___x_874_;
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
lean_dec_ref_known(v_p_858_, 3);
lean_dec(v_name_859_);
lean_dec_ref_known(v_a_857_, 4);
v___x_885_ = lean_box(0);
return v___x_885_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec_ref(v_p_858_);
lean_dec_ref_known(v_a_857_, 4);
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
lean_dec(v_catName_950_);
lean_dec_ref_known(v_p_u2082_946_, 2);
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
lean_dec(v_name_942_);
lean_dec_ref_known(v_p_941_, 3);
lean_dec_ref_known(v_a_940_, 3);
return v___x_933_;
}
}
else
{
lean_dec_ref_known(v_a_940_, 3);
lean_dec_ref(v_p_941_);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v___x_2123_, lean_object* v_as_2124_, size_t v_i_2125_, size_t v_stop_2126_){
_start:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_usize_dec_eq(v_i_2125_, v_stop_2126_);
if (v___x_2127_ == 0)
{
uint8_t v___x_2128_; uint8_t v___y_2130_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2128_ = 1;
v___x_2134_ = lean_array_uget_borrowed(v_as_2124_, v_i_2125_);
v___x_2135_ = lean_nat_dec_le(v___x_2121_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_unsigned_to_nat(1u);
v___x_2137_ = lean_nat_dec_lt(v___x_2136_, v___x_2122_);
v___y_2130_ = v___x_2137_;
goto v___jp_2129_;
}
else
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_nat_dec_le(v___x_2121_, v___x_2123_);
v___y_2130_ = v___x_2138_;
goto v___jp_2129_;
}
v___jp_2129_:
{
if (v___y_2130_ == 0)
{
size_t v___x_2131_; size_t v___x_2132_; 
v___x_2131_ = ((size_t)1ULL);
v___x_2132_ = lean_usize_add(v_i_2125_, v___x_2131_);
v_i_2125_ = v___x_2132_;
goto _start;
}
else
{
return v___x_2128_;
}
}
}
else
{
uint8_t v___x_2139_; 
v___x_2139_ = 0;
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v_as_2143_, lean_object* v_i_2144_, lean_object* v_stop_2145_){
_start:
{
size_t v_i_boxed_2146_; size_t v_stop_boxed_2147_; uint8_t v_res_2148_; lean_object* v_r_2149_; 
v_i_boxed_2146_ = lean_unbox_usize(v_i_2144_);
lean_dec(v_i_2144_);
v_stop_boxed_2147_ = lean_unbox_usize(v_stop_2145_);
lean_dec(v_stop_2145_);
v_res_2148_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2140_, v___x_2141_, v___x_2142_, v_as_2143_, v_i_boxed_2146_, v_stop_boxed_2147_);
lean_dec_ref(v_as_2143_);
lean_dec(v___x_2142_);
lean_dec(v___x_2141_);
lean_dec(v___x_2140_);
v_r_2149_ = lean_box(v_res_2148_);
return v_r_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t v_sz_2150_, size_t v_i_2151_, lean_object* v_bs_2152_){
_start:
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_usize_dec_lt(v_i_2151_, v_sz_2150_);
if (v___x_2153_ == 0)
{
return v_bs_2152_;
}
else
{
lean_object* v_v_2154_; lean_object* v_indentation_2155_; lean_object* v___x_2156_; lean_object* v_bs_x27_2157_; size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v_v_2154_ = lean_array_uget_borrowed(v_bs_2152_, v_i_2151_);
v_indentation_2155_ = lean_ctor_get(v_v_2154_, 1);
lean_inc(v_indentation_2155_);
v___x_2156_ = lean_unsigned_to_nat(0u);
v_bs_x27_2157_ = lean_array_uset(v_bs_2152_, v_i_2151_, v___x_2156_);
v___x_2158_ = ((size_t)1ULL);
v___x_2159_ = lean_usize_add(v_i_2151_, v___x_2158_);
v___x_2160_ = lean_array_uset(v_bs_x27_2157_, v_i_2151_, v_indentation_2155_);
v_i_2151_ = v___x_2159_;
v_bs_2152_ = v___x_2160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object* v_sz_2162_, lean_object* v_i_2163_, lean_object* v_bs_2164_){
_start:
{
size_t v_sz_boxed_2165_; size_t v_i_boxed_2166_; lean_object* v_res_2167_; 
v_sz_boxed_2165_ = lean_unbox_usize(v_sz_2162_);
lean_dec(v_sz_2162_);
v_i_boxed_2166_ = lean_unbox_usize(v_i_2163_);
lean_dec(v_i_2163_);
v_res_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_boxed_2165_, v_i_boxed_2166_, v_bs_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object* v_as_2168_, size_t v_i_2169_, size_t v_stop_2170_, lean_object* v_b_2171_){
_start:
{
lean_object* v___y_2173_; uint8_t v___x_2177_; 
v___x_2177_ = lean_usize_dec_eq(v_i_2169_, v_stop_2170_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = lean_array_uget_borrowed(v_as_2168_, v_i_2169_);
v___x_2179_ = lean_nat_dec_le(v_b_2171_, v___x_2178_);
if (v___x_2179_ == 0)
{
v___y_2173_ = v___x_2178_;
goto v___jp_2172_;
}
else
{
v___y_2173_ = v_b_2171_;
goto v___jp_2172_;
}
}
else
{
lean_inc(v_b_2171_);
return v_b_2171_;
}
v___jp_2172_:
{
size_t v___x_2174_; size_t v___x_2175_; 
v___x_2174_ = ((size_t)1ULL);
v___x_2175_ = lean_usize_add(v_i_2169_, v___x_2174_);
v_i_2169_ = v___x_2175_;
v_b_2171_ = v___y_2173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object* v_as_2180_, lean_object* v_i_2181_, lean_object* v_stop_2182_, lean_object* v_b_2183_){
_start:
{
size_t v_i_boxed_2184_; size_t v_stop_boxed_2185_; lean_object* v_res_2186_; 
v_i_boxed_2184_ = lean_unbox_usize(v_i_2181_);
lean_dec(v_i_2181_);
v_stop_boxed_2185_ = lean_unbox_usize(v_stop_2182_);
lean_dec(v_stop_2182_);
v_res_2186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_as_2180_, v_i_boxed_2184_, v_stop_boxed_2185_, v_b_2183_);
lean_dec(v_b_2183_);
lean_dec_ref(v_as_2180_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object* v_arr_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_array_fget_borrowed(v_arr_2187_, v___x_2188_);
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_array_get_size(v_arr_2187_);
v___x_2192_ = lean_nat_dec_lt(v___x_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_inc(v___x_2189_);
return v___x_2189_;
}
else
{
size_t v___x_2193_; size_t v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((size_t)1ULL);
v___x_2194_ = lean_usize_of_nat(v___x_2191_);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_arr_2187_, v___x_2193_, v___x_2194_, v___x_2189_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object* v_arr_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2196_);
lean_dec_ref(v_arr_2196_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object* v_arr_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = lean_array_get_size(v_arr_2198_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = lean_nat_dec_eq(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2198_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_box(0);
return v___x_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object* v_arr_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v_arr_2205_);
lean_dec_ref(v_arr_2205_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t v_isFallback_2207_, lean_object* v_stx_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_rawDoc_2212_; lean_object* v___y_2213_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2230_; lean_object* v___y_2231_; uint8_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = 0;
v___x_2236_ = l_Lean_Syntax_getPos_x3f(v_stx_2208_, v___x_2235_);
if (lean_obj_tag(v___x_2236_) == 1)
{
lean_object* v_val_2237_; lean_object* v___x_2238_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2208_, v___x_2235_);
if (lean_obj_tag(v___x_2238_) == 1)
{
lean_object* v_val_2239_; lean_object* v___x_2240_; 
v_val_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc_n(v_val_2239_, 2);
lean_dec_ref_known(v___x_2238_, 1);
lean_inc(v_val_2237_);
v___x_2240_ = l_Lean_Fmt_getLineInfos(v_val_2237_, v_val_2239_, v_a_2209_, v_a_2210_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_a_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_indentation_2246_; lean_object* v_line_2247_; lean_object* v_startPos_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___y_2253_; size_t v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2268_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc_n(v_a_2241_, 2);
v_a_2242_ = lean_ctor_get(v___x_2240_, 1);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2240_, 2);
v___x_2243_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = lean_array_get_borrowed(v___x_2243_, v_a_2241_, v___x_2244_);
v_indentation_2246_ = lean_ctor_get(v___x_2245_, 1);
lean_inc(v_indentation_2246_);
v_line_2247_ = lean_ctor_get(v___x_2245_, 2);
v_startPos_2248_ = lean_ctor_get(v___x_2245_, 4);
v___x_2249_ = lean_nat_sub(v_val_2237_, v_startPos_2248_);
v___x_2250_ = l_String_Pos_Raw_offsetOfPosAux(v_line_2247_, v___x_2249_, v___x_2244_, v___x_2244_);
lean_dec(v___x_2249_);
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_array_get_size(v_a_2241_);
v___x_2280_ = l_Array_toSubarray___redArg(v_a_2241_, v___x_2251_, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_2282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_2280_, v___x_2281_);
v___x_2283_ = lean_array_get_size(v___x_2282_);
v___x_2284_ = lean_nat_dec_lt(v___x_2244_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_dec_ref(v___x_2282_);
v___y_2268_ = v___x_2281_;
goto v___jp_2267_;
}
else
{
size_t v___x_2285_; size_t v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((size_t)0ULL);
v___x_2286_ = lean_usize_of_nat(v___x_2283_);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2282_, v___x_2285_, v___x_2286_, v___x_2281_);
lean_dec_ref(v___x_2282_);
v___y_2268_ = v___x_2287_;
goto v___jp_2267_;
}
v___jp_2252_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2256_, 0, v___y_2255_);
lean_ctor_set(v___x_2256_, 1, v_val_2237_);
lean_ctor_set(v___x_2256_, 2, v_val_2239_);
lean_inc(v_stx_2208_);
v___x_2257_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2208_, v___x_2256_, v_a_2209_, v_a_2242_);
lean_dec_ref_known(v___x_2256_, 3);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v_a_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
v_a_2259_ = lean_ctor_get(v___x_2257_, 1);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2257_, 2);
v___x_2260_ = lean_array_get_size(v_a_2241_);
lean_dec(v_a_2241_);
v___x_2261_ = lean_nat_dec_lt(v___x_2251_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_dec_ref(v___y_2253_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
v___y_2226_ = v_a_2259_;
v___y_2227_ = v_a_2258_;
goto v___jp_2225_;
}
else
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_nat_dec_le(v___x_2250_, v_indentation_2246_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = lean_array_get_size(v___y_2253_);
v___x_2264_ = lean_nat_dec_lt(v___x_2244_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_dec_ref(v___y_2253_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
v___y_2230_ = v_a_2259_;
v___y_2231_ = v_a_2258_;
goto v___jp_2229_;
}
else
{
if (v___x_2264_ == 0)
{
lean_dec_ref(v___y_2253_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
v___y_2230_ = v_a_2259_;
v___y_2231_ = v_a_2258_;
goto v___jp_2229_;
}
else
{
size_t v___x_2265_; uint8_t v___x_2266_; 
v___x_2265_ = lean_usize_of_nat(v___x_2263_);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2250_, v___x_2260_, v_indentation_2246_, v___y_2253_, v___y_2254_, v___x_2265_);
lean_dec_ref(v___y_2253_);
lean_dec(v_indentation_2246_);
lean_dec(v___x_2250_);
if (v___x_2266_ == 0)
{
v___y_2230_ = v_a_2259_;
v___y_2231_ = v_a_2258_;
goto v___jp_2229_;
}
else
{
v___y_2226_ = v_a_2259_;
v___y_2227_ = v_a_2258_;
goto v___jp_2225_;
}
}
}
}
else
{
lean_dec_ref(v___y_2253_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
v___y_2230_ = v_a_2259_;
v___y_2231_ = v_a_2258_;
goto v___jp_2229_;
}
}
}
else
{
lean_dec_ref(v___y_2253_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
lean_dec(v_a_2241_);
lean_dec(v_stx_2208_);
return v___x_2257_;
}
}
v___jp_2267_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; size_t v_sz_2271_; size_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2269_ = lean_mk_empty_array_with_capacity(v___x_2251_);
lean_inc(v___x_2250_);
v___x_2270_ = lean_array_push(v___x_2269_, v___x_2250_);
v_sz_2271_ = lean_array_size(v___y_2268_);
v___x_2272_ = ((size_t)0ULL);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_2271_, v___x_2272_, v___y_2268_);
v___x_2274_ = l_Array_append___redArg(v___x_2270_, v___x_2273_);
v___x_2275_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v___x_2274_);
lean_dec_ref(v___x_2274_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_2277_ = l_panic___at___00Lean_Fmt_fmtRaw_spec__4(v___x_2276_);
v___y_2253_ = v___x_2273_;
v___y_2254_ = v___x_2272_;
v___y_2255_ = v___x_2277_;
goto v___jp_2252_;
}
else
{
lean_object* v_val_2278_; 
v_val_2278_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_val_2278_);
lean_dec_ref_known(v___x_2275_, 1);
v___y_2253_ = v___x_2273_;
v___y_2254_ = v___x_2272_;
v___y_2255_ = v_val_2278_;
goto v___jp_2252_;
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v_val_2239_);
lean_dec(v_val_2237_);
lean_dec(v_stx_2208_);
v_a_2288_ = lean_ctor_get(v___x_2240_, 0);
v_a_2289_ = lean_ctor_get(v___x_2240_, 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2240_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_inc(v_a_2288_);
lean_dec(v___x_2240_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2288_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_dec(v___x_2238_);
lean_dec(v_val_2237_);
v___x_2297_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2298_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2297_, v_stx_2208_, v_a_2210_);
lean_dec(v_stx_2208_);
return v___x_2298_;
}
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec(v___x_2236_);
v___x_2299_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2300_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2299_, v_stx_2208_, v_a_2210_);
lean_dec(v_stx_2208_);
return v___x_2300_;
}
v___jp_2211_:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_rawDoc_2212_, v_stx_2208_, v___y_2213_);
lean_dec(v_stx_2208_);
if (lean_obj_tag(v___x_2214_) == 0)
{
if (v_isFallback_2207_ == 0)
{
return v___x_2214_;
}
else
{
lean_object* v_a_2215_; lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2224_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_a_2216_ = lean_ctor_get(v___x_2214_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2218_ = v___x_2214_;
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2224_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_2215_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_a_2216_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
return v___x_2214_;
}
}
v___jp_2225_:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2227_);
v_rawDoc_2212_ = v___x_2228_;
v___y_2213_ = v___y_2226_;
goto v___jp_2211_;
}
v___jp_2229_:
{
lean_object* v_doc_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_doc_2232_ = lean_ctor_get(v___y_2231_, 0);
lean_inc(v_doc_2232_);
lean_dec_ref(v___y_2231_);
v___x_2233_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_2232_);
v___x_2234_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2233_);
v_rawDoc_2212_ = v___x_2234_;
v___y_2213_ = v___y_2230_;
goto v___jp_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object* v_isFallback_2301_, lean_object* v_stx_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
uint8_t v_isFallback_boxed_2305_; lean_object* v_res_2306_; 
v_isFallback_boxed_2305_ = lean_unbox(v_isFallback_2301_);
v_res_2306_ = l_Lean_Fmt_fmtRaw(v_isFallback_boxed_2305_, v_stx_2302_, v_a_2303_, v_a_2304_);
lean_dec_ref(v_a_2303_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object* v_arr_2307_, lean_object* v_h_2308_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2307_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object* v_arr_2310_, lean_object* v_h_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(v_arr_2310_, v_h_2311_);
lean_dec_ref(v_arr_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object* v_a_2313_, lean_object* v_____r_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v_a_2313_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object* v_a_2319_, lean_object* v_____r_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2319_, v_____r_2320_, v___y_2321_, v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object* v_a_2324_, lean_object* v_b_2325_, lean_object* v_x_2326_){
_start:
{
if (lean_obj_tag(v_x_2326_) == 0)
{
lean_dec(v_b_2325_);
lean_dec_ref(v_a_2324_);
return v_x_2326_;
}
else
{
lean_object* v_key_2327_; lean_object* v_value_2328_; lean_object* v_tail_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2341_; 
v_key_2327_ = lean_ctor_get(v_x_2326_, 0);
v_value_2328_ = lean_ctor_get(v_x_2326_, 1);
v_tail_2329_ = lean_ctor_get(v_x_2326_, 2);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_x_2326_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2331_ = v_x_2326_;
v_isShared_2332_ = v_isSharedCheck_2341_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_tail_2329_);
lean_inc(v_value_2328_);
lean_inc(v_key_2327_);
lean_dec(v_x_2326_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2341_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
uint8_t v___x_2333_; 
v___x_2333_ = l_Lean_Syntax_instBEqRange_beq(v_key_2327_, v_a_2324_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2334_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2324_, v_b_2325_, v_tail_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 2, v___x_2334_);
v___x_2336_ = v___x_2331_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_key_2327_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_value_2328_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
else
{
lean_object* v___x_2339_; 
lean_dec(v_value_2328_);
lean_dec(v_key_2327_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v_b_2325_);
lean_ctor_set(v___x_2331_, 0, v_a_2324_);
v___x_2339_ = v___x_2331_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2324_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_b_2325_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_tail_2329_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2342_, lean_object* v_x_2343_){
_start:
{
if (lean_obj_tag(v_x_2343_) == 0)
{
return v_x_2342_;
}
else
{
lean_object* v_key_2344_; lean_object* v_value_2345_; lean_object* v_tail_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2369_; 
v_key_2344_ = lean_ctor_get(v_x_2343_, 0);
v_value_2345_ = lean_ctor_get(v_x_2343_, 1);
v_tail_2346_ = lean_ctor_get(v_x_2343_, 2);
v_isSharedCheck_2369_ = !lean_is_exclusive(v_x_2343_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2348_ = v_x_2343_;
v_isShared_2349_ = v_isSharedCheck_2369_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_tail_2346_);
lean_inc(v_value_2345_);
lean_inc(v_key_2344_);
lean_dec(v_x_2343_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2369_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; uint64_t v___x_2351_; uint64_t v___x_2352_; uint64_t v___x_2353_; uint64_t v_fold_2354_; uint64_t v___x_2355_; uint64_t v___x_2356_; uint64_t v___x_2357_; size_t v___x_2358_; size_t v___x_2359_; size_t v___x_2360_; size_t v___x_2361_; size_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2350_ = lean_array_get_size(v_x_2342_);
v___x_2351_ = l_Lean_Syntax_instHashableRange_hash(v_key_2344_);
v___x_2352_ = 32ULL;
v___x_2353_ = lean_uint64_shift_right(v___x_2351_, v___x_2352_);
v_fold_2354_ = lean_uint64_xor(v___x_2351_, v___x_2353_);
v___x_2355_ = 16ULL;
v___x_2356_ = lean_uint64_shift_right(v_fold_2354_, v___x_2355_);
v___x_2357_ = lean_uint64_xor(v_fold_2354_, v___x_2356_);
v___x_2358_ = lean_uint64_to_usize(v___x_2357_);
v___x_2359_ = lean_usize_of_nat(v___x_2350_);
v___x_2360_ = ((size_t)1ULL);
v___x_2361_ = lean_usize_sub(v___x_2359_, v___x_2360_);
v___x_2362_ = lean_usize_land(v___x_2358_, v___x_2361_);
v___x_2363_ = lean_array_uget_borrowed(v_x_2342_, v___x_2362_);
lean_inc(v___x_2363_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 2, v___x_2363_);
v___x_2365_ = v___x_2348_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_key_2344_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_value_2345_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; 
v___x_2366_ = lean_array_uset(v_x_2342_, v___x_2362_, v___x_2365_);
v_x_2342_ = v___x_2366_;
v_x_2343_ = v_tail_2346_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2370_, lean_object* v_source_2371_, lean_object* v_target_2372_){
_start:
{
lean_object* v___x_2373_; uint8_t v___x_2374_; 
v___x_2373_ = lean_array_get_size(v_source_2371_);
v___x_2374_ = lean_nat_dec_lt(v_i_2370_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_dec_ref(v_source_2371_);
lean_dec(v_i_2370_);
return v_target_2372_;
}
else
{
lean_object* v_es_2375_; lean_object* v___x_2376_; lean_object* v_source_2377_; lean_object* v_target_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_es_2375_ = lean_array_fget(v_source_2371_, v_i_2370_);
v___x_2376_ = lean_box(0);
v_source_2377_ = lean_array_fset(v_source_2371_, v_i_2370_, v___x_2376_);
v_target_2378_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2372_, v_es_2375_);
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_nat_add(v_i_2370_, v___x_2379_);
lean_dec(v_i_2370_);
v_i_2370_ = v___x_2380_;
v_source_2371_ = v_source_2377_;
v_target_2372_ = v_target_2378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object* v_data_2382_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_nbuckets_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2383_ = lean_array_get_size(v_data_2382_);
v___x_2384_ = lean_unsigned_to_nat(2u);
v_nbuckets_2385_ = lean_nat_mul(v___x_2383_, v___x_2384_);
v___x_2386_ = lean_unsigned_to_nat(0u);
v___x_2387_ = lean_box(0);
v___x_2388_ = lean_mk_array(v_nbuckets_2385_, v___x_2387_);
v___x_2389_ = lean_array_propagate_mark(v_data_2382_, v___x_2388_);
v___x_2390_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v___x_2386_, v_data_2382_, v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object* v_a_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
uint8_t v___x_2393_; 
v___x_2393_ = 0;
return v___x_2393_;
}
else
{
lean_object* v_key_2394_; lean_object* v_tail_2395_; uint8_t v___x_2396_; 
v_key_2394_ = lean_ctor_get(v_x_2392_, 0);
v_tail_2395_ = lean_ctor_get(v_x_2392_, 2);
v___x_2396_ = l_Lean_Syntax_instBEqRange_beq(v_key_2394_, v_a_2391_);
if (v___x_2396_ == 0)
{
v_x_2392_ = v_tail_2395_;
goto _start;
}
else
{
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object* v_a_2398_, lean_object* v_x_2399_){
_start:
{
uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_res_2400_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2398_, v_x_2399_);
lean_dec(v_x_2399_);
lean_dec_ref(v_a_2398_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object* v_m_2402_, lean_object* v_a_2403_, lean_object* v_b_2404_){
_start:
{
lean_object* v_size_2405_; lean_object* v_buckets_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2449_; 
v_size_2405_ = lean_ctor_get(v_m_2402_, 0);
v_buckets_2406_ = lean_ctor_get(v_m_2402_, 1);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_m_2402_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2408_ = v_m_2402_;
v_isShared_2409_ = v_isSharedCheck_2449_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_buckets_2406_);
lean_inc(v_size_2405_);
lean_dec(v_m_2402_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2449_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; uint64_t v___x_2411_; uint64_t v___x_2412_; uint64_t v___x_2413_; uint64_t v_fold_2414_; uint64_t v___x_2415_; uint64_t v___x_2416_; uint64_t v___x_2417_; size_t v___x_2418_; size_t v___x_2419_; size_t v___x_2420_; size_t v___x_2421_; size_t v___x_2422_; lean_object* v_bkt_2423_; uint8_t v___x_2424_; 
v___x_2410_ = lean_array_get_size(v_buckets_2406_);
v___x_2411_ = l_Lean_Syntax_instHashableRange_hash(v_a_2403_);
v___x_2412_ = 32ULL;
v___x_2413_ = lean_uint64_shift_right(v___x_2411_, v___x_2412_);
v_fold_2414_ = lean_uint64_xor(v___x_2411_, v___x_2413_);
v___x_2415_ = 16ULL;
v___x_2416_ = lean_uint64_shift_right(v_fold_2414_, v___x_2415_);
v___x_2417_ = lean_uint64_xor(v_fold_2414_, v___x_2416_);
v___x_2418_ = lean_uint64_to_usize(v___x_2417_);
v___x_2419_ = lean_usize_of_nat(v___x_2410_);
v___x_2420_ = ((size_t)1ULL);
v___x_2421_ = lean_usize_sub(v___x_2419_, v___x_2420_);
v___x_2422_ = lean_usize_land(v___x_2418_, v___x_2421_);
v_bkt_2423_ = lean_array_uget_borrowed(v_buckets_2406_, v___x_2422_);
v___x_2424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2403_, v_bkt_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v_size_x27_2426_; lean_object* v___x_2427_; lean_object* v_buckets_x27_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2425_ = lean_unsigned_to_nat(1u);
v_size_x27_2426_ = lean_nat_add(v_size_2405_, v___x_2425_);
lean_dec(v_size_2405_);
lean_inc(v_bkt_2423_);
v___x_2427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2427_, 0, v_a_2403_);
lean_ctor_set(v___x_2427_, 1, v_b_2404_);
lean_ctor_set(v___x_2427_, 2, v_bkt_2423_);
v_buckets_x27_2428_ = lean_array_uset(v_buckets_2406_, v___x_2422_, v___x_2427_);
v___x_2429_ = lean_unsigned_to_nat(4u);
v___x_2430_ = lean_nat_mul(v_size_x27_2426_, v___x_2429_);
v___x_2431_ = lean_unsigned_to_nat(3u);
v___x_2432_ = lean_nat_div(v___x_2430_, v___x_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_array_get_size(v_buckets_x27_2428_);
v___x_2434_ = lean_nat_dec_le(v___x_2432_, v___x_2433_);
lean_dec(v___x_2432_);
if (v___x_2434_ == 0)
{
lean_object* v_val_2435_; lean_object* v___x_2437_; 
v_val_2435_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_buckets_x27_2428_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v_val_2435_);
lean_ctor_set(v___x_2408_, 0, v_size_x27_2426_);
v___x_2437_ = v___x_2408_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_size_x27_2426_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_val_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
else
{
lean_object* v___x_2440_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v_buckets_x27_2428_);
lean_ctor_set(v___x_2408_, 0, v_size_x27_2426_);
v___x_2440_ = v___x_2408_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_size_x27_2426_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_buckets_x27_2428_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
lean_object* v___x_2442_; lean_object* v_buckets_x27_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_inc(v_bkt_2423_);
v___x_2442_ = lean_box(0);
v_buckets_x27_2443_ = lean_array_uset(v_buckets_2406_, v___x_2422_, v___x_2442_);
v___x_2444_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2403_, v_b_2404_, v_bkt_2423_);
v___x_2445_ = lean_array_uset(v_buckets_x27_2443_, v___x_2422_, v___x_2444_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v___x_2445_);
v___x_2447_ = v___x_2408_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_size_2405_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object* v_f_2450_, lean_object* v_formatterName_2451_, lean_object* v_stx_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___y_2456_; lean_object* v_a_2468_; lean_object* v_a_2469_; lean_object* v___x_2504_; 
lean_inc_ref(v_a_2453_);
lean_inc(v_stx_2452_);
v___x_2504_ = lean_apply_3(v_f_2450_, v_stx_2452_, v_a_2453_, v_a_2454_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
v_a_2506_ = lean_ctor_get(v___x_2504_, 1);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2504_, 2);
v___x_2507_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_a_2505_, v_stx_2452_, v_a_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v_stx_2452_);
lean_dec(v_formatterName_2451_);
v_a_2508_ = lean_ctor_get(v___x_2507_, 1);
v_a_2509_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2511_ = v___x_2507_;
v_isShared_2512_ = v_isSharedCheck_2532_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2508_);
lean_inc(v_a_2509_);
lean_dec(v___x_2507_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2532_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v_toBacktrackableState_2513_; lean_object* v_shareCommonState_2514_; lean_object* v_freshTagId_2515_; lean_object* v_missingFormatters_2516_; lean_object* v_partialFormatters_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2531_; 
v_toBacktrackableState_2513_ = lean_ctor_get(v_a_2508_, 0);
v_shareCommonState_2514_ = lean_ctor_get(v_a_2508_, 1);
v_freshTagId_2515_ = lean_ctor_get(v_a_2508_, 2);
v_missingFormatters_2516_ = lean_ctor_get(v_a_2508_, 3);
v_partialFormatters_2517_ = lean_ctor_get(v_a_2508_, 4);
v_isSharedCheck_2531_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2519_ = v_a_2508_;
v_isShared_2520_ = v_isSharedCheck_2531_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_partialFormatters_2517_);
lean_inc(v_missingFormatters_2516_);
lean_inc(v_freshTagId_2515_);
lean_inc(v_shareCommonState_2514_);
lean_inc(v_toBacktrackableState_2513_);
lean_dec(v_a_2508_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2531_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v_fst_2523_; lean_object* v_snd_2524_; lean_object* v___x_2526_; 
v___x_2521_ = l_Lean_ShareCommon_objectFactory;
v___x_2522_ = lean_state_sharecommon(v___x_2521_, v_shareCommonState_2514_, v_a_2509_);
v_fst_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_fst_2523_);
v_snd_2524_ = lean_ctor_get(v___x_2522_, 1);
lean_inc(v_snd_2524_);
lean_dec_ref(v___x_2522_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 1, v_snd_2524_);
v___x_2526_ = v___x_2519_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_toBacktrackableState_2513_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_snd_2524_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_freshTagId_2515_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_missingFormatters_2516_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_partialFormatters_2517_);
v___x_2526_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 1, v___x_2526_);
lean_ctor_set(v___x_2511_, 0, v_fst_2523_);
v___x_2528_ = v___x_2511_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_fst_2523_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v_a_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2533_);
v_a_2534_ = lean_ctor_get(v___x_2507_, 1);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2507_, 2);
v_a_2468_ = v_a_2533_;
v_a_2469_ = v_a_2534_;
goto v___jp_2467_;
}
}
else
{
lean_object* v_a_2535_; lean_object* v_a_2536_; 
v_a_2535_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2535_);
v_a_2536_ = lean_ctor_get(v___x_2504_, 1);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2504_, 2);
v_a_2468_ = v_a_2535_;
v_a_2469_ = v_a_2536_;
goto v___jp_2467_;
}
v___jp_2455_:
{
lean_object* v_a_2457_; lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2466_; 
v_a_2457_ = lean_ctor_get(v___y_2456_, 0);
v_a_2458_ = lean_ctor_get(v___y_2456_, 1);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___y_2456_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2460_ = v___y_2456_;
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_inc(v_a_2457_);
lean_dec(v___y_2456_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_a_2462_; lean_object* v___x_2464_; 
v_a_2462_ = lean_ctor_get(v_a_2457_, 0);
lean_inc(v_a_2462_);
lean_dec(v_a_2457_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v_a_2462_);
v___x_2464_ = v___x_2460_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2462_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_a_2458_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
v___jp_2467_:
{
if (lean_obj_tag(v_a_2468_) == 0)
{
uint8_t v_err_2470_; 
v_err_2470_ = lean_ctor_get_uint8(v_a_2468_, 0);
if (v_err_2470_ == 0)
{
uint8_t v___x_2471_; lean_object* v___x_2472_; 
lean_dec_ref_known(v_a_2468_, 0);
v___x_2471_ = 1;
lean_inc(v_stx_2452_);
v___x_2472_ = l_Lean_Fmt_fmtRaw(v___x_2471_, v_stx_2452_, v_a_2453_, v_a_2469_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2501_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_a_2474_ = lean_ctor_get(v___x_2472_, 1);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2476_ = v___x_2472_;
v_isShared_2477_ = v_isSharedCheck_2501_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2501_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
uint8_t v___x_2478_; lean_object* v___x_2479_; 
v___x_2478_ = 0;
v___x_2479_ = l_Lean_Syntax_getRange_x3f(v_stx_2452_, v___x_2478_);
if (lean_obj_tag(v___x_2479_) == 1)
{
lean_object* v_val_2480_; lean_object* v_toBacktrackableState_2481_; lean_object* v_shareCommonState_2482_; lean_object* v_freshTagId_2483_; lean_object* v_missingFormatters_2484_; lean_object* v_partialFormatters_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2498_; 
v_val_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v___x_2479_, 1);
v_toBacktrackableState_2481_ = lean_ctor_get(v_a_2474_, 0);
v_shareCommonState_2482_ = lean_ctor_get(v_a_2474_, 1);
v_freshTagId_2483_ = lean_ctor_get(v_a_2474_, 2);
v_missingFormatters_2484_ = lean_ctor_get(v_a_2474_, 3);
v_partialFormatters_2485_ = lean_ctor_get(v_a_2474_, 4);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_a_2474_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2487_ = v_a_2474_;
v_isShared_2488_ = v_isSharedCheck_2498_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_partialFormatters_2485_);
lean_inc(v_missingFormatters_2484_);
lean_inc(v_freshTagId_2483_);
lean_inc(v_shareCommonState_2482_);
lean_inc(v_toBacktrackableState_2481_);
lean_dec(v_a_2474_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2498_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_box(0);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v_formatterName_2451_);
lean_ctor_set(v___x_2476_, 0, v_stx_2452_);
v___x_2491_ = v___x_2476_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_stx_2452_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_formatterName_2451_);
v___x_2491_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_partialFormatters_2485_, v_val_2480_, v___x_2491_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 4, v___x_2492_);
v___x_2494_ = v___x_2487_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_toBacktrackableState_2481_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_shareCommonState_2482_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_freshTagId_2483_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_missingFormatters_2484_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2473_, v___x_2489_, v_a_2453_, v___x_2494_);
v___y_2456_ = v___x_2495_;
goto v___jp_2455_;
}
}
}
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v___x_2479_);
lean_del_object(v___x_2476_);
lean_dec(v_stx_2452_);
lean_dec(v_formatterName_2451_);
v___x_2499_ = lean_box(0);
v___x_2500_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2473_, v___x_2499_, v_a_2453_, v_a_2474_);
v___y_2456_ = v___x_2500_;
goto v___jp_2455_;
}
}
}
else
{
lean_dec(v_stx_2452_);
lean_dec(v_formatterName_2451_);
return v___x_2472_;
}
}
else
{
lean_object* v___x_2502_; 
lean_dec(v_stx_2452_);
lean_dec(v_formatterName_2451_);
v___x_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_a_2468_);
lean_ctor_set(v___x_2502_, 1, v_a_2469_);
return v___x_2502_;
}
}
else
{
lean_object* v___x_2503_; 
lean_dec(v_stx_2452_);
lean_dec(v_formatterName_2451_);
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2468_);
lean_ctor_set(v___x_2503_, 1, v_a_2469_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object* v_f_2537_, lean_object* v_formatterName_2538_, lean_object* v_stx_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Fmt_fmtWith(v_f_2537_, v_formatterName_2538_, v_stx_2539_, v_a_2540_, v_a_2541_);
lean_dec_ref(v_a_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object* v_00_u03b2_2543_, lean_object* v_m_2544_, lean_object* v_a_2545_, lean_object* v_b_2546_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_m_2544_, v_a_2545_, v_b_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object* v_00_u03b2_2548_, lean_object* v_a_2549_, lean_object* v_x_2550_){
_start:
{
uint8_t v___x_2551_; 
v___x_2551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2549_, v_x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2552_, lean_object* v_a_2553_, lean_object* v_x_2554_){
_start:
{
uint8_t v_res_2555_; lean_object* v_r_2556_; 
v_res_2555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(v_00_u03b2_2552_, v_a_2553_, v_x_2554_);
lean_dec(v_x_2554_);
lean_dec_ref(v_a_2553_);
v_r_2556_ = lean_box(v_res_2555_);
return v_r_2556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object* v_00_u03b2_2557_, lean_object* v_data_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_data_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object* v_00_u03b2_2560_, lean_object* v_a_2561_, lean_object* v_b_2562_, lean_object* v_x_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2561_, v_b_2562_, v_x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2565_, lean_object* v_i_2566_, lean_object* v_source_2567_, lean_object* v_target_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v_i_2566_, v_source_2567_, v_target_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2571_, v_x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object* v_a_2577_, lean_object* v_kind_2578_, lean_object* v_as_2579_, size_t v_sz_2580_, size_t v_i_2581_, lean_object* v_b_2582_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_usize_dec_lt(v_i_2581_, v_sz_2580_);
if (v___x_2583_ == 0)
{
lean_dec(v_kind_2578_);
lean_inc_ref(v_b_2582_);
return v_b_2582_;
}
else
{
lean_object* v_a_2584_; lean_object* v_provider_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2601_; 
v_a_2584_ = lean_array_uget(v_as_2579_, v_i_2581_);
v_provider_2585_ = lean_ctor_get(v_a_2584_, 1);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_a_2584_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v_a_2584_, 0);
lean_dec(v_unused_2602_);
v___x_2587_ = v_a_2584_;
v_isShared_2588_ = v_isSharedCheck_2601_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_provider_2585_);
lean_dec(v_a_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2601_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v_env_2589_; lean_object* v_opts_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_env_2589_ = lean_ctor_get(v_a_2577_, 0);
v_opts_2590_ = lean_ctor_get(v_a_2577_, 3);
v___x_2591_ = lean_box(0);
lean_inc(v_kind_2578_);
lean_inc_ref(v_opts_2590_);
lean_inc_ref(v_env_2589_);
v___x_2592_ = lean_apply_3(v_provider_2585_, v_env_2589_, v_opts_2590_, v_kind_2578_);
if (lean_obj_tag(v___x_2592_) == 1)
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_kind_2578_);
v___x_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 1, v___x_2591_);
lean_ctor_set(v___x_2587_, 0, v___x_2593_);
v___x_2595_ = v___x_2587_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v___x_2591_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
else
{
lean_object* v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; 
lean_dec(v___x_2592_);
lean_del_object(v___x_2587_);
v___x_2597_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v___x_2598_ = ((size_t)1ULL);
v___x_2599_ = lean_usize_add(v_i_2581_, v___x_2598_);
v_i_2581_ = v___x_2599_;
v_b_2582_ = v___x_2597_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object* v_a_2603_, lean_object* v_kind_2604_, lean_object* v_as_2605_, lean_object* v_sz_2606_, lean_object* v_i_2607_, lean_object* v_b_2608_){
_start:
{
size_t v_sz_boxed_2609_; size_t v_i_boxed_2610_; lean_object* v_res_2611_; 
v_sz_boxed_2609_ = lean_unbox_usize(v_sz_2606_);
lean_dec(v_sz_2606_);
v_i_boxed_2610_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2603_, v_kind_2604_, v_as_2605_, v_sz_boxed_2609_, v_i_boxed_2610_, v_b_2608_);
lean_dec_ref(v_b_2608_);
lean_dec_ref(v_as_2605_);
lean_dec_ref(v_a_2603_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object* v_kind_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_){
_start:
{
lean_object* v_env_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; size_t v_sz_2619_; size_t v___x_2620_; lean_object* v___x_2621_; lean_object* v_fst_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2633_; 
v_env_2615_ = lean_ctor_get(v_a_2613_, 0);
lean_inc_ref(v_env_2615_);
v___x_2616_ = l_Lean_Fmt_getFmtProviders(v_env_2615_);
v___x_2617_ = lean_box(0);
v___x_2618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v_sz_2619_ = lean_array_size(v___x_2616_);
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2613_, v_kind_2612_, v___x_2616_, v_sz_2619_, v___x_2620_, v___x_2618_);
lean_dec_ref(v___x_2616_);
v_fst_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; 
v_unused_2634_ = lean_ctor_get(v___x_2621_, 1);
lean_dec(v_unused_2634_);
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_fst_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2633_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
if (lean_obj_tag(v_fst_2622_) == 0)
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v_a_2614_);
lean_ctor_set(v___x_2624_, 0, v___x_2617_);
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_a_2614_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
else
{
lean_object* v_val_2629_; lean_object* v___x_2631_; 
v_val_2629_ = lean_ctor_get(v_fst_2622_, 0);
lean_inc(v_val_2629_);
lean_dec_ref_known(v_fst_2622_, 1);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v_a_2614_);
lean_ctor_set(v___x_2624_, 0, v_val_2629_);
v___x_2631_ = v___x_2624_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_val_2629_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_a_2614_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object* v_kind_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2635_, v_a_2636_, v_a_2637_);
lean_dec_ref(v_a_2636_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object* v_stx_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
switch(lean_obj_tag(v_stx_2639_))
{
case 0:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
lean_ctor_set(v___x_2643_, 1, v_a_2641_);
return v___x_2643_;
}
case 1:
{
lean_object* v_kind_2644_; lean_object* v___x_2645_; lean_object* v_a_2646_; 
lean_inc_ref(v_stx_2639_);
v_kind_2644_ = l_Lean_Syntax_getKind(v_stx_2639_);
lean_inc(v_kind_2644_);
v___x_2645_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2644_, v_a_2640_, v_a_2641_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
if (lean_obj_tag(v_a_2646_) == 1)
{
lean_object* v_val_2647_; lean_object* v_a_2648_; lean_object* v_fst_2649_; lean_object* v_snd_2650_; lean_object* v___x_2651_; 
lean_dec(v_kind_2644_);
v_val_2647_ = lean_ctor_get(v_a_2646_, 0);
lean_inc(v_val_2647_);
v_a_2648_ = lean_ctor_get(v___x_2645_, 1);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2645_);
v_fst_2649_ = lean_ctor_get(v_val_2647_, 0);
lean_inc(v_fst_2649_);
v_snd_2650_ = lean_ctor_get(v_val_2647_, 1);
lean_inc(v_snd_2650_);
lean_dec(v_val_2647_);
v___x_2651_ = l_Lean_Fmt_fmtWith(v_snd_2650_, v_fst_2649_, v_stx_2639_, v_a_2640_, v_a_2648_);
return v___x_2651_;
}
else
{
lean_object* v_a_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; 
v_a_2652_ = lean_ctor_get(v___x_2645_, 1);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2645_);
v___x_2653_ = 1;
lean_inc_ref(v_stx_2639_);
v___x_2654_ = l_Lean_Fmt_fmtRaw(v___x_2653_, v_stx_2639_, v_a_2640_, v_a_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_a_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_a_2656_ = lean_ctor_get(v___x_2654_, 1);
lean_inc(v_a_2656_);
v___x_2657_ = 0;
v___x_2658_ = l_Lean_Syntax_getRange_x3f(v_stx_2639_, v___x_2657_);
lean_dec_ref_known(v_stx_2639_, 3);
if (lean_obj_tag(v___x_2658_) == 1)
{
lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2679_; 
lean_inc(v_a_2655_);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2680_ = lean_ctor_get(v___x_2654_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v___x_2654_, 0);
lean_dec(v_unused_2681_);
v___x_2660_ = v___x_2654_;
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
else
{
lean_dec(v___x_2654_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_val_2662_; lean_object* v_toBacktrackableState_2663_; lean_object* v_shareCommonState_2664_; lean_object* v_freshTagId_2665_; lean_object* v_missingFormatters_2666_; lean_object* v_partialFormatters_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2678_; 
v_val_2662_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v___x_2658_, 1);
v_toBacktrackableState_2663_ = lean_ctor_get(v_a_2656_, 0);
v_shareCommonState_2664_ = lean_ctor_get(v_a_2656_, 1);
v_freshTagId_2665_ = lean_ctor_get(v_a_2656_, 2);
v_missingFormatters_2666_ = lean_ctor_get(v_a_2656_, 3);
v_partialFormatters_2667_ = lean_ctor_get(v_a_2656_, 4);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_a_2656_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2669_ = v_a_2656_;
v_isShared_2670_ = v_isSharedCheck_2678_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_partialFormatters_2667_);
lean_inc(v_missingFormatters_2666_);
lean_inc(v_freshTagId_2665_);
lean_inc(v_shareCommonState_2664_);
lean_inc(v_toBacktrackableState_2663_);
lean_dec(v_a_2656_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2678_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2671_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingFormatters_2666_, v_val_2662_, v_kind_2644_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 3, v___x_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_toBacktrackableState_2663_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_shareCommonState_2664_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_freshTagId_2665_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2677_, 4, v_partialFormatters_2667_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2673_);
v___x_2675_ = v___x_2660_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2655_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
else
{
lean_dec(v___x_2658_);
lean_dec(v_a_2656_);
lean_dec(v_kind_2644_);
return v___x_2654_;
}
}
else
{
lean_dec(v_kind_2644_);
lean_dec_ref_known(v_stx_2639_, 3);
return v___x_2654_;
}
}
}
case 2:
{
lean_object* v_val_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v_valDocs_2688_; lean_object* v___x_2689_; lean_object* v_valDoc_2690_; lean_object* v___x_2691_; 
v_val_2682_ = lean_ctor_get(v_stx_2639_, 1);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_string_utf8_byte_size(v_val_2682_);
lean_inc_ref_n(v_val_2682_, 2);
v___x_2685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2685_, 0, v_val_2682_);
lean_ctor_set(v___x_2685_, 1, v___x_2683_);
lean_ctor_set(v___x_2685_, 2, v___x_2684_);
v___x_2686_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_2687_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2688_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_val_2682_, v___x_2685_, v___x_2684_, v___x_2686_, v___x_2687_);
lean_dec_ref_known(v___x_2685_, 3);
v___x_2689_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2690_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2689_, v_valDocs_2688_);
v___x_2691_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2690_, v_stx_2639_, v_a_2641_);
lean_dec_ref_known(v_stx_2639_, 2);
return v___x_2691_;
}
default: 
{
lean_object* v_rawVal_2692_; lean_object* v_str_2693_; lean_object* v_startPos_2694_; lean_object* v_stopPos_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2711_; 
v_rawVal_2692_ = lean_ctor_get(v_stx_2639_, 1);
lean_inc_ref(v_rawVal_2692_);
v_str_2693_ = lean_ctor_get(v_rawVal_2692_, 0);
v_startPos_2694_ = lean_ctor_get(v_rawVal_2692_, 1);
v_stopPos_2695_ = lean_ctor_get(v_rawVal_2692_, 2);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_rawVal_2692_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2697_ = v_rawVal_2692_;
v_isShared_2698_ = v_isSharedCheck_2711_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_stopPos_2695_);
lean_inc(v_startPos_2694_);
lean_inc(v_str_2693_);
lean_dec(v_rawVal_2692_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2711_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2699_ = lean_string_utf8_extract(v_str_2693_, v_startPos_2694_, v_stopPos_2695_);
lean_dec(v_stopPos_2695_);
lean_dec(v_startPos_2694_);
lean_dec_ref(v_str_2693_);
v___x_2700_ = lean_unsigned_to_nat(0u);
v___x_2701_ = lean_string_utf8_byte_size(v___x_2699_);
lean_inc_ref(v___x_2699_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 2, v___x_2701_);
lean_ctor_set(v___x_2697_, 1, v___x_2700_);
lean_ctor_set(v___x_2697_, 0, v___x_2699_);
v___x_2703_ = v___x_2697_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v_valDocs_2706_; lean_object* v___x_2707_; lean_object* v_valDoc_2708_; lean_object* v___x_2709_; 
v___x_2704_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_2705_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2706_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_2699_, v___x_2703_, v___x_2701_, v___x_2704_, v___x_2705_);
lean_dec_ref(v___x_2703_);
v___x_2707_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2708_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2707_, v_valDocs_2706_);
v___x_2709_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2708_, v_stx_2639_, v_a_2641_);
lean_dec_ref_known(v_stx_2639_, 4);
return v___x_2709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object* v_stx_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_Fmt_fmt(v_stx_2712_, v_a_2713_, v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
uint8_t v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = 0;
v___x_2721_ = l_Lean_Syntax_getRange_x3f(v_a_2717_, v___x_2720_);
if (lean_obj_tag(v___x_2721_) == 1)
{
lean_object* v_val_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2787_; 
v_val_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2787_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_val_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2787_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_resolveChoiceNode_2726_; lean_object* v___x_2727_; 
v_resolveChoiceNode_2726_ = lean_ctor_get(v_a_2718_, 2);
lean_inc_ref(v_resolveChoiceNode_2726_);
v___x_2727_ = lean_apply_1(v_resolveChoiceNode_2726_, v_val_2722_);
if (lean_obj_tag(v___x_2727_) == 1)
{
lean_object* v_val_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2774_; 
lean_del_object(v___x_2724_);
v_val_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2774_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_val_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2774_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_stx_2732_; lean_object* v_chosenAltIdx_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2773_; 
v_stx_2732_ = lean_ctor_get(v_val_2728_, 0);
v_chosenAltIdx_2733_ = lean_ctor_get(v_val_2728_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_val_2728_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2735_ = v_val_2728_;
v_isShared_2736_ = v_isSharedCheck_2773_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_chosenAltIdx_2733_);
lean_inc(v_stx_2732_);
lean_dec(v_val_2728_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2773_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2737_ = l_Lean_Syntax_getNumArgs(v_stx_2732_);
lean_dec(v_stx_2732_);
v___x_2738_ = l_Lean_Syntax_getNumArgs(v_a_2717_);
v___x_2739_ = lean_nat_dec_eq(v___x_2737_, v___x_2738_);
lean_dec(v___x_2738_);
lean_dec(v___x_2737_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_dec(v_chosenAltIdx_2733_);
v___x_2740_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2741_ = lean_box(0);
lean_inc(v_a_2717_);
v___x_2742_ = l_Lean_Syntax_formatStx(v_a_2717_, v___x_2741_, v___x_2739_);
v___x_2743_ = l_Std_Format_defWidth;
v___x_2744_ = lean_unsigned_to_nat(0u);
v___x_2745_ = l_Std_Format_pretty(v___x_2742_, v___x_2743_, v___x_2744_, v___x_2744_);
v___x_2746_ = lean_string_append(v___x_2740_, v___x_2745_);
lean_dec_ref(v___x_2745_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 1);
lean_ctor_set(v___x_2735_, 1, v___x_2746_);
lean_ctor_set(v___x_2735_, 0, v_a_2717_);
v___x_2748_ = v___x_2735_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2717_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2750_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 2);
lean_ctor_set(v___x_2730_, 0, v___x_2748_);
v___x_2750_ = v___x_2730_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
lean_ctor_set(v___x_2751_, 1, v_a_2719_);
return v___x_2751_;
}
}
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2754_ = l_Lean_Syntax_getArgs(v_a_2717_);
v___x_2755_ = lean_array_get_size(v___x_2754_);
v___x_2756_ = lean_nat_dec_lt(v_chosenAltIdx_2733_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
lean_dec_ref(v___x_2754_);
lean_dec(v_chosenAltIdx_2733_);
v___x_2757_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2758_ = lean_box(0);
lean_inc(v_a_2717_);
v___x_2759_ = l_Lean_Syntax_formatStx(v_a_2717_, v___x_2758_, v___x_2756_);
v___x_2760_ = l_Std_Format_defWidth;
v___x_2761_ = lean_unsigned_to_nat(0u);
v___x_2762_ = l_Std_Format_pretty(v___x_2759_, v___x_2760_, v___x_2761_, v___x_2761_);
v___x_2763_ = lean_string_append(v___x_2757_, v___x_2762_);
lean_dec_ref(v___x_2762_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set_tag(v___x_2735_, 1);
lean_ctor_set(v___x_2735_, 1, v___x_2763_);
lean_ctor_set(v___x_2735_, 0, v_a_2717_);
v___x_2765_ = v___x_2735_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2717_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2767_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 2);
lean_ctor_set(v___x_2730_, 0, v___x_2765_);
v___x_2767_ = v___x_2730_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v_a_2719_);
return v___x_2768_;
}
}
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_del_object(v___x_2735_);
lean_del_object(v___x_2730_);
lean_dec(v_a_2717_);
v___x_2771_ = lean_array_fget(v___x_2754_, v_chosenAltIdx_2733_);
lean_dec(v_chosenAltIdx_2733_);
lean_dec_ref(v___x_2754_);
v___x_2772_ = l_Lean_Fmt_fmt(v___x_2771_, v_a_2718_, v_a_2719_);
return v___x_2772_;
}
}
}
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
lean_dec(v___x_2727_);
v___x_2775_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2776_ = lean_box(0);
lean_inc(v_a_2717_);
v___x_2777_ = l_Lean_Syntax_formatStx(v_a_2717_, v___x_2776_, v___x_2720_);
v___x_2778_ = l_Std_Format_defWidth;
v___x_2779_ = lean_unsigned_to_nat(0u);
v___x_2780_ = l_Std_Format_pretty(v___x_2777_, v___x_2778_, v___x_2779_, v___x_2779_);
v___x_2781_ = lean_string_append(v___x_2775_, v___x_2780_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_a_2717_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set_tag(v___x_2724_, 2);
lean_ctor_set(v___x_2724_, 0, v___x_2782_);
v___x_2784_ = v___x_2724_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v_a_2719_);
return v___x_2785_;
}
}
}
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_dec(v___x_2721_);
v___x_2788_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2789_ = lean_box(0);
lean_inc(v_a_2717_);
v___x_2790_ = l_Lean_Syntax_formatStx(v_a_2717_, v___x_2789_, v___x_2720_);
v___x_2791_ = l_Std_Format_defWidth;
v___x_2792_ = lean_unsigned_to_nat(0u);
v___x_2793_ = l_Std_Format_pretty(v___x_2790_, v___x_2791_, v___x_2792_, v___x_2792_);
v___x_2794_ = lean_string_append(v___x_2788_, v___x_2793_);
lean_dec_ref(v___x_2793_);
v___x_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2795_, 0, v_a_2717_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v_a_2719_);
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___boxed(lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec_ref(v_a_2799_);
return v_res_2801_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = l_Lean_Fmt_instInhabitedState_default;
v___x_2803_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v___x_2802_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object* v_msg_2805_){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_obj_once(&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0, &l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0);
v___x_2807_ = lean_panic_fn_borrowed(v___x_2806_, v_msg_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2808_){
_start:
{
lean_object* v_aPtr_2809_; lean_object* v_bPtr_2810_; size_t v_ptr_2811_; size_t v_ptr_2812_; uint64_t v___x_2813_; uint64_t v___x_2814_; uint64_t v___x_2815_; uint64_t v___x_2816_; uint64_t v___x_2817_; 
v_aPtr_2809_ = lean_ctor_get(v_x_2808_, 0);
v_bPtr_2810_ = lean_ctor_get(v_x_2808_, 1);
v_ptr_2811_ = lean_ctor_get_usize(v_aPtr_2809_, 1);
v_ptr_2812_ = lean_ctor_get_usize(v_bPtr_2810_, 1);
v___x_2813_ = 0ULL;
v___x_2814_ = lean_usize_to_uint64(v_ptr_2811_);
v___x_2815_ = lean_uint64_mix_hash(v___x_2813_, v___x_2814_);
v___x_2816_ = lean_usize_to_uint64(v_ptr_2812_);
v___x_2817_ = lean_uint64_mix_hash(v___x_2815_, v___x_2816_);
return v___x_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2818_){
_start:
{
uint64_t v_res_2819_; lean_object* v_r_2820_; 
v_res_2819_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_x_2818_);
lean_dec_ref(v_x_2818_);
v_r_2820_ = lean_box_uint64(v_res_2819_);
return v_r_2820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_x_2821_, lean_object* v_x_2822_){
_start:
{
lean_object* v_aPtr_2823_; lean_object* v_aPtr_2824_; lean_object* v_bPtr_2825_; lean_object* v_bPtr_2826_; size_t v_ptr_2827_; size_t v_ptr_2828_; uint8_t v___x_2829_; 
v_aPtr_2823_ = lean_ctor_get(v_x_2821_, 0);
v_aPtr_2824_ = lean_ctor_get(v_x_2822_, 0);
v_bPtr_2825_ = lean_ctor_get(v_x_2821_, 1);
v_bPtr_2826_ = lean_ctor_get(v_x_2822_, 1);
v_ptr_2827_ = lean_ctor_get_usize(v_aPtr_2823_, 1);
v_ptr_2828_ = lean_ctor_get_usize(v_aPtr_2824_, 1);
v___x_2829_ = lean_usize_dec_eq(v_ptr_2827_, v_ptr_2828_);
if (v___x_2829_ == 0)
{
return v___x_2829_;
}
else
{
size_t v_ptr_2830_; size_t v_ptr_2831_; uint8_t v___x_2832_; 
v_ptr_2830_ = lean_ctor_get_usize(v_bPtr_2825_, 1);
v_ptr_2831_ = lean_ctor_get_usize(v_bPtr_2826_, 1);
v___x_2832_ = lean_usize_dec_eq(v_ptr_2830_, v_ptr_2831_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_x_2833_, lean_object* v_x_2834_){
_start:
{
uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_res_2835_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_x_2833_, v_x_2834_);
lean_dec_ref(v_x_2834_);
lean_dec_ref(v_x_2833_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2837_, lean_object* v_x_2838_){
_start:
{
if (lean_obj_tag(v_x_2838_) == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_box(0);
return v___x_2839_;
}
else
{
lean_object* v_key_2840_; lean_object* v_value_2841_; lean_object* v_tail_2842_; uint8_t v___x_2843_; 
v_key_2840_ = lean_ctor_get(v_x_2838_, 0);
v_value_2841_ = lean_ctor_get(v_x_2838_, 1);
v_tail_2842_ = lean_ctor_get(v_x_2838_, 2);
v___x_2843_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2840_, v_a_2837_);
if (v___x_2843_ == 0)
{
v_x_2838_ = v_tail_2842_;
goto _start;
}
else
{
lean_object* v___x_2845_; 
lean_inc(v_value_2841_);
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_value_2841_);
return v___x_2845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2846_, lean_object* v_x_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2846_, v_x_2847_);
lean_dec(v_x_2847_);
lean_dec_ref(v_a_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(lean_object* v_m_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_buckets_2851_; lean_object* v___x_2852_; uint64_t v___x_2853_; uint64_t v___x_2854_; uint64_t v___x_2855_; uint64_t v_fold_2856_; uint64_t v___x_2857_; uint64_t v___x_2858_; uint64_t v___x_2859_; size_t v___x_2860_; size_t v___x_2861_; size_t v___x_2862_; size_t v___x_2863_; size_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_buckets_2851_ = lean_ctor_get(v_m_2849_, 1);
v___x_2852_ = lean_array_get_size(v_buckets_2851_);
v___x_2853_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2850_);
v___x_2854_ = 32ULL;
v___x_2855_ = lean_uint64_shift_right(v___x_2853_, v___x_2854_);
v_fold_2856_ = lean_uint64_xor(v___x_2853_, v___x_2855_);
v___x_2857_ = 16ULL;
v___x_2858_ = lean_uint64_shift_right(v_fold_2856_, v___x_2857_);
v___x_2859_ = lean_uint64_xor(v_fold_2856_, v___x_2858_);
v___x_2860_ = lean_uint64_to_usize(v___x_2859_);
v___x_2861_ = lean_usize_of_nat(v___x_2852_);
v___x_2862_ = ((size_t)1ULL);
v___x_2863_ = lean_usize_sub(v___x_2861_, v___x_2862_);
v___x_2864_ = lean_usize_land(v___x_2860_, v___x_2863_);
v___x_2865_ = lean_array_uget_borrowed(v_buckets_2851_, v___x_2864_);
v___x_2866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2850_, v___x_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_2867_, v_a_2868_);
lean_dec_ref(v_a_2868_);
lean_dec_ref(v_m_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(lean_object* v_x_2870_, lean_object* v_x_2871_){
_start:
{
if (lean_obj_tag(v_x_2871_) == 0)
{
return v_x_2870_;
}
else
{
lean_object* v_key_2872_; lean_object* v_value_2873_; lean_object* v_tail_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2897_; 
v_key_2872_ = lean_ctor_get(v_x_2871_, 0);
v_value_2873_ = lean_ctor_get(v_x_2871_, 1);
v_tail_2874_ = lean_ctor_get(v_x_2871_, 2);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_x_2871_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2876_ = v_x_2871_;
v_isShared_2877_ = v_isSharedCheck_2897_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_tail_2874_);
lean_inc(v_value_2873_);
lean_inc(v_key_2872_);
lean_dec(v_x_2871_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2897_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2878_; uint64_t v___x_2879_; uint64_t v___x_2880_; uint64_t v___x_2881_; uint64_t v_fold_2882_; uint64_t v___x_2883_; uint64_t v___x_2884_; uint64_t v___x_2885_; size_t v___x_2886_; size_t v___x_2887_; size_t v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2878_ = lean_array_get_size(v_x_2870_);
v___x_2879_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_key_2872_);
v___x_2880_ = 32ULL;
v___x_2881_ = lean_uint64_shift_right(v___x_2879_, v___x_2880_);
v_fold_2882_ = lean_uint64_xor(v___x_2879_, v___x_2881_);
v___x_2883_ = 16ULL;
v___x_2884_ = lean_uint64_shift_right(v_fold_2882_, v___x_2883_);
v___x_2885_ = lean_uint64_xor(v_fold_2882_, v___x_2884_);
v___x_2886_ = lean_uint64_to_usize(v___x_2885_);
v___x_2887_ = lean_usize_of_nat(v___x_2878_);
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_sub(v___x_2887_, v___x_2888_);
v___x_2890_ = lean_usize_land(v___x_2886_, v___x_2889_);
v___x_2891_ = lean_array_uget_borrowed(v_x_2870_, v___x_2890_);
lean_inc(v___x_2891_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 2, v___x_2891_);
v___x_2893_ = v___x_2876_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_key_2872_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_value_2873_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v___x_2891_);
v___x_2893_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; 
v___x_2894_ = lean_array_uset(v_x_2870_, v___x_2890_, v___x_2893_);
v_x_2870_ = v___x_2894_;
v_x_2871_ = v_tail_2874_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(lean_object* v_i_2898_, lean_object* v_source_2899_, lean_object* v_target_2900_){
_start:
{
lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = lean_array_get_size(v_source_2899_);
v___x_2902_ = lean_nat_dec_lt(v_i_2898_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_dec_ref(v_source_2899_);
lean_dec(v_i_2898_);
return v_target_2900_;
}
else
{
lean_object* v_es_2903_; lean_object* v___x_2904_; lean_object* v_source_2905_; lean_object* v_target_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_es_2903_ = lean_array_fget(v_source_2899_, v_i_2898_);
v___x_2904_ = lean_box(0);
v_source_2905_ = lean_array_fset(v_source_2899_, v_i_2898_, v___x_2904_);
v_target_2906_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_target_2900_, v_es_2903_);
v___x_2907_ = lean_unsigned_to_nat(1u);
v___x_2908_ = lean_nat_add(v_i_2898_, v___x_2907_);
lean_dec(v_i_2898_);
v_i_2898_ = v___x_2908_;
v_source_2899_ = v_source_2905_;
v_target_2900_ = v_target_2906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(lean_object* v_data_2910_){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_nbuckets_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2911_ = lean_array_get_size(v_data_2910_);
v___x_2912_ = lean_unsigned_to_nat(2u);
v_nbuckets_2913_ = lean_nat_mul(v___x_2911_, v___x_2912_);
v___x_2914_ = lean_unsigned_to_nat(0u);
v___x_2915_ = lean_box(0);
v___x_2916_ = lean_mk_array(v_nbuckets_2913_, v___x_2915_);
v___x_2917_ = lean_array_propagate_mark(v_data_2910_, v___x_2916_);
v___x_2918_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v___x_2914_, v_data_2910_, v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(lean_object* v_a_2919_, lean_object* v_x_2920_){
_start:
{
if (lean_obj_tag(v_x_2920_) == 0)
{
uint8_t v___x_2921_; 
v___x_2921_ = 0;
return v___x_2921_;
}
else
{
lean_object* v_key_2922_; lean_object* v_tail_2923_; uint8_t v___x_2924_; 
v_key_2922_ = lean_ctor_get(v_x_2920_, 0);
v_tail_2923_ = lean_ctor_get(v_x_2920_, 2);
v___x_2924_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2922_, v_a_2919_);
if (v___x_2924_ == 0)
{
v_x_2920_ = v_tail_2923_;
goto _start;
}
else
{
return v___x_2924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_a_2926_, lean_object* v_x_2927_){
_start:
{
uint8_t v_res_2928_; lean_object* v_r_2929_; 
v_res_2928_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2926_, v_x_2927_);
lean_dec(v_x_2927_);
lean_dec_ref(v_a_2926_);
v_r_2929_ = lean_box(v_res_2928_);
return v_r_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_a_2930_, lean_object* v_b_2931_, lean_object* v_x_2932_){
_start:
{
if (lean_obj_tag(v_x_2932_) == 0)
{
lean_dec(v_b_2931_);
lean_dec_ref(v_a_2930_);
return v_x_2932_;
}
else
{
lean_object* v_key_2933_; lean_object* v_value_2934_; lean_object* v_tail_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2947_; 
v_key_2933_ = lean_ctor_get(v_x_2932_, 0);
v_value_2934_ = lean_ctor_get(v_x_2932_, 1);
v_tail_2935_ = lean_ctor_get(v_x_2932_, 2);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_x_2932_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2937_ = v_x_2932_;
v_isShared_2938_ = v_isSharedCheck_2947_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_tail_2935_);
lean_inc(v_value_2934_);
lean_inc(v_key_2933_);
lean_dec(v_x_2932_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2947_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
uint8_t v___x_2939_; 
v___x_2939_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2933_, v_a_2930_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2930_, v_b_2931_, v_tail_2935_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 2, v___x_2940_);
v___x_2942_ = v___x_2937_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_key_2933_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_value_2934_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
else
{
lean_object* v___x_2945_; 
lean_dec(v_value_2934_);
lean_dec(v_key_2933_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v_b_2931_);
lean_ctor_set(v___x_2937_, 0, v_a_2930_);
v___x_2945_ = v___x_2937_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2930_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_b_2931_);
lean_ctor_set(v_reuseFailAlloc_2946_, 2, v_tail_2935_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(lean_object* v_m_2948_, lean_object* v_a_2949_, lean_object* v_b_2950_){
_start:
{
lean_object* v_size_2951_; lean_object* v_buckets_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2995_; 
v_size_2951_ = lean_ctor_get(v_m_2948_, 0);
v_buckets_2952_ = lean_ctor_get(v_m_2948_, 1);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_m_2948_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2954_ = v_m_2948_;
v_isShared_2955_ = v_isSharedCheck_2995_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_buckets_2952_);
lean_inc(v_size_2951_);
lean_dec(v_m_2948_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2995_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; uint64_t v___x_2957_; uint64_t v___x_2958_; uint64_t v___x_2959_; uint64_t v_fold_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; uint64_t v___x_2963_; size_t v___x_2964_; size_t v___x_2965_; size_t v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; lean_object* v_bkt_2969_; uint8_t v___x_2970_; 
v___x_2956_ = lean_array_get_size(v_buckets_2952_);
v___x_2957_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2949_);
v___x_2958_ = 32ULL;
v___x_2959_ = lean_uint64_shift_right(v___x_2957_, v___x_2958_);
v_fold_2960_ = lean_uint64_xor(v___x_2957_, v___x_2959_);
v___x_2961_ = 16ULL;
v___x_2962_ = lean_uint64_shift_right(v_fold_2960_, v___x_2961_);
v___x_2963_ = lean_uint64_xor(v_fold_2960_, v___x_2962_);
v___x_2964_ = lean_uint64_to_usize(v___x_2963_);
v___x_2965_ = lean_usize_of_nat(v___x_2956_);
v___x_2966_ = ((size_t)1ULL);
v___x_2967_ = lean_usize_sub(v___x_2965_, v___x_2966_);
v___x_2968_ = lean_usize_land(v___x_2964_, v___x_2967_);
v_bkt_2969_ = lean_array_uget_borrowed(v_buckets_2952_, v___x_2968_);
v___x_2970_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2949_, v_bkt_2969_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v_size_x27_2972_; lean_object* v___x_2973_; lean_object* v_buckets_x27_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2971_ = lean_unsigned_to_nat(1u);
v_size_x27_2972_ = lean_nat_add(v_size_2951_, v___x_2971_);
lean_dec(v_size_2951_);
lean_inc(v_bkt_2969_);
v___x_2973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2973_, 0, v_a_2949_);
lean_ctor_set(v___x_2973_, 1, v_b_2950_);
lean_ctor_set(v___x_2973_, 2, v_bkt_2969_);
v_buckets_x27_2974_ = lean_array_uset(v_buckets_2952_, v___x_2968_, v___x_2973_);
v___x_2975_ = lean_unsigned_to_nat(4u);
v___x_2976_ = lean_nat_mul(v_size_x27_2972_, v___x_2975_);
v___x_2977_ = lean_unsigned_to_nat(3u);
v___x_2978_ = lean_nat_div(v___x_2976_, v___x_2977_);
lean_dec(v___x_2976_);
v___x_2979_ = lean_array_get_size(v_buckets_x27_2974_);
v___x_2980_ = lean_nat_dec_le(v___x_2978_, v___x_2979_);
lean_dec(v___x_2978_);
if (v___x_2980_ == 0)
{
lean_object* v_val_2981_; lean_object* v___x_2983_; 
v_val_2981_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_buckets_x27_2974_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v_val_2981_);
lean_ctor_set(v___x_2954_, 0, v_size_x27_2972_);
v___x_2983_ = v___x_2954_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_size_x27_2972_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_val_2981_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
else
{
lean_object* v___x_2986_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v_buckets_x27_2974_);
lean_ctor_set(v___x_2954_, 0, v_size_x27_2972_);
v___x_2986_ = v___x_2954_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_size_x27_2972_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_buckets_x27_2974_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
else
{
lean_object* v___x_2988_; lean_object* v_buckets_x27_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
lean_inc(v_bkt_2969_);
v___x_2988_ = lean_box(0);
v_buckets_x27_2989_ = lean_array_uset(v_buckets_2952_, v___x_2968_, v___x_2988_);
v___x_2990_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2949_, v_b_2950_, v_bkt_2969_);
v___x_2991_ = lean_array_uset(v_buckets_x27_2989_, v___x_2968_, v___x_2990_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2991_);
v___x_2993_ = v___x_2954_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_size_2951_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object* v_a_2996_, lean_object* v_b_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v___y_3000_; lean_object* v_da1_3005_; lean_object* v_da2_3006_; lean_object* v_db1_3007_; lean_object* v_db2_3008_; lean_object* v___y_3009_; lean_object* v_sa_3016_; lean_object* v_sb_3017_; lean_object* v___y_3018_; 
switch(lean_obj_tag(v_a_2996_))
{
case 0:
{
if (lean_obj_tag(v_b_2997_) == 0)
{
uint8_t v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = 1;
v___x_3027_ = lean_box(v___x_3026_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
lean_ctor_set(v___x_3028_, 1, v_a_2998_);
return v___x_3028_;
}
else
{
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 1:
{
if (lean_obj_tag(v_b_2997_) == 1)
{
lean_object* v_f_3029_; lean_object* v_f_3030_; 
v_f_3029_ = lean_ctor_get(v_a_2996_, 1);
lean_inc_ref(v_f_3029_);
lean_dec_ref_known(v_a_2996_, 2);
v_f_3030_ = lean_ctor_get(v_b_2997_, 1);
lean_inc_ref(v_f_3030_);
lean_dec_ref_known(v_b_2997_, 2);
v_sa_3016_ = v_f_3029_;
v_sb_3017_ = v_f_3030_;
v___y_3018_ = v_a_2998_;
goto v___jp_3015_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 2:
{
if (lean_obj_tag(v_b_2997_) == 2)
{
lean_object* v_s_3031_; lean_object* v_s_3032_; 
v_s_3031_ = lean_ctor_get(v_a_2996_, 1);
lean_inc_ref(v_s_3031_);
lean_dec_ref_known(v_a_2996_, 2);
v_s_3032_ = lean_ctor_get(v_b_2997_, 1);
lean_inc_ref(v_s_3032_);
lean_dec_ref_known(v_b_2997_, 2);
v_sa_3016_ = v_s_3031_;
v_sb_3017_ = v_s_3032_;
v___y_3018_ = v_a_2998_;
goto v___jp_3015_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 3:
{
if (lean_obj_tag(v_b_2997_) == 3)
{
lean_object* v_id_3033_; lean_object* v_d_3034_; lean_object* v_id_3035_; lean_object* v_d_3036_; uint8_t v___x_3037_; 
v_id_3033_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_id_3033_);
v_d_3034_ = lean_ctor_get(v_a_2996_, 2);
lean_inc(v_d_3034_);
lean_dec_ref_known(v_a_2996_, 3);
v_id_3035_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_id_3035_);
v_d_3036_ = lean_ctor_get(v_b_2997_, 2);
lean_inc(v_d_3036_);
lean_dec_ref_known(v_b_2997_, 3);
v___x_3037_ = lean_nat_dec_eq(v_id_3033_, v_id_3035_);
lean_dec(v_id_3035_);
lean_dec(v_id_3033_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec(v_d_3036_);
lean_dec(v_d_3034_);
v___x_3038_ = lean_box(v___x_3037_);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v_a_2998_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3034_, v_d_3036_, v_a_2998_);
return v___x_3040_;
}
}
else
{
lean_dec_ref_known(v_a_2996_, 3);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 4:
{
if (lean_obj_tag(v_b_2997_) == 4)
{
lean_object* v_d_3041_; lean_object* v_d_3042_; lean_object* v___x_3043_; 
v_d_3041_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3041_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3042_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3042_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3043_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3041_, v_d_3042_, v_a_2998_);
return v___x_3043_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 5:
{
if (lean_obj_tag(v_b_2997_) == 5)
{
lean_object* v_d_3044_; lean_object* v_d_3045_; lean_object* v___x_3046_; 
v_d_3044_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3044_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3045_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3045_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3046_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3044_, v_d_3045_, v_a_2998_);
return v___x_3046_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 6:
{
if (lean_obj_tag(v_b_2997_) == 6)
{
lean_object* v_n_3047_; uint8_t v_isCumulative_3048_; lean_object* v_d_3049_; lean_object* v_n_3050_; uint8_t v_isCumulative_3051_; lean_object* v_d_3052_; uint8_t v___x_3053_; 
v_n_3047_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_n_3047_);
v_isCumulative_3048_ = lean_ctor_get_uint8(v_a_2996_, sizeof(void*)*3 + 8);
v_d_3049_ = lean_ctor_get(v_a_2996_, 2);
lean_inc(v_d_3049_);
lean_dec_ref_known(v_a_2996_, 3);
v_n_3050_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_n_3050_);
v_isCumulative_3051_ = lean_ctor_get_uint8(v_b_2997_, sizeof(void*)*3 + 8);
v_d_3052_ = lean_ctor_get(v_b_2997_, 2);
lean_inc(v_d_3052_);
lean_dec_ref_known(v_b_2997_, 3);
v___x_3053_ = lean_nat_dec_eq(v_n_3047_, v_n_3050_);
lean_dec(v_n_3050_);
lean_dec(v_n_3047_);
if (v___x_3053_ == 0)
{
lean_dec(v_d_3052_);
lean_dec(v_d_3049_);
goto v___jp_3022_;
}
else
{
if (v_isCumulative_3051_ == 0)
{
if (v_isCumulative_3048_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3049_, v_d_3052_, v_a_2998_);
return v___x_3054_;
}
else
{
lean_dec(v_d_3052_);
lean_dec(v_d_3049_);
goto v___jp_3022_;
}
}
else
{
if (v_isCumulative_3048_ == 0)
{
lean_dec(v_d_3052_);
lean_dec(v_d_3049_);
goto v___jp_3022_;
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3049_, v_d_3052_, v_a_2998_);
return v___x_3055_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2996_, 3);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 7:
{
if (lean_obj_tag(v_b_2997_) == 7)
{
lean_object* v_d_3056_; lean_object* v_d_3057_; lean_object* v___x_3058_; 
v_d_3056_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3056_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3057_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3057_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3058_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3056_, v_d_3057_, v_a_2998_);
return v___x_3058_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 8:
{
if (lean_obj_tag(v_b_2997_) == 8)
{
uint8_t v_onlyNonCumulative_3059_; 
v_onlyNonCumulative_3059_ = lean_ctor_get_uint8(v_b_2997_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_3059_ == 0)
{
uint8_t v_onlyNonCumulative_3060_; 
v_onlyNonCumulative_3060_ = lean_ctor_get_uint8(v_a_2996_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_3060_ == 0)
{
lean_object* v_d_3061_; lean_object* v_d_3062_; lean_object* v___x_3063_; 
v_d_3061_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3061_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3062_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3062_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3063_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3061_, v_d_3062_, v_a_2998_);
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec_ref_known(v_b_2997_, 2);
lean_dec_ref_known(v_a_2996_, 2);
v___x_3064_ = lean_box(v_onlyNonCumulative_3059_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v_a_2998_);
return v___x_3065_;
}
}
else
{
uint8_t v_onlyNonCumulative_3066_; 
v_onlyNonCumulative_3066_ = lean_ctor_get_uint8(v_a_2996_, sizeof(void*)*2 + 8);
if (v_onlyNonCumulative_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec_ref_known(v_b_2997_, 2);
lean_dec_ref_known(v_a_2996_, 2);
v___x_3067_ = lean_box(v_onlyNonCumulative_3066_);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v_a_2998_);
return v___x_3068_;
}
else
{
lean_object* v_d_3069_; lean_object* v_d_3070_; lean_object* v___x_3071_; 
v_d_3069_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3069_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3070_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3070_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3071_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3069_, v_d_3070_, v_a_2998_);
return v___x_3071_;
}
}
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 9:
{
if (lean_obj_tag(v_b_2997_) == 9)
{
lean_object* v_d_3072_; lean_object* v_d_3073_; lean_object* v___x_3074_; 
v_d_3072_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3072_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3073_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3073_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3074_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3072_, v_d_3073_, v_a_2998_);
return v___x_3074_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 10:
{
if (lean_obj_tag(v_b_2997_) == 10)
{
lean_object* v_d_3075_; lean_object* v_d_3076_; lean_object* v___x_3077_; 
v_d_3075_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3075_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3076_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3076_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3077_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3075_, v_d_3076_, v_a_2998_);
return v___x_3077_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 11:
{
if (lean_obj_tag(v_b_2997_) == 11)
{
lean_object* v_d_3078_; lean_object* v_d_3079_; lean_object* v___x_3080_; 
v_d_3078_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_d_3078_);
lean_dec_ref_known(v_a_2996_, 2);
v_d_3079_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_d_3079_);
lean_dec_ref_known(v_b_2997_, 2);
v___x_3080_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3078_, v_d_3079_, v_a_2998_);
return v___x_3080_;
}
else
{
lean_dec_ref_known(v_a_2996_, 2);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 12:
{
if (lean_obj_tag(v_b_2997_) == 12)
{
lean_object* v_p_3081_; lean_object* v_p_3082_; lean_object* v_d_3083_; lean_object* v_d_3084_; lean_object* v_id_3085_; lean_object* v_id_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3096_; 
v_p_3081_ = lean_ctor_get(v_a_2996_, 1);
lean_inc_ref(v_p_3081_);
v_p_3082_ = lean_ctor_get(v_b_2997_, 1);
lean_inc_ref(v_p_3082_);
v_d_3083_ = lean_ctor_get(v_a_2996_, 2);
lean_inc(v_d_3083_);
lean_dec_ref_known(v_a_2996_, 3);
v_d_3084_ = lean_ctor_get(v_b_2997_, 2);
lean_inc(v_d_3084_);
lean_dec_ref_known(v_b_2997_, 3);
v_id_3085_ = lean_ctor_get(v_p_3081_, 1);
lean_inc(v_id_3085_);
lean_dec_ref(v_p_3081_);
v_id_3086_ = lean_ctor_get(v_p_3082_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_p_3082_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v_p_3082_, 0);
lean_dec(v_unused_3097_);
v___x_3088_ = v_p_3082_;
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_id_3086_);
lean_dec(v_p_3082_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_name_eq(v_id_3085_, v_id_3086_);
lean_dec(v_id_3086_);
lean_dec(v_id_3085_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
lean_dec(v_d_3084_);
lean_dec(v_d_3083_);
v___x_3091_ = lean_box(v___x_3090_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 1, v_a_2998_);
lean_ctor_set(v___x_3088_, 0, v___x_3091_);
v___x_3093_ = v___x_3088_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_2998_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
else
{
lean_object* v___x_3095_; 
lean_del_object(v___x_3088_);
v___x_3095_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3083_, v_d_3084_, v_a_2998_);
return v___x_3095_;
}
}
}
else
{
lean_dec_ref_known(v_a_2996_, 3);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 13:
{
if (lean_obj_tag(v_b_2997_) == 13)
{
lean_object* v_cost_3098_; lean_object* v_d_3099_; lean_object* v_cost_3100_; lean_object* v_d_3101_; uint8_t v___x_3102_; 
v_cost_3098_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_cost_3098_);
v_d_3099_ = lean_ctor_get(v_a_2996_, 2);
lean_inc(v_d_3099_);
lean_dec_ref_known(v_a_2996_, 3);
v_cost_3100_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_cost_3100_);
v_d_3101_ = lean_ctor_get(v_b_2997_, 2);
lean_inc(v_d_3101_);
lean_dec_ref_known(v_b_2997_, 3);
v___x_3102_ = l_Lean_Fmt_instBEqDefaultCost_beq___redArg(v_cost_3098_, v_cost_3100_);
lean_dec(v_cost_3100_);
lean_dec(v_cost_3098_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_d_3101_);
lean_dec(v_d_3099_);
v___x_3103_ = lean_box(v___x_3102_);
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3103_);
lean_ctor_set(v___x_3104_, 1, v_a_2998_);
return v___x_3104_;
}
else
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3099_, v_d_3101_, v_a_2998_);
return v___x_3105_;
}
}
else
{
lean_dec_ref_known(v_a_2996_, 3);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
case 14:
{
if (lean_obj_tag(v_b_2997_) == 14)
{
lean_object* v_a_3106_; lean_object* v_b_3107_; lean_object* v_a_3108_; lean_object* v_b_3109_; 
v_a_3106_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_a_3106_);
v_b_3107_ = lean_ctor_get(v_a_2996_, 2);
lean_inc(v_b_3107_);
lean_dec_ref_known(v_a_2996_, 3);
v_a_3108_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_a_3108_);
v_b_3109_ = lean_ctor_get(v_b_2997_, 2);
lean_inc(v_b_3109_);
lean_dec_ref_known(v_b_2997_, 3);
v_da1_3005_ = v_a_3106_;
v_da2_3006_ = v_b_3107_;
v_db1_3007_ = v_a_3108_;
v_db2_3008_ = v_b_3109_;
v___y_3009_ = v_a_2998_;
goto v___jp_3004_;
}
else
{
lean_dec_ref_known(v_a_2996_, 3);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
default: 
{
if (lean_obj_tag(v_b_2997_) == 15)
{
lean_object* v_a_3110_; lean_object* v_b_3111_; lean_object* v_a_3112_; lean_object* v_b_3113_; 
v_a_3110_ = lean_ctor_get(v_a_2996_, 1);
lean_inc(v_a_3110_);
v_b_3111_ = lean_ctor_get(v_a_2996_, 2);
lean_inc(v_b_3111_);
lean_dec_ref_known(v_a_2996_, 3);
v_a_3112_ = lean_ctor_get(v_b_2997_, 1);
lean_inc(v_a_3112_);
v_b_3113_ = lean_ctor_get(v_b_2997_, 2);
lean_inc(v_b_3113_);
lean_dec_ref_known(v_b_2997_, 3);
v_da1_3005_ = v_a_3110_;
v_da2_3006_ = v_b_3111_;
v_db1_3007_ = v_a_3112_;
v_db2_3008_ = v_b_3113_;
v___y_3009_ = v_a_2998_;
goto v___jp_3004_;
}
else
{
lean_dec_ref_known(v_a_2996_, 3);
lean_dec(v_b_2997_);
v___y_3000_ = v_a_2998_;
goto v___jp_2999_;
}
}
}
v___jp_2999_:
{
uint8_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3001_ = 0;
v___x_3002_ = lean_box(v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set(v___x_3003_, 1, v___y_3000_);
return v___x_3003_;
}
v___jp_3004_:
{
lean_object* v___x_3010_; lean_object* v_fst_3011_; uint8_t v___x_3012_; 
v___x_3010_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da1_3005_, v_db1_3007_, v___y_3009_);
v_fst_3011_ = lean_ctor_get(v___x_3010_, 0);
v___x_3012_ = lean_unbox(v_fst_3011_);
if (v___x_3012_ == 0)
{
lean_dec(v_db2_3008_);
lean_dec(v_da2_3006_);
return v___x_3010_;
}
else
{
lean_object* v_snd_3013_; lean_object* v___x_3014_; 
v_snd_3013_ = lean_ctor_get(v___x_3010_, 1);
lean_inc(v_snd_3013_);
lean_dec_ref(v___x_3010_);
v___x_3014_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da2_3006_, v_db2_3008_, v_snd_3013_);
return v___x_3014_;
}
}
v___jp_3015_:
{
uint8_t v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = lean_string_dec_eq(v_sa_3016_, v_sb_3017_);
lean_dec_ref(v_sb_3017_);
lean_dec_ref(v_sa_3016_);
v___x_3020_ = lean_box(v___x_3019_);
v___x_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v___y_3018_);
return v___x_3021_;
}
v___jp_3022_:
{
uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = 0;
v___x_3024_ = lean_box(v___x_3023_);
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v_a_2998_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object* v_a_3114_, lean_object* v_b_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_cacheKey_3119_; lean_object* v___x_3120_; 
lean_inc(v_a_3114_);
v___x_3117_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3114_);
lean_inc(v_b_3115_);
v___x_3118_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3115_);
v_cacheKey_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3119_, 0, v___x_3117_);
lean_ctor_set(v_cacheKey_3119_, 1, v___x_3118_);
v___x_3120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_a_3116_, v_cacheKey_3119_);
if (lean_obj_tag(v___x_3120_) == 1)
{
lean_object* v_val_3121_; lean_object* v___x_3122_; 
lean_dec_ref_known(v_cacheKey_3119_, 2);
lean_dec(v_b_3115_);
lean_dec(v_a_3114_);
v_val_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_val_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v_val_3121_);
lean_ctor_set(v___x_3122_, 1, v_a_3116_);
return v___x_3122_;
}
else
{
lean_object* v___x_3123_; lean_object* v_fst_3124_; lean_object* v_snd_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v___x_3120_);
v___x_3123_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(v_a_3114_, v_b_3115_, v_a_3116_);
v_fst_3124_ = lean_ctor_get(v___x_3123_, 0);
v_snd_3125_ = lean_ctor_get(v___x_3123_, 1);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3127_ = v___x_3123_;
v_isShared_3128_ = v_isSharedCheck_3133_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_snd_3125_);
lean_inc(v_fst_3124_);
lean_dec(v___x_3123_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3133_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
lean_inc(v_fst_3124_);
v___x_3129_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_snd_3125_, v_cacheKey_3119_, v_fst_3124_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3129_);
v___x_3131_ = v___x_3127_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_fst_3124_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_unsigned_to_nat(16u);
v___x_3136_ = lean_mk_array(v___x_3135_, v___x_3134_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
lean_ctor_set(v___x_3139_, 1, v___x_3137_);
return v___x_3139_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object* v_a_3140_, lean_object* v_b_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v_fst_3144_; uint8_t v___x_3145_; 
v___x_3142_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1);
v___x_3143_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_a_3140_, v_b_3141_, v___x_3142_);
v_fst_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_fst_3144_);
lean_dec_ref(v___x_3143_);
v___x_3145_ = lean_unbox(v_fst_3144_);
lean_dec(v_fst_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object* v_a_3146_, lean_object* v_b_3147_){
_start:
{
uint8_t v_res_3148_; lean_object* v_r_3149_; 
v_res_3148_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_a_3146_, v_b_3147_);
v_r_3149_ = lean_box(v_res_3148_);
return v_r_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object* v_a_3150_, lean_object* v_choiceStx_3151_, lean_object* v_as_3152_, size_t v_sz_3153_, size_t v_i_3154_, lean_object* v_b_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_a_3159_; lean_object* v_a_3160_; uint8_t v___x_3164_; 
v___x_3164_ = lean_usize_dec_lt(v_i_3154_, v_sz_3153_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; 
lean_dec(v_choiceStx_3151_);
lean_dec_ref(v_a_3150_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v_b_3155_);
lean_ctor_set(v___x_3165_, 1, v___y_3157_);
return v___x_3165_;
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3167_; 
lean_dec_ref(v___y_3157_);
v_a_3166_ = lean_array_uget_borrowed(v_as_3152_, v_i_3154_);
lean_inc_ref(v_a_3150_);
lean_inc(v_a_3166_);
v___x_3167_ = l_Lean_Fmt_fmt(v_a_3166_, v___y_3156_, v_a_3150_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_snd_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3244_; 
v_snd_3168_ = lean_ctor_get(v_b_3155_, 1);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_b_3155_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v_b_3155_, 0);
lean_dec(v_unused_3245_);
v___x_3170_ = v_b_3155_;
v_isShared_3171_ = v_isSharedCheck_3244_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_snd_3168_);
lean_dec(v_b_3155_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3244_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_a_3172_; lean_object* v_a_3173_; lean_object* v_fst_3174_; lean_object* v_snd_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3243_; 
v_a_3172_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3172_);
v_a_3173_ = lean_ctor_get(v___x_3167_, 1);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3167_, 2);
v_fst_3174_ = lean_ctor_get(v_snd_3168_, 0);
v_snd_3175_ = lean_ctor_get(v_snd_3168_, 1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_snd_3168_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3177_ = v_snd_3168_;
v_isShared_3178_ = v_isSharedCheck_3243_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_snd_3175_);
lean_inc(v_fst_3174_);
lean_dec(v_snd_3168_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3243_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v_first_x3f_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; 
v___x_3179_ = lean_box(0);
if (lean_obj_tag(v_fst_3174_) == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
lean_inc(v_a_3173_);
lean_inc(v_a_3172_);
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v_a_3172_);
lean_ctor_set(v___x_3241_, 1, v_a_3173_);
v___x_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
v_first_x3f_3181_ = v___x_3242_;
v___y_3182_ = v___y_3156_;
v___y_3183_ = v_a_3173_;
goto v___jp_3180_;
}
else
{
v_first_x3f_3181_ = v_fst_3174_;
v___y_3182_ = v___y_3156_;
v___y_3183_ = v_a_3173_;
goto v___jp_3180_;
}
v___jp_3180_:
{
uint8_t v___x_3184_; 
lean_inc(v_a_3172_);
v___x_3184_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_a_3172_);
if (v___x_3184_ == 0)
{
if (lean_obj_tag(v_snd_3175_) == 1)
{
lean_object* v_val_3185_; lean_object* v_fst_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3225_; 
lean_del_object(v___x_3170_);
v_val_3185_ = lean_ctor_get(v_snd_3175_, 0);
lean_inc(v_val_3185_);
v_fst_3186_ = lean_ctor_get(v_val_3185_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_val_3185_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v_val_3185_, 1);
lean_dec(v_unused_3226_);
v___x_3188_ = v_val_3185_;
v_isShared_3189_ = v_isSharedCheck_3225_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_fst_3186_);
lean_dec(v_val_3185_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3225_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_doc_3190_; lean_object* v_doc_3191_; uint8_t v___x_3192_; 
v_doc_3190_ = lean_ctor_get(v_a_3172_, 0);
lean_inc(v_doc_3190_);
lean_dec(v_a_3172_);
v_doc_3191_ = lean_ctor_get(v_fst_3186_, 0);
lean_inc(v_doc_3191_);
lean_dec(v_fst_3186_);
v___x_3192_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_doc_3190_, v_doc_3191_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; 
lean_dec_ref(v___y_3183_);
v___x_3193_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_choiceStx_3151_, v___y_3182_, v_a_3150_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3209_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_a_3195_ = lean_ctor_get(v___x_3193_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3197_ = v___x_3193_;
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3199_, 0, v_a_3194_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v_snd_3175_);
lean_ctor_set(v___x_3188_, 0, v_first_x3f_3181_);
v___x_3201_ = v___x_3188_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_first_x3f_3181_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_snd_3175_);
v___x_3201_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 1, v___x_3201_);
lean_ctor_set(v___x_3177_, 0, v___x_3199_);
v___x_3203_ = v___x_3177_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v___x_3203_);
v___x_3205_ = v___x_3197_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_a_3195_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_del_object(v___x_3188_);
lean_dec_ref_known(v_snd_3175_, 1);
lean_dec(v_first_x3f_3181_);
lean_del_object(v___x_3177_);
v_a_3210_ = lean_ctor_get(v___x_3193_, 0);
v_a_3211_ = lean_ctor_get(v___x_3193_, 1);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3193_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_inc(v_a_3210_);
lean_dec(v___x_3193_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3210_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v___x_3220_; 
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 1, v_snd_3175_);
lean_ctor_set(v___x_3188_, 0, v_first_x3f_3181_);
v___x_3220_ = v___x_3188_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_first_x3f_3181_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_snd_3175_);
v___x_3220_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 1, v___x_3220_);
lean_ctor_set(v___x_3177_, 0, v___x_3179_);
v___x_3222_ = v___x_3177_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
v_a_3159_ = v___x_3222_;
v_a_3160_ = v___y_3183_;
goto v___jp_3158_;
}
}
}
}
}
else
{
lean_object* v___x_3228_; 
lean_dec(v_snd_3175_);
lean_inc_ref(v___y_3183_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 1, v___y_3183_);
lean_ctor_set(v___x_3177_, 0, v_a_3172_);
v___x_3228_ = v___x_3177_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3172_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___y_3183_);
v___x_3228_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___x_3229_);
lean_ctor_set(v___x_3170_, 0, v_first_x3f_3181_);
v___x_3231_ = v___x_3170_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_first_x3f_3181_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3179_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v_a_3159_ = v___x_3232_;
v_a_3160_ = v___y_3183_;
goto v___jp_3158_;
}
}
}
}
else
{
lean_object* v___x_3236_; 
lean_dec(v_a_3172_);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v_first_x3f_3181_);
v___x_3236_ = v___x_3177_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_first_x3f_3181_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_snd_3175_);
v___x_3236_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3238_; 
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___x_3236_);
lean_ctor_set(v___x_3170_, 0, v___x_3179_);
v___x_3238_ = v___x_3170_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
v_a_3159_ = v___x_3238_;
v_a_3160_ = v___y_3183_;
goto v___jp_3158_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v_b_3155_);
lean_dec(v_choiceStx_3151_);
lean_dec_ref(v_a_3150_);
v_a_3246_ = lean_ctor_get(v___x_3167_, 0);
v_a_3247_ = lean_ctor_get(v___x_3167_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3167_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_inc(v_a_3246_);
lean_dec(v___x_3167_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3246_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
v___jp_3158_:
{
size_t v___x_3161_; size_t v___x_3162_; 
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3154_, v___x_3161_);
v_i_3154_ = v___x_3162_;
v_b_3155_ = v_a_3159_;
v___y_3157_ = v_a_3160_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1___boxed(lean_object* v_a_3255_, lean_object* v_choiceStx_3256_, lean_object* v_as_3257_, lean_object* v_sz_3258_, lean_object* v_i_3259_, lean_object* v_b_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
size_t v_sz_boxed_3263_; size_t v_i_boxed_3264_; lean_object* v_res_3265_; 
v_sz_boxed_3263_ = lean_unbox_usize(v_sz_3258_);
lean_dec(v_sz_3258_);
v_i_boxed_3264_ = lean_unbox_usize(v_i_3259_);
lean_dec(v_i_3259_);
v_res_3265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3255_, v_choiceStx_3256_, v_as_3257_, v_sz_boxed_3263_, v_i_boxed_3264_, v_b_3260_, v___y_3261_, v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec_ref(v_as_3257_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object* v_choiceStx_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v___y_3275_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3285_ = l_Lean_Syntax_getNumArgs(v_choiceStx_3271_);
v___x_3286_ = lean_unsigned_to_nat(0u);
v___x_3287_ = lean_nat_dec_eq(v___x_3285_, v___x_3286_);
lean_dec(v___x_3285_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; size_t v_sz_3290_; size_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3288_ = l_Lean_Syntax_getArgs(v_choiceStx_3271_);
v___x_3289_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1));
v_sz_3290_ = lean_array_size(v___x_3288_);
v___x_3291_ = ((size_t)0ULL);
lean_inc_ref(v_a_3273_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3273_, v_choiceStx_3271_, v___x_3288_, v_sz_3290_, v___x_3291_, v___x_3289_, v_a_3272_, v_a_3273_);
lean_dec_ref(v___x_3288_);
if (lean_obj_tag(v___x_3292_) == 0)
{
lean_object* v_a_3293_; lean_object* v_fst_3294_; 
v_a_3293_ = lean_ctor_get(v___x_3292_, 0);
v_fst_3294_ = lean_ctor_get(v_a_3293_, 0);
if (lean_obj_tag(v_fst_3294_) == 0)
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3310_; 
lean_inc(v_a_3293_);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3310_ == 0)
{
lean_object* v_unused_3311_; lean_object* v_unused_3312_; 
v_unused_3311_ = lean_ctor_get(v___x_3292_, 1);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v___x_3292_, 0);
lean_dec(v_unused_3312_);
v___x_3296_ = v___x_3292_;
v_isShared_3297_ = v_isSharedCheck_3310_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v___x_3292_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3310_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_snd_3298_; lean_object* v_snd_3299_; 
v_snd_3298_ = lean_ctor_get(v_a_3293_, 1);
lean_inc(v_snd_3298_);
lean_dec(v_a_3293_);
v_snd_3299_ = lean_ctor_get(v_snd_3298_, 1);
if (lean_obj_tag(v_snd_3299_) == 1)
{
lean_object* v_val_3300_; lean_object* v_fst_3301_; lean_object* v_snd_3302_; lean_object* v___x_3304_; 
lean_inc_ref(v_snd_3299_);
lean_dec(v_snd_3298_);
v_val_3300_ = lean_ctor_get(v_snd_3299_, 0);
lean_inc(v_val_3300_);
lean_dec_ref_known(v_snd_3299_, 1);
v_fst_3301_ = lean_ctor_get(v_val_3300_, 0);
lean_inc(v_fst_3301_);
v_snd_3302_ = lean_ctor_get(v_val_3300_, 1);
lean_inc(v_snd_3302_);
lean_dec(v_val_3300_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 1, v_snd_3302_);
lean_ctor_set(v___x_3296_, 0, v_fst_3301_);
v___x_3304_ = v___x_3296_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_fst_3301_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_snd_3302_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
else
{
lean_object* v_fst_3306_; 
lean_del_object(v___x_3296_);
v_fst_3306_ = lean_ctor_get(v_snd_3298_, 0);
lean_inc(v_fst_3306_);
lean_dec(v_snd_3298_);
if (lean_obj_tag(v_fst_3306_) == 0)
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3308_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v___x_3307_);
v___y_3275_ = v___x_3308_;
goto v___jp_3274_;
}
else
{
lean_object* v_val_3309_; 
v_val_3309_ = lean_ctor_get(v_fst_3306_, 0);
lean_inc(v_val_3309_);
lean_dec_ref_known(v_fst_3306_, 1);
v___y_3275_ = v_val_3309_;
goto v___jp_3274_;
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3321_; 
lean_inc_ref(v_fst_3294_);
v_a_3313_ = lean_ctor_get(v___x_3292_, 1);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v___x_3292_, 0);
lean_dec(v_unused_3322_);
v___x_3315_ = v___x_3292_;
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3292_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3321_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v_val_3317_; lean_object* v___x_3319_; 
v_val_3317_ = lean_ctor_get(v_fst_3294_, 0);
lean_inc(v_val_3317_);
lean_dec_ref_known(v_fst_3294_, 1);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v_val_3317_);
v___x_3319_ = v___x_3315_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_val_3317_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_a_3313_);
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
lean_object* v_a_3323_; lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3331_; 
v_a_3323_ = lean_ctor_get(v___x_3292_, 0);
v_a_3324_ = lean_ctor_get(v___x_3292_, 1);
v_isSharedCheck_3331_ = !lean_is_exclusive(v___x_3292_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3326_ = v___x_3292_;
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_inc(v_a_3323_);
lean_dec(v___x_3292_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3331_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3329_; 
if (v_isShared_3327_ == 0)
{
v___x_3329_ = v___x_3326_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3323_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_a_3324_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3333_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_3332_, v_choiceStx_3271_, v_a_3273_);
lean_dec(v_choiceStx_3271_);
return v___x_3333_;
}
v___jp_3274_:
{
lean_object* v_fst_3276_; lean_object* v_snd_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
v_fst_3276_ = lean_ctor_get(v___y_3275_, 0);
v_snd_3277_ = lean_ctor_get(v___y_3275_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___y_3275_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___y_3275_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_snd_3277_);
lean_inc(v_fst_3276_);
lean_dec(v___y_3275_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_fst_3276_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_snd_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object* v_choiceStx_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(v_choiceStx_3334_, v_a_3335_, v_a_3336_);
lean_dec_ref(v_a_3335_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3338_, lean_object* v_m_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_3339_, v_a_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3342_, lean_object* v_m_3343_, lean_object* v_a_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(v_00_u03b2_3342_, v_m_3343_, v_a_3344_);
lean_dec_ref(v_a_3344_);
lean_dec_ref(v_m_3343_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3346_, lean_object* v_m_3347_, lean_object* v_a_3348_, lean_object* v_b_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_m_3347_, v_a_3348_, v_b_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3351_, lean_object* v_a_3352_, lean_object* v_x_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_3352_, v_x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3355_, lean_object* v_a_3356_, lean_object* v_x_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_3355_, v_a_3356_, v_x_3357_);
lean_dec(v_x_3357_);
lean_dec_ref(v_a_3356_);
return v_res_3358_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_3359_, lean_object* v_a_3360_, lean_object* v_x_3361_){
_start:
{
uint8_t v___x_3362_; 
v___x_3362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_3360_, v_x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3363_, lean_object* v_a_3364_, lean_object* v_x_3365_){
_start:
{
uint8_t v_res_3366_; lean_object* v_r_3367_; 
v_res_3366_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(v_00_u03b2_3363_, v_a_3364_, v_x_3365_);
lean_dec(v_x_3365_);
lean_dec_ref(v_a_3364_);
v_r_3367_ = lean_box(v_res_3366_);
return v_r_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9(lean_object* v_00_u03b2_3368_, lean_object* v_data_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_data_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b2_3371_, lean_object* v_a_3372_, lean_object* v_b_3373_, lean_object* v_x_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_3372_, v_b_3373_, v_x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11(lean_object* v_00_u03b2_3376_, lean_object* v_i_3377_, lean_object* v_source_3378_, lean_object* v_target_3379_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v_i_3377_, v_source_3378_, v_target_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12(lean_object* v_00_u03b2_3381_, lean_object* v_x_3382_, lean_object* v_x_3383_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_x_3382_, v_x_3383_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(size_t v_sz_3385_, size_t v_i_3386_, lean_object* v_bs_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
uint8_t v___x_3390_; 
v___x_3390_ = lean_usize_dec_lt(v_i_3386_, v_sz_3385_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_bs_3387_);
lean_ctor_set(v___x_3391_, 1, v___y_3389_);
return v___x_3391_;
}
else
{
lean_object* v_v_3392_; lean_object* v___x_3393_; 
v_v_3392_ = lean_array_uget_borrowed(v_bs_3387_, v_i_3386_);
lean_inc(v_v_3392_);
v___x_3393_ = l_Lean_Fmt_fmt(v_v_3392_, v___y_3388_, v___y_3389_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v_a_3395_; lean_object* v___x_3396_; lean_object* v_bs_x27_3397_; size_t v___x_3398_; size_t v___x_3399_; lean_object* v___x_3400_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
v_a_3395_ = lean_ctor_get(v___x_3393_, 1);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3393_, 2);
v___x_3396_ = lean_unsigned_to_nat(0u);
v_bs_x27_3397_ = lean_array_uset(v_bs_3387_, v_i_3386_, v___x_3396_);
v___x_3398_ = ((size_t)1ULL);
v___x_3399_ = lean_usize_add(v_i_3386_, v___x_3398_);
v___x_3400_ = lean_array_uset(v_bs_x27_3397_, v_i_3386_, v_a_3394_);
v_i_3386_ = v___x_3399_;
v_bs_3387_ = v___x_3400_;
v___y_3389_ = v_a_3395_;
goto _start;
}
else
{
lean_object* v_a_3402_; lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec_ref(v_bs_3387_);
v_a_3402_ = lean_ctor_get(v___x_3393_, 0);
v_a_3403_ = lean_ctor_get(v___x_3393_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3393_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_inc(v_a_3402_);
lean_dec(v___x_3393_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3402_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1___boxed(lean_object* v_sz_3411_, lean_object* v_i_3412_, lean_object* v_bs_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
size_t v_sz_boxed_3416_; size_t v_i_boxed_3417_; lean_object* v_res_3418_; 
v_sz_boxed_3416_ = lean_unbox_usize(v_sz_3411_);
lean_dec(v_sz_3411_);
v_i_boxed_3417_ = lean_unbox_usize(v_i_3412_);
lean_dec(v_i_3412_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_boxed_3416_, v_i_boxed_3417_, v_bs_3413_, v___y_3414_, v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3419_, lean_object* v_x_3420_){
_start:
{
if (lean_obj_tag(v_x_3420_) == 0)
{
return v_x_3419_;
}
else
{
lean_object* v_key_3421_; lean_object* v_value_3422_; lean_object* v_tail_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3449_; 
v_key_3421_ = lean_ctor_get(v_x_3420_, 0);
v_value_3422_ = lean_ctor_get(v_x_3420_, 1);
v_tail_3423_ = lean_ctor_get(v_x_3420_, 2);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_x_3420_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3425_ = v_x_3420_;
v_isShared_3426_ = v_isSharedCheck_3449_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_tail_3423_);
lean_inc(v_value_3422_);
lean_inc(v_key_3421_);
lean_dec(v_x_3420_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3449_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; uint64_t v___y_3429_; 
v___x_3427_ = lean_array_get_size(v_x_3419_);
if (lean_obj_tag(v_key_3421_) == 0)
{
uint64_t v___x_3447_; 
v___x_3447_ = 1723ULL;
v___y_3429_ = v___x_3447_;
goto v___jp_3428_;
}
else
{
uint64_t v_hash_3448_; 
v_hash_3448_ = lean_ctor_get_uint64(v_key_3421_, sizeof(void*)*2);
v___y_3429_ = v_hash_3448_;
goto v___jp_3428_;
}
v___jp_3428_:
{
uint64_t v___x_3430_; uint64_t v___x_3431_; uint64_t v_fold_3432_; uint64_t v___x_3433_; uint64_t v___x_3434_; uint64_t v___x_3435_; size_t v___x_3436_; size_t v___x_3437_; size_t v___x_3438_; size_t v___x_3439_; size_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3430_ = 32ULL;
v___x_3431_ = lean_uint64_shift_right(v___y_3429_, v___x_3430_);
v_fold_3432_ = lean_uint64_xor(v___y_3429_, v___x_3431_);
v___x_3433_ = 16ULL;
v___x_3434_ = lean_uint64_shift_right(v_fold_3432_, v___x_3433_);
v___x_3435_ = lean_uint64_xor(v_fold_3432_, v___x_3434_);
v___x_3436_ = lean_uint64_to_usize(v___x_3435_);
v___x_3437_ = lean_usize_of_nat(v___x_3427_);
v___x_3438_ = ((size_t)1ULL);
v___x_3439_ = lean_usize_sub(v___x_3437_, v___x_3438_);
v___x_3440_ = lean_usize_land(v___x_3436_, v___x_3439_);
v___x_3441_ = lean_array_uget_borrowed(v_x_3419_, v___x_3440_);
lean_inc(v___x_3441_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 2, v___x_3441_);
v___x_3443_ = v___x_3425_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_key_3421_);
lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_value_3422_);
lean_ctor_set(v_reuseFailAlloc_3446_, 2, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; 
v___x_3444_ = lean_array_uset(v_x_3419_, v___x_3440_, v___x_3443_);
v_x_3419_ = v___x_3444_;
v_x_3420_ = v_tail_3423_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(lean_object* v_i_3450_, lean_object* v_source_3451_, lean_object* v_target_3452_){
_start:
{
lean_object* v___x_3453_; uint8_t v___x_3454_; 
v___x_3453_ = lean_array_get_size(v_source_3451_);
v___x_3454_ = lean_nat_dec_lt(v_i_3450_, v___x_3453_);
if (v___x_3454_ == 0)
{
lean_dec_ref(v_source_3451_);
lean_dec(v_i_3450_);
return v_target_3452_;
}
else
{
lean_object* v_es_3455_; lean_object* v___x_3456_; lean_object* v_source_3457_; lean_object* v_target_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_es_3455_ = lean_array_fget(v_source_3451_, v_i_3450_);
v___x_3456_ = lean_box(0);
v_source_3457_ = lean_array_fset(v_source_3451_, v_i_3450_, v___x_3456_);
v_target_3458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_target_3452_, v_es_3455_);
v___x_3459_ = lean_unsigned_to_nat(1u);
v___x_3460_ = lean_nat_add(v_i_3450_, v___x_3459_);
lean_dec(v_i_3450_);
v_i_3450_ = v___x_3460_;
v_source_3451_ = v_source_3457_;
v_target_3452_ = v_target_3458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(lean_object* v_data_3462_){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v_nbuckets_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___x_3463_ = lean_array_get_size(v_data_3462_);
v___x_3464_ = lean_unsigned_to_nat(2u);
v_nbuckets_3465_ = lean_nat_mul(v___x_3463_, v___x_3464_);
v___x_3466_ = lean_unsigned_to_nat(0u);
v___x_3467_ = lean_box(0);
v___x_3468_ = lean_mk_array(v_nbuckets_3465_, v___x_3467_);
v___x_3469_ = lean_array_propagate_mark(v_data_3462_, v___x_3468_);
v___x_3470_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v___x_3466_, v_data_3462_, v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(lean_object* v_m_3471_, lean_object* v_a_3472_, lean_object* v_b_3473_){
_start:
{
lean_object* v_size_3474_; lean_object* v_buckets_3475_; lean_object* v___x_3476_; uint64_t v___y_3478_; 
v_size_3474_ = lean_ctor_get(v_m_3471_, 0);
v_buckets_3475_ = lean_ctor_get(v_m_3471_, 1);
v___x_3476_ = lean_array_get_size(v_buckets_3475_);
if (lean_obj_tag(v_a_3472_) == 0)
{
uint64_t v___x_3515_; 
v___x_3515_ = 1723ULL;
v___y_3478_ = v___x_3515_;
goto v___jp_3477_;
}
else
{
uint64_t v_hash_3516_; 
v_hash_3516_ = lean_ctor_get_uint64(v_a_3472_, sizeof(void*)*2);
v___y_3478_ = v_hash_3516_;
goto v___jp_3477_;
}
v___jp_3477_:
{
uint64_t v___x_3479_; uint64_t v___x_3480_; uint64_t v_fold_3481_; uint64_t v___x_3482_; uint64_t v___x_3483_; uint64_t v___x_3484_; size_t v___x_3485_; size_t v___x_3486_; size_t v___x_3487_; size_t v___x_3488_; size_t v___x_3489_; lean_object* v_bkt_3490_; uint8_t v___x_3491_; 
v___x_3479_ = 32ULL;
v___x_3480_ = lean_uint64_shift_right(v___y_3478_, v___x_3479_);
v_fold_3481_ = lean_uint64_xor(v___y_3478_, v___x_3480_);
v___x_3482_ = 16ULL;
v___x_3483_ = lean_uint64_shift_right(v_fold_3481_, v___x_3482_);
v___x_3484_ = lean_uint64_xor(v_fold_3481_, v___x_3483_);
v___x_3485_ = lean_uint64_to_usize(v___x_3484_);
v___x_3486_ = lean_usize_of_nat(v___x_3476_);
v___x_3487_ = ((size_t)1ULL);
v___x_3488_ = lean_usize_sub(v___x_3486_, v___x_3487_);
v___x_3489_ = lean_usize_land(v___x_3485_, v___x_3488_);
v_bkt_3490_ = lean_array_uget_borrowed(v_buckets_3475_, v___x_3489_);
v___x_3491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_3472_, v_bkt_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3512_; 
lean_inc_ref(v_buckets_3475_);
lean_inc(v_size_3474_);
v_isSharedCheck_3512_ = !lean_is_exclusive(v_m_3471_);
if (v_isSharedCheck_3512_ == 0)
{
lean_object* v_unused_3513_; lean_object* v_unused_3514_; 
v_unused_3513_ = lean_ctor_get(v_m_3471_, 1);
lean_dec(v_unused_3513_);
v_unused_3514_ = lean_ctor_get(v_m_3471_, 0);
lean_dec(v_unused_3514_);
v___x_3493_ = v_m_3471_;
v_isShared_3494_ = v_isSharedCheck_3512_;
goto v_resetjp_3492_;
}
else
{
lean_dec(v_m_3471_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3512_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v_size_x27_3496_; lean_object* v___x_3497_; lean_object* v_buckets_x27_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v___x_3495_ = lean_unsigned_to_nat(1u);
v_size_x27_3496_ = lean_nat_add(v_size_3474_, v___x_3495_);
lean_dec(v_size_3474_);
lean_inc(v_bkt_3490_);
v___x_3497_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3497_, 0, v_a_3472_);
lean_ctor_set(v___x_3497_, 1, v_b_3473_);
lean_ctor_set(v___x_3497_, 2, v_bkt_3490_);
v_buckets_x27_3498_ = lean_array_uset(v_buckets_3475_, v___x_3489_, v___x_3497_);
v___x_3499_ = lean_unsigned_to_nat(4u);
v___x_3500_ = lean_nat_mul(v_size_x27_3496_, v___x_3499_);
v___x_3501_ = lean_unsigned_to_nat(3u);
v___x_3502_ = lean_nat_div(v___x_3500_, v___x_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_array_get_size(v_buckets_x27_3498_);
v___x_3504_ = lean_nat_dec_le(v___x_3502_, v___x_3503_);
lean_dec(v___x_3502_);
if (v___x_3504_ == 0)
{
lean_object* v_val_3505_; lean_object* v___x_3507_; 
v_val_3505_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_buckets_x27_3498_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v_val_3505_);
lean_ctor_set(v___x_3493_, 0, v_size_x27_3496_);
v___x_3507_ = v___x_3493_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_size_x27_3496_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_val_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
else
{
lean_object* v___x_3510_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v_buckets_x27_3498_);
lean_ctor_set(v___x_3493_, 0, v_size_x27_3496_);
v___x_3510_ = v___x_3493_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_size_x27_3496_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_buckets_x27_3498_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
else
{
lean_dec(v_b_3473_);
lean_dec(v_a_3472_);
return v_m_3471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object* v_op_3517_, lean_object* v_stx_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
uint8_t v_sparse_3521_; uint8_t v_separateFinalOperand_3522_; lean_object* v_precs_x3f_3523_; lean_object* v_extendedChainKinds_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3565_; 
v_sparse_3521_ = lean_ctor_get_uint8(v_op_3517_, sizeof(void*)*2);
v_separateFinalOperand_3522_ = lean_ctor_get_uint8(v_op_3517_, sizeof(void*)*2 + 1);
v_precs_x3f_3523_ = lean_ctor_get(v_op_3517_, 0);
v_extendedChainKinds_3524_ = lean_ctor_get(v_op_3517_, 1);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_op_3517_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3526_ = v_op_3517_;
v_isShared_3527_ = v_isSharedCheck_3565_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_extendedChainKinds_3524_);
lean_inc(v_precs_x3f_3523_);
lean_dec(v_op_3517_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3565_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_env_3528_; lean_object* v_opts_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3534_; 
v_env_3528_ = lean_ctor_get(v_a_3519_, 0);
v_opts_3529_ = lean_ctor_get(v_a_3519_, 3);
lean_inc(v_stx_3518_);
v___x_3530_ = l_Lean_Syntax_getKind(v_stx_3518_);
v___x_3531_ = lean_box(0);
v___x_3532_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_extendedChainKinds_3524_, v___x_3530_, v___x_3531_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 1, v___x_3532_);
v___x_3534_ = v___x_3526_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_precs_x3f_3523_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v___x_3532_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*2, v_sparse_3521_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*2 + 1, v_separateFinalOperand_3522_);
v___x_3534_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3535_; size_t v_sz_3536_; size_t v___x_3537_; lean_object* v___x_3538_; 
lean_inc_ref(v_env_3528_);
v___x_3535_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_3528_, v_opts_3529_, v___x_3534_, v_stx_3518_);
lean_dec_ref(v___x_3534_);
v_sz_3536_ = lean_array_size(v___x_3535_);
v___x_3537_ = ((size_t)0ULL);
v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_3536_, v___x_3537_, v___x_3535_, v_a_3519_, v_a_3520_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3554_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_a_3540_ = lean_ctor_get(v___x_3538_, 1);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3542_ = v___x_3538_;
v_isShared_3543_ = v_isSharedCheck_3554_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3554_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___y_3545_; uint8_t v___x_3550_; 
v___x_3550_ = 1;
if (v_sparse_3521_ == 0)
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3551_, 0, v___x_3550_);
lean_ctor_set_uint8(v___x_3551_, 1, v_sparse_3521_);
lean_ctor_set_uint8(v___x_3551_, 2, v___x_3550_);
lean_ctor_set_uint8(v___x_3551_, 3, v___x_3550_);
v___y_3545_ = v___x_3551_;
goto v___jp_3544_;
}
else
{
uint8_t v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = 0;
v___x_3553_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_3553_, 0, v___x_3550_);
lean_ctor_set_uint8(v___x_3553_, 1, v___x_3552_);
lean_ctor_set_uint8(v___x_3553_, 2, v___x_3550_);
lean_ctor_set_uint8(v___x_3553_, 3, v___x_3552_);
lean_ctor_set_uint8(v___x_3553_, 4, v_separateFinalOperand_3522_);
v___y_3545_ = v___x_3553_;
goto v___jp_3544_;
}
v___jp_3544_:
{
lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3546_ = l_Lean_Fmt_Layouts_infixOperator(v_a_3539_, v___y_3545_);
lean_dec_ref(v___y_3545_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3546_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_a_3540_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
v_a_3555_ = lean_ctor_get(v___x_3538_, 0);
v_a_3556_ = lean_ctor_get(v___x_3538_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3538_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_inc(v_a_3555_);
lean_dec(v___x_3538_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3555_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object* v_op_3566_, lean_object* v_stx_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_Fmt_fmtInfixOperator(v_op_3566_, v_stx_3567_, v_a_3568_, v_a_3569_);
lean_dec_ref(v_a_3568_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0(lean_object* v_00_u03b2_3571_, lean_object* v_m_3572_, lean_object* v_a_3573_, lean_object* v_b_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_m_3572_, v_a_3573_, v_b_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0(lean_object* v_00_u03b2_3576_, lean_object* v_data_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_data_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3579_, lean_object* v_i_3580_, lean_object* v_source_3581_, lean_object* v_target_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v_i_3580_, v_source_3581_, v_target_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3585_, v_x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(lean_object* v_x_3588_, lean_object* v_x_3589_){
_start:
{
if (lean_obj_tag(v_x_3588_) == 0)
{
if (lean_obj_tag(v_x_3589_) == 0)
{
uint8_t v___x_3590_; 
v___x_3590_ = 1;
return v___x_3590_;
}
else
{
uint8_t v___x_3591_; 
v___x_3591_ = 0;
return v___x_3591_;
}
}
else
{
if (lean_obj_tag(v_x_3589_) == 0)
{
uint8_t v___x_3592_; 
v___x_3592_ = 0;
return v___x_3592_;
}
else
{
lean_object* v_val_3593_; lean_object* v_val_3594_; uint8_t v___x_3595_; 
v_val_3593_ = lean_ctor_get(v_x_3588_, 0);
v_val_3594_ = lean_ctor_get(v_x_3589_, 0);
v___x_3595_ = lean_string_dec_eq(v_val_3593_, v_val_3594_);
return v___x_3595_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0___boxed(lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
uint8_t v_res_3598_; lean_object* v_r_3599_; 
v_res_3598_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v_x_3596_, v_x_3597_);
lean_dec(v_x_3597_);
lean_dec(v_x_3596_);
v_r_3599_ = lean_box(v_res_3598_);
return v_r_3599_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(lean_object* v_msg_3600_){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = l_String_instInhabitedSlice;
v___x_3602_ = lean_panic_fn_borrowed(v___x_3601_, v_msg_3600_);
return v___x_3602_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(lean_object* v_s_3603_, lean_object* v_a_3604_, uint8_t v_b_3605_){
_start:
{
lean_object* v_str_3606_; lean_object* v_startInclusive_3607_; lean_object* v_endExclusive_3608_; lean_object* v___x_3609_; uint8_t v_decide_3610_; 
v_str_3606_ = lean_ctor_get(v_s_3603_, 0);
v_startInclusive_3607_ = lean_ctor_get(v_s_3603_, 1);
v_endExclusive_3608_ = lean_ctor_get(v_s_3603_, 2);
v___x_3609_ = lean_nat_sub(v_endExclusive_3608_, v_startInclusive_3607_);
v_decide_3610_ = lean_nat_dec_eq(v_a_3604_, v___x_3609_);
lean_dec(v___x_3609_);
if (v_decide_3610_ == 0)
{
lean_object* v___x_3611_; uint32_t v___x_3612_; uint32_t v___x_3613_; uint8_t v___x_3614_; 
v___x_3611_ = lean_nat_add(v_startInclusive_3607_, v_a_3604_);
lean_dec(v_a_3604_);
v___x_3612_ = lean_string_utf8_get_fast(v_str_3606_, v___x_3611_);
v___x_3613_ = l_Lean_idEndEscape;
v___x_3614_ = lean_uint32_dec_eq(v___x_3612_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_string_utf8_next_fast(v_str_3606_, v___x_3611_);
lean_dec(v___x_3611_);
v___x_3616_ = lean_nat_sub(v___x_3615_, v_startInclusive_3607_);
v_a_3604_ = v___x_3616_;
v_b_3605_ = v___x_3614_;
goto _start;
}
else
{
lean_dec(v___x_3611_);
return v___x_3614_;
}
}
else
{
lean_dec(v_a_3604_);
return v_b_3605_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg___boxed(lean_object* v_s_3618_, lean_object* v_a_3619_, lean_object* v_b_3620_){
_start:
{
uint8_t v_b_boxed_3621_; uint8_t v_res_3622_; lean_object* v_r_3623_; 
v_b_boxed_3621_ = lean_unbox(v_b_3620_);
v_res_3622_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3618_, v_a_3619_, v_b_boxed_3621_);
lean_dec_ref(v_s_3618_);
v_r_3623_ = lean_box(v_res_3622_);
return v_r_3623_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(lean_object* v_s_3624_){
_start:
{
lean_object* v_searcher_3625_; uint8_t v___x_3626_; uint8_t v___x_3627_; 
v_searcher_3625_ = lean_unsigned_to_nat(0u);
v___x_3626_ = 0;
v___x_3627_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3624_, v_searcher_3625_, v___x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1___boxed(lean_object* v_s_3628_){
_start:
{
uint8_t v_res_3629_; lean_object* v_r_3630_; 
v_res_3629_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v_s_3628_);
lean_dec_ref(v_s_3628_);
v_r_3630_ = lean_box(v_res_3629_);
return v_r_3630_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(lean_object* v_s_3631_, lean_object* v_pos_3632_){
_start:
{
lean_object* v_str_3633_; lean_object* v_startInclusive_3634_; lean_object* v_endExclusive_3635_; lean_object* v___x_3636_; lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v_decide_3647_; 
v_str_3633_ = lean_ctor_get(v_s_3631_, 0);
v_startInclusive_3634_ = lean_ctor_get(v_s_3631_, 1);
v_endExclusive_3635_ = lean_ctor_get(v_s_3631_, 2);
v___x_3636_ = lean_nat_add(v_startInclusive_3634_, v_pos_3632_);
v___x_3645_ = lean_unsigned_to_nat(0u);
v___x_3646_ = lean_nat_sub(v_endExclusive_3635_, v___x_3636_);
v_decide_3647_ = lean_nat_dec_eq(v___x_3645_, v___x_3646_);
lean_dec(v___x_3646_);
if (v_decide_3647_ == 0)
{
uint32_t v___x_3648_; uint32_t v___x_3670_; uint8_t v___x_3671_; 
v___x_3648_ = lean_string_utf8_get_fast(v_str_3633_, v___x_3636_);
v___x_3670_ = 65;
v___x_3671_ = lean_uint32_dec_le(v___x_3670_, v___x_3648_);
if (v___x_3671_ == 0)
{
goto v___jp_3665_;
}
else
{
uint32_t v___x_3672_; uint8_t v___x_3673_; 
v___x_3672_ = 90;
v___x_3673_ = lean_uint32_dec_le(v___x_3648_, v___x_3672_);
if (v___x_3673_ == 0)
{
goto v___jp_3665_;
}
else
{
goto v___jp_3637_;
}
}
v___jp_3649_:
{
uint32_t v___x_3650_; uint8_t v___x_3651_; 
v___x_3650_ = 95;
v___x_3651_ = lean_uint32_dec_eq(v___x_3648_, v___x_3650_);
if (v___x_3651_ == 0)
{
uint32_t v___x_3652_; uint8_t v___x_3653_; 
v___x_3652_ = 39;
v___x_3653_ = lean_uint32_dec_eq(v___x_3648_, v___x_3652_);
if (v___x_3653_ == 0)
{
uint32_t v___x_3654_; uint8_t v___x_3655_; 
v___x_3654_ = 33;
v___x_3655_ = lean_uint32_dec_eq(v___x_3648_, v___x_3654_);
if (v___x_3655_ == 0)
{
uint32_t v___x_3656_; uint8_t v___x_3657_; 
v___x_3656_ = 63;
v___x_3657_ = lean_uint32_dec_eq(v___x_3648_, v___x_3656_);
if (v___x_3657_ == 0)
{
uint8_t v___x_3658_; 
v___x_3658_ = l_Lean_isLetterLike(v___x_3648_);
if (v___x_3658_ == 0)
{
uint8_t v___x_3659_; 
v___x_3659_ = l_Lean_isSubScriptAlnum(v___x_3648_);
if (v___x_3659_ == 0)
{
lean_dec(v___x_3636_);
return v_pos_3632_;
}
else
{
goto v___jp_3637_;
}
}
else
{
goto v___jp_3637_;
}
}
else
{
goto v___jp_3637_;
}
}
else
{
goto v___jp_3637_;
}
}
else
{
goto v___jp_3637_;
}
}
else
{
goto v___jp_3637_;
}
}
v___jp_3660_:
{
uint32_t v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = 48;
v___x_3662_ = lean_uint32_dec_le(v___x_3661_, v___x_3648_);
if (v___x_3662_ == 0)
{
goto v___jp_3649_;
}
else
{
uint32_t v___x_3663_; uint8_t v___x_3664_; 
v___x_3663_ = 57;
v___x_3664_ = lean_uint32_dec_le(v___x_3648_, v___x_3663_);
if (v___x_3664_ == 0)
{
goto v___jp_3649_;
}
else
{
goto v___jp_3637_;
}
}
}
v___jp_3665_:
{
uint32_t v___x_3666_; uint8_t v___x_3667_; 
v___x_3666_ = 97;
v___x_3667_ = lean_uint32_dec_le(v___x_3666_, v___x_3648_);
if (v___x_3667_ == 0)
{
goto v___jp_3660_;
}
else
{
uint32_t v___x_3668_; uint8_t v___x_3669_; 
v___x_3668_ = 122;
v___x_3669_ = lean_uint32_dec_le(v___x_3648_, v___x_3668_);
if (v___x_3669_ == 0)
{
goto v___jp_3660_;
}
else
{
goto v___jp_3637_;
}
}
}
}
else
{
lean_dec(v___x_3636_);
return v_pos_3632_;
}
v___jp_3637_:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3638_ = lean_string_utf8_next_fast(v_str_3633_, v___x_3636_);
v___x_3639_ = lean_nat_sub(v___x_3638_, v___x_3636_);
lean_dec(v___x_3636_);
v___x_3640_ = lean_nat_add(v_pos_3632_, v___x_3639_);
lean_dec(v___x_3639_);
v___x_3641_ = lean_unsigned_to_nat(1u);
v___x_3642_ = lean_nat_add(v_pos_3632_, v___x_3641_);
v___x_3643_ = lean_nat_dec_le(v___x_3642_, v___x_3640_);
lean_dec(v___x_3642_);
if (v___x_3643_ == 0)
{
lean_dec(v___x_3640_);
return v_pos_3632_;
}
else
{
lean_dec(v_pos_3632_);
v_pos_3632_ = v___x_3640_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2___boxed(lean_object* v_s_3674_, lean_object* v_pos_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v_s_3674_, v_pos_3675_);
lean_dec_ref(v_s_3674_);
return v_res_3676_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__0(void){
_start:
{
uint32_t v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = l_Lean_idBeginEscape;
v___x_3678_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3679_ = lean_string_push(v___x_3678_, v___x_3677_);
return v___x_3679_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__1(void){
_start:
{
uint32_t v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = l_Lean_idEndEscape;
v___x_3681_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3682_ = lean_string_push(v___x_3681_, v___x_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object* v_stx_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; uint8_t v___y_3690_; lean_object* v___x_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3693_ = l_Lean_Syntax_getNumArgs(v_stx_3683_);
v___x_3694_ = lean_unsigned_to_nat(2u);
v___x_3695_ = lean_nat_dec_eq(v___x_3693_, v___x_3694_);
lean_dec(v___x_3693_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
lean_ctor_set(v___x_3697_, 1, v_a_3685_);
return v___x_3697_;
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3683_, v___x_3698_, v_a_3685_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v_a_3701_; lean_object* v___x_3702_; lean_object* v___y_3704_; lean_object* v___y_3739_; lean_object* v_startInclusive_3740_; lean_object* v_endExclusive_3741_; uint32_t v___y_3761_; uint32_t v___y_3766_; uint32_t v___y_3772_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
v_a_3701_ = lean_ctor_get(v___x_3699_, 1);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3699_, 2);
v___x_3702_ = l_Lean_Syntax_getAtomVal(v_a_3700_);
v___x_3788_ = lean_string_utf8_byte_size(v___x_3702_);
v___x_3789_ = lean_nat_dec_lt(v___x_3698_, v___x_3788_);
if (v___x_3789_ == 0)
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3790_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3791_ = lean_string_append(v___x_3790_, v___x_3702_);
v___x_3792_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3793_ = lean_string_append(v___x_3791_, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
v___y_3704_ = v___x_3794_;
goto v___jp_3703_;
}
else
{
uint8_t v_c_3795_; uint8_t v___x_3804_; uint8_t v___x_3805_; 
v_c_3795_ = lean_string_get_byte_fast(v___x_3702_, v___x_3698_);
v___x_3804_ = 97;
v___x_3805_ = lean_uint8_dec_le(v___x_3804_, v_c_3795_);
if (v___x_3805_ == 0)
{
goto v___jp_3799_;
}
else
{
uint8_t v___x_3806_; uint8_t v___x_3807_; 
v___x_3806_ = 122;
v___x_3807_ = lean_uint8_dec_le(v_c_3795_, v___x_3806_);
if (v___x_3807_ == 0)
{
goto v___jp_3799_;
}
else
{
goto v___jp_3784_;
}
}
v___jp_3796_:
{
uint8_t v___x_3797_; uint8_t v___x_3798_; 
v___x_3797_ = 95;
v___x_3798_ = lean_uint8_dec_eq(v_c_3795_, v___x_3797_);
if (v___x_3798_ == 0)
{
goto v___jp_3777_;
}
else
{
goto v___jp_3784_;
}
}
v___jp_3799_:
{
uint8_t v___x_3800_; uint8_t v___x_3801_; 
v___x_3800_ = 65;
v___x_3801_ = lean_uint8_dec_le(v___x_3800_, v_c_3795_);
if (v___x_3801_ == 0)
{
goto v___jp_3796_;
}
else
{
uint8_t v___x_3802_; uint8_t v___x_3803_; 
v___x_3802_ = 90;
v___x_3803_ = lean_uint8_dec_le(v_c_3795_, v___x_3802_);
if (v___x_3803_ == 0)
{
goto v___jp_3796_;
}
else
{
goto v___jp_3784_;
}
}
}
}
v___jp_3703_:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_Fmt_fmt(v_a_3700_, v_a_3684_, v_a_3701_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v_a_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
v_a_3707_ = lean_ctor_get(v___x_3705_, 1);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3705_, 2);
v___x_3708_ = lean_unsigned_to_nat(1u);
v___x_3709_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3683_, v___x_3708_, v_a_3707_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
v_a_3711_ = lean_ctor_get(v___x_3709_, 1);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3709_, 2);
v___x_3712_ = l_Lean_Fmt_fmt(v_a_3710_, v_a_3684_, v_a_3711_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v_a_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
v_a_3714_ = lean_ctor_get(v___x_3712_, 1);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3712_, 2);
v___x_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3702_);
v___x_3716_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3704_, v___x_3715_);
lean_dec_ref_known(v___x_3715_, 1);
lean_dec(v___y_3704_);
if (v___x_3716_ == 0)
{
uint8_t v___x_3717_; 
v___x_3717_ = 1;
v___y_3687_ = v_a_3706_;
v___y_3688_ = v_a_3714_;
v___y_3689_ = v_a_3713_;
v___y_3690_ = v___x_3717_;
goto v___jp_3686_;
}
else
{
uint8_t v___x_3718_; 
v___x_3718_ = 2;
v___y_3687_ = v_a_3706_;
v___y_3688_ = v_a_3714_;
v___y_3689_ = v_a_3713_;
v___y_3690_ = v___x_3718_;
goto v___jp_3686_;
}
}
else
{
lean_dec(v_a_3706_);
lean_dec(v___y_3704_);
lean_dec_ref(v___x_3702_);
return v___x_3712_;
}
}
else
{
lean_object* v_a_3719_; lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec(v_a_3706_);
lean_dec(v___y_3704_);
lean_dec_ref(v___x_3702_);
v_a_3719_ = lean_ctor_get(v___x_3709_, 0);
v_a_3720_ = lean_ctor_get(v___x_3709_, 1);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3709_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_inc(v_a_3719_);
lean_dec(v___x_3709_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3719_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
else
{
lean_dec(v___y_3704_);
lean_dec_ref(v___x_3702_);
return v___x_3705_;
}
}
v___jp_3728_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v___x_3729_ = lean_string_utf8_byte_size(v___x_3702_);
lean_inc_ref(v___x_3702_);
v___x_3730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3702_);
lean_ctor_set(v___x_3730_, 1, v___x_3698_);
lean_ctor_set(v___x_3730_, 2, v___x_3729_);
v___x_3731_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3730_);
lean_dec_ref_known(v___x_3730_, 3);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3732_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3733_ = lean_string_append(v___x_3732_, v___x_3702_);
v___x_3734_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3735_ = lean_string_append(v___x_3733_, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
v___y_3704_ = v___x_3736_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3737_; 
v___x_3737_ = lean_box(0);
v___y_3704_ = v___x_3737_;
goto v___jp_3703_;
}
}
v___jp_3738_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v_decide_3744_; 
v___x_3742_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3739_, v___x_3698_);
lean_dec_ref(v___y_3739_);
v___x_3743_ = lean_nat_sub(v_endExclusive_3741_, v_startInclusive_3740_);
lean_dec(v_startInclusive_3740_);
lean_dec(v_endExclusive_3741_);
v_decide_3744_ = lean_nat_dec_eq(v___x_3742_, v___x_3743_);
lean_dec(v___x_3743_);
lean_dec(v___x_3742_);
if (v_decide_3744_ == 0)
{
goto v___jp_3728_;
}
else
{
lean_object* v___x_3745_; 
lean_inc_ref(v___x_3702_);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3702_);
v___y_3704_ = v___x_3745_;
goto v___jp_3703_;
}
}
v___jp_3746_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v_startInclusive_3749_; lean_object* v_endExclusive_3750_; 
v___x_3747_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3748_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3747_);
v_startInclusive_3749_ = lean_ctor_get(v___x_3748_, 1);
lean_inc(v_startInclusive_3749_);
v_endExclusive_3750_ = lean_ctor_get(v___x_3748_, 2);
lean_inc(v_endExclusive_3750_);
v___y_3739_ = v___x_3748_;
v_startInclusive_3740_ = v_startInclusive_3749_;
v_endExclusive_3741_ = v_endExclusive_3750_;
goto v___jp_3738_;
}
v___jp_3751_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; 
v___x_3752_ = lean_string_utf8_byte_size(v___x_3702_);
lean_inc_ref(v___x_3702_);
v___x_3753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3702_);
lean_ctor_set(v___x_3753_, 1, v___x_3698_);
lean_ctor_set(v___x_3753_, 2, v___x_3752_);
v___x_3754_ = lean_unsigned_to_nat(1u);
v___x_3755_ = l_Substring_Raw_nextn(v___x_3753_, v___x_3754_, v___x_3698_);
lean_dec_ref_known(v___x_3753_, 3);
v___x_3756_ = lean_string_is_valid_pos(v___x_3702_, v___x_3755_);
if (v___x_3756_ == 0)
{
lean_dec(v___x_3755_);
goto v___jp_3746_;
}
else
{
uint8_t v___x_3757_; 
v___x_3757_ = lean_string_is_valid_pos(v___x_3702_, v___x_3752_);
if (v___x_3757_ == 0)
{
lean_dec(v___x_3755_);
goto v___jp_3746_;
}
else
{
uint8_t v___x_3758_; 
v___x_3758_ = lean_nat_dec_le(v___x_3755_, v___x_3752_);
if (v___x_3758_ == 0)
{
lean_dec(v___x_3755_);
goto v___jp_3746_;
}
else
{
lean_object* v___x_3759_; 
lean_inc(v___x_3755_);
lean_inc_ref(v___x_3702_);
v___x_3759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3702_);
lean_ctor_set(v___x_3759_, 1, v___x_3755_);
lean_ctor_set(v___x_3759_, 2, v___x_3752_);
v___y_3739_ = v___x_3759_;
v_startInclusive_3740_ = v___x_3755_;
v_endExclusive_3741_ = v___x_3752_;
goto v___jp_3738_;
}
}
}
}
v___jp_3760_:
{
uint32_t v___x_3762_; uint8_t v___x_3763_; 
v___x_3762_ = 95;
v___x_3763_ = lean_uint32_dec_eq(v___y_3761_, v___x_3762_);
if (v___x_3763_ == 0)
{
uint8_t v___x_3764_; 
v___x_3764_ = l_Lean_isLetterLike(v___y_3761_);
if (v___x_3764_ == 0)
{
goto v___jp_3728_;
}
else
{
goto v___jp_3751_;
}
}
else
{
goto v___jp_3751_;
}
}
v___jp_3765_:
{
uint32_t v___x_3767_; uint8_t v___x_3768_; 
v___x_3767_ = 97;
v___x_3768_ = lean_uint32_dec_le(v___x_3767_, v___y_3766_);
if (v___x_3768_ == 0)
{
v___y_3761_ = v___y_3766_;
goto v___jp_3760_;
}
else
{
uint32_t v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = 122;
v___x_3770_ = lean_uint32_dec_le(v___y_3766_, v___x_3769_);
if (v___x_3770_ == 0)
{
v___y_3761_ = v___y_3766_;
goto v___jp_3760_;
}
else
{
goto v___jp_3751_;
}
}
}
v___jp_3771_:
{
uint32_t v___x_3773_; uint8_t v___x_3774_; 
v___x_3773_ = 65;
v___x_3774_ = lean_uint32_dec_le(v___x_3773_, v___y_3772_);
if (v___x_3774_ == 0)
{
v___y_3766_ = v___y_3772_;
goto v___jp_3765_;
}
else
{
uint32_t v___x_3775_; uint8_t v___x_3776_; 
v___x_3775_ = 90;
v___x_3776_ = lean_uint32_dec_le(v___y_3772_, v___x_3775_);
if (v___x_3776_ == 0)
{
v___y_3766_ = v___y_3772_;
goto v___jp_3765_;
}
else
{
goto v___jp_3751_;
}
}
}
v___jp_3777_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = lean_string_utf8_byte_size(v___x_3702_);
lean_inc_ref(v___x_3702_);
v___x_3779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3702_);
lean_ctor_set(v___x_3779_, 1, v___x_3698_);
lean_ctor_set(v___x_3779_, 2, v___x_3778_);
v___x_3780_ = l_String_Slice_Pos_get_x3f(v___x_3779_, v___x_3698_);
lean_dec_ref_known(v___x_3779_, 3);
if (lean_obj_tag(v___x_3780_) == 0)
{
uint32_t v___x_3781_; 
v___x_3781_ = 65;
v___y_3772_ = v___x_3781_;
goto v___jp_3771_;
}
else
{
lean_object* v_val_3782_; uint32_t v___x_3783_; 
v_val_3782_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_val_3782_);
lean_dec_ref_known(v___x_3780_, 1);
v___x_3783_ = lean_unbox_uint32(v_val_3782_);
lean_dec(v_val_3782_);
v___y_3772_ = v___x_3783_;
goto v___jp_3771_;
}
}
v___jp_3784_:
{
lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3785_ = lean_unsigned_to_nat(1u);
v___x_3786_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3702_, v___x_3785_);
if (v___x_3786_ == 0)
{
goto v___jp_3777_;
}
else
{
lean_object* v___x_3787_; 
lean_inc_ref(v___x_3702_);
v___x_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3702_);
v___y_3704_ = v___x_3787_;
goto v___jp_3703_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
v_a_3808_ = lean_ctor_get(v___x_3699_, 0);
v_a_3809_ = lean_ctor_get(v___x_3699_, 1);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3699_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_inc(v_a_3808_);
lean_dec(v___x_3699_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3808_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
v___jp_3686_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_3687_, v___y_3689_, v___y_3690_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
lean_ctor_set(v___x_3692_, 1, v___y_3688_);
return v___x_3692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object* v_stx_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Fmt_fmtPrefixOperator(v_stx_3817_, v_a_3818_, v_a_3819_);
lean_dec_ref(v_a_3818_);
lean_dec(v_stx_3817_);
return v_res_3820_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(lean_object* v_s_3821_, lean_object* v_inst_3822_, lean_object* v_R_3823_, lean_object* v_a_3824_, uint8_t v_b_3825_, lean_object* v_c_3826_){
_start:
{
uint8_t v___x_3827_; 
v___x_3827_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3821_, v_a_3824_, v_b_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___boxed(lean_object* v_s_3828_, lean_object* v_inst_3829_, lean_object* v_R_3830_, lean_object* v_a_3831_, lean_object* v_b_3832_, lean_object* v_c_3833_){
_start:
{
uint8_t v_b_boxed_3834_; uint8_t v_res_3835_; lean_object* v_r_3836_; 
v_b_boxed_3834_ = lean_unbox(v_b_3832_);
v_res_3835_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(v_s_3828_, v_inst_3829_, v_R_3830_, v_a_3831_, v_b_boxed_3834_, v_c_3833_);
lean_dec_ref(v_s_3828_);
v_r_3836_ = lean_box(v_res_3835_);
return v_r_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object* v_stx_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3840_ = l_Lean_Syntax_getNumArgs(v_stx_3837_);
v___x_3841_ = lean_unsigned_to_nat(2u);
v___x_3842_ = lean_nat_dec_eq(v___x_3840_, v___x_3841_);
lean_dec(v___x_3840_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
lean_ctor_set(v___x_3844_, 1, v_a_3839_);
return v___x_3844_;
}
else
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3837_, v___x_3845_, v_a_3839_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v_a_3848_; lean_object* v___x_3849_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
v_a_3848_ = lean_ctor_get(v___x_3846_, 1);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3846_, 2);
v___x_3849_ = l_Lean_Fmt_fmt(v_a_3847_, v_a_3838_, v_a_3848_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3964_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
v_a_3851_ = lean_ctor_get(v___x_3849_, 1);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3853_ = v___x_3849_;
v_isShared_3854_ = v_isSharedCheck_3964_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_inc(v_a_3850_);
lean_dec(v___x_3849_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3964_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___y_3856_; lean_object* v___y_3857_; uint8_t v___y_3858_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_unsigned_to_nat(1u);
v___x_3864_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3837_, v___x_3863_, v_a_3851_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v_a_3866_; lean_object* v___x_3867_; lean_object* v___y_3869_; lean_object* v___y_3888_; lean_object* v_startInclusive_3889_; lean_object* v_endExclusive_3890_; uint32_t v___y_3909_; uint32_t v___y_3914_; uint32_t v___y_3920_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
v_a_3866_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3864_, 2);
v___x_3867_ = l_Lean_Syntax_getAtomVal(v_a_3865_);
v___x_3935_ = lean_string_utf8_byte_size(v___x_3867_);
v___x_3936_ = lean_nat_dec_lt(v___x_3845_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3937_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3938_ = lean_string_append(v___x_3937_, v___x_3867_);
v___x_3939_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3940_ = lean_string_append(v___x_3938_, v___x_3939_);
v___x_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
v___y_3869_ = v___x_3941_;
goto v___jp_3868_;
}
else
{
uint8_t v_c_3942_; uint8_t v___x_3951_; uint8_t v___x_3952_; 
v_c_3942_ = lean_string_get_byte_fast(v___x_3867_, v___x_3845_);
v___x_3951_ = 97;
v___x_3952_ = lean_uint8_dec_le(v___x_3951_, v_c_3942_);
if (v___x_3952_ == 0)
{
goto v___jp_3946_;
}
else
{
uint8_t v___x_3953_; uint8_t v___x_3954_; 
v___x_3953_ = 122;
v___x_3954_ = lean_uint8_dec_le(v_c_3942_, v___x_3953_);
if (v___x_3954_ == 0)
{
goto v___jp_3946_;
}
else
{
goto v___jp_3932_;
}
}
v___jp_3943_:
{
uint8_t v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = 95;
v___x_3945_ = lean_uint8_dec_eq(v_c_3942_, v___x_3944_);
if (v___x_3945_ == 0)
{
goto v___jp_3925_;
}
else
{
goto v___jp_3932_;
}
}
v___jp_3946_:
{
uint8_t v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = 65;
v___x_3948_ = lean_uint8_dec_le(v___x_3947_, v_c_3942_);
if (v___x_3948_ == 0)
{
goto v___jp_3943_;
}
else
{
uint8_t v___x_3949_; uint8_t v___x_3950_; 
v___x_3949_ = 90;
v___x_3950_ = lean_uint8_dec_le(v_c_3942_, v___x_3949_);
if (v___x_3950_ == 0)
{
goto v___jp_3943_;
}
else
{
goto v___jp_3932_;
}
}
}
}
v___jp_3868_:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_Fmt_fmt(v_a_3865_, v_a_3838_, v_a_3866_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_a_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
v_a_3872_ = lean_ctor_get(v___x_3870_, 1);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3870_, 2);
v___x_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3867_);
v___x_3874_ = l_instBEqOption_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3869_, v___x_3873_);
lean_dec_ref_known(v___x_3873_, 1);
lean_dec(v___y_3869_);
if (v___x_3874_ == 0)
{
uint8_t v___x_3875_; 
v___x_3875_ = 0;
v___y_3856_ = v_a_3872_;
v___y_3857_ = v_a_3871_;
v___y_3858_ = v___x_3875_;
goto v___jp_3855_;
}
else
{
uint8_t v___x_3876_; 
v___x_3876_ = 1;
v___y_3856_ = v_a_3872_;
v___y_3857_ = v_a_3871_;
v___y_3858_ = v___x_3876_;
goto v___jp_3855_;
}
}
else
{
lean_dec(v___y_3869_);
lean_dec_ref(v___x_3867_);
lean_del_object(v___x_3853_);
lean_dec(v_a_3850_);
return v___x_3870_;
}
}
v___jp_3877_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; uint8_t v___x_3880_; 
v___x_3878_ = lean_string_utf8_byte_size(v___x_3867_);
lean_inc_ref(v___x_3867_);
v___x_3879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3867_);
lean_ctor_set(v___x_3879_, 1, v___x_3845_);
lean_ctor_set(v___x_3879_, 2, v___x_3878_);
v___x_3880_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3879_);
lean_dec_ref_known(v___x_3879_, 3);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3881_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3882_ = lean_string_append(v___x_3881_, v___x_3867_);
v___x_3883_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3884_ = lean_string_append(v___x_3882_, v___x_3883_);
v___x_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3884_);
v___y_3869_ = v___x_3885_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_box(0);
v___y_3869_ = v___x_3886_;
goto v___jp_3868_;
}
}
v___jp_3887_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v_decide_3893_; 
v___x_3891_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3888_, v___x_3845_);
lean_dec_ref(v___y_3888_);
v___x_3892_ = lean_nat_sub(v_endExclusive_3890_, v_startInclusive_3889_);
lean_dec(v_startInclusive_3889_);
lean_dec(v_endExclusive_3890_);
v_decide_3893_ = lean_nat_dec_eq(v___x_3891_, v___x_3892_);
lean_dec(v___x_3892_);
lean_dec(v___x_3891_);
if (v_decide_3893_ == 0)
{
goto v___jp_3877_;
}
else
{
lean_object* v___x_3894_; 
lean_inc_ref(v___x_3867_);
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3867_);
v___y_3869_ = v___x_3894_;
goto v___jp_3868_;
}
}
v___jp_3895_:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v_startInclusive_3898_; lean_object* v_endExclusive_3899_; 
v___x_3896_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3897_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3896_);
v_startInclusive_3898_ = lean_ctor_get(v___x_3897_, 1);
lean_inc(v_startInclusive_3898_);
v_endExclusive_3899_ = lean_ctor_get(v___x_3897_, 2);
lean_inc(v_endExclusive_3899_);
v___y_3888_ = v___x_3897_;
v_startInclusive_3889_ = v_startInclusive_3898_;
v_endExclusive_3890_ = v_endExclusive_3899_;
goto v___jp_3887_;
}
v___jp_3900_:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v___x_3901_ = lean_string_utf8_byte_size(v___x_3867_);
lean_inc_ref(v___x_3867_);
v___x_3902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3867_);
lean_ctor_set(v___x_3902_, 1, v___x_3845_);
lean_ctor_set(v___x_3902_, 2, v___x_3901_);
v___x_3903_ = l_Substring_Raw_nextn(v___x_3902_, v___x_3863_, v___x_3845_);
lean_dec_ref_known(v___x_3902_, 3);
v___x_3904_ = lean_string_is_valid_pos(v___x_3867_, v___x_3903_);
if (v___x_3904_ == 0)
{
lean_dec(v___x_3903_);
goto v___jp_3895_;
}
else
{
uint8_t v___x_3905_; 
v___x_3905_ = lean_string_is_valid_pos(v___x_3867_, v___x_3901_);
if (v___x_3905_ == 0)
{
lean_dec(v___x_3903_);
goto v___jp_3895_;
}
else
{
uint8_t v___x_3906_; 
v___x_3906_ = lean_nat_dec_le(v___x_3903_, v___x_3901_);
if (v___x_3906_ == 0)
{
lean_dec(v___x_3903_);
goto v___jp_3895_;
}
else
{
lean_object* v___x_3907_; 
lean_inc(v___x_3903_);
lean_inc_ref(v___x_3867_);
v___x_3907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3867_);
lean_ctor_set(v___x_3907_, 1, v___x_3903_);
lean_ctor_set(v___x_3907_, 2, v___x_3901_);
v___y_3888_ = v___x_3907_;
v_startInclusive_3889_ = v___x_3903_;
v_endExclusive_3890_ = v___x_3901_;
goto v___jp_3887_;
}
}
}
}
v___jp_3908_:
{
uint32_t v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = 95;
v___x_3911_ = lean_uint32_dec_eq(v___y_3909_, v___x_3910_);
if (v___x_3911_ == 0)
{
uint8_t v___x_3912_; 
v___x_3912_ = l_Lean_isLetterLike(v___y_3909_);
if (v___x_3912_ == 0)
{
goto v___jp_3877_;
}
else
{
goto v___jp_3900_;
}
}
else
{
goto v___jp_3900_;
}
}
v___jp_3913_:
{
uint32_t v___x_3915_; uint8_t v___x_3916_; 
v___x_3915_ = 97;
v___x_3916_ = lean_uint32_dec_le(v___x_3915_, v___y_3914_);
if (v___x_3916_ == 0)
{
v___y_3909_ = v___y_3914_;
goto v___jp_3908_;
}
else
{
uint32_t v___x_3917_; uint8_t v___x_3918_; 
v___x_3917_ = 122;
v___x_3918_ = lean_uint32_dec_le(v___y_3914_, v___x_3917_);
if (v___x_3918_ == 0)
{
v___y_3909_ = v___y_3914_;
goto v___jp_3908_;
}
else
{
goto v___jp_3900_;
}
}
}
v___jp_3919_:
{
uint32_t v___x_3921_; uint8_t v___x_3922_; 
v___x_3921_ = 65;
v___x_3922_ = lean_uint32_dec_le(v___x_3921_, v___y_3920_);
if (v___x_3922_ == 0)
{
v___y_3914_ = v___y_3920_;
goto v___jp_3913_;
}
else
{
uint32_t v___x_3923_; uint8_t v___x_3924_; 
v___x_3923_ = 90;
v___x_3924_ = lean_uint32_dec_le(v___y_3920_, v___x_3923_);
if (v___x_3924_ == 0)
{
v___y_3914_ = v___y_3920_;
goto v___jp_3913_;
}
else
{
goto v___jp_3900_;
}
}
}
v___jp_3925_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_string_utf8_byte_size(v___x_3867_);
lean_inc_ref(v___x_3867_);
v___x_3927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3867_);
lean_ctor_set(v___x_3927_, 1, v___x_3845_);
lean_ctor_set(v___x_3927_, 2, v___x_3926_);
v___x_3928_ = l_String_Slice_Pos_get_x3f(v___x_3927_, v___x_3845_);
lean_dec_ref_known(v___x_3927_, 3);
if (lean_obj_tag(v___x_3928_) == 0)
{
uint32_t v___x_3929_; 
v___x_3929_ = 65;
v___y_3920_ = v___x_3929_;
goto v___jp_3919_;
}
else
{
lean_object* v_val_3930_; uint32_t v___x_3931_; 
v_val_3930_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_val_3930_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3931_ = lean_unbox_uint32(v_val_3930_);
lean_dec(v_val_3930_);
v___y_3920_ = v___x_3931_;
goto v___jp_3919_;
}
}
v___jp_3932_:
{
uint8_t v___x_3933_; 
v___x_3933_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3867_, v___x_3863_);
if (v___x_3933_ == 0)
{
goto v___jp_3925_;
}
else
{
lean_object* v___x_3934_; 
lean_inc_ref(v___x_3867_);
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3867_);
v___y_3869_ = v___x_3934_;
goto v___jp_3868_;
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_del_object(v___x_3853_);
lean_dec(v_a_3850_);
v_a_3955_ = lean_ctor_get(v___x_3864_, 0);
v_a_3956_ = lean_ctor_get(v___x_3864_, 1);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3864_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_inc(v_a_3955_);
lean_dec(v___x_3864_);
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
v___jp_3855_:
{
lean_object* v___x_3859_; lean_object* v___x_3861_; 
v___x_3859_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_3850_, v___y_3857_, v___y_3858_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 1, v___y_3856_);
lean_ctor_set(v___x_3853_, 0, v___x_3859_);
v___x_3861_ = v___x_3853_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v___y_3856_);
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
else
{
return v___x_3849_;
}
}
else
{
lean_object* v_a_3965_; lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
v_a_3965_ = lean_ctor_get(v___x_3846_, 0);
v_a_3966_ = lean_ctor_get(v___x_3846_, 1);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3846_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_inc(v_a_3965_);
lean_dec(v___x_3846_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3965_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_a_3966_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object* v_stx_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Fmt_fmtPostfixOperator(v_stx_3974_, v_a_3975_, v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_stx_3974_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t v_sz_3978_, size_t v_i_3979_, lean_object* v_bs_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
uint8_t v___x_3983_; 
v___x_3983_ = lean_usize_dec_lt(v_i_3979_, v_sz_3978_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v_bs_3980_);
lean_ctor_set(v___x_3984_, 1, v___y_3982_);
return v___x_3984_;
}
else
{
lean_object* v_v_3985_; lean_object* v_elseTk_3986_; lean_object* v_ifTk_3987_; lean_object* v_cond_3988_; lean_object* v_thenTk_3989_; lean_object* v_body_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4051_; 
v_v_3985_ = lean_array_uget(v_bs_3980_, v_i_3979_);
v_elseTk_3986_ = lean_ctor_get(v_v_3985_, 0);
v_ifTk_3987_ = lean_ctor_get(v_v_3985_, 1);
v_cond_3988_ = lean_ctor_get(v_v_3985_, 2);
v_thenTk_3989_ = lean_ctor_get(v_v_3985_, 3);
v_body_3990_ = lean_ctor_get(v_v_3985_, 4);
v_isSharedCheck_4051_ = !lean_is_exclusive(v_v_3985_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_3992_ = v_v_3985_;
v_isShared_3993_ = v_isSharedCheck_4051_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_body_3990_);
lean_inc(v_thenTk_3989_);
lean_inc(v_cond_3988_);
lean_inc(v_ifTk_3987_);
lean_inc(v_elseTk_3986_);
lean_dec(v_v_3985_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4051_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; 
v___x_3994_ = l_Lean_Fmt_fmt(v_elseTk_3986_, v___y_3981_, v___y_3982_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v_a_3996_; lean_object* v___x_3997_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
v_a_3996_ = lean_ctor_get(v___x_3994_, 1);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3994_, 2);
v___x_3997_ = l_Lean_Fmt_fmt(v_ifTk_3987_, v___y_3981_, v_a_3996_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v_a_3999_; lean_object* v___x_4000_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
v_a_3999_ = lean_ctor_get(v___x_3997_, 1);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3997_, 2);
v___x_4000_ = l_Lean_Fmt_fmt(v_thenTk_3989_, v___y_3981_, v_a_3999_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v_a_4002_; lean_object* v___x_4003_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
v_a_4002_ = lean_ctor_get(v___x_4000_, 1);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4000_, 2);
v___x_4003_ = l_Lean_Fmt_fmt(v_body_3990_, v___y_3981_, v_a_4002_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v_a_4005_; lean_object* v___x_4006_; lean_object* v_bs_x27_4007_; lean_object* v___x_4009_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
v_a_4005_ = lean_ctor_get(v___x_4003_, 1);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4003_, 2);
v___x_4006_ = lean_unsigned_to_nat(0u);
v_bs_x27_4007_ = lean_array_uset(v_bs_3980_, v_i_3979_, v___x_4006_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 4, v_a_4004_);
lean_ctor_set(v___x_3992_, 3, v_a_4001_);
lean_ctor_set(v___x_3992_, 1, v_a_3998_);
lean_ctor_set(v___x_3992_, 0, v_a_3995_);
v___x_4009_ = v___x_3992_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_3995_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v_a_3998_);
lean_ctor_set(v_reuseFailAlloc_4014_, 2, v_cond_3988_);
lean_ctor_set(v_reuseFailAlloc_4014_, 3, v_a_4001_);
lean_ctor_set(v_reuseFailAlloc_4014_, 4, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
size_t v___x_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_add(v_i_3979_, v___x_4010_);
v___x_4012_ = lean_array_uset(v_bs_x27_4007_, v_i_3979_, v___x_4009_);
v_i_3979_ = v___x_4011_;
v_bs_3980_ = v___x_4012_;
v___y_3982_ = v_a_4005_;
goto _start;
}
}
else
{
lean_object* v_a_4015_; lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_a_4001_);
lean_dec(v_a_3998_);
lean_dec(v_a_3995_);
lean_del_object(v___x_3992_);
lean_dec_ref(v_cond_3988_);
lean_dec_ref(v_bs_3980_);
v_a_4015_ = lean_ctor_get(v___x_4003_, 0);
v_a_4016_ = lean_ctor_get(v___x_4003_, 1);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4003_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_inc(v_a_4015_);
lean_dec(v___x_4003_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4015_);
lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v_a_3998_);
lean_dec(v_a_3995_);
lean_del_object(v___x_3992_);
lean_dec(v_body_3990_);
lean_dec_ref(v_cond_3988_);
lean_dec_ref(v_bs_3980_);
v_a_4024_ = lean_ctor_get(v___x_4000_, 0);
v_a_4025_ = lean_ctor_get(v___x_4000_, 1);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4000_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_inc(v_a_4024_);
lean_dec(v___x_4000_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4024_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_object* v_a_4033_; lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4041_; 
lean_dec(v_a_3995_);
lean_del_object(v___x_3992_);
lean_dec(v_body_3990_);
lean_dec(v_thenTk_3989_);
lean_dec_ref(v_cond_3988_);
lean_dec_ref(v_bs_3980_);
v_a_4033_ = lean_ctor_get(v___x_3997_, 0);
v_a_4034_ = lean_ctor_get(v___x_3997_, 1);
v_isSharedCheck_4041_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4041_ == 0)
{
v___x_4036_ = v___x_3997_;
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_inc(v_a_4033_);
lean_dec(v___x_3997_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4041_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4039_; 
if (v_isShared_4037_ == 0)
{
v___x_4039_ = v___x_4036_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v_a_4033_);
lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_del_object(v___x_3992_);
lean_dec(v_body_3990_);
lean_dec(v_thenTk_3989_);
lean_dec_ref(v_cond_3988_);
lean_dec(v_ifTk_3987_);
lean_dec_ref(v_bs_3980_);
v_a_4042_ = lean_ctor_get(v___x_3994_, 0);
v_a_4043_ = lean_ctor_get(v___x_3994_, 1);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_3994_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_inc(v_a_4042_);
lean_dec(v___x_3994_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4042_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object* v_sz_4052_, lean_object* v_i_4053_, lean_object* v_bs_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
size_t v_sz_boxed_4057_; size_t v_i_boxed_4058_; lean_object* v_res_4059_; 
v_sz_boxed_4057_ = lean_unbox_usize(v_sz_4052_);
lean_dec(v_sz_4052_);
v_i_boxed_4058_ = lean_unbox_usize(v_i_4053_);
lean_dec(v_i_4053_);
v_res_4059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_boxed_4057_, v_i_boxed_4058_, v_bs_4054_, v___y_4055_, v___y_4056_);
lean_dec_ref(v___y_4055_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object* v_a_4060_, lean_object* v_x_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v_a_4060_);
v___x_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v___y_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object* v_a_4066_, lean_object* v_x_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4066_, v_x_4067_, v___y_4068_, v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec_ref(v_x_4067_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object* v___x_4071_, lean_object* v_val_4072_, lean_object* v_elseIfs_4073_, lean_object* v_ifTk_4074_, lean_object* v_cond_4075_, lean_object* v_thenTk_4076_, lean_object* v_thenBody_4077_, lean_object* v_a_4078_, lean_object* v_____r_4079_, lean_object* v_elseBody_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_inc(v_elseBody_4080_);
v___x_4083_ = l_Lean_Syntax_getKind(v_elseBody_4080_);
v___x_4084_ = l_Lean_Fmt_getConditionalFormatter_x3f(v___x_4071_, v___x_4083_);
lean_dec(v___x_4083_);
if (lean_obj_tag(v___x_4084_) == 1)
{
lean_object* v_val_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4145_; 
v_val_4085_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4087_ = v___x_4084_;
v_isShared_4088_ = v_isSharedCheck_4145_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_val_4085_);
lean_dec(v___x_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4145_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; 
lean_inc_ref(v___y_4081_);
v___x_4089_ = lean_apply_3(v_val_4085_, v_elseBody_4080_, v___y_4081_, v___y_4082_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
if (lean_obj_tag(v_a_4090_) == 1)
{
lean_object* v_val_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4123_; 
lean_del_object(v___x_4087_);
lean_dec_ref(v_a_4078_);
v_val_4091_ = lean_ctor_get(v_a_4090_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v_a_4090_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4093_ = v_a_4090_;
v_isShared_4094_ = v_isSharedCheck_4123_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_val_4091_);
lean_dec(v_a_4090_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4123_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4121_; 
v_a_4095_ = lean_ctor_get(v___x_4089_, 1);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4121_ == 0)
{
lean_object* v_unused_4122_; 
v_unused_4122_ = lean_ctor_get(v___x_4089_, 0);
lean_dec(v_unused_4122_);
v___x_4097_ = v___x_4089_;
v_isShared_4098_ = v_isSharedCheck_4121_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4089_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4121_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v_ifTk_4099_; lean_object* v_cond_4100_; lean_object* v_thenTk_4101_; lean_object* v_thenBody_4102_; lean_object* v_elseTk_x3f_4103_; lean_object* v_elseBody_x3f_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4119_; 
v_ifTk_4099_ = lean_ctor_get(v_val_4091_, 0);
v_cond_4100_ = lean_ctor_get(v_val_4091_, 1);
v_thenTk_4101_ = lean_ctor_get(v_val_4091_, 2);
v_thenBody_4102_ = lean_ctor_get(v_val_4091_, 3);
v_elseTk_x3f_4103_ = lean_ctor_get(v_val_4091_, 5);
v_elseBody_x3f_4104_ = lean_ctor_get(v_val_4091_, 6);
v_isSharedCheck_4119_ = !lean_is_exclusive(v_val_4091_);
if (v_isSharedCheck_4119_ == 0)
{
lean_object* v_unused_4120_; 
v_unused_4120_ = lean_ctor_get(v_val_4091_, 4);
lean_dec(v_unused_4120_);
v___x_4106_ = v_val_4091_;
v_isShared_4107_ = v_isSharedCheck_4119_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_elseBody_x3f_4104_);
lean_inc(v_elseTk_x3f_4103_);
lean_inc(v_thenBody_4102_);
lean_inc(v_thenTk_4101_);
lean_inc(v_cond_4100_);
lean_inc(v_ifTk_4099_);
lean_dec(v_val_4091_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4119_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4111_; 
v___x_4108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4108_, 0, v_val_4072_);
lean_ctor_set(v___x_4108_, 1, v_ifTk_4099_);
lean_ctor_set(v___x_4108_, 2, v_cond_4100_);
lean_ctor_set(v___x_4108_, 3, v_thenTk_4101_);
lean_ctor_set(v___x_4108_, 4, v_thenBody_4102_);
v___x_4109_ = lean_array_push(v_elseIfs_4073_, v___x_4108_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 4, v___x_4109_);
lean_ctor_set(v___x_4106_, 3, v_thenBody_4077_);
lean_ctor_set(v___x_4106_, 2, v_thenTk_4076_);
lean_ctor_set(v___x_4106_, 1, v_cond_4075_);
lean_ctor_set(v___x_4106_, 0, v_ifTk_4074_);
v___x_4111_ = v___x_4106_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_ifTk_4074_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_cond_4075_);
lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_thenTk_4076_);
lean_ctor_set(v_reuseFailAlloc_4118_, 3, v_thenBody_4077_);
lean_ctor_set(v_reuseFailAlloc_4118_, 4, v___x_4109_);
lean_ctor_set(v_reuseFailAlloc_4118_, 5, v_elseTk_x3f_4103_);
lean_ctor_set(v_reuseFailAlloc_4118_, 6, v_elseBody_x3f_4104_);
v___x_4111_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4113_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 0, v___x_4111_);
v___x_4113_ = v___x_4093_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4115_; 
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4113_);
v___x_4115_ = v___x_4097_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4113_);
lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_a_4095_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v_a_4090_);
lean_dec(v_thenBody_4077_);
lean_dec(v_thenTk_4076_);
lean_dec_ref(v_cond_4075_);
lean_dec(v_ifTk_4074_);
lean_dec_ref(v_elseIfs_4073_);
lean_dec(v_val_4072_);
v_a_4124_ = lean_ctor_get(v___x_4089_, 1);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4134_ == 0)
{
lean_object* v_unused_4135_; 
v_unused_4135_ = lean_ctor_get(v___x_4089_, 0);
lean_dec(v_unused_4135_);
v___x_4126_ = v___x_4089_;
v_isShared_4127_ = v_isSharedCheck_4134_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4089_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4134_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 0);
lean_ctor_set(v___x_4087_, 0, v_a_4078_);
v___x_4129_ = v___x_4087_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4078_);
v___x_4129_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4131_; 
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v___x_4129_);
v___x_4131_ = v___x_4126_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_a_4124_);
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
}
else
{
lean_object* v_a_4136_; lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_del_object(v___x_4087_);
lean_dec_ref(v_a_4078_);
lean_dec(v_thenBody_4077_);
lean_dec(v_thenTk_4076_);
lean_dec_ref(v_cond_4075_);
lean_dec(v_ifTk_4074_);
lean_dec_ref(v_elseIfs_4073_);
lean_dec(v_val_4072_);
v_a_4136_ = lean_ctor_get(v___x_4089_, 0);
v_a_4137_ = lean_ctor_get(v___x_4089_, 1);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4089_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_inc(v_a_4136_);
lean_dec(v___x_4089_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4136_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
else
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
lean_dec(v___x_4084_);
lean_dec(v_elseBody_4080_);
lean_dec(v_thenBody_4077_);
lean_dec(v_thenTk_4076_);
lean_dec_ref(v_cond_4075_);
lean_dec(v_ifTk_4074_);
lean_dec_ref(v_elseIfs_4073_);
lean_dec(v_val_4072_);
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_a_4078_);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
lean_ctor_set(v___x_4147_, 1, v___y_4082_);
return v___x_4147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object* v___x_4148_, lean_object* v_val_4149_, lean_object* v_elseIfs_4150_, lean_object* v_ifTk_4151_, lean_object* v_cond_4152_, lean_object* v_thenTk_4153_, lean_object* v_thenBody_4154_, lean_object* v_a_4155_, lean_object* v_____r_4156_, lean_object* v_elseBody_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4148_, v_val_4149_, v_elseIfs_4150_, v_ifTk_4151_, v_cond_4152_, v_thenTk_4153_, v_thenBody_4154_, v_a_4155_, v_____r_4156_, v_elseBody_4157_, v___y_4158_, v___y_4159_);
lean_dec_ref(v___y_4158_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object* v___x_4175_, lean_object* v_a_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___y_4180_; lean_object* v_elseTk_x3f_4204_; 
v_elseTk_x3f_4204_ = lean_ctor_get(v_a_4176_, 5);
if (lean_obj_tag(v_elseTk_x3f_4204_) == 1)
{
lean_object* v_elseBody_x3f_4205_; 
v_elseBody_x3f_4205_ = lean_ctor_get(v_a_4176_, 6);
if (lean_obj_tag(v_elseBody_x3f_4205_) == 1)
{
lean_object* v_ifTk_4206_; lean_object* v_cond_4207_; lean_object* v_thenTk_4208_; lean_object* v_thenBody_4209_; lean_object* v_elseIfs_4210_; lean_object* v_val_4211_; lean_object* v_val_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; 
v_ifTk_4206_ = lean_ctor_get(v_a_4176_, 0);
lean_inc(v_ifTk_4206_);
v_cond_4207_ = lean_ctor_get(v_a_4176_, 1);
lean_inc_ref(v_cond_4207_);
v_thenTk_4208_ = lean_ctor_get(v_a_4176_, 2);
lean_inc(v_thenTk_4208_);
v_thenBody_4209_ = lean_ctor_get(v_a_4176_, 3);
lean_inc(v_thenBody_4209_);
v_elseIfs_4210_ = lean_ctor_get(v_a_4176_, 4);
lean_inc_ref(v_elseIfs_4210_);
v_val_4211_ = lean_ctor_get(v_elseTk_x3f_4204_, 0);
lean_inc(v_val_4211_);
v_val_4212_ = lean_ctor_get(v_elseBody_x3f_4205_, 0);
v___x_4213_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3));
lean_inc(v_val_4212_);
v___x_4214_ = l_Lean_Syntax_isOfKind(v_val_4212_, v___x_4213_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
lean_inc(v_val_4212_);
v___x_4215_ = lean_box(0);
lean_inc_ref(v___x_4175_);
v___x_4216_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4175_, v_val_4211_, v_elseIfs_4210_, v_ifTk_4206_, v_cond_4207_, v_thenTk_4208_, v_thenBody_4209_, v_a_4176_, v___x_4215_, v_val_4212_, v___y_4177_, v___y_4178_);
v___y_4180_ = v___x_4216_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = l_Lean_Syntax_getArg(v_val_4212_, v___x_4217_);
v___x_4219_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5));
lean_inc(v___x_4218_);
v___x_4220_ = l_Lean_Syntax_isOfKind(v___x_4218_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
lean_inc(v_val_4212_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
lean_inc_ref(v___x_4175_);
v___x_4222_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4175_, v_val_4211_, v_elseIfs_4210_, v_ifTk_4206_, v_cond_4207_, v_thenTk_4208_, v_thenBody_4209_, v_a_4176_, v___x_4221_, v_val_4212_, v___y_4177_, v___y_4178_);
v___y_4180_ = v___x_4222_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4223_ = l_Lean_Syntax_getArg(v___x_4218_, v___x_4217_);
lean_dec(v___x_4218_);
v___x_4224_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4223_);
v___x_4225_ = l_Lean_Syntax_matchesNull(v___x_4223_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_inc(v_val_4212_);
lean_dec(v___x_4223_);
v___x_4226_ = lean_box(0);
lean_inc_ref(v___x_4175_);
v___x_4227_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4175_, v_val_4211_, v_elseIfs_4210_, v_ifTk_4206_, v_cond_4207_, v_thenTk_4208_, v_thenBody_4209_, v_a_4176_, v___x_4226_, v_val_4212_, v___y_4177_, v___y_4178_);
v___y_4180_ = v___x_4227_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4228_ = l_Lean_Syntax_getArg(v___x_4223_, v___x_4217_);
lean_dec(v___x_4223_);
v___x_4229_ = lean_box(0);
lean_inc_ref(v___x_4175_);
v___x_4230_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4175_, v_val_4211_, v_elseIfs_4210_, v_ifTk_4206_, v_cond_4207_, v_thenTk_4208_, v_thenBody_4209_, v_a_4176_, v___x_4229_, v___x_4228_, v___y_4177_, v___y_4178_);
v___y_4180_ = v___x_4230_;
goto v___jp_4179_;
}
}
}
}
else
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
lean_inc(v_elseBody_x3f_4205_);
lean_inc_ref(v_elseTk_x3f_4204_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v_elseTk_x3f_4204_);
lean_ctor_set(v___x_4231_, 1, v_elseBody_x3f_4205_);
v___x_4232_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4176_, v___x_4231_, v___y_4177_, v___y_4178_);
lean_dec_ref_known(v___x_4231_, 2);
v___y_4180_ = v___x_4232_;
goto v___jp_4179_;
}
}
else
{
lean_object* v_elseBody_x3f_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v_elseBody_x3f_4233_ = lean_ctor_get(v_a_4176_, 6);
lean_inc(v_elseBody_x3f_4233_);
lean_inc(v_elseTk_x3f_4204_);
v___x_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4234_, 0, v_elseTk_x3f_4204_);
lean_ctor_set(v___x_4234_, 1, v_elseBody_x3f_4233_);
v___x_4235_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4176_, v___x_4234_, v___y_4177_, v___y_4178_);
lean_dec_ref_known(v___x_4234_, 2);
v___y_4180_ = v___x_4235_;
goto v___jp_4179_;
}
v___jp_4179_:
{
if (lean_obj_tag(v___y_4180_) == 0)
{
lean_object* v_a_4181_; 
v_a_4181_ = lean_ctor_get(v___y_4180_, 0);
lean_inc(v_a_4181_);
if (lean_obj_tag(v_a_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4190_; 
lean_dec_ref(v___x_4175_);
v_a_4182_ = lean_ctor_get(v___y_4180_, 1);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___y_4180_);
if (v_isSharedCheck_4190_ == 0)
{
lean_object* v_unused_4191_; 
v_unused_4191_ = lean_ctor_get(v___y_4180_, 0);
lean_dec(v_unused_4191_);
v___x_4184_ = v___y_4180_;
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___y_4180_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4190_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v_a_4186_; lean_object* v___x_4188_; 
v_a_4186_ = lean_ctor_get(v_a_4181_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v_a_4181_, 1);
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 0, v_a_4186_);
v___x_4188_ = v___x_4184_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4186_);
lean_ctor_set(v_reuseFailAlloc_4189_, 1, v_a_4182_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
else
{
lean_object* v_a_4192_; lean_object* v_a_4193_; 
v_a_4192_ = lean_ctor_get(v___y_4180_, 1);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___y_4180_, 2);
v_a_4193_ = lean_ctor_get(v_a_4181_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v_a_4181_, 1);
v_a_4176_ = v_a_4193_;
v___y_4178_ = v_a_4192_;
goto _start;
}
}
else
{
lean_object* v_a_4195_; lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_dec_ref(v___x_4175_);
v_a_4195_ = lean_ctor_get(v___y_4180_, 0);
v_a_4196_ = lean_ctor_get(v___y_4180_, 1);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___y_4180_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___y_4180_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_inc(v_a_4195_);
lean_dec(v___y_4180_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4195_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object* v___x_4236_, lean_object* v_a_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4236_, v_a_4237_, v___y_4238_, v___y_4239_);
lean_dec_ref(v___y_4238_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object* v_initialFmt_4241_, lean_object* v_stx_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; uint8_t v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v_env_4272_; lean_object* v___x_4273_; 
v_env_4272_ = lean_ctor_get(v_a_4243_, 0);
lean_inc_ref(v_a_4243_);
lean_inc(v_stx_4242_);
v___x_4273_ = lean_apply_3(v_initialFmt_4241_, v_stx_4242_, v_a_4243_, v_a_4244_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
if (lean_obj_tag(v_a_4274_) == 1)
{
lean_object* v_a_4275_; lean_object* v_val_4276_; lean_object* v___x_4277_; 
v_a_4275_ = lean_ctor_get(v___x_4273_, 1);
lean_inc(v_a_4275_);
lean_dec_ref_known(v___x_4273_, 2);
v_val_4276_ = lean_ctor_get(v_a_4274_, 0);
lean_inc(v_val_4276_);
lean_dec_ref_known(v_a_4274_, 1);
v___x_4277_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_4242_, v_a_4243_, v_a_4275_);
lean_dec(v_stx_4242_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v_a_4279_; uint8_t v___y_4281_; uint8_t v___x_4331_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
v_a_4279_ = lean_ctor_get(v___x_4277_, 1);
lean_inc(v_a_4279_);
lean_dec_ref_known(v___x_4277_, 2);
v___x_4331_ = lean_unbox(v_a_4278_);
lean_dec(v_a_4278_);
if (v___x_4331_ == 0)
{
uint8_t v___x_4332_; 
v___x_4332_ = 1;
v___y_4281_ = v___x_4332_;
goto v___jp_4280_;
}
else
{
uint8_t v___x_4333_; 
v___x_4333_ = 0;
v___y_4281_ = v___x_4333_;
goto v___jp_4280_;
}
v___jp_4280_:
{
lean_object* v___x_4282_; 
lean_inc_ref(v_env_4272_);
v___x_4282_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v_env_4272_, v_val_4276_, v_a_4243_, v_a_4279_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v_a_4284_; lean_object* v_ifTk_4285_; lean_object* v_cond_4286_; lean_object* v_thenTk_4287_; lean_object* v_thenBody_4288_; lean_object* v_elseIfs_4289_; lean_object* v_elseTk_x3f_4290_; lean_object* v_elseBody_x3f_4291_; lean_object* v___x_4292_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_a_4283_);
v_a_4284_ = lean_ctor_get(v___x_4282_, 1);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4282_, 2);
v_ifTk_4285_ = lean_ctor_get(v_a_4283_, 0);
lean_inc(v_ifTk_4285_);
v_cond_4286_ = lean_ctor_get(v_a_4283_, 1);
lean_inc_ref(v_cond_4286_);
v_thenTk_4287_ = lean_ctor_get(v_a_4283_, 2);
lean_inc(v_thenTk_4287_);
v_thenBody_4288_ = lean_ctor_get(v_a_4283_, 3);
lean_inc(v_thenBody_4288_);
v_elseIfs_4289_ = lean_ctor_get(v_a_4283_, 4);
lean_inc_ref(v_elseIfs_4289_);
v_elseTk_x3f_4290_ = lean_ctor_get(v_a_4283_, 5);
lean_inc(v_elseTk_x3f_4290_);
v_elseBody_x3f_4291_ = lean_ctor_get(v_a_4283_, 6);
lean_inc(v_elseBody_x3f_4291_);
lean_dec(v_a_4283_);
v___x_4292_ = l_Lean_Fmt_fmt(v_ifTk_4285_, v_a_4243_, v_a_4284_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v_a_4294_; lean_object* v___x_4295_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
v_a_4294_ = lean_ctor_get(v___x_4292_, 1);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4292_, 2);
v___x_4295_ = l_Lean_Fmt_fmt(v_thenTk_4287_, v_a_4243_, v_a_4294_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v_a_4297_; lean_object* v___x_4298_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
v_a_4297_ = lean_ctor_get(v___x_4295_, 1);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4295_, 2);
v___x_4298_ = l_Lean_Fmt_fmt(v_thenBody_4288_, v_a_4243_, v_a_4297_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v_a_4300_; size_t v_sz_4301_; size_t v___x_4302_; lean_object* v___x_4303_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
v_a_4300_ = lean_ctor_get(v___x_4298_, 1);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4298_, 2);
v_sz_4301_ = lean_array_size(v_elseIfs_4289_);
v___x_4302_ = ((size_t)0ULL);
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_4301_, v___x_4302_, v_elseIfs_4289_, v_a_4243_, v_a_4300_);
if (lean_obj_tag(v___x_4303_) == 0)
{
if (lean_obj_tag(v_elseTk_x3f_4290_) == 0)
{
lean_object* v_a_4304_; lean_object* v_a_4305_; lean_object* v___x_4306_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
v_a_4305_ = lean_ctor_get(v___x_4303_, 1);
lean_inc(v_a_4305_);
lean_dec_ref_known(v___x_4303_, 2);
v___x_4306_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4258_ = v_elseBody_x3f_4291_;
v___y_4259_ = v_a_4296_;
v___y_4260_ = v_a_4305_;
v___y_4261_ = v_a_4299_;
v___y_4262_ = v_cond_4286_;
v___y_4263_ = v___y_4281_;
v___y_4264_ = v_a_4293_;
v___y_4265_ = v_a_4304_;
v___y_4266_ = v___x_4306_;
goto v___jp_4257_;
}
else
{
lean_object* v_a_4307_; lean_object* v_a_4308_; lean_object* v_val_4309_; lean_object* v___x_4310_; 
v_a_4307_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4307_);
v_a_4308_ = lean_ctor_get(v___x_4303_, 1);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4303_, 2);
v_val_4309_ = lean_ctor_get(v_elseTk_x3f_4290_, 0);
lean_inc(v_val_4309_);
lean_dec_ref_known(v_elseTk_x3f_4290_, 1);
v___x_4310_ = l_Lean_Fmt_fmt(v_val_4309_, v_a_4243_, v_a_4308_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v_a_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
v_a_4312_ = lean_ctor_get(v___x_4310_, 1);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4310_, 2);
v___y_4258_ = v_elseBody_x3f_4291_;
v___y_4259_ = v_a_4296_;
v___y_4260_ = v_a_4312_;
v___y_4261_ = v_a_4299_;
v___y_4262_ = v_cond_4286_;
v___y_4263_ = v___y_4281_;
v___y_4264_ = v_a_4293_;
v___y_4265_ = v_a_4307_;
v___y_4266_ = v_a_4311_;
goto v___jp_4257_;
}
else
{
lean_dec(v_a_4307_);
lean_dec(v_a_4299_);
lean_dec(v_a_4296_);
lean_dec(v_a_4293_);
lean_dec(v_elseBody_x3f_4291_);
lean_dec_ref(v_cond_4286_);
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4321_; 
lean_dec(v_a_4299_);
lean_dec(v_a_4296_);
lean_dec(v_a_4293_);
lean_dec(v_elseBody_x3f_4291_);
lean_dec(v_elseTk_x3f_4290_);
lean_dec_ref(v_cond_4286_);
v_a_4313_ = lean_ctor_get(v___x_4303_, 0);
v_a_4314_ = lean_ctor_get(v___x_4303_, 1);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4316_ = v___x_4303_;
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_inc(v_a_4313_);
lean_dec(v___x_4303_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4321_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4319_; 
if (v_isShared_4317_ == 0)
{
v___x_4319_ = v___x_4316_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_a_4313_);
lean_ctor_set(v_reuseFailAlloc_4320_, 1, v_a_4314_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
else
{
lean_dec(v_a_4296_);
lean_dec(v_a_4293_);
lean_dec(v_elseBody_x3f_4291_);
lean_dec(v_elseTk_x3f_4290_);
lean_dec_ref(v_elseIfs_4289_);
lean_dec_ref(v_cond_4286_);
return v___x_4298_;
}
}
else
{
lean_dec(v_a_4293_);
lean_dec(v_elseBody_x3f_4291_);
lean_dec(v_elseTk_x3f_4290_);
lean_dec_ref(v_elseIfs_4289_);
lean_dec(v_thenBody_4288_);
lean_dec_ref(v_cond_4286_);
return v___x_4295_;
}
}
else
{
lean_dec(v_elseBody_x3f_4291_);
lean_dec(v_elseTk_x3f_4290_);
lean_dec_ref(v_elseIfs_4289_);
lean_dec(v_thenBody_4288_);
lean_dec(v_thenTk_4287_);
lean_dec_ref(v_cond_4286_);
return v___x_4292_;
}
}
else
{
lean_object* v_a_4322_; lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_a_4322_ = lean_ctor_get(v___x_4282_, 0);
v_a_4323_ = lean_ctor_get(v___x_4282_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4282_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_inc(v_a_4322_);
lean_dec(v___x_4282_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4322_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec(v_val_4276_);
v_a_4334_ = lean_ctor_get(v___x_4277_, 0);
v_a_4335_ = lean_ctor_get(v___x_4277_, 1);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4277_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_inc(v_a_4334_);
lean_dec(v___x_4277_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4334_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_a_4274_);
lean_dec(v_stx_4242_);
v_a_4343_ = lean_ctor_get(v___x_4273_, 1);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4351_ == 0)
{
lean_object* v_unused_4352_; 
v_unused_4352_ = lean_ctor_get(v___x_4273_, 0);
lean_dec(v_unused_4352_);
v___x_4345_ = v___x_4273_;
v_isShared_4346_ = v_isSharedCheck_4351_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4273_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4351_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4347_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4346_ == 0)
{
lean_ctor_set_tag(v___x_4345_, 1);
lean_ctor_set(v___x_4345_, 0, v___x_4347_);
v___x_4349_ = v___x_4345_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4347_);
lean_ctor_set(v_reuseFailAlloc_4350_, 1, v_a_4343_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4353_; lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec(v_stx_4242_);
v_a_4353_ = lean_ctor_get(v___x_4273_, 0);
v_a_4354_ = lean_ctor_get(v___x_4273_, 1);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4273_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_inc(v_a_4353_);
lean_dec(v___x_4273_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4353_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
v___jp_4245_:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = l_Lean_Fmt_Layouts_conditional(v___y_4251_, v___y_4249_, v___y_4246_, v___y_4248_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4250_);
lean_dec_ref(v___y_4252_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
lean_ctor_set(v___x_4256_, 1, v___y_4247_);
return v___x_4256_;
}
v___jp_4257_:
{
if (lean_obj_tag(v___y_4258_) == 0)
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4246_ = v___y_4259_;
v___y_4247_ = v___y_4260_;
v___y_4248_ = v___y_4261_;
v___y_4249_ = v___y_4262_;
v___y_4250_ = v___y_4263_;
v___y_4251_ = v___y_4264_;
v___y_4252_ = v___y_4265_;
v___y_4253_ = v___y_4266_;
v___y_4254_ = v___x_4267_;
goto v___jp_4245_;
}
else
{
lean_object* v_val_4268_; lean_object* v___x_4269_; 
v_val_4268_ = lean_ctor_get(v___y_4258_, 0);
lean_inc(v_val_4268_);
lean_dec_ref_known(v___y_4258_, 1);
v___x_4269_ = l_Lean_Fmt_fmt(v_val_4268_, v_a_4243_, v___y_4260_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; lean_object* v_a_4271_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
v_a_4271_ = lean_ctor_get(v___x_4269_, 1);
lean_inc(v_a_4271_);
lean_dec_ref_known(v___x_4269_, 2);
v___y_4246_ = v___y_4259_;
v___y_4247_ = v_a_4271_;
v___y_4248_ = v___y_4261_;
v___y_4249_ = v___y_4262_;
v___y_4250_ = v___y_4263_;
v___y_4251_ = v___y_4264_;
v___y_4252_ = v___y_4265_;
v___y_4253_ = v___y_4266_;
v___y_4254_ = v_a_4270_;
goto v___jp_4245_;
}
else
{
lean_dec_ref(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec_ref(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v___y_4259_);
return v___x_4269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object* v_initialFmt_4362_, lean_object* v_stx_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_Fmt_fmtConditional(v_initialFmt_4362_, v_stx_4363_, v_a_4364_, v_a_4365_);
lean_dec_ref(v_a_4364_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object* v___x_4367_, lean_object* v_inst_4368_, lean_object* v_a_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4367_, v_a_4369_, v___y_4370_, v___y_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object* v___x_4373_, lean_object* v_inst_4374_, lean_object* v_a_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(v___x_4373_, v_inst_4374_, v_a_4375_, v___y_4376_, v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t v_sz_4379_, size_t v_i_4380_, lean_object* v_bs_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
uint8_t v___x_4384_; 
v___x_4384_ = lean_usize_dec_lt(v_i_4380_, v_sz_4379_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; 
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v_bs_4381_);
lean_ctor_set(v___x_4385_, 1, v___y_4383_);
return v___x_4385_;
}
else
{
lean_object* v_v_4386_; size_t v_sz_4387_; size_t v___x_4388_; lean_object* v___x_4389_; 
v_v_4386_ = lean_array_uget_borrowed(v_bs_4381_, v_i_4380_);
v_sz_4387_ = lean_array_size(v_v_4386_);
v___x_4388_ = ((size_t)0ULL);
lean_inc(v_v_4386_);
v___x_4389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_4387_, v___x_4388_, v_v_4386_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v_bs_x27_4393_; size_t v___x_4394_; size_t v___x_4395_; lean_object* v___x_4396_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc(v_a_4390_);
v_a_4391_ = lean_ctor_get(v___x_4389_, 1);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4389_, 2);
v___x_4392_ = lean_unsigned_to_nat(0u);
v_bs_x27_4393_ = lean_array_uset(v_bs_4381_, v_i_4380_, v___x_4392_);
v___x_4394_ = ((size_t)1ULL);
v___x_4395_ = lean_usize_add(v_i_4380_, v___x_4394_);
v___x_4396_ = lean_array_uset(v_bs_x27_4393_, v_i_4380_, v_a_4390_);
v_i_4380_ = v___x_4395_;
v_bs_4381_ = v___x_4396_;
v___y_4383_ = v_a_4391_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4381_);
return v___x_4389_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object* v_sz_4398_, lean_object* v_i_4399_, lean_object* v_bs_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
size_t v_sz_boxed_4403_; size_t v_i_boxed_4404_; lean_object* v_res_4405_; 
v_sz_boxed_4403_ = lean_unbox_usize(v_sz_4398_);
lean_dec(v_sz_4398_);
v_i_boxed_4404_ = lean_unbox_usize(v_i_4399_);
lean_dec(v_i_4399_);
v_res_4405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_boxed_4403_, v_i_boxed_4404_, v_bs_4400_, v___y_4401_, v___y_4402_);
lean_dec_ref(v___y_4401_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(size_t v_sz_4406_, size_t v_i_4407_, lean_object* v_bs_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
uint8_t v___x_4411_; 
v___x_4411_ = lean_usize_dec_lt(v_i_4407_, v_sz_4406_);
if (v___x_4411_ == 0)
{
lean_object* v___x_4412_; 
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v_bs_4408_);
lean_ctor_set(v___x_4412_, 1, v___y_4410_);
return v___x_4412_;
}
else
{
lean_object* v_v_4413_; size_t v_sz_4414_; size_t v___x_4415_; lean_object* v___x_4416_; 
v_v_4413_ = lean_array_uget_borrowed(v_bs_4408_, v_i_4407_);
v_sz_4414_ = lean_array_size(v_v_4413_);
v___x_4415_ = ((size_t)0ULL);
lean_inc(v_v_4413_);
v___x_4416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_4414_, v___x_4415_, v_v_4413_, v___y_4409_, v___y_4410_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; lean_object* v_a_4418_; lean_object* v___x_4419_; lean_object* v_bs_x27_4420_; size_t v___x_4421_; size_t v___x_4422_; lean_object* v___x_4423_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
v_a_4418_ = lean_ctor_get(v___x_4416_, 1);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4416_, 2);
v___x_4419_ = lean_unsigned_to_nat(0u);
v_bs_x27_4420_ = lean_array_uset(v_bs_4408_, v_i_4407_, v___x_4419_);
v___x_4421_ = ((size_t)1ULL);
v___x_4422_ = lean_usize_add(v_i_4407_, v___x_4421_);
v___x_4423_ = lean_array_uset(v_bs_x27_4420_, v_i_4407_, v_a_4417_);
v_i_4407_ = v___x_4422_;
v_bs_4408_ = v___x_4423_;
v___y_4410_ = v_a_4418_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4408_);
return v___x_4416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1___boxed(lean_object* v_sz_4425_, lean_object* v_i_4426_, lean_object* v_bs_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
size_t v_sz_boxed_4430_; size_t v_i_boxed_4431_; lean_object* v_res_4432_; 
v_sz_boxed_4430_ = lean_unbox_usize(v_sz_4425_);
lean_dec(v_sz_4425_);
v_i_boxed_4431_ = lean_unbox_usize(v_i_4426_);
lean_dec(v_i_4426_);
v_res_4432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_boxed_4430_, v_i_boxed_4431_, v_bs_4427_, v___y_4428_, v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object* v_bgs_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_){
_start:
{
size_t v_sz_4436_; size_t v___x_4437_; lean_object* v___x_4438_; 
v_sz_4436_ = lean_array_size(v_bgs_4433_);
v___x_4437_ = ((size_t)0ULL);
v___x_4438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_4436_, v___x_4437_, v_bgs_4433_, v_a_4434_, v_a_4435_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object* v_bgs_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l_Lean_Fmt_fmtBinderGroups(v_bgs_4439_, v_a_4440_, v_a_4441_);
lean_dec_ref(v_a_4440_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object* v_lhs_4443_, lean_object* v_rhs_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_){
_start:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_Fmt_fmt(v_lhs_4443_, v_a_4445_, v_a_4446_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v_a_4449_; lean_object* v___x_4450_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
v_a_4449_ = lean_ctor_get(v___x_4447_, 1);
lean_inc(v_a_4449_);
lean_dec_ref_known(v___x_4447_, 2);
v___x_4450_ = l_Lean_Fmt_fmt(v_rhs_4444_, v_a_4445_, v_a_4449_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4466_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_a_4452_ = lean_ctor_get(v___x_4450_, 1);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4454_ = v___x_4450_;
v_isShared_4455_ = v_isSharedCheck_4466_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4466_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; uint8_t v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4456_ = lean_unsigned_to_nat(2u);
v___x_4457_ = lean_mk_empty_array_with_capacity(v___x_4456_);
v___x_4458_ = lean_array_push(v___x_4457_, v_a_4448_);
v___x_4459_ = lean_array_push(v___x_4458_, v_a_4451_);
v___x_4460_ = 1;
v___x_4461_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4459_, v___x_4460_);
lean_dec_ref(v___x_4459_);
v___x_4462_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4461_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v___x_4462_);
v___x_4464_ = v___x_4454_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4465_, 1, v_a_4452_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
else
{
lean_dec(v_a_4448_);
return v___x_4450_;
}
}
else
{
lean_dec(v_rhs_4444_);
return v___x_4447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object* v_lhs_4467_, lean_object* v_rhs_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4467_, v_rhs_4468_, v_a_4469_, v_a_4470_);
lean_dec_ref(v_a_4469_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object* v_head_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v_quantifier_4475_; lean_object* v_binders_4476_; lean_object* v_typeAscriptionTk_x3f_4477_; lean_object* v_type_x3f_4478_; lean_object* v_commaTk_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4592_; 
v_quantifier_4475_ = lean_ctor_get(v_head_4472_, 0);
v_binders_4476_ = lean_ctor_get(v_head_4472_, 1);
v_typeAscriptionTk_x3f_4477_ = lean_ctor_get(v_head_4472_, 2);
v_type_x3f_4478_ = lean_ctor_get(v_head_4472_, 3);
v_commaTk_4479_ = lean_ctor_get(v_head_4472_, 4);
v_isSharedCheck_4592_ = !lean_is_exclusive(v_head_4472_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4481_ = v_head_4472_;
v_isShared_4482_ = v_isSharedCheck_4592_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_commaTk_4479_);
lean_inc(v_type_x3f_4478_);
lean_inc(v_typeAscriptionTk_x3f_4477_);
lean_inc(v_binders_4476_);
lean_inc(v_quantifier_4475_);
lean_dec(v_head_4472_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4592_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_Fmt_fmt(v_quantifier_4475_, v_a_4473_, v_a_4474_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v_a_4485_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v_binderGroups_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
v_a_4485_ = lean_ctor_get(v___x_4483_, 1);
lean_inc(v_a_4485_);
lean_dec_ref_known(v___x_4483_, 2);
if (lean_obj_tag(v_binders_4476_) == 0)
{
lean_object* v_group_4551_; lean_object* v___x_4552_; 
v_group_4551_ = lean_ctor_get(v_binders_4476_, 0);
lean_inc_ref(v_group_4551_);
lean_dec_ref_known(v_binders_4476_, 1);
v___x_4552_ = l_Lean_Fmt_fmtBinderGroups(v_group_4551_, v_a_4473_, v_a_4485_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v_a_4554_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
v_a_4554_ = lean_ctor_get(v___x_4552_, 1);
lean_inc(v_a_4554_);
lean_dec_ref_known(v___x_4552_, 2);
v_binderGroups_4534_ = v_a_4553_;
v___y_4535_ = v_a_4473_;
v___y_4536_ = v_a_4554_;
goto v___jp_4533_;
}
else
{
lean_object* v_a_4555_; lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v_a_4484_);
lean_del_object(v___x_4481_);
lean_dec(v_commaTk_4479_);
lean_dec(v_type_x3f_4478_);
lean_dec(v_typeAscriptionTk_x3f_4477_);
v_a_4555_ = lean_ctor_get(v___x_4552_, 0);
v_a_4556_ = lean_ctor_get(v___x_4552_, 1);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4552_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_inc(v_a_4555_);
lean_dec(v___x_4552_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4555_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
lean_object* v_lhs_4564_; lean_object* v_rhs_4565_; lean_object* v___x_4566_; 
v_lhs_4564_ = lean_ctor_get(v_binders_4476_, 0);
lean_inc(v_lhs_4564_);
v_rhs_4565_ = lean_ctor_get(v_binders_4476_, 1);
lean_inc(v_rhs_4565_);
lean_dec_ref_known(v_binders_4476_, 2);
v___x_4566_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4564_, v_rhs_4565_, v_a_4473_, v_a_4485_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v_a_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
v_a_4568_ = lean_ctor_get(v___x_4566_, 1);
lean_inc(v_a_4568_);
lean_dec_ref_known(v___x_4566_, 2);
v___x_4569_ = lean_unsigned_to_nat(1u);
v___x_4570_ = lean_mk_empty_array_with_capacity(v___x_4569_);
lean_inc_ref_n(v___x_4570_, 2);
v___x_4571_ = lean_array_push(v___x_4570_, v_a_4567_);
v___x_4572_ = lean_array_push(v___x_4570_, v___x_4571_);
v___x_4573_ = lean_array_push(v___x_4570_, v___x_4572_);
v_binderGroups_4534_ = v___x_4573_;
v___y_4535_ = v_a_4473_;
v___y_4536_ = v_a_4568_;
goto v___jp_4533_;
}
else
{
lean_object* v_a_4574_; lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_a_4484_);
lean_del_object(v___x_4481_);
lean_dec(v_commaTk_4479_);
lean_dec(v_type_x3f_4478_);
lean_dec(v_typeAscriptionTk_x3f_4477_);
v_a_4574_ = lean_ctor_get(v___x_4566_, 0);
v_a_4575_ = lean_ctor_get(v___x_4566_, 1);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4566_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_inc(v_a_4574_);
lean_dec(v___x_4566_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4574_);
lean_ctor_set(v_reuseFailAlloc_4581_, 1, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
v___jp_4486_:
{
lean_object* v___x_4492_; 
v___x_4492_ = l_Lean_Fmt_fmt(v_commaTk_4479_, v___y_4487_, v___y_4490_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4504_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_a_4494_ = lean_ctor_get(v___x_4492_, 1);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4496_ = v___x_4492_;
v_isShared_4497_ = v_isSharedCheck_4504_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4504_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 4, v_a_4493_);
lean_ctor_set(v___x_4481_, 3, v___y_4491_);
lean_ctor_set(v___x_4481_, 2, v___y_4489_);
lean_ctor_set(v___x_4481_, 1, v___y_4488_);
lean_ctor_set(v___x_4481_, 0, v_a_4484_);
v___x_4499_ = v___x_4481_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4484_);
lean_ctor_set(v_reuseFailAlloc_4503_, 1, v___y_4488_);
lean_ctor_set(v_reuseFailAlloc_4503_, 2, v___y_4489_);
lean_ctor_set(v_reuseFailAlloc_4503_, 3, v___y_4491_);
lean_ctor_set(v_reuseFailAlloc_4503_, 4, v_a_4493_);
v___x_4499_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
lean_object* v___x_4501_; 
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v___x_4499_);
v___x_4501_ = v___x_4496_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4502_, 1, v_a_4494_);
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
else
{
lean_object* v_a_4505_; lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref(v___y_4491_);
lean_dec_ref(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v_a_4484_);
lean_del_object(v___x_4481_);
v_a_4505_ = lean_ctor_get(v___x_4492_, 0);
v_a_4506_ = lean_ctor_get(v___x_4492_, 1);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4492_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_inc(v_a_4505_);
lean_dec(v___x_4492_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4505_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
v___jp_4514_:
{
if (lean_obj_tag(v_type_x3f_4478_) == 0)
{
lean_object* v___x_4519_; 
v___x_4519_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4487_ = v___y_4515_;
v___y_4488_ = v___y_4517_;
v___y_4489_ = v___y_4518_;
v___y_4490_ = v___y_4516_;
v___y_4491_ = v___x_4519_;
goto v___jp_4486_;
}
else
{
lean_object* v_val_4520_; lean_object* v___x_4521_; 
v_val_4520_ = lean_ctor_get(v_type_x3f_4478_, 0);
lean_inc(v_val_4520_);
lean_dec_ref_known(v_type_x3f_4478_, 1);
v___x_4521_ = l_Lean_Fmt_fmt(v_val_4520_, v___y_4515_, v___y_4516_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v_a_4523_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
v_a_4523_ = lean_ctor_get(v___x_4521_, 1);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4521_, 2);
v___y_4487_ = v___y_4515_;
v___y_4488_ = v___y_4517_;
v___y_4489_ = v___y_4518_;
v___y_4490_ = v_a_4523_;
v___y_4491_ = v_a_4522_;
goto v___jp_4486_;
}
else
{
lean_object* v_a_4524_; lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4532_; 
lean_dec_ref(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec(v_a_4484_);
lean_del_object(v___x_4481_);
lean_dec(v_commaTk_4479_);
v_a_4524_ = lean_ctor_get(v___x_4521_, 0);
v_a_4525_ = lean_ctor_get(v___x_4521_, 1);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4527_ = v___x_4521_;
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_inc(v_a_4524_);
lean_dec(v___x_4521_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4532_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v___x_4530_; 
if (v_isShared_4528_ == 0)
{
v___x_4530_ = v___x_4527_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v_a_4524_);
lean_ctor_set(v_reuseFailAlloc_4531_, 1, v_a_4525_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
}
v___jp_4533_:
{
if (lean_obj_tag(v_typeAscriptionTk_x3f_4477_) == 0)
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4515_ = v___y_4535_;
v___y_4516_ = v___y_4536_;
v___y_4517_ = v_binderGroups_4534_;
v___y_4518_ = v___x_4537_;
goto v___jp_4514_;
}
else
{
lean_object* v_val_4538_; lean_object* v___x_4539_; 
v_val_4538_ = lean_ctor_get(v_typeAscriptionTk_x3f_4477_, 0);
lean_inc(v_val_4538_);
lean_dec_ref_known(v_typeAscriptionTk_x3f_4477_, 1);
v___x_4539_ = l_Lean_Fmt_fmt(v_val_4538_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v_a_4541_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc(v_a_4540_);
v_a_4541_ = lean_ctor_get(v___x_4539_, 1);
lean_inc(v_a_4541_);
lean_dec_ref_known(v___x_4539_, 2);
v___y_4515_ = v___y_4535_;
v___y_4516_ = v_a_4541_;
v___y_4517_ = v_binderGroups_4534_;
v___y_4518_ = v_a_4540_;
goto v___jp_4514_;
}
else
{
lean_object* v_a_4542_; lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec_ref(v_binderGroups_4534_);
lean_dec(v_a_4484_);
lean_del_object(v___x_4481_);
lean_dec(v_commaTk_4479_);
lean_dec(v_type_x3f_4478_);
v_a_4542_ = lean_ctor_get(v___x_4539_, 0);
v_a_4543_ = lean_ctor_get(v___x_4539_, 1);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4539_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_inc(v_a_4542_);
lean_dec(v___x_4539_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4542_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4591_; 
lean_del_object(v___x_4481_);
lean_dec(v_commaTk_4479_);
lean_dec(v_type_x3f_4478_);
lean_dec(v_typeAscriptionTk_x3f_4477_);
lean_dec_ref(v_binders_4476_);
v_a_4583_ = lean_ctor_get(v___x_4483_, 0);
v_a_4584_ = lean_ctor_get(v___x_4483_, 1);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4586_ = v___x_4483_;
v_isShared_4587_ = v_isSharedCheck_4591_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_inc(v_a_4583_);
lean_dec(v___x_4483_);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object* v_head_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Fmt_fmtQuantifierHead(v_head_4593_, v_a_4594_, v_a_4595_);
lean_dec_ref(v_a_4594_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t v_sz_4597_, size_t v_i_4598_, lean_object* v_bs_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
uint8_t v___x_4602_; 
v___x_4602_ = lean_usize_dec_lt(v_i_4598_, v_sz_4597_);
if (v___x_4602_ == 0)
{
lean_object* v___x_4603_; 
v___x_4603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4603_, 0, v_bs_4599_);
lean_ctor_set(v___x_4603_, 1, v___y_4601_);
return v___x_4603_;
}
else
{
lean_object* v_v_4604_; lean_object* v___x_4605_; 
v_v_4604_ = lean_array_uget_borrowed(v_bs_4599_, v_i_4598_);
lean_inc(v_v_4604_);
v___x_4605_ = l_Lean_Fmt_fmtQuantifierHead(v_v_4604_, v___y_4600_, v___y_4601_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v_a_4607_; lean_object* v___x_4608_; lean_object* v_bs_x27_4609_; size_t v___x_4610_; size_t v___x_4611_; lean_object* v___x_4612_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
v_a_4607_ = lean_ctor_get(v___x_4605_, 1);
lean_inc(v_a_4607_);
lean_dec_ref_known(v___x_4605_, 2);
v___x_4608_ = lean_unsigned_to_nat(0u);
v_bs_x27_4609_ = lean_array_uset(v_bs_4599_, v_i_4598_, v___x_4608_);
v___x_4610_ = ((size_t)1ULL);
v___x_4611_ = lean_usize_add(v_i_4598_, v___x_4610_);
v___x_4612_ = lean_array_uset(v_bs_x27_4609_, v_i_4598_, v_a_4606_);
v_i_4598_ = v___x_4611_;
v_bs_4599_ = v___x_4612_;
v___y_4601_ = v_a_4607_;
goto _start;
}
else
{
lean_object* v_a_4614_; lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec_ref(v_bs_4599_);
v_a_4614_ = lean_ctor_get(v___x_4605_, 0);
v_a_4615_ = lean_ctor_get(v___x_4605_, 1);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4605_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_inc(v_a_4614_);
lean_dec(v___x_4605_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4614_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_a_4615_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object* v_sz_4623_, lean_object* v_i_4624_, lean_object* v_bs_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
size_t v_sz_boxed_4628_; size_t v_i_boxed_4629_; lean_object* v_res_4630_; 
v_sz_boxed_4628_ = lean_unbox_usize(v_sz_4623_);
lean_dec(v_sz_4623_);
v_i_boxed_4629_ = lean_unbox_usize(v_i_4624_);
lean_dec(v_i_4624_);
v_res_4630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_boxed_4628_, v_i_boxed_4629_, v_bs_4625_, v___y_4626_, v___y_4627_);
lean_dec_ref(v___y_4626_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object* v_deconstructQuantifier_x3f_4631_, lean_object* v_stx_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
lean_object* v_env_4635_; lean_object* v___x_4636_; lean_object* v_quantifiers_4637_; lean_object* v_body_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4674_; 
v_env_4635_ = lean_ctor_get(v_a_4633_, 0);
lean_inc_ref(v_env_4635_);
v___x_4636_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(v_env_4635_, v_deconstructQuantifier_x3f_4631_, v_stx_4632_);
v_quantifiers_4637_ = lean_ctor_get(v___x_4636_, 0);
v_body_4638_ = lean_ctor_get(v___x_4636_, 1);
v_isSharedCheck_4674_ = !lean_is_exclusive(v___x_4636_);
if (v_isSharedCheck_4674_ == 0)
{
v___x_4640_ = v___x_4636_;
v_isShared_4641_ = v_isSharedCheck_4674_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_body_4638_);
lean_inc(v_quantifiers_4637_);
lean_dec(v___x_4636_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4674_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4642_ = lean_array_get_size(v_quantifiers_4637_);
v___x_4643_ = lean_unsigned_to_nat(0u);
v___x_4644_ = lean_nat_dec_eq(v___x_4642_, v___x_4643_);
if (v___x_4644_ == 0)
{
size_t v_sz_4645_; size_t v___x_4646_; lean_object* v___x_4647_; 
lean_del_object(v___x_4640_);
v_sz_4645_ = lean_array_size(v_quantifiers_4637_);
v___x_4646_ = ((size_t)0ULL);
v___x_4647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_4645_, v___x_4646_, v_quantifiers_4637_, v_a_4633_, v_a_4634_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v_a_4649_; lean_object* v___x_4650_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
v_a_4649_ = lean_ctor_get(v___x_4647_, 1);
lean_inc(v_a_4649_);
lean_dec_ref_known(v___x_4647_, 2);
v___x_4650_ = l_Lean_Fmt_fmt(v_body_4638_, v_a_4633_, v_a_4649_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4660_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
v_a_4652_ = lean_ctor_get(v___x_4650_, 1);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4654_ = v___x_4650_;
v_isShared_4655_ = v_isSharedCheck_4660_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_inc(v_a_4651_);
lean_dec(v___x_4650_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4660_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4656_; lean_object* v___x_4658_; 
v___x_4656_ = l_Lean_Fmt_Layouts_quantified(v_a_4648_, v_a_4651_);
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 0, v___x_4656_);
v___x_4658_ = v___x_4654_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_a_4652_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
else
{
lean_dec(v_a_4648_);
return v___x_4650_;
}
}
else
{
lean_object* v_a_4661_; lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec(v_body_4638_);
v_a_4661_ = lean_ctor_get(v___x_4647_, 0);
v_a_4662_ = lean_ctor_get(v___x_4647_, 1);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4647_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_inc(v_a_4661_);
lean_dec(v___x_4647_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4661_);
lean_ctor_set(v_reuseFailAlloc_4668_, 1, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
else
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
lean_dec(v_body_4638_);
lean_dec_ref(v_quantifiers_4637_);
v___x_4670_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4641_ == 0)
{
lean_ctor_set_tag(v___x_4640_, 1);
lean_ctor_set(v___x_4640_, 1, v_a_4634_);
lean_ctor_set(v___x_4640_, 0, v___x_4670_);
v___x_4672_ = v___x_4640_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4673_, 1, v_a_4634_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object* v_deconstructQuantifier_x3f_4675_, lean_object* v_stx_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Lean_Fmt_fmtQuantifier(v_deconstructQuantifier_x3f_4675_, v_stx_4676_, v_a_4677_, v_a_4678_);
lean_dec_ref(v_a_4677_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
uint8_t v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = 0;
v___x_4684_ = l_Lean_Fmt_fmtRaw(v___x_4683_, v_a_4680_, v_a_4681_, v_a_4682_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_){
_start:
{
lean_object* v_res_4688_; 
v_res_4688_ = l_Lean_Fmt_fmtAtomic(v_a_4685_, v_a_4686_, v_a_4687_);
lean_dec_ref(v_a_4686_);
return v_res_4688_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___x_4695_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed), 3, 0);
v___x_4696_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2));
v___x_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
lean_ctor_set(v___x_4697_, 1, v___x_4695_);
return v___x_4697_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4(void){
_start:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3);
v___x_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object* v_kind_4700_){
_start:
{
lean_object* v___x_4701_; uint8_t v___x_4702_; 
v___x_4701_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_4702_ = lean_name_eq(v_kind_4700_, v___x_4701_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; 
v___x_4703_ = lean_box(0);
return v___x_4703_;
}
else
{
lean_object* v___x_4704_; 
v___x_4704_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4);
return v___x_4704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object* v_kind_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4705_);
lean_dec(v_kind_4705_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object* v_x_4707_, lean_object* v_x_4708_, lean_object* v_kind_4709_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object* v_x_4711_, lean_object* v_x_4712_, lean_object* v_kind_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(v_x_4711_, v_x_4712_, v_kind_4713_);
lean_dec(v_kind_4713_);
lean_dec_ref(v_x_4712_);
lean_dec_ref(v_x_4711_);
return v_res_4714_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object* v_x_4720_){
_start:
{
if (lean_obj_tag(v_x_4720_) == 1)
{
lean_object* v_pre_4721_; lean_object* v_str_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; 
v_pre_4721_ = lean_ctor_get(v_x_4720_, 0);
v_str_4722_ = lean_ctor_get(v_x_4720_, 1);
v___x_4723_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0));
v___x_4724_ = lean_string_dec_eq(v_str_4722_, v___x_4723_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; uint8_t v___x_4726_; 
v___x_4725_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1));
v___x_4726_ = lean_string_dec_eq(v_str_4722_, v___x_4725_);
if (v___x_4726_ == 0)
{
lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4727_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2));
v___x_4728_ = lean_string_dec_eq(v_str_4722_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; uint8_t v___x_4730_; 
v___x_4729_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3));
v___x_4730_ = lean_string_dec_eq(v_str_4722_, v___x_4729_);
if (v___x_4730_ == 0)
{
lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4731_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4));
v___x_4732_ = lean_string_dec_eq(v_str_4722_, v___x_4731_);
if (v___x_4732_ == 0)
{
return v___x_4732_;
}
else
{
if (lean_obj_tag(v_pre_4721_) == 0)
{
return v___x_4732_;
}
else
{
return v___x_4730_;
}
}
}
else
{
return v___x_4730_;
}
}
else
{
return v___x_4728_;
}
}
else
{
return v___x_4726_;
}
}
else
{
return v___x_4724_;
}
}
else
{
uint8_t v___x_4733_; 
v___x_4733_ = 0;
return v___x_4733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object* v_x_4734_){
_start:
{
uint8_t v_res_4735_; lean_object* v_r_4736_; 
v_res_4735_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_x_4734_);
lean_dec(v_x_4734_);
v_r_4736_ = lean_box(v_res_4735_);
return v_r_4736_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2(void){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4742_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAtomic___boxed), 3, 0);
v___x_4743_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1));
v___x_4744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4743_);
lean_ctor_set(v___x_4744_, 1, v___x_4742_);
return v___x_4744_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4745_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2);
v___x_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object* v_kind_4747_){
_start:
{
uint8_t v___x_4748_; 
v___x_4748_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_kind_4747_);
if (v___x_4748_ == 0)
{
lean_object* v___x_4749_; 
v___x_4749_ = lean_box(0);
return v___x_4749_;
}
else
{
lean_object* v___x_4750_; 
v___x_4750_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object* v_kind_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4751_);
lean_dec(v_kind_4751_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object* v_x_4753_, lean_object* v_x_4754_, lean_object* v_kind_4755_){
_start:
{
lean_object* v___x_4756_; 
v___x_4756_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4755_);
return v___x_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object* v_x_4757_, lean_object* v_x_4758_, lean_object* v_kind_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(v_x_4757_, v_x_4758_, v_kind_4759_);
lean_dec(v_kind_4759_);
lean_dec_ref(v_x_4758_);
lean_dec_ref(v_x_4757_);
return v_res_4760_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4(void){
_start:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4771_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostfixOperator___boxed), 3, 0);
v___x_4772_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3));
v___x_4773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
lean_ctor_set(v___x_4773_, 1, v___x_4771_);
return v___x_4773_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5(void){
_start:
{
lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4774_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4);
v___x_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
return v___x_4775_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4781_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrefixOperator___boxed), 3, 0);
v___x_4782_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7));
v___x_4783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4782_);
lean_ctor_set(v___x_4783_, 1, v___x_4781_);
return v___x_4783_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8);
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object* v_env_4786_, lean_object* v_opts_4787_, lean_object* v_kind_4788_){
_start:
{
lean_object* v___x_4789_; 
lean_inc(v_kind_4788_);
lean_inc_ref(v_env_4786_);
v___x_4789_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_4786_, v_opts_4787_, v_kind_4788_);
if (lean_obj_tag(v___x_4789_) == 1)
{
lean_object* v_val_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v_kind_4788_);
lean_dec_ref(v_env_4786_);
v_val_4790_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4792_ = v___x_4789_;
v_isShared_4793_ = v_isSharedCheck_4800_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_val_4790_);
lean_dec(v___x_4789_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4800_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4798_; 
v___x_4794_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1));
v___x_4795_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInfixOperator___boxed), 4, 1);
lean_closure_set(v___x_4795_, 0, v_val_4790_);
v___x_4796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4794_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 0, v___x_4796_);
v___x_4798_ = v___x_4792_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
else
{
uint8_t v___x_4801_; 
lean_dec(v___x_4789_);
lean_inc(v_kind_4788_);
lean_inc_ref(v_env_4786_);
v___x_4801_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_4786_, v_opts_4787_, v_kind_4788_);
if (v___x_4801_ == 0)
{
uint8_t v___x_4802_; 
v___x_4802_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_4786_, v_opts_4787_, v_kind_4788_);
if (v___x_4802_ == 0)
{
lean_object* v___x_4803_; 
v___x_4803_ = lean_box(0);
return v___x_4803_;
}
else
{
lean_object* v___x_4804_; 
v___x_4804_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5);
return v___x_4804_;
}
}
else
{
lean_object* v___x_4805_; 
lean_dec(v_kind_4788_);
lean_dec_ref(v_env_4786_);
v___x_4805_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9);
return v___x_4805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object* v_env_4806_, lean_object* v_opts_4807_, lean_object* v_kind_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(v_env_4806_, v_opts_4807_, v_kind_4808_);
lean_dec_ref(v_opts_4807_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object* v_env_4810_, lean_object* v_opts_4811_, lean_object* v_kind_4812_){
_start:
{
uint8_t v___x_4813_; 
v___x_4813_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_4810_, v_opts_4811_, v_kind_4812_);
if (v___x_4813_ == 0)
{
lean_object* v___x_4814_; 
v___x_4814_ = lean_box(0);
return v___x_4814_;
}
else
{
lean_object* v___x_4815_; 
v___x_4815_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object* v_env_4816_, lean_object* v_opts_4817_, lean_object* v_kind_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(v_env_4816_, v_opts_4817_, v_kind_4818_);
lean_dec_ref(v_opts_4817_);
return v_res_4819_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(lean_object* v_x_4820_, lean_object* v_x_4821_){
_start:
{
if (lean_obj_tag(v_x_4820_) == 0)
{
if (lean_obj_tag(v_x_4821_) == 0)
{
uint8_t v___x_4822_; 
v___x_4822_ = 1;
return v___x_4822_;
}
else
{
uint8_t v___x_4823_; 
v___x_4823_ = 0;
return v___x_4823_;
}
}
else
{
if (lean_obj_tag(v_x_4821_) == 0)
{
uint8_t v___x_4824_; 
v___x_4824_ = 0;
return v___x_4824_;
}
else
{
lean_object* v_val_4825_; lean_object* v_val_4826_; uint8_t v___x_4827_; 
v_val_4825_ = lean_ctor_get(v_x_4820_, 0);
v_val_4826_ = lean_ctor_get(v_x_4821_, 0);
v___x_4827_ = lean_nat_dec_eq(v_val_4825_, v_val_4826_);
return v___x_4827_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0___boxed(lean_object* v_x_4828_, lean_object* v_x_4829_){
_start:
{
uint8_t v_res_4830_; lean_object* v_r_4831_; 
v_res_4830_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v_x_4828_, v_x_4829_);
lean_dec(v_x_4829_);
lean_dec(v_x_4828_);
v_r_4831_ = lean_box(v_res_4830_);
return v_r_4831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(lean_object* v_lineInfos_4832_, lean_object* v___f_4833_, lean_object* v___f_4834_, lean_object* v_pos_4835_){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_4832_, v_pos_4835_, v___f_4833_, v___f_4834_);
if (lean_obj_tag(v___x_4836_) == 0)
{
lean_object* v___x_4837_; 
v___x_4837_ = lean_box(0);
return v___x_4837_;
}
else
{
lean_object* v_val_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4846_; 
v_val_4838_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4840_ = v___x_4836_;
v_isShared_4841_ = v_isSharedCheck_4846_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_val_4838_);
lean_dec(v___x_4836_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4846_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v_fst_4842_; lean_object* v___x_4844_; 
v_fst_4842_ = lean_ctor_get(v_val_4838_, 0);
lean_inc(v_fst_4842_);
lean_dec(v_val_4838_);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 0, v_fst_4842_);
v___x_4844_ = v___x_4840_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_fst_4842_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2___boxed(lean_object* v_lineInfos_4847_, lean_object* v___f_4848_, lean_object* v___f_4849_, lean_object* v_pos_4850_){
_start:
{
lean_object* v_res_4851_; 
v_res_4851_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4847_, v___f_4848_, v___f_4849_, v_pos_4850_);
lean_dec_ref(v_lineInfos_4847_);
return v_res_4851_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(lean_object* v_lineInfos_4852_, lean_object* v_a_4853_, lean_object* v_b_4854_){
_start:
{
lean_object* v___f_4855_; lean_object* v___f_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v___f_4855_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_4856_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___x_4857_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4852_, v___f_4855_, v___f_4856_, v_a_4853_);
v___x_4858_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4852_, v___f_4855_, v___f_4856_, v_b_4854_);
v___x_4859_ = l_instBEqOption_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v___x_4857_, v___x_4858_);
lean_dec(v___x_4858_);
lean_dec(v___x_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___boxed(lean_object* v_lineInfos_4860_, lean_object* v_a_4861_, lean_object* v_b_4862_){
_start:
{
uint8_t v_res_4863_; lean_object* v_r_4864_; 
v_res_4863_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4860_, v_a_4861_, v_b_4862_);
lean_dec_ref(v_lineInfos_4860_);
v_r_4864_ = lean_box(v_res_4863_);
return v_r_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(lean_object* v_val_4865_, uint8_t v_opOnRhsLine_4866_, lean_object* v_val_4867_, lean_object* v_val_4868_, lean_object* v___x_4869_, uint8_t v_opOnLhsLine_4870_, lean_object* v___x_4871_, lean_object* v_as_4872_, size_t v_sz_4873_, size_t v_i_4874_, lean_object* v_b_4875_){
_start:
{
lean_object* v_a_4877_; uint8_t v___x_4881_; 
v___x_4881_ = lean_usize_dec_lt(v_i_4874_, v_sz_4873_);
if (v___x_4881_ == 0)
{
lean_dec_ref(v_val_4868_);
lean_dec_ref(v_val_4867_);
lean_dec_ref(v_val_4865_);
return v_b_4875_;
}
else
{
lean_object* v_a_4882_; uint8_t v_kind_4883_; uint8_t v_placement_4884_; lean_object* v_originalTokenRange_4885_; lean_object* v_originalWhitespaceRange_4886_; uint8_t v_originalWhitespaceKind_4887_; lean_object* v_content_4888_; uint8_t v_emptyLineBefore_4889_; uint8_t v___y_4896_; uint8_t v___y_4897_; lean_object* v___x_4902_; uint8_t v___x_4903_; uint8_t v___y_4905_; 
v_a_4882_ = lean_array_uget_borrowed(v_as_4872_, v_i_4874_);
v_kind_4883_ = lean_ctor_get_uint8(v_a_4882_, sizeof(void*)*3);
v_placement_4884_ = lean_ctor_get_uint8(v_a_4882_, sizeof(void*)*3 + 1);
v_originalTokenRange_4885_ = lean_ctor_get(v_a_4882_, 0);
v_originalWhitespaceRange_4886_ = lean_ctor_get(v_a_4882_, 1);
v_originalWhitespaceKind_4887_ = lean_ctor_get_uint8(v_a_4882_, sizeof(void*)*3 + 2);
v_content_4888_ = lean_ctor_get(v_a_4882_, 2);
v_emptyLineBefore_4889_ = lean_ctor_get_uint8(v_a_4882_, sizeof(void*)*3 + 3);
v___x_4902_ = lean_unsigned_to_nat(0u);
v___x_4903_ = lean_nat_dec_eq(v___x_4869_, v___x_4902_);
if (v_placement_4884_ == 0)
{
lean_object* v___x_4906_; uint8_t v___x_4907_; 
v___x_4906_ = lean_unsigned_to_nat(3u);
v___x_4907_ = lean_nat_dec_eq(v___x_4871_, v___x_4906_);
v___y_4905_ = v___x_4907_;
goto v___jp_4904_;
}
else
{
v___y_4905_ = v___x_4903_;
goto v___jp_4904_;
}
v___jp_4890_:
{
uint8_t v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4891_ = 1;
lean_inc_ref(v_content_4888_);
lean_inc_ref(v_originalWhitespaceRange_4886_);
lean_inc_ref(v_originalTokenRange_4885_);
v___x_4892_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4892_, 0, v_originalTokenRange_4885_);
lean_ctor_set(v___x_4892_, 1, v_originalWhitespaceRange_4886_);
lean_ctor_set(v___x_4892_, 2, v_content_4888_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*3, v_kind_4883_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*3 + 1, v___x_4891_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_4887_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*3 + 3, v_emptyLineBefore_4889_);
lean_inc_ref(v_val_4865_);
v___x_4893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
lean_ctor_set(v___x_4893_, 1, v_val_4865_);
v___x_4894_ = lean_array_push(v_b_4875_, v___x_4893_);
v_a_4877_ = v___x_4894_;
goto v___jp_4876_;
}
v___jp_4895_:
{
if (v___y_4897_ == 0)
{
if (v___y_4896_ == 0)
{
goto v___jp_4890_;
}
else
{
if (v_opOnRhsLine_4866_ == 0)
{
goto v___jp_4890_;
}
else
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
lean_inc_ref(v_val_4867_);
lean_inc(v_a_4882_);
v___x_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4898_, 0, v_a_4882_);
lean_ctor_set(v___x_4898_, 1, v_val_4867_);
v___x_4899_ = lean_array_push(v_b_4875_, v___x_4898_);
v_a_4877_ = v___x_4899_;
goto v___jp_4876_;
}
}
}
else
{
if (v_opOnRhsLine_4866_ == 0)
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
lean_inc_ref(v_val_4868_);
lean_inc(v_a_4882_);
v___x_4900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4900_, 0, v_a_4882_);
lean_ctor_set(v___x_4900_, 1, v_val_4868_);
v___x_4901_ = lean_array_push(v_b_4875_, v___x_4900_);
v_a_4877_ = v___x_4901_;
goto v___jp_4876_;
}
else
{
v_a_4877_ = v_b_4875_;
goto v___jp_4876_;
}
}
}
v___jp_4904_:
{
if (v___y_4905_ == 0)
{
v___y_4896_ = v___y_4905_;
v___y_4897_ = v___x_4903_;
goto v___jp_4895_;
}
else
{
v___y_4896_ = v___y_4905_;
v___y_4897_ = v_opOnLhsLine_4870_;
goto v___jp_4895_;
}
}
}
v___jp_4876_:
{
size_t v___x_4878_; size_t v___x_4879_; 
v___x_4878_ = ((size_t)1ULL);
v___x_4879_ = lean_usize_add(v_i_4874_, v___x_4878_);
v_i_4874_ = v___x_4879_;
v_b_4875_ = v_a_4877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0___boxed(lean_object* v_val_4908_, lean_object* v_opOnRhsLine_4909_, lean_object* v_val_4910_, lean_object* v_val_4911_, lean_object* v___x_4912_, lean_object* v_opOnLhsLine_4913_, lean_object* v___x_4914_, lean_object* v_as_4915_, lean_object* v_sz_4916_, lean_object* v_i_4917_, lean_object* v_b_4918_){
_start:
{
uint8_t v_opOnRhsLine_boxed_4919_; uint8_t v_opOnLhsLine_boxed_4920_; size_t v_sz_boxed_4921_; size_t v_i_boxed_4922_; lean_object* v_res_4923_; 
v_opOnRhsLine_boxed_4919_ = lean_unbox(v_opOnRhsLine_4909_);
v_opOnLhsLine_boxed_4920_ = lean_unbox(v_opOnLhsLine_4913_);
v_sz_boxed_4921_ = lean_unbox_usize(v_sz_4916_);
lean_dec(v_sz_4916_);
v_i_boxed_4922_ = lean_unbox_usize(v_i_4917_);
lean_dec(v_i_4917_);
v_res_4923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_4908_, v_opOnRhsLine_boxed_4919_, v_val_4910_, v_val_4911_, v___x_4912_, v_opOnLhsLine_boxed_4920_, v___x_4914_, v_as_4915_, v_sz_boxed_4921_, v_i_boxed_4922_, v_b_4918_);
lean_dec_ref(v_as_4915_);
lean_dec(v___x_4914_);
lean_dec(v___x_4912_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector(lean_object* v_ctx_4926_, lean_object* v_stx_4927_){
_start:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; uint8_t v___x_4932_; 
v___x_4930_ = l_Lean_Syntax_getNumArgs(v_stx_4927_);
v___x_4931_ = lean_unsigned_to_nat(3u);
v___x_4932_ = lean_nat_dec_eq(v___x_4930_, v___x_4931_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; 
lean_dec(v___x_4930_);
lean_dec(v_stx_4927_);
lean_dec_ref(v_ctx_4926_);
v___x_4933_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4933_;
}
else
{
lean_object* v___x_4934_; lean_object* v___x_4935_; uint8_t v___x_4936_; 
v___x_4934_ = lean_unsigned_to_nat(1u);
v___x_4935_ = l_Lean_Syntax_getArg(v_stx_4927_, v___x_4934_);
v___x_4936_ = l_Lean_Syntax_isAtom(v___x_4935_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4937_; 
lean_dec(v___x_4935_);
lean_dec(v___x_4930_);
lean_dec(v_stx_4927_);
lean_dec_ref(v_ctx_4926_);
v___x_4937_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4937_;
}
else
{
lean_object* v_env_4938_; lean_object* v_opts_4939_; lean_object* v_lineInfos_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v_env_4938_ = lean_ctor_get(v_ctx_4926_, 0);
v_opts_4939_ = lean_ctor_get(v_ctx_4926_, 1);
v_lineInfos_4940_ = lean_ctor_get(v_ctx_4926_, 2);
lean_inc_ref(v_lineInfos_4940_);
v___x_4941_ = lean_unsigned_to_nat(0u);
v___x_4942_ = l_Lean_Syntax_getArg(v_stx_4927_, v___x_4941_);
v___x_4943_ = lean_unsigned_to_nat(2u);
v___x_4944_ = l_Lean_Syntax_getArg(v_stx_4927_, v___x_4943_);
v___x_4945_ = l_Lean_Syntax_getKind(v_stx_4927_);
lean_inc_ref(v_env_4938_);
v___x_4946_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_4938_, v_opts_4939_, v___x_4945_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v___x_4947_; 
lean_dec(v___x_4944_);
lean_dec(v___x_4942_);
lean_dec_ref(v_lineInfos_4940_);
lean_dec(v___x_4935_);
lean_dec(v___x_4930_);
lean_dec_ref(v_ctx_4926_);
v___x_4947_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4947_;
}
else
{
lean_object* v_comments_4948_; lean_object* v___x_4949_; uint8_t v___x_4950_; 
lean_dec_ref_known(v___x_4946_, 1);
v_comments_4948_ = l_Lean_Fmt_CommentCollector_Context_trailingComments(v_ctx_4926_, v___x_4935_);
lean_dec_ref(v_ctx_4926_);
v___x_4949_ = lean_array_get_size(v_comments_4948_);
v___x_4950_ = lean_nat_dec_eq(v___x_4949_, v___x_4941_);
if (v___x_4950_ == 0)
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4951_ = l_Lean_Syntax_getTailInfo(v___x_4942_);
lean_dec(v___x_4942_);
v___x_4952_ = l_Lean_SourceInfo_getRange_x3f(v___x_4950_, v___x_4951_);
lean_dec(v___x_4951_);
v___x_4953_ = l_Lean_Syntax_getRange_x3f(v___x_4935_, v___x_4950_);
lean_dec(v___x_4935_);
if (lean_obj_tag(v___x_4952_) == 1)
{
if (lean_obj_tag(v___x_4953_) == 1)
{
lean_object* v_val_4954_; lean_object* v_val_4955_; lean_object* v___x_4956_; 
v_val_4954_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_val_4954_);
lean_dec_ref_known(v___x_4952_, 1);
v_val_4955_ = lean_ctor_get(v___x_4953_, 0);
lean_inc(v_val_4955_);
lean_dec_ref_known(v___x_4953_, 1);
v___x_4956_ = l_Lean_Syntax_getPos_x3f(v___x_4944_, v___x_4950_);
if (lean_obj_tag(v___x_4956_) == 1)
{
lean_object* v_val_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v_val_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_val_4957_);
lean_dec_ref_known(v___x_4956_, 1);
v___x_4958_ = l_Lean_Syntax_getTailInfo(v___x_4944_);
lean_dec(v___x_4944_);
v___x_4959_ = l_Lean_SourceInfo_getRange_x3f(v___x_4950_, v___x_4958_);
lean_dec(v___x_4958_);
if (lean_obj_tag(v___x_4959_) == 1)
{
lean_object* v_val_4960_; lean_object* v_stop_4961_; lean_object* v_start_4962_; lean_object* v_stop_4963_; uint8_t v_opOnLhsLine_4964_; uint8_t v_opOnRhsLine_4965_; lean_object* v_r_4966_; size_t v_sz_4967_; size_t v___x_4968_; lean_object* v___x_4969_; 
v_val_4960_ = lean_ctor_get(v___x_4959_, 0);
lean_inc(v_val_4960_);
lean_dec_ref_known(v___x_4959_, 1);
v_stop_4961_ = lean_ctor_get(v_val_4954_, 1);
v_start_4962_ = lean_ctor_get(v_val_4955_, 0);
v_stop_4963_ = lean_ctor_get(v_val_4955_, 1);
lean_inc(v_start_4962_);
lean_inc(v_stop_4961_);
v_opOnLhsLine_4964_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4940_, v_stop_4961_, v_start_4962_);
lean_inc(v_stop_4963_);
v_opOnRhsLine_4965_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4940_, v_stop_4963_, v_val_4957_);
lean_dec_ref(v_lineInfos_4940_);
v_r_4966_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
v_sz_4967_ = lean_array_size(v_comments_4948_);
v___x_4968_ = ((size_t)0ULL);
v___x_4969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_4955_, v_opOnRhsLine_4965_, v_val_4960_, v_val_4954_, v___x_4949_, v_opOnLhsLine_4964_, v___x_4930_, v_comments_4948_, v_sz_4967_, v___x_4968_, v_r_4966_);
lean_dec_ref(v_comments_4948_);
lean_dec(v___x_4930_);
return v___x_4969_;
}
else
{
lean_dec(v___x_4959_);
lean_dec(v_val_4957_);
lean_dec(v_val_4955_);
lean_dec(v_val_4954_);
lean_dec_ref(v_comments_4948_);
lean_dec_ref(v_lineInfos_4940_);
lean_dec(v___x_4930_);
goto v___jp_4928_;
}
}
else
{
lean_dec(v___x_4956_);
lean_dec(v_val_4955_);
lean_dec(v_val_4954_);
lean_dec_ref(v_comments_4948_);
lean_dec(v___x_4944_);
lean_dec_ref(v_lineInfos_4940_);
lean_dec(v___x_4930_);
goto v___jp_4928_;
}
}
else
{
lean_dec_ref_known(v___x_4952_, 1);
lean_dec(v___x_4953_);
lean_dec_ref(v_comments_4948_);
lean_dec(v___x_4944_);
lean_dec_ref(v_lineInfos_4940_);
lean_dec(v___x_4930_);
goto v___jp_4928_;
}
}
else
{
lean_dec(v___x_4953_);
lean_dec(v___x_4952_);
lean_dec_ref(v_comments_4948_);
lean_dec(v___x_4944_);
lean_dec_ref(v_lineInfos_4940_);
lean_dec(v___x_4930_);
goto v___jp_4928_;
}
}
else
{
lean_object* v___x_4970_; 
lean_dec_ref(v_comments_4948_);
lean_dec(v___x_4944_);
lean_dec(v___x_4942_);
lean_dec_ref(v_lineInfos_4940_);
lean_dec(v___x_4935_);
lean_dec(v___x_4930_);
v___x_4970_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4970_;
}
}
}
}
v___jp_4928_:
{
lean_object* v___x_4929_; 
v___x_4929_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v___x_4975_; 
lean_inc_ref(v___y_4973_);
v___x_4975_ = lean_apply_3(v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
lean_object* v_res_4980_; 
v_res_4980_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
lean_dec_ref(v___y_4978_);
return v_res_4980_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___f_4983_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4984_ = l_Lean_Fmt_fmtAttribute;
v___x_4985_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4985_, 0, lean_box(0));
lean_closure_set(v___x_4985_, 1, v___x_4984_);
lean_closure_set(v___x_4985_, 2, v___f_4983_);
return v___x_4985_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___f_4986_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4987_ = l_Lean_Fmt_infixFmtAttribute;
v___x_4988_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4988_, 0, lean_box(0));
lean_closure_set(v___x_4988_, 1, v___x_4987_);
lean_closure_set(v___x_4988_, 2, v___f_4986_);
return v___x_4988_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4990_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4991_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_4992_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4992_, 0, lean_box(0));
lean_closure_set(v___x_4992_, 1, v___x_4991_);
lean_closure_set(v___x_4992_, 2, v___x_4990_);
return v___x_4992_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4994_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_4995_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_4996_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_4996_, 0, lean_box(0));
lean_closure_set(v___x_4996_, 1, v___x_4995_);
lean_closure_set(v___x_4996_, 2, v___x_4994_);
return v___x_4996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4998_ = lean_unsigned_to_nat(1100u);
v___x_4999_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed), 3, 0);
v___x_5000_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_4998_, v___x_4999_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
lean_dec_ref_known(v___x_5000_, 1);
v___x_5001_ = lean_unsigned_to_nat(1000u);
v___x_5002_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5003_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5001_, v___x_5002_);
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
lean_dec_ref_known(v___x_5003_, 1);
v___x_5004_ = lean_unsigned_to_nat(900u);
v___x_5005_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed), 3, 0);
v___x_5006_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5004_, v___x_5005_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
lean_dec_ref_known(v___x_5006_, 1);
v___x_5007_ = lean_unsigned_to_nat(800u);
v___x_5008_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5009_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5007_, v___x_5008_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
lean_dec_ref_known(v___x_5009_, 1);
v___x_5010_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5011_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5007_, v___x_5010_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
lean_dec_ref_known(v___x_5011_, 1);
v___x_5012_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5013_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5007_, v___x_5012_);
if (lean_obj_tag(v___x_5013_) == 0)
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
lean_dec_ref_known(v___x_5013_, 1);
v___x_5014_ = lean_unsigned_to_nat(600u);
v___x_5015_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed), 3, 0);
v___x_5016_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5014_, v___x_5015_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
lean_dec_ref_known(v___x_5016_, 1);
v___x_5017_ = lean_unsigned_to_nat(400u);
v___x_5018_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed), 3, 0);
v___x_5019_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5017_, v___x_5018_);
return v___x_5019_;
}
else
{
return v___x_5016_;
}
}
else
{
return v___x_5013_;
}
}
else
{
return v___x_5011_;
}
}
else
{
return v___x_5009_;
}
}
else
{
return v___x_5006_;
}
}
else
{
return v___x_5003_;
}
}
else
{
return v___x_5000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v_a_5020_){
_start:
{
lean_object* v_res_5021_; 
v_res_5021_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_();
return v_res_5021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5023_ = lean_unsigned_to_nat(500u);
v___x_5024_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector), 2, 0);
v___x_5025_ = l_Lean_Fmt_addBuiltinCommentCollector(v___x_5023_, v___x_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2____boxed(lean_object* v_a_5026_){
_start:
{
lean_object* v_res_5027_; 
v_res_5027_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_();
return v_res_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object* v_stx_x3f_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5028_) == 1)
{
lean_object* v_val_5031_; lean_object* v___x_5032_; 
v_val_5031_ = lean_ctor_get(v_stx_x3f_5028_, 0);
lean_inc(v_val_5031_);
lean_dec_ref_known(v_stx_x3f_5028_, 1);
v___x_5032_ = l_Lean_Fmt_fmt(v_val_5031_, v_a_5029_, v_a_5030_);
return v___x_5032_;
}
else
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
lean_dec(v_stx_x3f_5028_);
v___x_5033_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v___x_5033_);
lean_ctor_set(v___x_5034_, 1, v_a_5030_);
return v___x_5034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object* v_stx_x3f_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Lean_Fmt_fmt_x3f(v_stx_x3f_5035_, v_a_5036_, v_a_5037_);
lean_dec_ref(v_a_5036_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object* v_f_5039_, lean_object* v_formatterName_5040_, lean_object* v_stx_x3f_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5041_) == 1)
{
lean_object* v_val_5044_; lean_object* v___x_5045_; 
v_val_5044_ = lean_ctor_get(v_stx_x3f_5041_, 0);
lean_inc(v_val_5044_);
lean_dec_ref_known(v_stx_x3f_5041_, 1);
v___x_5045_ = l_Lean_Fmt_fmtWith(v_f_5039_, v_formatterName_5040_, v_val_5044_, v_a_5042_, v_a_5043_);
return v___x_5045_;
}
else
{
lean_object* v___x_5046_; lean_object* v___x_5047_; 
lean_dec(v_stx_x3f_5041_);
lean_dec(v_formatterName_5040_);
lean_dec_ref(v_f_5039_);
v___x_5046_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5046_);
lean_ctor_set(v___x_5047_, 1, v_a_5043_);
return v___x_5047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object* v_f_5048_, lean_object* v_formatterName_5049_, lean_object* v_stx_x3f_5050_, lean_object* v_a_5051_, lean_object* v_a_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_Fmt_fmtWith_x3f(v_f_5048_, v_formatterName_5049_, v_stx_x3f_5050_, v_a_5051_, v_a_5052_);
lean_dec_ref(v_a_5051_);
return v_res_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object* v_array_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_){
_start:
{
size_t v_sz_5057_; size_t v___x_5058_; lean_object* v___x_5059_; 
v_sz_5057_ = lean_array_size(v_array_5054_);
v___x_5058_ = ((size_t)0ULL);
v___x_5059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5057_, v___x_5058_, v_array_5054_, v_a_5055_, v_a_5056_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object* v_array_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Lean_Fmt_fmtArray___redArg(v_array_5060_, v_a_5061_, v_a_5062_);
lean_dec_ref(v_a_5061_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object* v_ks_5064_, lean_object* v_array_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_){
_start:
{
lean_object* v___x_5068_; 
v___x_5068_ = l_Lean_Fmt_fmtArray___redArg(v_array_5065_, v_a_5066_, v_a_5067_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object* v_ks_5069_, lean_object* v_array_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Lean_Fmt_fmtArray(v_ks_5069_, v_array_5070_, v_a_5071_, v_a_5072_);
lean_dec_ref(v_a_5071_);
lean_dec(v_ks_5069_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object* v_f_5074_, lean_object* v_formatterName_5075_, size_t v_sz_5076_, size_t v_i_5077_, lean_object* v_bs_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
uint8_t v___x_5081_; 
v___x_5081_ = lean_usize_dec_lt(v_i_5077_, v_sz_5076_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; 
lean_dec(v_formatterName_5075_);
lean_dec_ref(v_f_5074_);
v___x_5082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5082_, 0, v_bs_5078_);
lean_ctor_set(v___x_5082_, 1, v___y_5080_);
return v___x_5082_;
}
else
{
lean_object* v_v_5083_; lean_object* v___x_5084_; 
v_v_5083_ = lean_array_uget_borrowed(v_bs_5078_, v_i_5077_);
lean_inc(v_v_5083_);
lean_inc(v_formatterName_5075_);
lean_inc_ref(v_f_5074_);
v___x_5084_ = l_Lean_Fmt_fmtWith(v_f_5074_, v_formatterName_5075_, v_v_5083_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v_a_5086_; lean_object* v___x_5087_; lean_object* v_bs_x27_5088_; size_t v___x_5089_; size_t v___x_5090_; lean_object* v___x_5091_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
v_a_5086_ = lean_ctor_get(v___x_5084_, 1);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___x_5084_, 2);
v___x_5087_ = lean_unsigned_to_nat(0u);
v_bs_x27_5088_ = lean_array_uset(v_bs_5078_, v_i_5077_, v___x_5087_);
v___x_5089_ = ((size_t)1ULL);
v___x_5090_ = lean_usize_add(v_i_5077_, v___x_5089_);
v___x_5091_ = lean_array_uset(v_bs_x27_5088_, v_i_5077_, v_a_5085_);
v_i_5077_ = v___x_5090_;
v_bs_5078_ = v___x_5091_;
v___y_5080_ = v_a_5086_;
goto _start;
}
else
{
lean_object* v_a_5093_; lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5101_; 
lean_dec_ref(v_bs_5078_);
lean_dec(v_formatterName_5075_);
lean_dec_ref(v_f_5074_);
v_a_5093_ = lean_ctor_get(v___x_5084_, 0);
v_a_5094_ = lean_ctor_get(v___x_5084_, 1);
v_isSharedCheck_5101_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5101_ == 0)
{
v___x_5096_ = v___x_5084_;
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_inc(v_a_5093_);
lean_dec(v___x_5084_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5101_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5099_; 
if (v_isShared_5097_ == 0)
{
v___x_5099_ = v___x_5096_;
goto v_reusejp_5098_;
}
else
{
lean_object* v_reuseFailAlloc_5100_; 
v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5093_);
lean_ctor_set(v_reuseFailAlloc_5100_, 1, v_a_5094_);
v___x_5099_ = v_reuseFailAlloc_5100_;
goto v_reusejp_5098_;
}
v_reusejp_5098_:
{
return v___x_5099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object* v_f_5102_, lean_object* v_formatterName_5103_, lean_object* v_sz_5104_, lean_object* v_i_5105_, lean_object* v_bs_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
size_t v_sz_boxed_5109_; size_t v_i_boxed_5110_; lean_object* v_res_5111_; 
v_sz_boxed_5109_ = lean_unbox_usize(v_sz_5104_);
lean_dec(v_sz_5104_);
v_i_boxed_5110_ = lean_unbox_usize(v_i_5105_);
lean_dec(v_i_5105_);
v_res_5111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5102_, v_formatterName_5103_, v_sz_boxed_5109_, v_i_boxed_5110_, v_bs_5106_, v___y_5107_, v___y_5108_);
lean_dec_ref(v___y_5107_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object* v_f_5112_, lean_object* v_formatterName_5113_, lean_object* v_array_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_){
_start:
{
size_t v_sz_5117_; size_t v___x_5118_; lean_object* v___x_5119_; 
v_sz_5117_ = lean_array_size(v_array_5114_);
v___x_5118_ = ((size_t)0ULL);
v___x_5119_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5112_, v_formatterName_5113_, v_sz_5117_, v___x_5118_, v_array_5114_, v_a_5115_, v_a_5116_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object* v_f_5120_, lean_object* v_formatterName_5121_, lean_object* v_array_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5120_, v_formatterName_5121_, v_array_5122_, v_a_5123_, v_a_5124_);
lean_dec_ref(v_a_5123_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object* v_ks_5126_, lean_object* v_f_5127_, lean_object* v_formatterName_5128_, lean_object* v_array_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v___x_5132_; 
v___x_5132_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5127_, v_formatterName_5128_, v_array_5129_, v_a_5130_, v_a_5131_);
return v___x_5132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object* v_ks_5133_, lean_object* v_f_5134_, lean_object* v_formatterName_5135_, lean_object* v_array_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Lean_Fmt_fmtArrayWith(v_ks_5133_, v_f_5134_, v_formatterName_5135_, v_array_5136_, v_a_5137_, v_a_5138_);
lean_dec_ref(v_a_5137_);
lean_dec(v_ks_5133_);
return v_res_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object* v_sepArray_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_){
_start:
{
size_t v_sz_5143_; size_t v___x_5144_; lean_object* v___x_5145_; 
v_sz_5143_ = lean_array_size(v_sepArray_5140_);
v___x_5144_ = ((size_t)0ULL);
v___x_5145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5143_, v___x_5144_, v_sepArray_5140_, v_a_5141_, v_a_5142_);
if (lean_obj_tag(v___x_5145_) == 0)
{
lean_object* v_a_5146_; lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
v_a_5147_ = lean_ctor_get(v___x_5145_, 1);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5145_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_inc(v_a_5146_);
lean_dec(v___x_5145_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5146_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
else
{
lean_object* v_a_5155_; lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
v_a_5155_ = lean_ctor_get(v___x_5145_, 0);
v_a_5156_ = lean_ctor_get(v___x_5145_, 1);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5145_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_inc(v_a_5155_);
lean_dec(v___x_5145_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5155_);
lean_ctor_set(v_reuseFailAlloc_5162_, 1, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object* v_sepArray_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5164_, v_a_5165_, v_a_5166_);
lean_dec_ref(v_a_5165_);
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object* v_sep_5168_, lean_object* v_sepArray_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_){
_start:
{
lean_object* v___x_5172_; 
v___x_5172_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5169_, v_a_5170_, v_a_5171_);
return v___x_5172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object* v_sep_5173_, lean_object* v_sepArray_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Fmt_fmtSepArray(v_sep_5173_, v_sepArray_5174_, v_a_5175_, v_a_5176_);
lean_dec_ref(v_a_5175_);
lean_dec_ref(v_sep_5173_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object* v_f_5178_, lean_object* v_formatterName_5179_, size_t v_sz_5180_, size_t v_i_5181_, lean_object* v_bs_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
uint8_t v___x_5185_; 
v___x_5185_ = lean_usize_dec_lt(v_i_5181_, v_sz_5180_);
if (v___x_5185_ == 0)
{
lean_object* v___x_5186_; 
lean_dec(v_formatterName_5179_);
lean_dec_ref(v_f_5178_);
v___x_5186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5186_, 0, v_bs_5182_);
lean_ctor_set(v___x_5186_, 1, v___y_5184_);
return v___x_5186_;
}
else
{
lean_object* v_v_5187_; lean_object* v___x_5188_; lean_object* v_bs_x27_5189_; lean_object* v___y_5191_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; uint8_t v___x_5210_; 
v_v_5187_ = lean_array_uget(v_bs_5182_, v_i_5181_);
v___x_5188_ = lean_unsigned_to_nat(0u);
v_bs_x27_5189_ = lean_array_uset(v_bs_5182_, v_i_5181_, v___x_5188_);
v___x_5207_ = lean_usize_to_nat(v_i_5181_);
v___x_5208_ = lean_unsigned_to_nat(2u);
v___x_5209_ = lean_nat_mod(v___x_5207_, v___x_5208_);
lean_dec(v___x_5207_);
v___x_5210_ = lean_nat_dec_eq(v___x_5209_, v___x_5188_);
lean_dec(v___x_5209_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; 
v___x_5211_ = l_Lean_Fmt_fmt(v_v_5187_, v___y_5183_, v___y_5184_);
v___y_5191_ = v___x_5211_;
goto v___jp_5190_;
}
else
{
lean_object* v___x_5212_; 
lean_inc(v_formatterName_5179_);
lean_inc_ref(v_f_5178_);
v___x_5212_ = l_Lean_Fmt_fmtWith(v_f_5178_, v_formatterName_5179_, v_v_5187_, v___y_5183_, v___y_5184_);
v___y_5191_ = v___x_5212_;
goto v___jp_5190_;
}
v___jp_5190_:
{
if (lean_obj_tag(v___y_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v_a_5193_; size_t v___x_5194_; size_t v___x_5195_; lean_object* v___x_5196_; 
v_a_5192_ = lean_ctor_get(v___y_5191_, 0);
lean_inc(v_a_5192_);
v_a_5193_ = lean_ctor_get(v___y_5191_, 1);
lean_inc(v_a_5193_);
lean_dec_ref_known(v___y_5191_, 2);
v___x_5194_ = ((size_t)1ULL);
v___x_5195_ = lean_usize_add(v_i_5181_, v___x_5194_);
v___x_5196_ = lean_array_uset(v_bs_x27_5189_, v_i_5181_, v_a_5192_);
v_i_5181_ = v___x_5195_;
v_bs_5182_ = v___x_5196_;
v___y_5184_ = v_a_5193_;
goto _start;
}
else
{
lean_object* v_a_5198_; lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
lean_dec_ref(v_bs_x27_5189_);
lean_dec(v_formatterName_5179_);
lean_dec_ref(v_f_5178_);
v_a_5198_ = lean_ctor_get(v___y_5191_, 0);
v_a_5199_ = lean_ctor_get(v___y_5191_, 1);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___y_5191_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___y_5191_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_inc(v_a_5198_);
lean_dec(v___y_5191_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5198_);
lean_ctor_set(v_reuseFailAlloc_5205_, 1, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object* v_f_5213_, lean_object* v_formatterName_5214_, lean_object* v_sz_5215_, lean_object* v_i_5216_, lean_object* v_bs_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
size_t v_sz_boxed_5220_; size_t v_i_boxed_5221_; lean_object* v_res_5222_; 
v_sz_boxed_5220_ = lean_unbox_usize(v_sz_5215_);
lean_dec(v_sz_5215_);
v_i_boxed_5221_ = lean_unbox_usize(v_i_5216_);
lean_dec(v_i_5216_);
v_res_5222_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5213_, v_formatterName_5214_, v_sz_boxed_5220_, v_i_boxed_5221_, v_bs_5217_, v___y_5218_, v___y_5219_);
lean_dec_ref(v___y_5218_);
return v_res_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object* v_f_5223_, lean_object* v_formatterName_5224_, lean_object* v_sepArray_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_){
_start:
{
size_t v_sz_5228_; size_t v___x_5229_; lean_object* v___x_5230_; 
v_sz_5228_ = lean_array_size(v_sepArray_5225_);
v___x_5229_ = ((size_t)0ULL);
v___x_5230_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5223_, v_formatterName_5224_, v_sz_5228_, v___x_5229_, v_sepArray_5225_, v_a_5226_, v_a_5227_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5239_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
v_a_5232_ = lean_ctor_get(v___x_5230_, 1);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5234_ = v___x_5230_;
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_inc(v_a_5231_);
lean_dec(v___x_5230_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5239_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___x_5237_; 
if (v_isShared_5235_ == 0)
{
v___x_5237_ = v___x_5234_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v_a_5231_);
lean_ctor_set(v_reuseFailAlloc_5238_, 1, v_a_5232_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
}
}
}
else
{
lean_object* v_a_5240_; lean_object* v_a_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5248_; 
v_a_5240_ = lean_ctor_get(v___x_5230_, 0);
v_a_5241_ = lean_ctor_get(v___x_5230_, 1);
v_isSharedCheck_5248_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5243_ = v___x_5230_;
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_a_5241_);
lean_inc(v_a_5240_);
lean_dec(v___x_5230_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5248_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5246_; 
if (v_isShared_5244_ == 0)
{
v___x_5246_ = v___x_5243_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5247_; 
v_reuseFailAlloc_5247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_a_5240_);
lean_ctor_set(v_reuseFailAlloc_5247_, 1, v_a_5241_);
v___x_5246_ = v_reuseFailAlloc_5247_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
return v___x_5246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object* v_f_5249_, lean_object* v_formatterName_5250_, lean_object* v_sepArray_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5249_, v_formatterName_5250_, v_sepArray_5251_, v_a_5252_, v_a_5253_);
lean_dec_ref(v_a_5252_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object* v_sep_5255_, lean_object* v_f_5256_, lean_object* v_formatterName_5257_, lean_object* v_sepArray_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5256_, v_formatterName_5257_, v_sepArray_5258_, v_a_5259_, v_a_5260_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object* v_sep_5262_, lean_object* v_f_5263_, lean_object* v_formatterName_5264_, lean_object* v_sepArray_5265_, lean_object* v_a_5266_, lean_object* v_a_5267_){
_start:
{
lean_object* v_res_5268_; 
v_res_5268_ = l_Lean_Fmt_fmtSepArrayWith(v_sep_5262_, v_f_5263_, v_formatterName_5264_, v_sepArray_5265_, v_a_5266_, v_a_5267_);
lean_dec_ref(v_a_5266_);
lean_dec_ref(v_sep_5262_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object* v_f_5269_, lean_object* v_formatterName_5270_, lean_object* v_as_5271_, size_t v_sz_5272_, size_t v_i_5273_, lean_object* v_bs_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
lean_object* v___x_5277_; 
v___x_5277_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5269_, v_formatterName_5270_, v_sz_5272_, v_i_5273_, v_bs_5274_, v___y_5275_, v___y_5276_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object* v_f_5278_, lean_object* v_formatterName_5279_, lean_object* v_as_5280_, lean_object* v_sz_5281_, lean_object* v_i_5282_, lean_object* v_bs_5283_, lean_object* v___y_5284_, lean_object* v___y_5285_){
_start:
{
size_t v_sz_boxed_5286_; size_t v_i_boxed_5287_; lean_object* v_res_5288_; 
v_sz_boxed_5286_ = lean_unbox_usize(v_sz_5281_);
lean_dec(v_sz_5281_);
v_i_boxed_5287_ = lean_unbox_usize(v_i_5282_);
lean_dec(v_i_5282_);
v_res_5288_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(v_f_5278_, v_formatterName_5279_, v_as_5280_, v_sz_boxed_5286_, v_i_boxed_5287_, v_bs_5283_, v___y_5284_, v___y_5285_);
lean_dec_ref(v___y_5284_);
lean_dec_ref(v_as_5280_);
return v_res_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object* v_sepArray_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_){
_start:
{
size_t v_sz_5292_; size_t v___x_5293_; lean_object* v___x_5294_; 
v_sz_5292_ = lean_array_size(v_sepArray_5289_);
v___x_5293_ = ((size_t)0ULL);
v___x_5294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5292_, v___x_5293_, v_sepArray_5289_, v_a_5290_, v_a_5291_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
v_a_5296_ = lean_ctor_get(v___x_5294_, 1);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5294_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_inc(v_a_5295_);
lean_dec(v___x_5294_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5295_);
lean_ctor_set(v_reuseFailAlloc_5302_, 1, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
else
{
lean_object* v_a_5304_; lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
v_a_5304_ = lean_ctor_get(v___x_5294_, 0);
v_a_5305_ = lean_ctor_get(v___x_5294_, 1);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5294_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_inc(v_a_5304_);
lean_dec(v___x_5294_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5304_);
lean_ctor_set(v_reuseFailAlloc_5311_, 1, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object* v_sepArray_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5313_, v_a_5314_, v_a_5315_);
lean_dec_ref(v_a_5314_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object* v_ks_5317_, lean_object* v_sep_5318_, lean_object* v_sepArray_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_){
_start:
{
lean_object* v___x_5322_; 
v___x_5322_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5319_, v_a_5320_, v_a_5321_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object* v_ks_5323_, lean_object* v_sep_5324_, lean_object* v_sepArray_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_Lean_Fmt_fmtTSepArray(v_ks_5323_, v_sep_5324_, v_sepArray_5325_, v_a_5326_, v_a_5327_);
lean_dec_ref(v_a_5326_);
lean_dec_ref(v_sep_5324_);
lean_dec(v_ks_5323_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object* v_f_5329_, lean_object* v_formatterName_5330_, lean_object* v_sepArray_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_){
_start:
{
size_t v_sz_5334_; size_t v___x_5335_; lean_object* v___x_5336_; 
v_sz_5334_ = lean_array_size(v_sepArray_5331_);
v___x_5335_ = ((size_t)0ULL);
v___x_5336_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5329_, v_formatterName_5330_, v_sz_5334_, v___x_5335_, v_sepArray_5331_, v_a_5332_, v_a_5333_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_a_5337_; lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
v_a_5338_ = lean_ctor_get(v___x_5336_, 1);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5340_ = v___x_5336_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_inc(v_a_5337_);
lean_dec(v___x_5336_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5337_);
lean_ctor_set(v_reuseFailAlloc_5344_, 1, v_a_5338_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
return v___x_5343_;
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v_a_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5354_; 
v_a_5346_ = lean_ctor_get(v___x_5336_, 0);
v_a_5347_ = lean_ctor_get(v___x_5336_, 1);
v_isSharedCheck_5354_ = !lean_is_exclusive(v___x_5336_);
if (v_isSharedCheck_5354_ == 0)
{
v___x_5349_ = v___x_5336_;
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_a_5347_);
lean_inc(v_a_5346_);
lean_dec(v___x_5336_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5354_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___x_5352_; 
if (v_isShared_5350_ == 0)
{
v___x_5352_ = v___x_5349_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5346_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v_a_5347_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object* v_f_5355_, lean_object* v_formatterName_5356_, lean_object* v_sepArray_5357_, lean_object* v_a_5358_, lean_object* v_a_5359_){
_start:
{
lean_object* v_res_5360_; 
v_res_5360_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5355_, v_formatterName_5356_, v_sepArray_5357_, v_a_5358_, v_a_5359_);
lean_dec_ref(v_a_5358_);
return v_res_5360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object* v_ks_5361_, lean_object* v_sep_5362_, lean_object* v_f_5363_, lean_object* v_formatterName_5364_, lean_object* v_sepArray_5365_, lean_object* v_a_5366_, lean_object* v_a_5367_){
_start:
{
lean_object* v___x_5368_; 
v___x_5368_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5363_, v_formatterName_5364_, v_sepArray_5365_, v_a_5366_, v_a_5367_);
return v___x_5368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object* v_ks_5369_, lean_object* v_sep_5370_, lean_object* v_f_5371_, lean_object* v_formatterName_5372_, lean_object* v_sepArray_5373_, lean_object* v_a_5374_, lean_object* v_a_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_Fmt_fmtTSepArrayWith(v_ks_5369_, v_sep_5370_, v_f_5371_, v_formatterName_5372_, v_sepArray_5373_, v_a_5374_, v_a_5375_);
lean_dec_ref(v_a_5374_);
lean_dec_ref(v_sep_5370_);
lean_dec(v_ks_5369_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(uint8_t v___x_5377_, lean_object* v___x_5378_, lean_object* v___x_5379_, lean_object* v___x_5380_, lean_object* v_a_5381_, lean_object* v_b_5382_){
_start:
{
lean_object* v___x_5383_; uint8_t v_decide_5384_; 
v___x_5383_ = lean_nat_sub(v___x_5378_, v___x_5379_);
v_decide_5384_ = lean_nat_dec_eq(v_a_5381_, v___x_5383_);
lean_dec(v___x_5383_);
if (v_decide_5384_ == 0)
{
uint32_t v___x_5385_; lean_object* v___x_5386_; uint32_t v___x_5387_; uint8_t v___x_5388_; 
v___x_5385_ = 10;
v___x_5386_ = lean_nat_add(v___x_5379_, v_a_5381_);
v___x_5387_ = lean_string_utf8_get_fast(v___x_5380_, v___x_5386_);
v___x_5388_ = lean_uint32_dec_eq(v___x_5387_, v___x_5385_);
if (v___x_5388_ == 0)
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
lean_dec(v_a_5381_);
v___x_5389_ = lean_string_utf8_next_fast(v___x_5380_, v___x_5386_);
lean_dec(v___x_5386_);
v___x_5390_ = lean_nat_sub(v___x_5389_, v___x_5379_);
v_a_5381_ = v___x_5390_;
goto _start;
}
else
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5392_ = lean_string_utf8_next_fast(v___x_5380_, v___x_5386_);
v___x_5393_ = lean_nat_sub(v___x_5392_, v___x_5386_);
lean_dec(v___x_5386_);
v___x_5394_ = lean_nat_add(v_a_5381_, v___x_5393_);
lean_dec(v___x_5393_);
lean_dec(v_a_5381_);
if (v___x_5377_ == 0)
{
v_a_5381_ = v___x_5394_;
goto _start;
}
else
{
lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5396_ = lean_unsigned_to_nat(1u);
v___x_5397_ = lean_nat_add(v_b_5382_, v___x_5396_);
lean_dec(v_b_5382_);
v_a_5381_ = v___x_5394_;
v_b_5382_ = v___x_5397_;
goto _start;
}
}
}
else
{
lean_dec(v_a_5381_);
return v_b_5382_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___x_5399_, lean_object* v___x_5400_, lean_object* v___x_5401_, lean_object* v___x_5402_, lean_object* v_a_5403_, lean_object* v_b_5404_){
_start:
{
uint8_t v___x_2013__boxed_5405_; lean_object* v_res_5406_; 
v___x_2013__boxed_5405_ = lean_unbox(v___x_5399_);
v_res_5406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_2013__boxed_5405_, v___x_5400_, v___x_5401_, v___x_5402_, v_a_5403_, v_b_5404_);
lean_dec_ref(v___x_5402_);
lean_dec(v___x_5401_);
lean_dec(v___x_5400_);
return v_res_5406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5409_, lean_object* v_minNewlines_5410_, lean_object* v_leadingTk_5411_, lean_object* v_leading_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_){
_start:
{
lean_object* v___y_5422_; lean_object* v___y_5433_; lean_object* v_str_5435_; lean_object* v_startPos_5436_; lean_object* v_stopPos_5437_; uint8_t v___x_5438_; 
v_str_5435_ = lean_ctor_get(v_leading_5412_, 0);
v_startPos_5436_ = lean_ctor_get(v_leading_5412_, 1);
v_stopPos_5437_ = lean_ctor_get(v_leading_5412_, 2);
v___x_5438_ = lean_string_is_valid_pos(v_str_5435_, v_startPos_5436_);
if (v___x_5438_ == 0)
{
lean_dec(v_minNewlines_5410_);
lean_dec(v_maxNewlines_5409_);
goto v___jp_5415_;
}
else
{
uint8_t v___x_5439_; 
v___x_5439_ = lean_string_is_valid_pos(v_str_5435_, v_stopPos_5437_);
if (v___x_5439_ == 0)
{
lean_dec(v_minNewlines_5410_);
lean_dec(v_maxNewlines_5409_);
goto v___jp_5415_;
}
else
{
uint8_t v___x_5440_; 
v___x_5440_ = lean_nat_dec_le(v_startPos_5436_, v_stopPos_5437_);
if (v___x_5440_ == 0)
{
lean_dec(v_minNewlines_5410_);
lean_dec(v_maxNewlines_5409_);
goto v___jp_5415_;
}
else
{
lean_object* v_searcher_5441_; lean_object* v_numNewlines_5442_; uint8_t v___x_5443_; 
lean_dec(v_leadingTk_5411_);
v_searcher_5441_ = lean_unsigned_to_nat(0u);
v_numNewlines_5442_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5440_, v_stopPos_5437_, v_startPos_5436_, v_str_5435_, v_searcher_5441_, v_searcher_5441_);
v___x_5443_ = lean_nat_dec_le(v_numNewlines_5442_, v_minNewlines_5410_);
if (v___x_5443_ == 0)
{
lean_dec(v_minNewlines_5410_);
v___y_5433_ = v_numNewlines_5442_;
goto v___jp_5432_;
}
else
{
lean_dec(v_numNewlines_5442_);
v___y_5433_ = v_minNewlines_5410_;
goto v___jp_5432_;
}
}
}
}
v___jp_5415_:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; 
v___x_5416_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5417_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5418_, 0, v_leadingTk_5411_);
lean_ctor_set(v___x_5418_, 1, v___x_5416_);
lean_ctor_set(v___x_5418_, 2, v___x_5417_);
v___x_5419_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5418_);
v___x_5420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5420_, 0, v___x_5419_);
lean_ctor_set(v___x_5420_, 1, v___y_5414_);
return v___x_5420_;
}
v___jp_5421_:
{
lean_object* v___x_5423_; lean_object* v_nls_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; 
v___x_5423_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5424_ = lean_mk_array(v___y_5422_, v___x_5423_);
v___x_5425_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5424_);
v___x_5426_ = lean_box(0);
v___x_5427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5427_, 0, v___x_5425_);
lean_ctor_set(v___x_5427_, 1, v___x_5426_);
v___x_5428_ = lean_unsigned_to_nat(1u);
v___x_5429_ = lean_mk_empty_array_with_capacity(v___x_5428_);
v___x_5430_ = lean_array_push(v___x_5429_, v___x_5427_);
v___x_5431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5430_);
lean_ctor_set(v___x_5431_, 1, v___y_5414_);
return v___x_5431_;
}
v___jp_5432_:
{
uint8_t v___x_5434_; 
v___x_5434_ = lean_nat_dec_le(v___y_5433_, v_maxNewlines_5409_);
if (v___x_5434_ == 0)
{
lean_dec(v___y_5433_);
v___y_5422_ = v_maxNewlines_5409_;
goto v___jp_5421_;
}
else
{
lean_dec(v_maxNewlines_5409_);
v___y_5422_ = v___y_5433_;
goto v___jp_5421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5444_, lean_object* v_minNewlines_5445_, lean_object* v_leadingTk_5446_, lean_object* v_leading_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(v_maxNewlines_5444_, v_minNewlines_5445_, v_leadingTk_5446_, v_leading_5447_, v___y_5448_, v___y_5449_);
lean_dec_ref(v___y_5448_);
lean_dec_ref(v_leading_5447_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object* v_stx_5451_, lean_object* v_minNewlines_5452_, lean_object* v_maxNewlines_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_){
_start:
{
lean_object* v___f_5456_; lean_object* v___x_5457_; 
v___f_5456_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5456_, 0, v_maxNewlines_5453_);
lean_closure_set(v___f_5456_, 1, v_minNewlines_5452_);
v___x_5457_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_5451_, v___f_5456_, v_a_5454_, v_a_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object* v_stx_5458_, lean_object* v_minNewlines_5459_, lean_object* v_maxNewlines_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines(v_stx_5458_, v_minNewlines_5459_, v_maxNewlines_5460_, v_a_5461_, v_a_5462_);
lean_dec_ref(v_a_5461_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(uint8_t v___x_5464_, lean_object* v___x_5465_, lean_object* v___x_5466_, lean_object* v___x_5467_, lean_object* v___x_5468_, lean_object* v_inst_5469_, lean_object* v_R_5470_, lean_object* v_a_5471_, lean_object* v_b_5472_, lean_object* v_c_5473_){
_start:
{
lean_object* v___x_5474_; 
v___x_5474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5464_, v___x_5465_, v___x_5466_, v___x_5468_, v_a_5471_, v_b_5472_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object* v___x_5475_, lean_object* v___x_5476_, lean_object* v___x_5477_, lean_object* v___x_5478_, lean_object* v___x_5479_, lean_object* v_inst_5480_, lean_object* v_R_5481_, lean_object* v_a_5482_, lean_object* v_b_5483_, lean_object* v_c_5484_){
_start:
{
uint8_t v___x_2122__boxed_5485_; lean_object* v_res_5486_; 
v___x_2122__boxed_5485_ = lean_unbox(v___x_5475_);
v_res_5486_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(v___x_2122__boxed_5485_, v___x_5476_, v___x_5477_, v___x_5478_, v___x_5479_, v_inst_5480_, v_R_5481_, v_a_5482_, v_b_5483_, v_c_5484_);
lean_dec_ref(v___x_5479_);
lean_dec_ref(v___x_5478_);
lean_dec(v___x_5477_);
lean_dec(v___x_5476_);
return v_res_5486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5487_, lean_object* v_minNewlines_5488_, lean_object* v_trailingTk_5489_, lean_object* v_trailing_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_){
_start:
{
lean_object* v___y_5500_; lean_object* v___y_5511_; lean_object* v_str_5513_; lean_object* v_startPos_5514_; lean_object* v_stopPos_5515_; uint8_t v___x_5516_; 
v_str_5513_ = lean_ctor_get(v_trailing_5490_, 0);
v_startPos_5514_ = lean_ctor_get(v_trailing_5490_, 1);
v_stopPos_5515_ = lean_ctor_get(v_trailing_5490_, 2);
v___x_5516_ = lean_string_is_valid_pos(v_str_5513_, v_startPos_5514_);
if (v___x_5516_ == 0)
{
lean_dec(v_minNewlines_5488_);
lean_dec(v_maxNewlines_5487_);
goto v___jp_5493_;
}
else
{
uint8_t v___x_5517_; 
v___x_5517_ = lean_string_is_valid_pos(v_str_5513_, v_stopPos_5515_);
if (v___x_5517_ == 0)
{
lean_dec(v_minNewlines_5488_);
lean_dec(v_maxNewlines_5487_);
goto v___jp_5493_;
}
else
{
uint8_t v___x_5518_; 
v___x_5518_ = lean_nat_dec_le(v_startPos_5514_, v_stopPos_5515_);
if (v___x_5518_ == 0)
{
lean_dec(v_minNewlines_5488_);
lean_dec(v_maxNewlines_5487_);
goto v___jp_5493_;
}
else
{
lean_object* v_searcher_5519_; lean_object* v_numNewlines_5520_; uint8_t v___x_5521_; 
lean_dec(v_trailingTk_5489_);
v_searcher_5519_ = lean_unsigned_to_nat(0u);
v_numNewlines_5520_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5518_, v_stopPos_5515_, v_startPos_5514_, v_str_5513_, v_searcher_5519_, v_searcher_5519_);
v___x_5521_ = lean_nat_dec_le(v_numNewlines_5520_, v_minNewlines_5488_);
if (v___x_5521_ == 0)
{
lean_dec(v_minNewlines_5488_);
v___y_5511_ = v_numNewlines_5520_;
goto v___jp_5510_;
}
else
{
lean_dec(v_numNewlines_5520_);
v___y_5511_ = v_minNewlines_5488_;
goto v___jp_5510_;
}
}
}
}
v___jp_5493_:
{
lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
v___x_5494_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5495_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_5496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5496_, 0, v_trailingTk_5489_);
lean_ctor_set(v___x_5496_, 1, v___x_5494_);
lean_ctor_set(v___x_5496_, 2, v___x_5495_);
v___x_5497_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5496_);
v___x_5498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5498_, 0, v___x_5497_);
lean_ctor_set(v___x_5498_, 1, v___y_5492_);
return v___x_5498_;
}
v___jp_5499_:
{
lean_object* v___x_5501_; lean_object* v_nls_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5501_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5502_ = lean_mk_array(v___y_5500_, v___x_5501_);
v___x_5503_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5502_);
v___x_5504_ = lean_box(0);
v___x_5505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5505_, 0, v___x_5503_);
lean_ctor_set(v___x_5505_, 1, v___x_5504_);
v___x_5506_ = lean_unsigned_to_nat(1u);
v___x_5507_ = lean_mk_empty_array_with_capacity(v___x_5506_);
v___x_5508_ = lean_array_push(v___x_5507_, v___x_5505_);
v___x_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5509_, 0, v___x_5508_);
lean_ctor_set(v___x_5509_, 1, v___y_5492_);
return v___x_5509_;
}
v___jp_5510_:
{
uint8_t v___x_5512_; 
v___x_5512_ = lean_nat_dec_le(v___y_5511_, v_maxNewlines_5487_);
if (v___x_5512_ == 0)
{
lean_dec(v___y_5511_);
v___y_5500_ = v_maxNewlines_5487_;
goto v___jp_5499_;
}
else
{
lean_dec(v_maxNewlines_5487_);
v___y_5500_ = v___y_5511_;
goto v___jp_5499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5522_, lean_object* v_minNewlines_5523_, lean_object* v_trailingTk_5524_, lean_object* v_trailing_5525_, lean_object* v___y_5526_, lean_object* v___y_5527_){
_start:
{
lean_object* v_res_5528_; 
v_res_5528_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(v_maxNewlines_5522_, v_minNewlines_5523_, v_trailingTk_5524_, v_trailing_5525_, v___y_5526_, v___y_5527_);
lean_dec_ref(v___y_5526_);
lean_dec_ref(v_trailing_5525_);
return v_res_5528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object* v_stx_5529_, lean_object* v_minNewlines_5530_, lean_object* v_maxNewlines_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_){
_start:
{
lean_object* v___f_5534_; lean_object* v___x_5535_; 
v___f_5534_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5534_, 0, v_maxNewlines_5531_);
lean_closure_set(v___f_5534_, 1, v_minNewlines_5530_);
v___x_5535_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_5529_, v___f_5534_, v_a_5532_, v_a_5533_);
return v___x_5535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object* v_stx_5536_, lean_object* v_minNewlines_5537_, lean_object* v_maxNewlines_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_){
_start:
{
lean_object* v_res_5541_; 
v_res_5541_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v_stx_5536_, v_minNewlines_5537_, v_maxNewlines_5538_, v_a_5539_, v_a_5540_);
lean_dec_ref(v_a_5539_);
return v_res_5541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object* v_b_5542_, lean_object* v_a_5543_, lean_object* v_trailingDoc_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_){
_start:
{
lean_object* v___y_5548_; uint8_t v___x_5552_; 
v___x_5552_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_5543_);
if (v___x_5552_ == 0)
{
uint8_t v___x_5553_; 
v___x_5553_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_trailingDoc_5544_);
if (v___x_5553_ == 0)
{
lean_object* v_doc_5554_; lean_object* v_doc_5555_; uint8_t v___x_5556_; 
v_doc_5554_ = lean_ctor_get(v_a_5543_, 0);
lean_inc(v_doc_5554_);
lean_dec_ref(v_a_5543_);
v_doc_5555_ = lean_ctor_get(v_trailingDoc_5544_, 0);
lean_inc(v_doc_5555_);
lean_dec_ref(v_trailingDoc_5544_);
v___x_5556_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5554_);
if (v___x_5556_ == 0)
{
uint8_t v___x_5557_; 
v___x_5557_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5555_);
if (v___x_5557_ == 0)
{
lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5558_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_5554_, v_doc_5555_);
v___x_5559_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_5558_);
v___y_5548_ = v___x_5559_;
goto v___jp_5547_;
}
else
{
lean_object* v___x_5560_; 
lean_dec(v_doc_5555_);
v___x_5560_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5554_);
v___y_5548_ = v___x_5560_;
goto v___jp_5547_;
}
}
else
{
lean_object* v___x_5561_; 
lean_dec(v_doc_5554_);
v___x_5561_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5555_);
v___y_5548_ = v___x_5561_;
goto v___jp_5547_;
}
}
else
{
lean_dec_ref(v_trailingDoc_5544_);
v___y_5548_ = v_a_5543_;
goto v___jp_5547_;
}
}
else
{
lean_dec_ref(v_a_5543_);
v___y_5548_ = v_trailingDoc_5544_;
goto v___jp_5547_;
}
v___jp_5547_:
{
lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5549_ = lean_array_push(v_b_5542_, v___y_5548_);
v___x_5550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5549_);
v___x_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5551_, 0, v___x_5550_);
lean_ctor_set(v___x_5551_, 1, v___y_5546_);
return v___x_5551_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object* v_b_5562_, lean_object* v_a_5563_, lean_object* v_trailingDoc_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_){
_start:
{
lean_object* v_res_5567_; 
v_res_5567_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5562_, v_a_5563_, v_trailingDoc_5564_, v___y_5565_, v___y_5566_);
lean_dec_ref(v___y_5565_);
return v_res_5567_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object* v_upperBound_5568_, lean_object* v_stxs_5569_, lean_object* v___x_5570_, lean_object* v_a_5571_, lean_object* v_b_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_){
_start:
{
uint8_t v___x_5575_; 
v___x_5575_ = lean_nat_dec_lt(v_a_5571_, v_upperBound_5568_);
if (v___x_5575_ == 0)
{
lean_object* v___x_5576_; 
lean_dec(v_a_5571_);
v___x_5576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5576_, 0, v_b_5572_);
lean_ctor_set(v___x_5576_, 1, v___y_5574_);
return v___x_5576_;
}
else
{
lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5577_ = lean_array_fget_borrowed(v_stxs_5569_, v_a_5571_);
lean_inc(v___x_5577_);
v___x_5578_ = l_Lean_Fmt_fmt(v___x_5577_, v___y_5573_, v___y_5574_);
if (lean_obj_tag(v___x_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v_a_5580_; lean_object* v___x_5581_; lean_object* v___y_5583_; lean_object* v___x_5608_; uint8_t v___x_5609_; 
v_a_5579_ = lean_ctor_get(v___x_5578_, 0);
lean_inc(v_a_5579_);
v_a_5580_ = lean_ctor_get(v___x_5578_, 1);
lean_inc(v_a_5580_);
lean_dec_ref_known(v___x_5578_, 2);
v___x_5581_ = lean_unsigned_to_nat(1u);
v___x_5608_ = lean_nat_sub(v___x_5570_, v___x_5581_);
v___x_5609_ = lean_nat_dec_lt(v_a_5571_, v___x_5608_);
lean_dec(v___x_5608_);
if (v___x_5609_ == 0)
{
lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5610_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5572_, v_a_5579_, v___x_5610_, v___y_5573_, v_a_5580_);
v___y_5583_ = v___x_5611_;
goto v___jp_5582_;
}
else
{
lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5612_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5577_);
v___x_5613_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v___x_5577_, v___x_5581_, v___x_5612_, v___y_5573_, v_a_5580_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_object* v_a_5614_; lean_object* v_a_5615_; lean_object* v___x_5616_; 
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
lean_inc(v_a_5614_);
v_a_5615_ = lean_ctor_get(v___x_5613_, 1);
lean_inc(v_a_5615_);
lean_dec_ref_known(v___x_5613_, 2);
v___x_5616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5572_, v_a_5579_, v_a_5614_, v___y_5573_, v_a_5615_);
v___y_5583_ = v___x_5616_;
goto v___jp_5582_;
}
else
{
lean_object* v_a_5617_; lean_object* v_a_5618_; lean_object* v___x_5620_; uint8_t v_isShared_5621_; uint8_t v_isSharedCheck_5625_; 
lean_dec(v_a_5579_);
lean_dec_ref(v_b_5572_);
lean_dec(v_a_5571_);
v_a_5617_ = lean_ctor_get(v___x_5613_, 0);
v_a_5618_ = lean_ctor_get(v___x_5613_, 1);
v_isSharedCheck_5625_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5625_ == 0)
{
v___x_5620_ = v___x_5613_;
v_isShared_5621_ = v_isSharedCheck_5625_;
goto v_resetjp_5619_;
}
else
{
lean_inc(v_a_5618_);
lean_inc(v_a_5617_);
lean_dec(v___x_5613_);
v___x_5620_ = lean_box(0);
v_isShared_5621_ = v_isSharedCheck_5625_;
goto v_resetjp_5619_;
}
v_resetjp_5619_:
{
lean_object* v___x_5623_; 
if (v_isShared_5621_ == 0)
{
v___x_5623_ = v___x_5620_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_a_5617_);
lean_ctor_set(v_reuseFailAlloc_5624_, 1, v_a_5618_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
}
v___jp_5582_:
{
if (lean_obj_tag(v___y_5583_) == 0)
{
lean_object* v_a_5584_; 
v_a_5584_ = lean_ctor_get(v___y_5583_, 0);
lean_inc(v_a_5584_);
if (lean_obj_tag(v_a_5584_) == 0)
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5593_; 
lean_dec(v_a_5571_);
v_a_5585_ = lean_ctor_get(v___y_5583_, 1);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___y_5583_);
if (v_isSharedCheck_5593_ == 0)
{
lean_object* v_unused_5594_; 
v_unused_5594_ = lean_ctor_get(v___y_5583_, 0);
lean_dec(v_unused_5594_);
v___x_5587_ = v___y_5583_;
v_isShared_5588_ = v_isSharedCheck_5593_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___y_5583_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5593_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v_a_5589_; lean_object* v___x_5591_; 
v_a_5589_ = lean_ctor_get(v_a_5584_, 0);
lean_inc(v_a_5589_);
lean_dec_ref_known(v_a_5584_, 1);
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 0, v_a_5589_);
v___x_5591_ = v___x_5587_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_a_5589_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v_a_5585_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
return v___x_5591_;
}
}
}
else
{
lean_object* v_a_5595_; lean_object* v_a_5596_; lean_object* v___x_5597_; 
v_a_5595_ = lean_ctor_get(v___y_5583_, 1);
lean_inc(v_a_5595_);
lean_dec_ref_known(v___y_5583_, 2);
v_a_5596_ = lean_ctor_get(v_a_5584_, 0);
lean_inc(v_a_5596_);
lean_dec_ref_known(v_a_5584_, 1);
v___x_5597_ = lean_nat_add(v_a_5571_, v___x_5581_);
lean_dec(v_a_5571_);
v_a_5571_ = v___x_5597_;
v_b_5572_ = v_a_5596_;
v___y_5574_ = v_a_5595_;
goto _start;
}
}
else
{
lean_object* v_a_5599_; lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
lean_dec(v_a_5571_);
v_a_5599_ = lean_ctor_get(v___y_5583_, 0);
v_a_5600_ = lean_ctor_get(v___y_5583_, 1);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___y_5583_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___y_5583_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_inc(v_a_5599_);
lean_dec(v___y_5583_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5599_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v_a_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
}
else
{
lean_object* v_a_5626_; lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5634_; 
lean_dec_ref(v_b_5572_);
lean_dec(v_a_5571_);
v_a_5626_ = lean_ctor_get(v___x_5578_, 0);
v_a_5627_ = lean_ctor_get(v___x_5578_, 1);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5578_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5629_ = v___x_5578_;
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_inc(v_a_5626_);
lean_dec(v___x_5578_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5632_; 
if (v_isShared_5630_ == 0)
{
v___x_5632_ = v___x_5629_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5626_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v_a_5627_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object* v_upperBound_5635_, lean_object* v_stxs_5636_, lean_object* v___x_5637_, lean_object* v_a_5638_, lean_object* v_b_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
lean_object* v_res_5642_; 
v_res_5642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5635_, v_stxs_5636_, v___x_5637_, v_a_5638_, v_b_5639_, v___y_5640_, v___y_5641_);
lean_dec_ref(v___y_5640_);
lean_dec(v___x_5637_);
lean_dec_ref(v_stxs_5636_);
lean_dec(v_upperBound_5635_);
return v_res_5642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object* v_stxs_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_){
_start:
{
lean_object* v___x_5648_; lean_object* v___x_5649_; uint8_t v___x_5650_; 
v___x_5648_ = lean_array_get_size(v_stxs_5645_);
v___x_5649_ = lean_unsigned_to_nat(1u);
v___x_5650_ = lean_nat_dec_eq(v___x_5648_, v___x_5649_);
if (v___x_5650_ == 0)
{
lean_object* v___x_5651_; lean_object* v_acc_5652_; lean_object* v___x_5653_; 
v___x_5651_ = lean_unsigned_to_nat(0u);
v_acc_5652_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_5653_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v___x_5648_, v_stxs_5645_, v___x_5648_, v___x_5651_, v_acc_5652_, v_a_5646_, v_a_5647_);
if (lean_obj_tag(v___x_5653_) == 0)
{
lean_object* v_a_5654_; lean_object* v_a_5655_; lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5663_; 
v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
v_a_5655_ = lean_ctor_get(v___x_5653_, 1);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5657_ = v___x_5653_;
v_isShared_5658_ = v_isSharedCheck_5663_;
goto v_resetjp_5656_;
}
else
{
lean_inc(v_a_5655_);
lean_inc(v_a_5654_);
lean_dec(v___x_5653_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5663_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v___x_5659_; lean_object* v___x_5661_; 
v___x_5659_ = l_Lean_Fmt_TaggedDoc_join(v_a_5654_);
if (v_isShared_5658_ == 0)
{
lean_ctor_set(v___x_5657_, 0, v___x_5659_);
v___x_5661_ = v___x_5657_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5659_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v_a_5655_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
else
{
lean_object* v_a_5664_; lean_object* v_a_5665_; lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5672_; 
v_a_5664_ = lean_ctor_get(v___x_5653_, 0);
v_a_5665_ = lean_ctor_get(v___x_5653_, 1);
v_isSharedCheck_5672_ = !lean_is_exclusive(v___x_5653_);
if (v_isSharedCheck_5672_ == 0)
{
v___x_5667_ = v___x_5653_;
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
else
{
lean_inc(v_a_5665_);
lean_inc(v_a_5664_);
lean_dec(v___x_5653_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v___x_5670_; 
if (v_isShared_5668_ == 0)
{
v___x_5670_ = v___x_5667_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v_a_5664_);
lean_ctor_set(v_reuseFailAlloc_5671_, 1, v_a_5665_);
v___x_5670_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
return v___x_5670_;
}
}
}
}
else
{
lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; 
v___x_5673_ = lean_box(0);
v___x_5674_ = lean_unsigned_to_nat(0u);
v___x_5675_ = lean_array_get_borrowed(v___x_5673_, v_stxs_5645_, v___x_5674_);
lean_inc(v___x_5675_);
v___x_5676_ = l_Lean_Fmt_fmt(v___x_5675_, v_a_5646_, v_a_5647_);
return v___x_5676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object* v_stxs_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_){
_start:
{
lean_object* v_res_5680_; 
v_res_5680_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(v_stxs_5677_, v_a_5678_, v_a_5679_);
lean_dec_ref(v_a_5678_);
lean_dec_ref(v_stxs_5677_);
return v_res_5680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object* v_upperBound_5681_, lean_object* v_stxs_5682_, lean_object* v___x_5683_, lean_object* v_inst_5684_, lean_object* v_R_5685_, lean_object* v_a_5686_, lean_object* v_b_5687_, lean_object* v_c_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
lean_object* v___x_5691_; 
v___x_5691_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5681_, v_stxs_5682_, v___x_5683_, v_a_5686_, v_b_5687_, v___y_5689_, v___y_5690_);
return v___x_5691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object* v_upperBound_5692_, lean_object* v_stxs_5693_, lean_object* v___x_5694_, lean_object* v_inst_5695_, lean_object* v_R_5696_, lean_object* v_a_5697_, lean_object* v_b_5698_, lean_object* v_c_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_){
_start:
{
lean_object* v_res_5702_; 
v_res_5702_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(v_upperBound_5692_, v_stxs_5693_, v___x_5694_, v_inst_5695_, v_R_5696_, v_a_5697_, v_b_5698_, v_c_5699_, v___y_5700_, v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___x_5694_);
lean_dec_ref(v_stxs_5693_);
lean_dec(v_upperBound_5692_);
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object* v_comments_5703_, lean_object* v_out_5704_, lean_object* v_a_5705_){
_start:
{
lean_object* v___x_5706_; uint8_t v___x_5707_; 
v___x_5706_ = lean_array_get_size(v_comments_5703_);
v___x_5707_ = lean_nat_dec_lt(v_a_5705_, v___x_5706_);
if (v___x_5707_ == 0)
{
return v_a_5705_;
}
else
{
lean_object* v___x_5708_; lean_object* v_originalWhitespaceRange_5709_; lean_object* v_stop_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; uint8_t v___x_5713_; 
v___x_5708_ = lean_array_fget_borrowed(v_comments_5703_, v_a_5705_);
v_originalWhitespaceRange_5709_ = lean_ctor_get(v___x_5708_, 1);
v_stop_5710_ = lean_ctor_get(v_originalWhitespaceRange_5709_, 1);
v___x_5711_ = lean_unsigned_to_nat(1u);
v___x_5712_ = lean_nat_add(v_out_5704_, v___x_5711_);
v___x_5713_ = lean_nat_dec_le(v___x_5712_, v_stop_5710_);
lean_dec(v___x_5712_);
if (v___x_5713_ == 0)
{
lean_object* v___x_5714_; 
v___x_5714_ = lean_nat_add(v_a_5705_, v___x_5711_);
lean_dec(v_a_5705_);
v_a_5705_ = v___x_5714_;
goto _start;
}
else
{
return v_a_5705_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object* v_comments_5716_, lean_object* v_out_5717_, lean_object* v_a_5718_){
_start:
{
lean_object* v_res_5719_; 
v_res_5719_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5716_, v_out_5717_, v_a_5718_);
lean_dec(v_out_5717_);
lean_dec_ref(v_comments_5716_);
return v_res_5719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_5720_, lean_object* v_x_5721_){
_start:
{
if (lean_obj_tag(v_x_5721_) == 0)
{
return v_x_5720_;
}
else
{
lean_object* v_key_5722_; lean_object* v_value_5723_; lean_object* v_tail_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5747_; 
v_key_5722_ = lean_ctor_get(v_x_5721_, 0);
v_value_5723_ = lean_ctor_get(v_x_5721_, 1);
v_tail_5724_ = lean_ctor_get(v_x_5721_, 2);
v_isSharedCheck_5747_ = !lean_is_exclusive(v_x_5721_);
if (v_isSharedCheck_5747_ == 0)
{
v___x_5726_ = v_x_5721_;
v_isShared_5727_ = v_isSharedCheck_5747_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_tail_5724_);
lean_inc(v_value_5723_);
lean_inc(v_key_5722_);
lean_dec(v_x_5721_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5747_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v___x_5728_; uint64_t v___x_5729_; uint64_t v___x_5730_; uint64_t v___x_5731_; uint64_t v_fold_5732_; uint64_t v___x_5733_; uint64_t v___x_5734_; uint64_t v___x_5735_; size_t v___x_5736_; size_t v___x_5737_; size_t v___x_5738_; size_t v___x_5739_; size_t v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5743_; 
v___x_5728_ = lean_array_get_size(v_x_5720_);
v___x_5729_ = lean_uint64_of_nat(v_key_5722_);
v___x_5730_ = 32ULL;
v___x_5731_ = lean_uint64_shift_right(v___x_5729_, v___x_5730_);
v_fold_5732_ = lean_uint64_xor(v___x_5729_, v___x_5731_);
v___x_5733_ = 16ULL;
v___x_5734_ = lean_uint64_shift_right(v_fold_5732_, v___x_5733_);
v___x_5735_ = lean_uint64_xor(v_fold_5732_, v___x_5734_);
v___x_5736_ = lean_uint64_to_usize(v___x_5735_);
v___x_5737_ = lean_usize_of_nat(v___x_5728_);
v___x_5738_ = ((size_t)1ULL);
v___x_5739_ = lean_usize_sub(v___x_5737_, v___x_5738_);
v___x_5740_ = lean_usize_land(v___x_5736_, v___x_5739_);
v___x_5741_ = lean_array_uget_borrowed(v_x_5720_, v___x_5740_);
lean_inc(v___x_5741_);
if (v_isShared_5727_ == 0)
{
lean_ctor_set(v___x_5726_, 2, v___x_5741_);
v___x_5743_ = v___x_5726_;
goto v_reusejp_5742_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_key_5722_);
lean_ctor_set(v_reuseFailAlloc_5746_, 1, v_value_5723_);
lean_ctor_set(v_reuseFailAlloc_5746_, 2, v___x_5741_);
v___x_5743_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5742_;
}
v_reusejp_5742_:
{
lean_object* v___x_5744_; 
v___x_5744_ = lean_array_uset(v_x_5720_, v___x_5740_, v___x_5743_);
v_x_5720_ = v___x_5744_;
v_x_5721_ = v_tail_5724_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object* v_i_5748_, lean_object* v_source_5749_, lean_object* v_target_5750_){
_start:
{
lean_object* v___x_5751_; uint8_t v___x_5752_; 
v___x_5751_ = lean_array_get_size(v_source_5749_);
v___x_5752_ = lean_nat_dec_lt(v_i_5748_, v___x_5751_);
if (v___x_5752_ == 0)
{
lean_dec_ref(v_source_5749_);
lean_dec(v_i_5748_);
return v_target_5750_;
}
else
{
lean_object* v_es_5753_; lean_object* v___x_5754_; lean_object* v_source_5755_; lean_object* v_target_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; 
v_es_5753_ = lean_array_fget(v_source_5749_, v_i_5748_);
v___x_5754_ = lean_box(0);
v_source_5755_ = lean_array_fset(v_source_5749_, v_i_5748_, v___x_5754_);
v_target_5756_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_target_5750_, v_es_5753_);
v___x_5757_ = lean_unsigned_to_nat(1u);
v___x_5758_ = lean_nat_add(v_i_5748_, v___x_5757_);
lean_dec(v_i_5748_);
v_i_5748_ = v___x_5758_;
v_source_5749_ = v_source_5755_;
v_target_5750_ = v_target_5756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object* v_data_5760_){
_start:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v_nbuckets_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; 
v___x_5761_ = lean_array_get_size(v_data_5760_);
v___x_5762_ = lean_unsigned_to_nat(2u);
v_nbuckets_5763_ = lean_nat_mul(v___x_5761_, v___x_5762_);
v___x_5764_ = lean_unsigned_to_nat(0u);
v___x_5765_ = lean_box(0);
v___x_5766_ = lean_mk_array(v_nbuckets_5763_, v___x_5765_);
v___x_5767_ = lean_array_propagate_mark(v_data_5760_, v___x_5766_);
v___x_5768_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v___x_5764_, v_data_5760_, v___x_5767_);
return v___x_5768_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object* v_a_5769_, lean_object* v_x_5770_){
_start:
{
if (lean_obj_tag(v_x_5770_) == 0)
{
uint8_t v___x_5771_; 
v___x_5771_ = 0;
return v___x_5771_;
}
else
{
lean_object* v_key_5772_; lean_object* v_tail_5773_; uint8_t v___x_5774_; 
v_key_5772_ = lean_ctor_get(v_x_5770_, 0);
v_tail_5773_ = lean_ctor_get(v_x_5770_, 2);
v___x_5774_ = lean_nat_dec_eq(v_key_5772_, v_a_5769_);
if (v___x_5774_ == 0)
{
v_x_5770_ = v_tail_5773_;
goto _start;
}
else
{
return v___x_5774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object* v_a_5776_, lean_object* v_x_5777_){
_start:
{
uint8_t v_res_5778_; lean_object* v_r_5779_; 
v_res_5778_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5776_, v_x_5777_);
lean_dec(v_x_5777_);
lean_dec(v_a_5776_);
v_r_5779_ = lean_box(v_res_5778_);
return v_r_5779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object* v_x_5782_){
_start:
{
if (lean_obj_tag(v_x_5782_) == 0)
{
lean_object* v___x_5783_; 
v___x_5783_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0));
return v___x_5783_;
}
else
{
lean_object* v_val_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5793_; 
v_val_5784_ = lean_ctor_get(v_x_5782_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v_x_5782_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5786_ = v_x_5782_;
v_isShared_5787_ = v_isSharedCheck_5793_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_val_5784_);
lean_dec(v_x_5782_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5793_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5791_; 
v___x_5788_ = lean_unsigned_to_nat(1u);
v___x_5789_ = lean_nat_add(v_val_5784_, v___x_5788_);
lean_dec(v_val_5784_);
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 0, v___x_5789_);
v___x_5791_ = v___x_5786_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v___x_5789_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5794_ = lean_box(0);
v___x_5795_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5794_);
return v___x_5795_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object* v_a_5796_, lean_object* v_x_5797_){
_start:
{
if (lean_obj_tag(v_x_5797_) == 0)
{
lean_object* v___x_5798_; lean_object* v_val_5799_; lean_object* v___x_5800_; 
v___x_5798_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0);
v_val_5799_ = lean_ctor_get(v___x_5798_, 0);
lean_inc(v_val_5799_);
v___x_5800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5800_, 0, v_a_5796_);
lean_ctor_set(v___x_5800_, 1, v_val_5799_);
lean_ctor_set(v___x_5800_, 2, v_x_5797_);
return v___x_5800_;
}
else
{
lean_object* v_key_5801_; lean_object* v_value_5802_; lean_object* v_tail_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5818_; 
v_key_5801_ = lean_ctor_get(v_x_5797_, 0);
v_value_5802_ = lean_ctor_get(v_x_5797_, 1);
v_tail_5803_ = lean_ctor_get(v_x_5797_, 2);
v_isSharedCheck_5818_ = !lean_is_exclusive(v_x_5797_);
if (v_isSharedCheck_5818_ == 0)
{
v___x_5805_ = v_x_5797_;
v_isShared_5806_ = v_isSharedCheck_5818_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_tail_5803_);
lean_inc(v_value_5802_);
lean_inc(v_key_5801_);
lean_dec(v_x_5797_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5818_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
uint8_t v___x_5807_; 
v___x_5807_ = lean_nat_dec_eq(v_key_5801_, v_a_5796_);
if (v___x_5807_ == 0)
{
lean_object* v_tail_5808_; lean_object* v___x_5810_; 
v_tail_5808_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5796_, v_tail_5803_);
if (v_isShared_5806_ == 0)
{
lean_ctor_set(v___x_5805_, 2, v_tail_5808_);
v___x_5810_ = v___x_5805_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v_key_5801_);
lean_ctor_set(v_reuseFailAlloc_5811_, 1, v_value_5802_);
lean_ctor_set(v_reuseFailAlloc_5811_, 2, v_tail_5808_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
else
{
lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v_val_5814_; lean_object* v___x_5816_; 
lean_dec(v_key_5801_);
v___x_5812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5812_, 0, v_value_5802_);
v___x_5813_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5812_);
v_val_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_val_5814_);
lean_dec(v___x_5813_);
if (v_isShared_5806_ == 0)
{
lean_ctor_set(v___x_5805_, 1, v_val_5814_);
lean_ctor_set(v___x_5805_, 0, v_a_5796_);
v___x_5816_ = v___x_5805_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5796_);
lean_ctor_set(v_reuseFailAlloc_5817_, 1, v_val_5814_);
lean_ctor_set(v_reuseFailAlloc_5817_, 2, v_tail_5803_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
return v___x_5816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object* v_m_5819_, lean_object* v_a_5820_){
_start:
{
lean_object* v_size_5821_; lean_object* v_buckets_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5870_; 
v_size_5821_ = lean_ctor_get(v_m_5819_, 0);
v_buckets_5822_ = lean_ctor_get(v_m_5819_, 1);
v_isSharedCheck_5870_ = !lean_is_exclusive(v_m_5819_);
if (v_isSharedCheck_5870_ == 0)
{
v___x_5824_ = v_m_5819_;
v_isShared_5825_ = v_isSharedCheck_5870_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_buckets_5822_);
lean_inc(v_size_5821_);
lean_dec(v_m_5819_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5870_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5826_; uint64_t v___x_5827_; uint64_t v___x_5828_; uint64_t v___x_5829_; uint64_t v_fold_5830_; uint64_t v___x_5831_; uint64_t v___x_5832_; uint64_t v___x_5833_; size_t v___x_5834_; size_t v___x_5835_; size_t v___x_5836_; size_t v___x_5837_; size_t v___x_5838_; lean_object* v_bkt_5839_; uint8_t v___x_5840_; 
v___x_5826_ = lean_array_get_size(v_buckets_5822_);
v___x_5827_ = lean_uint64_of_nat(v_a_5820_);
v___x_5828_ = 32ULL;
v___x_5829_ = lean_uint64_shift_right(v___x_5827_, v___x_5828_);
v_fold_5830_ = lean_uint64_xor(v___x_5827_, v___x_5829_);
v___x_5831_ = 16ULL;
v___x_5832_ = lean_uint64_shift_right(v_fold_5830_, v___x_5831_);
v___x_5833_ = lean_uint64_xor(v_fold_5830_, v___x_5832_);
v___x_5834_ = lean_uint64_to_usize(v___x_5833_);
v___x_5835_ = lean_usize_of_nat(v___x_5826_);
v___x_5836_ = ((size_t)1ULL);
v___x_5837_ = lean_usize_sub(v___x_5835_, v___x_5836_);
v___x_5838_ = lean_usize_land(v___x_5834_, v___x_5837_);
v_bkt_5839_ = lean_array_uget_borrowed(v_buckets_5822_, v___x_5838_);
v___x_5840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5820_, v_bkt_5839_);
if (v___x_5840_ == 0)
{
lean_object* v___x_5841_; lean_object* v_size_x27_5842_; lean_object* v___x_5843_; lean_object* v_buckets_x27_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; uint8_t v___x_5850_; 
v___x_5841_ = lean_unsigned_to_nat(1u);
v_size_x27_5842_ = lean_nat_add(v_size_5821_, v___x_5841_);
lean_dec(v_size_5821_);
lean_inc(v_bkt_5839_);
v___x_5843_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5843_, 0, v_a_5820_);
lean_ctor_set(v___x_5843_, 1, v___x_5841_);
lean_ctor_set(v___x_5843_, 2, v_bkt_5839_);
v_buckets_x27_5844_ = lean_array_uset(v_buckets_5822_, v___x_5838_, v___x_5843_);
v___x_5845_ = lean_unsigned_to_nat(4u);
v___x_5846_ = lean_nat_mul(v_size_x27_5842_, v___x_5845_);
v___x_5847_ = lean_unsigned_to_nat(3u);
v___x_5848_ = lean_nat_div(v___x_5846_, v___x_5847_);
lean_dec(v___x_5846_);
v___x_5849_ = lean_array_get_size(v_buckets_x27_5844_);
v___x_5850_ = lean_nat_dec_le(v___x_5848_, v___x_5849_);
lean_dec(v___x_5848_);
if (v___x_5850_ == 0)
{
lean_object* v_val_5851_; lean_object* v___x_5853_; 
v_val_5851_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_buckets_x27_5844_);
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 1, v_val_5851_);
lean_ctor_set(v___x_5824_, 0, v_size_x27_5842_);
v___x_5853_ = v___x_5824_;
goto v_reusejp_5852_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_size_x27_5842_);
lean_ctor_set(v_reuseFailAlloc_5854_, 1, v_val_5851_);
v___x_5853_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5852_;
}
v_reusejp_5852_:
{
return v___x_5853_;
}
}
else
{
lean_object* v___x_5856_; 
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 1, v_buckets_x27_5844_);
lean_ctor_set(v___x_5824_, 0, v_size_x27_5842_);
v___x_5856_ = v___x_5824_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_size_x27_5842_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_buckets_x27_5844_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
return v___x_5856_;
}
}
}
else
{
lean_object* v___x_5858_; lean_object* v_buckets_x27_5859_; lean_object* v_bkt_x27_5860_; lean_object* v___y_5862_; uint8_t v___x_5867_; 
lean_inc(v_bkt_5839_);
v___x_5858_ = lean_box(0);
v_buckets_x27_5859_ = lean_array_uset(v_buckets_5822_, v___x_5838_, v___x_5858_);
lean_inc(v_a_5820_);
v_bkt_x27_5860_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5820_, v_bkt_5839_);
v___x_5867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5820_, v_bkt_x27_5860_);
lean_dec(v_a_5820_);
if (v___x_5867_ == 0)
{
lean_object* v___x_5868_; lean_object* v___x_5869_; 
v___x_5868_ = lean_unsigned_to_nat(1u);
v___x_5869_ = lean_nat_sub(v_size_5821_, v___x_5868_);
lean_dec(v_size_5821_);
v___y_5862_ = v___x_5869_;
goto v___jp_5861_;
}
else
{
v___y_5862_ = v_size_5821_;
goto v___jp_5861_;
}
v___jp_5861_:
{
lean_object* v___x_5863_; lean_object* v___x_5865_; 
v___x_5863_ = lean_array_uset(v_buckets_x27_5859_, v___x_5838_, v_bkt_x27_5860_);
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 1, v___x_5863_);
lean_ctor_set(v___x_5824_, 0, v___y_5862_);
v___x_5865_ = v___x_5824_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___y_5862_);
lean_ctor_set(v_reuseFailAlloc_5866_, 1, v___x_5863_);
v___x_5865_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
return v___x_5865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object* v_fst_5871_, lean_object* v___x_5872_, lean_object* v_____r_5873_){
_start:
{
lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; 
lean_inc(v___x_5872_);
v___x_5874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(v_fst_5871_, v___x_5872_);
v___x_5875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5875_, 0, v___x_5874_);
lean_ctor_set(v___x_5875_, 1, v___x_5872_);
v___x_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5876_, 0, v___x_5875_);
return v___x_5876_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object* v_comments_5877_, lean_object* v_whitespace_5878_, lean_object* v_a_5879_, lean_object* v_b_5880_){
_start:
{
lean_object* v_str_5881_; lean_object* v_startInclusive_5882_; lean_object* v_endExclusive_5883_; lean_object* v___x_5884_; uint8_t v_decide_5885_; 
v_str_5881_ = lean_ctor_get(v_whitespace_5878_, 0);
v_startInclusive_5882_ = lean_ctor_get(v_whitespace_5878_, 1);
v_endExclusive_5883_ = lean_ctor_get(v_whitespace_5878_, 2);
v___x_5884_ = lean_nat_sub(v_endExclusive_5883_, v_startInclusive_5882_);
v_decide_5885_ = lean_nat_dec_eq(v_a_5879_, v___x_5884_);
lean_dec(v___x_5884_);
if (v_decide_5885_ == 0)
{
uint32_t v___x_5886_; lean_object* v___x_5887_; uint32_t v___x_5888_; uint8_t v___x_5889_; 
v___x_5886_ = 10;
v___x_5887_ = lean_nat_add(v_startInclusive_5882_, v_a_5879_);
v___x_5888_ = lean_string_utf8_get_fast(v_str_5881_, v___x_5887_);
v___x_5889_ = lean_uint32_dec_eq(v___x_5888_, v___x_5886_);
if (v___x_5889_ == 0)
{
lean_object* v___x_5890_; lean_object* v___x_5891_; 
lean_dec(v_a_5879_);
v___x_5890_ = lean_string_utf8_next_fast(v_str_5881_, v___x_5887_);
lean_dec(v___x_5887_);
v___x_5891_ = lean_nat_sub(v___x_5890_, v_startInclusive_5882_);
v_a_5879_ = v___x_5891_;
goto _start;
}
else
{
lean_object* v_fst_5893_; lean_object* v_snd_5894_; lean_object* v___x_5896_; uint8_t v_isShared_5897_; uint8_t v_isSharedCheck_5920_; 
v_fst_5893_ = lean_ctor_get(v_b_5880_, 0);
v_snd_5894_ = lean_ctor_get(v_b_5880_, 1);
v_isSharedCheck_5920_ = !lean_is_exclusive(v_b_5880_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5896_ = v_b_5880_;
v_isShared_5897_ = v_isSharedCheck_5920_;
goto v_resetjp_5895_;
}
else
{
lean_inc(v_snd_5894_);
lean_inc(v_fst_5893_);
lean_dec(v_b_5880_);
v___x_5896_ = lean_box(0);
v_isShared_5897_ = v_isSharedCheck_5920_;
goto v_resetjp_5895_;
}
v_resetjp_5895_:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v_val_5902_; lean_object* v___x_5906_; lean_object* v___x_5907_; uint8_t v___x_5908_; 
v___x_5898_ = lean_string_utf8_next_fast(v_str_5881_, v___x_5887_);
v___x_5899_ = lean_nat_sub(v___x_5898_, v___x_5887_);
v___x_5900_ = lean_nat_add(v_a_5879_, v___x_5899_);
lean_dec(v___x_5899_);
lean_dec(v_a_5879_);
v___x_5906_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5877_, v___x_5887_, v_snd_5894_);
v___x_5907_ = lean_array_get_size(v_comments_5877_);
v___x_5908_ = lean_nat_dec_lt(v___x_5906_, v___x_5907_);
if (v___x_5908_ == 0)
{
lean_object* v___x_5909_; lean_object* v___x_5910_; 
lean_del_object(v___x_5896_);
lean_dec(v___x_5887_);
v___x_5909_ = lean_box(0);
v___x_5910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5893_, v___x_5906_, v___x_5909_);
v_val_5902_ = v___x_5910_;
goto v___jp_5901_;
}
else
{
lean_object* v___x_5911_; lean_object* v_originalWhitespaceRange_5912_; uint8_t v___x_5913_; 
v___x_5911_ = lean_array_fget_borrowed(v_comments_5877_, v___x_5906_);
v_originalWhitespaceRange_5912_ = lean_ctor_get(v___x_5911_, 1);
v___x_5913_ = l_Lean_Syntax_Range_contains(v_originalWhitespaceRange_5912_, v___x_5887_, v_decide_5885_);
lean_dec(v___x_5887_);
if (v___x_5913_ == 0)
{
lean_object* v___x_5914_; lean_object* v___x_5915_; 
lean_del_object(v___x_5896_);
v___x_5914_ = lean_box(0);
v___x_5915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5893_, v___x_5906_, v___x_5914_);
v_val_5902_ = v___x_5915_;
goto v___jp_5901_;
}
else
{
lean_object* v___x_5917_; 
if (v_isShared_5897_ == 0)
{
lean_ctor_set(v___x_5896_, 1, v___x_5906_);
v___x_5917_ = v___x_5896_;
goto v_reusejp_5916_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_fst_5893_);
lean_ctor_set(v_reuseFailAlloc_5919_, 1, v___x_5906_);
v___x_5917_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5916_;
}
v_reusejp_5916_:
{
v_a_5879_ = v___x_5900_;
v_b_5880_ = v___x_5917_;
goto _start;
}
}
}
v___jp_5901_:
{
if (lean_obj_tag(v_val_5902_) == 0)
{
lean_object* v_a_5903_; 
lean_dec(v___x_5900_);
v_a_5903_ = lean_ctor_get(v_val_5902_, 0);
lean_inc(v_a_5903_);
lean_dec_ref_known(v_val_5902_, 1);
return v_a_5903_;
}
else
{
lean_object* v_a_5904_; 
v_a_5904_ = lean_ctor_get(v_val_5902_, 0);
lean_inc(v_a_5904_);
lean_dec_ref_known(v_val_5902_, 1);
v_a_5879_ = v___x_5900_;
v_b_5880_ = v_a_5904_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_5879_);
return v_b_5880_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object* v_comments_5921_, lean_object* v_whitespace_5922_, lean_object* v_a_5923_, lean_object* v_b_5924_){
_start:
{
lean_object* v_res_5925_; 
v_res_5925_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5921_, v_whitespace_5922_, v_a_5923_, v_b_5924_);
lean_dec_ref(v_whitespace_5922_);
lean_dec_ref(v_comments_5921_);
return v_res_5925_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0(void){
_start:
{
lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; 
v___x_5926_ = lean_box(0);
v___x_5927_ = lean_unsigned_to_nat(16u);
v___x_5928_ = lean_mk_array(v___x_5927_, v___x_5926_);
return v___x_5928_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1(void){
_start:
{
lean_object* v___x_5929_; lean_object* v_newlinePositions_5930_; lean_object* v_newlinesBeforeComment_5931_; 
v___x_5929_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0);
v_newlinePositions_5930_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_newlinesBeforeComment_5931_, 0, v_newlinePositions_5930_);
lean_ctor_set(v_newlinesBeforeComment_5931_, 1, v___x_5929_);
return v_newlinesBeforeComment_5931_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2(void){
_start:
{
lean_object* v_newlinePositions_5932_; lean_object* v_newlinesBeforeComment_5933_; lean_object* v___x_5934_; 
v_newlinePositions_5932_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5933_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1);
v___x_5934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5934_, 0, v_newlinesBeforeComment_5933_);
lean_ctor_set(v___x_5934_, 1, v_newlinePositions_5932_);
return v___x_5934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object* v_comments_5935_, lean_object* v_whitespace_5936_){
_start:
{
lean_object* v_newlinePositions_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v_fst_5940_; 
v_newlinePositions_5937_ = lean_unsigned_to_nat(0u);
v___x_5938_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2);
v___x_5939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5935_, v_whitespace_5936_, v_newlinePositions_5937_, v___x_5938_);
v_fst_5940_ = lean_ctor_get(v___x_5939_, 0);
lean_inc(v_fst_5940_);
lean_dec_ref(v___x_5939_);
return v_fst_5940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object* v_comments_5941_, lean_object* v_whitespace_5942_){
_start:
{
lean_object* v_res_5943_; 
v_res_5943_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v_comments_5941_, v_whitespace_5942_);
lean_dec_ref(v_whitespace_5942_);
lean_dec_ref(v_comments_5941_);
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object* v_comments_5944_, lean_object* v_out_5945_, lean_object* v_inst_5946_, lean_object* v_a_5947_){
_start:
{
lean_object* v___x_5948_; 
v___x_5948_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5944_, v_out_5945_, v_a_5947_);
return v___x_5948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object* v_comments_5949_, lean_object* v_out_5950_, lean_object* v_inst_5951_, lean_object* v_a_5952_){
_start:
{
lean_object* v_res_5953_; 
v_res_5953_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(v_comments_5949_, v_out_5950_, v_inst_5951_, v_a_5952_);
lean_dec(v_out_5950_);
lean_dec_ref(v_comments_5949_);
return v_res_5953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object* v_comments_5954_, lean_object* v_whitespace_5955_, lean_object* v_inst_5956_, lean_object* v_R_5957_, lean_object* v_a_5958_, lean_object* v_b_5959_, lean_object* v_c_5960_){
_start:
{
lean_object* v___x_5961_; 
v___x_5961_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5954_, v_whitespace_5955_, v_a_5958_, v_b_5959_);
return v___x_5961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object* v_comments_5962_, lean_object* v_whitespace_5963_, lean_object* v_inst_5964_, lean_object* v_R_5965_, lean_object* v_a_5966_, lean_object* v_b_5967_, lean_object* v_c_5968_){
_start:
{
lean_object* v_res_5969_; 
v_res_5969_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(v_comments_5962_, v_whitespace_5963_, v_inst_5964_, v_R_5965_, v_a_5966_, v_b_5967_, v_c_5968_);
lean_dec_ref(v_whitespace_5963_);
lean_dec_ref(v_comments_5962_);
return v_res_5969_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object* v_00_u03b2_5970_, lean_object* v_a_5971_, lean_object* v_x_5972_){
_start:
{
uint8_t v___x_5973_; 
v___x_5973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5971_, v_x_5972_);
return v___x_5973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object* v_00_u03b2_5974_, lean_object* v_a_5975_, lean_object* v_x_5976_){
_start:
{
uint8_t v_res_5977_; lean_object* v_r_5978_; 
v_res_5977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(v_00_u03b2_5974_, v_a_5975_, v_x_5976_);
lean_dec(v_x_5976_);
lean_dec(v_a_5975_);
v_r_5978_ = lean_box(v_res_5977_);
return v_r_5978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object* v_00_u03b2_5979_, lean_object* v_data_5980_){
_start:
{
lean_object* v___x_5981_; 
v___x_5981_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_data_5980_);
return v___x_5981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_5982_, lean_object* v_i_5983_, lean_object* v_source_5984_, lean_object* v_target_5985_){
_start:
{
lean_object* v___x_5986_; 
v___x_5986_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v_i_5983_, v_source_5984_, v_target_5985_);
return v___x_5986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_5987_, lean_object* v_x_5988_, lean_object* v_x_5989_){
_start:
{
lean_object* v___x_5990_; 
v___x_5990_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_x_5988_, v_x_5989_);
return v___x_5990_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_5994_; 
v___x_5994_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0));
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___dummy_5995_){
_start:
{
lean_object* v_res_5996_; 
v_res_5996_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v_res_5996_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5997_; 
v___x_5997_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v___x_5997_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object* v_s_5998_){
_start:
{
lean_object* v___x_5999_; 
v___x_5999_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
return v___x_5999_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object* v_s_6000_){
_start:
{
lean_object* v_res_6001_; 
v_res_6001_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(v_s_6000_);
lean_dec_ref(v_s_6000_);
return v_res_6001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t v_sz_6002_, size_t v_i_6003_, lean_object* v_bs_6004_){
_start:
{
uint8_t v___x_6005_; 
v___x_6005_ = lean_usize_dec_lt(v_i_6003_, v_sz_6002_);
if (v___x_6005_ == 0)
{
return v_bs_6004_;
}
else
{
lean_object* v_v_6006_; lean_object* v_rendered_6007_; lean_object* v___x_6008_; lean_object* v_bs_x27_6009_; size_t v___x_6010_; size_t v___x_6011_; lean_object* v___x_6012_; 
v_v_6006_ = lean_array_uget_borrowed(v_bs_6004_, v_i_6003_);
v_rendered_6007_ = lean_ctor_get(v_v_6006_, 0);
lean_inc_ref(v_rendered_6007_);
v___x_6008_ = lean_unsigned_to_nat(0u);
v_bs_x27_6009_ = lean_array_uset(v_bs_6004_, v_i_6003_, v___x_6008_);
v___x_6010_ = ((size_t)1ULL);
v___x_6011_ = lean_usize_add(v_i_6003_, v___x_6010_);
v___x_6012_ = lean_array_uset(v_bs_x27_6009_, v_i_6003_, v_rendered_6007_);
v_i_6003_ = v___x_6011_;
v_bs_6004_ = v___x_6012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object* v_sz_6014_, lean_object* v_i_6015_, lean_object* v_bs_6016_){
_start:
{
size_t v_sz_boxed_6017_; size_t v_i_boxed_6018_; lean_object* v_res_6019_; 
v_sz_boxed_6017_ = lean_unbox_usize(v_sz_6014_);
lean_dec(v_sz_6014_);
v_i_boxed_6018_ = lean_unbox_usize(v_i_6015_);
lean_dec(v_i_6015_);
v_res_6019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_boxed_6017_, v_i_boxed_6018_, v_bs_6016_);
return v_res_6019_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6020_ = lean_box(0);
v___x_6021_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6021_);
lean_ctor_set(v___x_6022_, 1, v___x_6020_);
return v___x_6022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object* v_upperBound_6023_, lean_object* v_next_6024_, lean_object* v_upperBound_6025_, lean_object* v_a_6026_, lean_object* v_b_6027_){
_start:
{
uint8_t v___x_6028_; 
v___x_6028_ = lean_nat_dec_lt(v_a_6026_, v_upperBound_6023_);
if (v___x_6028_ == 0)
{
lean_dec(v_a_6026_);
return v_b_6027_;
}
else
{
lean_object* v_fst_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6043_; 
v_fst_6029_ = lean_ctor_get(v_b_6027_, 0);
v_isSharedCheck_6043_ = !lean_is_exclusive(v_b_6027_);
if (v_isSharedCheck_6043_ == 0)
{
lean_object* v_unused_6044_; 
v_unused_6044_ = lean_ctor_get(v_b_6027_, 1);
lean_dec(v_unused_6044_);
v___x_6031_ = v_b_6027_;
v_isShared_6032_ = v_isSharedCheck_6043_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_fst_6029_);
lean_dec(v_b_6027_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6043_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
uint8_t v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6038_; 
v___x_6033_ = lean_nat_dec_lt(v_next_6024_, v_upperBound_6025_);
v___x_6034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6035_ = lean_array_push(v_fst_6029_, v___x_6034_);
v___x_6036_ = lean_box(v___x_6033_);
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 1, v___x_6036_);
lean_ctor_set(v___x_6031_, 0, v___x_6035_);
v___x_6038_ = v___x_6031_;
goto v_reusejp_6037_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v___x_6035_);
lean_ctor_set(v_reuseFailAlloc_6042_, 1, v___x_6036_);
v___x_6038_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6037_;
}
v_reusejp_6037_:
{
lean_object* v___x_6039_; lean_object* v___x_6040_; 
v___x_6039_ = lean_unsigned_to_nat(1u);
v___x_6040_ = lean_nat_add(v_a_6026_, v___x_6039_);
lean_dec(v_a_6026_);
v_a_6026_ = v___x_6040_;
v_b_6027_ = v___x_6038_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object* v_upperBound_6045_, lean_object* v_next_6046_, lean_object* v_upperBound_6047_, lean_object* v_a_6048_, lean_object* v_b_6049_){
_start:
{
lean_object* v_res_6050_; 
v_res_6050_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6045_, v_next_6046_, v_upperBound_6047_, v_a_6048_, v_b_6049_);
lean_dec(v_upperBound_6047_);
lean_dec(v_next_6046_);
lean_dec(v_upperBound_6045_);
return v_res_6050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(lean_object* v_originalWhitespaceRange_6051_, lean_object* v_fst_6052_, lean_object* v_____r_6053_, uint8_t v_insertedAnyNewlines_6054_, lean_object* v_d_6055_){
_start:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; 
v___x_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6056_, 0, v_originalWhitespaceRange_6051_);
v___x_6057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6057_, 0, v_d_6055_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___x_6058_ = lean_array_push(v_fst_6052_, v___x_6057_);
v___x_6059_ = lean_box(v_insertedAnyNewlines_6054_);
v___x_6060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6058_);
lean_ctor_set(v___x_6060_, 1, v___x_6059_);
v___x_6061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6060_);
return v___x_6061_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed(lean_object* v_originalWhitespaceRange_6062_, lean_object* v_fst_6063_, lean_object* v_____r_6064_, lean_object* v_insertedAnyNewlines_6065_, lean_object* v_d_6066_){
_start:
{
uint8_t v_insertedAnyNewlines_boxed_6067_; lean_object* v_res_6068_; 
v_insertedAnyNewlines_boxed_6067_ = lean_unbox(v_insertedAnyNewlines_6065_);
v_res_6068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6062_, v_fst_6063_, v_____r_6064_, v_insertedAnyNewlines_boxed_6067_, v_d_6066_);
return v_res_6068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object* v_a_6069_, lean_object* v___x_6070_, lean_object* v___x_6071_, lean_object* v_a_6072_, lean_object* v_b_6073_){
_start:
{
lean_object* v_it_6075_; lean_object* v_startInclusive_6076_; lean_object* v_endExclusive_6077_; 
if (lean_obj_tag(v_a_6072_) == 0)
{
lean_object* v_currPos_6083_; lean_object* v_searcher_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6107_; 
v_currPos_6083_ = lean_ctor_get(v_a_6072_, 0);
v_searcher_6084_ = lean_ctor_get(v_a_6072_, 1);
v_isSharedCheck_6107_ = !lean_is_exclusive(v_a_6072_);
if (v_isSharedCheck_6107_ == 0)
{
v___x_6086_ = v_a_6072_;
v_isShared_6087_ = v_isSharedCheck_6107_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_searcher_6084_);
lean_inc(v_currPos_6083_);
lean_dec(v_a_6072_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6107_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
uint8_t v_decide_6088_; 
v_decide_6088_ = lean_nat_dec_eq(v_searcher_6084_, v___x_6071_);
if (v_decide_6088_ == 0)
{
uint32_t v___x_6089_; uint32_t v___x_6090_; uint8_t v___x_6091_; 
v___x_6089_ = 10;
v___x_6090_ = lean_string_utf8_get_fast(v_a_6069_, v_searcher_6084_);
v___x_6091_ = lean_uint32_dec_eq(v___x_6090_, v___x_6089_);
if (v___x_6091_ == 0)
{
lean_object* v___x_6092_; lean_object* v___x_6094_; 
v___x_6092_ = lean_string_utf8_next_fast(v_a_6069_, v_searcher_6084_);
lean_dec(v_searcher_6084_);
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 1, v___x_6092_);
v___x_6094_ = v___x_6086_;
goto v_reusejp_6093_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v_currPos_6083_);
lean_ctor_set(v_reuseFailAlloc_6096_, 1, v___x_6092_);
v___x_6094_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6093_;
}
v_reusejp_6093_:
{
v_a_6072_ = v___x_6094_;
goto _start;
}
}
else
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v_slice_6100_; lean_object* v_nextIt_6102_; 
v___x_6097_ = lean_string_utf8_next_fast(v_a_6069_, v_searcher_6084_);
v___x_6098_ = lean_nat_sub(v___x_6097_, v_searcher_6084_);
v___x_6099_ = lean_nat_add(v_searcher_6084_, v___x_6098_);
lean_dec(v___x_6098_);
v_slice_6100_ = l_String_Slice_subslice_x21(v___x_6070_, v_currPos_6083_, v_searcher_6084_);
lean_inc(v___x_6099_);
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 1, v___x_6099_);
lean_ctor_set(v___x_6086_, 0, v___x_6099_);
v_nextIt_6102_ = v___x_6086_;
goto v_reusejp_6101_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6099_);
lean_ctor_set(v_reuseFailAlloc_6105_, 1, v___x_6099_);
v_nextIt_6102_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6101_;
}
v_reusejp_6101_:
{
lean_object* v_startInclusive_6103_; lean_object* v_endExclusive_6104_; 
v_startInclusive_6103_ = lean_ctor_get(v_slice_6100_, 0);
lean_inc(v_startInclusive_6103_);
v_endExclusive_6104_ = lean_ctor_get(v_slice_6100_, 1);
lean_inc(v_endExclusive_6104_);
lean_dec_ref(v_slice_6100_);
v_it_6075_ = v_nextIt_6102_;
v_startInclusive_6076_ = v_startInclusive_6103_;
v_endExclusive_6077_ = v_endExclusive_6104_;
goto v___jp_6074_;
}
}
}
else
{
lean_object* v___x_6106_; 
lean_del_object(v___x_6086_);
lean_dec(v_searcher_6084_);
v___x_6106_ = lean_box(1);
lean_inc(v___x_6071_);
v_it_6075_ = v___x_6106_;
v_startInclusive_6076_ = v_currPos_6083_;
v_endExclusive_6077_ = v___x_6071_;
goto v___jp_6074_;
}
}
}
else
{
lean_dec(v___x_6071_);
lean_dec_ref(v_a_6069_);
return v_b_6073_;
}
v___jp_6074_:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; 
lean_inc_ref(v_a_6069_);
v___x_6078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6078_, 0, v_a_6069_);
lean_ctor_set(v___x_6078_, 1, v_startInclusive_6076_);
lean_ctor_set(v___x_6078_, 2, v_endExclusive_6077_);
v___x_6079_ = l_String_Slice_toString(v___x_6078_);
lean_dec_ref_known(v___x_6078_, 3);
v___x_6080_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_6079_);
v___x_6081_ = lean_array_push(v_b_6073_, v___x_6080_);
v_a_6072_ = v_it_6075_;
v_b_6073_ = v___x_6081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object* v_a_6108_, lean_object* v___x_6109_, lean_object* v___x_6110_, lean_object* v_a_6111_, lean_object* v_b_6112_){
_start:
{
lean_object* v_res_6113_; 
v_res_6113_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6108_, v___x_6109_, v___x_6110_, v_a_6111_, v_b_6112_);
lean_dec_ref(v___x_6109_);
return v_res_6113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(size_t v_sz_6114_, size_t v_i_6115_, lean_object* v_bs_6116_){
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
lean_object* v_v_6118_; lean_object* v___x_6119_; lean_object* v_bs_x27_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; size_t v___x_6129_; size_t v___x_6130_; lean_object* v___x_6131_; 
v_v_6118_ = lean_array_uget(v_bs_6116_, v_i_6115_);
v___x_6119_ = lean_unsigned_to_nat(0u);
v_bs_x27_6120_ = lean_array_uset(v_bs_6116_, v_i_6115_, v___x_6119_);
v___x_6121_ = lean_string_utf8_byte_size(v_v_6118_);
lean_inc(v_v_6118_);
v___x_6122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6122_, 0, v_v_6118_);
lean_ctor_set(v___x_6122_, 1, v___x_6119_);
lean_ctor_set(v___x_6122_, 2, v___x_6121_);
v___x_6123_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
v___x_6124_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_6125_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_v_6118_, v___x_6122_, v___x_6121_, v___x_6123_, v___x_6124_);
lean_dec_ref_known(v___x_6122_, 3);
v___x_6126_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_6127_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_6126_, v___x_6125_);
v___x_6128_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6127_);
v___x_6129_ = ((size_t)1ULL);
v___x_6130_ = lean_usize_add(v_i_6115_, v___x_6129_);
v___x_6131_ = lean_array_uset(v_bs_x27_6120_, v_i_6115_, v___x_6128_);
v_i_6115_ = v___x_6130_;
v_bs_6116_ = v___x_6131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg___boxed(lean_object* v_sz_6133_, lean_object* v_i_6134_, lean_object* v_bs_6135_){
_start:
{
size_t v_sz_boxed_6136_; size_t v_i_boxed_6137_; lean_object* v_res_6138_; 
v_sz_boxed_6136_ = lean_unbox_usize(v_sz_6133_);
lean_dec(v_sz_6133_);
v_i_boxed_6137_ = lean_unbox_usize(v_i_6134_);
lean_dec(v_i_6134_);
v_res_6138_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_boxed_6136_, v_i_boxed_6137_, v_bs_6135_);
return v_res_6138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object* v_a_6139_, lean_object* v_x_6140_){
_start:
{
if (lean_obj_tag(v_x_6140_) == 0)
{
lean_object* v___x_6141_; 
v___x_6141_ = lean_box(0);
return v___x_6141_;
}
else
{
lean_object* v_key_6142_; lean_object* v_value_6143_; lean_object* v_tail_6144_; uint8_t v___x_6145_; 
v_key_6142_ = lean_ctor_get(v_x_6140_, 0);
v_value_6143_ = lean_ctor_get(v_x_6140_, 1);
v_tail_6144_ = lean_ctor_get(v_x_6140_, 2);
v___x_6145_ = lean_nat_dec_eq(v_key_6142_, v_a_6139_);
if (v___x_6145_ == 0)
{
v_x_6140_ = v_tail_6144_;
goto _start;
}
else
{
lean_object* v___x_6147_; 
lean_inc(v_value_6143_);
v___x_6147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6147_, 0, v_value_6143_);
return v___x_6147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object* v_a_6148_, lean_object* v_x_6149_){
_start:
{
lean_object* v_res_6150_; 
v_res_6150_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6148_, v_x_6149_);
lean_dec(v_x_6149_);
lean_dec(v_a_6148_);
return v_res_6150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object* v_m_6151_, lean_object* v_a_6152_){
_start:
{
lean_object* v_buckets_6153_; lean_object* v___x_6154_; uint64_t v___x_6155_; uint64_t v___x_6156_; uint64_t v___x_6157_; uint64_t v_fold_6158_; uint64_t v___x_6159_; uint64_t v___x_6160_; uint64_t v___x_6161_; size_t v___x_6162_; size_t v___x_6163_; size_t v___x_6164_; size_t v___x_6165_; size_t v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; 
v_buckets_6153_ = lean_ctor_get(v_m_6151_, 1);
v___x_6154_ = lean_array_get_size(v_buckets_6153_);
v___x_6155_ = lean_uint64_of_nat(v_a_6152_);
v___x_6156_ = 32ULL;
v___x_6157_ = lean_uint64_shift_right(v___x_6155_, v___x_6156_);
v_fold_6158_ = lean_uint64_xor(v___x_6155_, v___x_6157_);
v___x_6159_ = 16ULL;
v___x_6160_ = lean_uint64_shift_right(v_fold_6158_, v___x_6159_);
v___x_6161_ = lean_uint64_xor(v_fold_6158_, v___x_6160_);
v___x_6162_ = lean_uint64_to_usize(v___x_6161_);
v___x_6163_ = lean_usize_of_nat(v___x_6154_);
v___x_6164_ = ((size_t)1ULL);
v___x_6165_ = lean_usize_sub(v___x_6163_, v___x_6164_);
v___x_6166_ = lean_usize_land(v___x_6162_, v___x_6165_);
v___x_6167_ = lean_array_uget_borrowed(v_buckets_6153_, v___x_6166_);
v___x_6168_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6152_, v___x_6167_);
return v___x_6168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object* v_m_6169_, lean_object* v_a_6170_){
_start:
{
lean_object* v_res_6171_; 
v_res_6171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6169_, v_a_6170_);
lean_dec(v_a_6170_);
lean_dec_ref(v_m_6169_);
return v_res_6171_;
}
}
static uint8_t _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_6172_; uint8_t v___x_6173_; 
v___x_6172_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6173_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6172_);
return v___x_6173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(lean_object* v_upperBound_6174_, lean_object* v_comments_6175_, lean_object* v_numNewlinesBeforeComments_6176_, lean_object* v_a_6177_, lean_object* v_b_6178_){
_start:
{
lean_object* v___y_6180_; uint8_t v___x_6186_; lean_object* v___y_6188_; lean_object* v___y_6189_; 
v___x_6186_ = lean_nat_dec_lt(v_a_6177_, v_upperBound_6174_);
if (v___x_6186_ == 0)
{
lean_dec(v_a_6177_);
return v_b_6178_;
}
else
{
lean_object* v_fst_6193_; lean_object* v_snd_6194_; lean_object* v___x_6196_; uint8_t v_isShared_6197_; uint8_t v_isSharedCheck_6260_; 
v_fst_6193_ = lean_ctor_get(v_b_6178_, 0);
v_snd_6194_ = lean_ctor_get(v_b_6178_, 1);
v_isSharedCheck_6260_ = !lean_is_exclusive(v_b_6178_);
if (v_isSharedCheck_6260_ == 0)
{
v___x_6196_ = v_b_6178_;
v_isShared_6197_ = v_isSharedCheck_6260_;
goto v_resetjp_6195_;
}
else
{
lean_inc(v_snd_6194_);
lean_inc(v_fst_6193_);
lean_dec(v_b_6178_);
v___x_6196_ = lean_box(0);
v_isShared_6197_ = v_isSharedCheck_6260_;
goto v_resetjp_6195_;
}
v_resetjp_6195_:
{
lean_object* v___x_6198_; lean_object* v___y_6200_; lean_object* v___y_6234_; lean_object* v___y_6235_; lean_object* v___y_6238_; uint8_t v___y_6241_; lean_object* v___y_6242_; uint8_t v___y_6246_; lean_object* v___y_6247_; uint8_t v___y_6251_; uint8_t v_insertedAnyNewlines_6254_; uint8_t v___x_6255_; 
v___x_6198_ = lean_unsigned_to_nat(0u);
v_insertedAnyNewlines_6254_ = 0;
v___x_6255_ = lean_nat_dec_eq(v_a_6177_, v___x_6198_);
if (v___x_6255_ == 0)
{
lean_object* v___x_6256_; lean_object* v___x_6257_; lean_object* v___x_6258_; uint8_t v_kind_6259_; 
v___x_6256_ = lean_unsigned_to_nat(1u);
v___x_6257_ = lean_nat_sub(v_a_6177_, v___x_6256_);
v___x_6258_ = lean_array_fget_borrowed(v_comments_6175_, v___x_6257_);
lean_dec(v___x_6257_);
v_kind_6259_ = lean_ctor_get_uint8(v___x_6258_, sizeof(void*)*3);
if (v_kind_6259_ == 1)
{
v___y_6251_ = v___x_6186_;
goto v___jp_6250_;
}
else
{
v___y_6251_ = v_insertedAnyNewlines_6254_;
goto v___jp_6250_;
}
}
else
{
v___y_6251_ = v_insertedAnyNewlines_6254_;
goto v___jp_6250_;
}
v___jp_6199_:
{
lean_object* v___x_6202_; 
if (v_isShared_6197_ == 0)
{
v___x_6202_ = v___x_6196_;
goto v_reusejp_6201_;
}
else
{
lean_object* v_reuseFailAlloc_6232_; 
v_reuseFailAlloc_6232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_fst_6193_);
lean_ctor_set(v_reuseFailAlloc_6232_, 1, v_snd_6194_);
v___x_6202_ = v_reuseFailAlloc_6232_;
goto v_reusejp_6201_;
}
v_reusejp_6201_:
{
lean_object* v___x_6203_; lean_object* v_fst_6204_; lean_object* v_snd_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; size_t v_sz_6208_; size_t v___x_6209_; lean_object* v___x_6210_; size_t v_sz_6211_; uint8_t v_kind_6212_; lean_object* v_originalWhitespaceRange_6213_; lean_object* v___x_6214_; lean_object* v___f_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; 
v___x_6203_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v___y_6200_, v_a_6177_, v_upperBound_6174_, v___x_6198_, v___x_6202_);
lean_dec(v___y_6200_);
v_fst_6204_ = lean_ctor_get(v___x_6203_, 0);
lean_inc_n(v_fst_6204_, 2);
v_snd_6205_ = lean_ctor_get(v___x_6203_, 1);
lean_inc(v_snd_6205_);
lean_dec_ref(v___x_6203_);
v___x_6206_ = lean_array_fget_borrowed(v_comments_6175_, v_a_6177_);
lean_inc(v___x_6206_);
v___x_6207_ = l_Lean_Fmt_Comment_render(v___x_6206_);
v_sz_6208_ = lean_array_size(v___x_6207_);
v___x_6209_ = ((size_t)0ULL);
v___x_6210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_6208_, v___x_6209_, v___x_6207_);
v_sz_6211_ = lean_array_size(v___x_6210_);
v_kind_6212_ = lean_ctor_get_uint8(v___x_6206_, sizeof(void*)*3);
v_originalWhitespaceRange_6213_ = lean_ctor_get(v___x_6206_, 1);
v___x_6214_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6211_, v___x_6209_, v___x_6210_);
lean_inc_ref(v_originalWhitespaceRange_6213_);
v___f_6215_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_6215_, 0, v_originalWhitespaceRange_6213_);
lean_closure_set(v___f_6215_, 1, v_fst_6204_);
v___x_6216_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_6214_);
v___x_6217_ = l_Lean_Fmt_TaggedDoc_free(v___x_6216_);
if (v_kind_6212_ == 0)
{
lean_object* v___x_6218_; uint8_t v___x_6219_; 
lean_dec(v_snd_6205_);
lean_dec(v_fst_6204_);
v___x_6218_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6219_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6217_);
if (v___x_6219_ == 0)
{
uint8_t v___x_6220_; 
v___x_6220_ = lean_uint8_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0);
if (v___x_6220_ == 0)
{
lean_object* v_doc_6221_; lean_object* v_doc_6222_; uint8_t v___x_6223_; 
v_doc_6221_ = lean_ctor_get(v___x_6217_, 0);
lean_inc(v_doc_6221_);
lean_dec_ref(v___x_6217_);
v_doc_6222_ = lean_ctor_get(v___x_6218_, 0);
v___x_6223_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6221_);
if (v___x_6223_ == 0)
{
uint8_t v___x_6224_; 
v___x_6224_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6222_);
if (v___x_6224_ == 0)
{
lean_object* v___x_6225_; lean_object* v___x_6226_; 
lean_inc(v_doc_6222_);
v___x_6225_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_6221_, v_doc_6222_);
v___x_6226_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6225_);
v___y_6188_ = v___f_6215_;
v___y_6189_ = v___x_6226_;
goto v___jp_6187_;
}
else
{
lean_object* v___x_6227_; 
v___x_6227_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6221_);
v___y_6188_ = v___f_6215_;
v___y_6189_ = v___x_6227_;
goto v___jp_6187_;
}
}
else
{
lean_object* v___x_6228_; 
lean_dec(v_doc_6221_);
lean_inc(v_doc_6222_);
v___x_6228_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6222_);
v___y_6188_ = v___f_6215_;
v___y_6189_ = v___x_6228_;
goto v___jp_6187_;
}
}
else
{
v___y_6188_ = v___f_6215_;
v___y_6189_ = v___x_6217_;
goto v___jp_6187_;
}
}
else
{
lean_dec_ref(v___x_6217_);
v___y_6188_ = v___f_6215_;
v___y_6189_ = v___x_6218_;
goto v___jp_6187_;
}
}
else
{
lean_object* v___x_6229_; uint8_t v___x_6230_; lean_object* v___x_6231_; 
lean_dec_ref(v___f_6215_);
v___x_6229_ = lean_box(0);
v___x_6230_ = lean_unbox(v_snd_6205_);
lean_dec(v_snd_6205_);
lean_inc_ref(v_originalWhitespaceRange_6213_);
v___x_6231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v_originalWhitespaceRange_6213_, v_fst_6204_, v___x_6229_, v___x_6230_, v___x_6217_);
v___y_6180_ = v___x_6231_;
goto v___jp_6179_;
}
}
}
v___jp_6233_:
{
uint8_t v___x_6236_; 
v___x_6236_ = lean_nat_dec_le(v___y_6234_, v___y_6235_);
if (v___x_6236_ == 0)
{
lean_dec(v___y_6234_);
v___y_6200_ = v___y_6235_;
goto v___jp_6199_;
}
else
{
lean_dec(v___y_6235_);
v___y_6200_ = v___y_6234_;
goto v___jp_6199_;
}
}
v___jp_6237_:
{
lean_object* v___x_6239_; 
v___x_6239_ = lean_unsigned_to_nat(2u);
v___y_6234_ = v___y_6238_;
v___y_6235_ = v___x_6239_;
goto v___jp_6233_;
}
v___jp_6240_:
{
uint8_t v___x_6243_; 
v___x_6243_ = lean_nat_dec_eq(v_a_6177_, v___x_6198_);
if (v___x_6243_ == 0)
{
if (v___y_6241_ == 0)
{
lean_object* v___x_6244_; 
v___x_6244_ = lean_unsigned_to_nat(1u);
v___y_6234_ = v___y_6242_;
v___y_6235_ = v___x_6244_;
goto v___jp_6233_;
}
else
{
v___y_6238_ = v___y_6242_;
goto v___jp_6237_;
}
}
else
{
v___y_6238_ = v___y_6242_;
goto v___jp_6237_;
}
}
v___jp_6245_:
{
if (v___y_6246_ == 0)
{
v___y_6241_ = v___y_6246_;
v___y_6242_ = v___y_6247_;
goto v___jp_6240_;
}
else
{
lean_object* v___x_6248_; uint8_t v___x_6249_; 
v___x_6248_ = lean_unsigned_to_nat(1u);
v___x_6249_ = lean_nat_dec_le(v___y_6247_, v___x_6248_);
if (v___x_6249_ == 0)
{
v___y_6241_ = v___y_6246_;
v___y_6242_ = v___y_6247_;
goto v___jp_6240_;
}
else
{
lean_dec(v___y_6247_);
v___y_6241_ = v___y_6246_;
v___y_6242_ = v___x_6248_;
goto v___jp_6240_;
}
}
}
v___jp_6250_:
{
lean_object* v___x_6252_; 
v___x_6252_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_numNewlinesBeforeComments_6176_, v_a_6177_);
if (lean_obj_tag(v___x_6252_) == 0)
{
v___y_6246_ = v___y_6251_;
v___y_6247_ = v___x_6198_;
goto v___jp_6245_;
}
else
{
lean_object* v_val_6253_; 
v_val_6253_ = lean_ctor_get(v___x_6252_, 0);
lean_inc(v_val_6253_);
lean_dec_ref_known(v___x_6252_, 1);
v___y_6246_ = v___y_6251_;
v___y_6247_ = v_val_6253_;
goto v___jp_6245_;
}
}
}
}
v___jp_6179_:
{
if (lean_obj_tag(v___y_6180_) == 0)
{
lean_object* v_a_6181_; 
lean_dec(v_a_6177_);
v_a_6181_ = lean_ctor_get(v___y_6180_, 0);
lean_inc(v_a_6181_);
lean_dec_ref_known(v___y_6180_, 1);
return v_a_6181_;
}
else
{
lean_object* v_a_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; 
v_a_6182_ = lean_ctor_get(v___y_6180_, 0);
lean_inc(v_a_6182_);
lean_dec_ref_known(v___y_6180_, 1);
v___x_6183_ = lean_unsigned_to_nat(1u);
v___x_6184_ = lean_nat_add(v_a_6177_, v___x_6183_);
lean_dec(v_a_6177_);
v_a_6177_ = v___x_6184_;
v_b_6178_ = v_a_6182_;
goto _start;
}
}
v___jp_6187_:
{
lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; 
v___x_6190_ = lean_box(0);
v___x_6191_ = lean_box(v___x_6186_);
v___x_6192_ = lean_apply_3(v___y_6188_, v___x_6190_, v___x_6191_, v___y_6189_);
v___y_6180_ = v___x_6192_;
goto v___jp_6179_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___boxed(lean_object* v_upperBound_6261_, lean_object* v_comments_6262_, lean_object* v_numNewlinesBeforeComments_6263_, lean_object* v_a_6264_, lean_object* v_b_6265_){
_start:
{
lean_object* v_res_6266_; 
v_res_6266_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6261_, v_comments_6262_, v_numNewlinesBeforeComments_6263_, v_a_6264_, v_b_6265_);
lean_dec_ref(v_numNewlinesBeforeComments_6263_);
lean_dec_ref(v_comments_6262_);
lean_dec(v_upperBound_6261_);
return v_res_6266_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object* v_upperBound_6267_, lean_object* v_a_6268_, lean_object* v_b_6269_){
_start:
{
uint8_t v___x_6270_; 
v___x_6270_ = lean_nat_dec_lt(v_a_6268_, v_upperBound_6267_);
if (v___x_6270_ == 0)
{
lean_dec(v_a_6268_);
return v_b_6269_;
}
else
{
lean_object* v_fst_6271_; lean_object* v___x_6273_; uint8_t v_isShared_6274_; uint8_t v_isSharedCheck_6284_; 
v_fst_6271_ = lean_ctor_get(v_b_6269_, 0);
v_isSharedCheck_6284_ = !lean_is_exclusive(v_b_6269_);
if (v_isSharedCheck_6284_ == 0)
{
lean_object* v_unused_6285_; 
v_unused_6285_ = lean_ctor_get(v_b_6269_, 1);
lean_dec(v_unused_6285_);
v___x_6273_ = v_b_6269_;
v_isShared_6274_ = v_isSharedCheck_6284_;
goto v_resetjp_6272_;
}
else
{
lean_inc(v_fst_6271_);
lean_dec(v_b_6269_);
v___x_6273_ = lean_box(0);
v_isShared_6274_ = v_isSharedCheck_6284_;
goto v_resetjp_6272_;
}
v_resetjp_6272_:
{
lean_object* v___x_6275_; lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6279_; 
v___x_6275_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6276_ = lean_array_push(v_fst_6271_, v___x_6275_);
v___x_6277_ = lean_box(v___x_6270_);
if (v_isShared_6274_ == 0)
{
lean_ctor_set(v___x_6273_, 1, v___x_6277_);
lean_ctor_set(v___x_6273_, 0, v___x_6276_);
v___x_6279_ = v___x_6273_;
goto v_reusejp_6278_;
}
else
{
lean_object* v_reuseFailAlloc_6283_; 
v_reuseFailAlloc_6283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6283_, 0, v___x_6276_);
lean_ctor_set(v_reuseFailAlloc_6283_, 1, v___x_6277_);
v___x_6279_ = v_reuseFailAlloc_6283_;
goto v_reusejp_6278_;
}
v_reusejp_6278_:
{
lean_object* v___x_6280_; lean_object* v___x_6281_; 
v___x_6280_ = lean_unsigned_to_nat(1u);
v___x_6281_ = lean_nat_add(v_a_6268_, v___x_6280_);
lean_dec(v_a_6268_);
v_a_6268_ = v___x_6281_;
v_b_6269_ = v___x_6279_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object* v_upperBound_6286_, lean_object* v_a_6287_, lean_object* v_b_6288_){
_start:
{
lean_object* v_res_6289_; 
v_res_6289_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6286_, v_a_6287_, v_b_6288_);
lean_dec(v_upperBound_6286_);
return v_res_6289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(lean_object* v_as_6290_, size_t v_i_6291_, size_t v_stop_6292_, lean_object* v_b_6293_){
_start:
{
lean_object* v___y_6295_; uint8_t v___x_6299_; 
v___x_6299_ = lean_usize_dec_eq(v_i_6291_, v_stop_6292_);
if (v___x_6299_ == 0)
{
lean_object* v___x_6300_; uint8_t v_placement_6301_; 
v___x_6300_ = lean_array_uget_borrowed(v_as_6290_, v_i_6291_);
v_placement_6301_ = lean_ctor_get_uint8(v___x_6300_, sizeof(void*)*3 + 1);
if (v_placement_6301_ == 0)
{
v___y_6295_ = v_b_6293_;
goto v___jp_6294_;
}
else
{
lean_object* v___x_6302_; 
lean_inc(v___x_6300_);
v___x_6302_ = lean_array_push(v_b_6293_, v___x_6300_);
v___y_6295_ = v___x_6302_;
goto v___jp_6294_;
}
}
else
{
return v_b_6293_;
}
v___jp_6294_:
{
size_t v___x_6296_; size_t v___x_6297_; 
v___x_6296_ = ((size_t)1ULL);
v___x_6297_ = lean_usize_add(v_i_6291_, v___x_6296_);
v_i_6291_ = v___x_6297_;
v_b_6293_ = v___y_6295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8___boxed(lean_object* v_as_6303_, lean_object* v_i_6304_, lean_object* v_stop_6305_, lean_object* v_b_6306_){
_start:
{
size_t v_i_boxed_6307_; size_t v_stop_boxed_6308_; lean_object* v_res_6309_; 
v_i_boxed_6307_ = lean_unbox_usize(v_i_6304_);
lean_dec(v_i_6304_);
v_stop_boxed_6308_ = lean_unbox_usize(v_stop_6305_);
lean_dec(v_stop_6305_);
v_res_6309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_as_6303_, v_i_boxed_6307_, v_stop_boxed_6308_, v_b_6306_);
lean_dec_ref(v_as_6303_);
return v_res_6309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object* v_comments_6316_, lean_object* v_whitespace_6317_, uint8_t v_isLeading_6318_){
_start:
{
lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___y_6322_; lean_object* v___y_6323_; lean_object* v___y_6324_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6343_; lean_object* v___y_6344_; lean_object* v___y_6345_; lean_object* v___x_6347_; uint8_t v___y_6349_; lean_object* v___y_6350_; lean_object* v___y_6351_; lean_object* v___y_6352_; uint8_t v___y_6358_; lean_object* v___y_6359_; lean_object* v___y_6360_; lean_object* v___y_6361_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; uint8_t v___y_6368_; lean_object* v___y_6372_; lean_object* v___x_6385_; uint8_t v___x_6386_; 
v___x_6319_ = l_Lean_Fmt_instInhabitedComment_default;
v___x_6320_ = lean_unsigned_to_nat(0u);
v___x_6347_ = lean_array_get_size(v_comments_6316_);
v___x_6385_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6386_ = lean_nat_dec_lt(v___x_6320_, v___x_6347_);
if (v___x_6386_ == 0)
{
v___y_6372_ = v___x_6385_;
goto v___jp_6371_;
}
else
{
size_t v___x_6387_; size_t v___x_6388_; lean_object* v___x_6389_; 
v___x_6387_ = ((size_t)0ULL);
v___x_6388_ = lean_usize_of_nat(v___x_6347_);
v___x_6389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_comments_6316_, v___x_6387_, v___x_6388_, v___x_6385_);
v___y_6372_ = v___x_6389_;
goto v___jp_6371_;
}
v___jp_6321_:
{
lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v_fst_6327_; lean_object* v_snd_6328_; lean_object* v___x_6330_; uint8_t v_isShared_6331_; uint8_t v_isSharedCheck_6335_; 
v___x_6325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6325_, 0, v___y_6323_);
lean_ctor_set(v___x_6325_, 1, v___y_6322_);
v___x_6326_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v___y_6324_, v___x_6320_, v___x_6325_);
lean_dec(v___y_6324_);
v_fst_6327_ = lean_ctor_get(v___x_6326_, 0);
v_snd_6328_ = lean_ctor_get(v___x_6326_, 1);
v_isSharedCheck_6335_ = !lean_is_exclusive(v___x_6326_);
if (v_isSharedCheck_6335_ == 0)
{
v___x_6330_ = v___x_6326_;
v_isShared_6331_ = v_isSharedCheck_6335_;
goto v_resetjp_6329_;
}
else
{
lean_inc(v_snd_6328_);
lean_inc(v_fst_6327_);
lean_dec(v___x_6326_);
v___x_6330_ = lean_box(0);
v_isShared_6331_ = v_isSharedCheck_6335_;
goto v_resetjp_6329_;
}
v_resetjp_6329_:
{
lean_object* v___x_6333_; 
if (v_isShared_6331_ == 0)
{
v___x_6333_ = v___x_6330_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_fst_6327_);
lean_ctor_set(v_reuseFailAlloc_6334_, 1, v_snd_6328_);
v___x_6333_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
return v___x_6333_;
}
}
}
v___jp_6336_:
{
uint8_t v___x_6341_; 
v___x_6341_ = lean_nat_dec_le(v___y_6337_, v___y_6340_);
if (v___x_6341_ == 0)
{
lean_dec(v___y_6337_);
v___y_6322_ = v___y_6338_;
v___y_6323_ = v___y_6339_;
v___y_6324_ = v___y_6340_;
goto v___jp_6321_;
}
else
{
lean_dec(v___y_6340_);
v___y_6322_ = v___y_6338_;
v___y_6323_ = v___y_6339_;
v___y_6324_ = v___y_6337_;
goto v___jp_6321_;
}
}
v___jp_6342_:
{
lean_object* v___x_6346_; 
v___x_6346_ = lean_unsigned_to_nat(2u);
v___y_6337_ = v___y_6343_;
v___y_6338_ = v___y_6344_;
v___y_6339_ = v___y_6345_;
v___y_6340_ = v___x_6346_;
goto v___jp_6336_;
}
v___jp_6348_:
{
if (v_isLeading_6318_ == 0)
{
uint8_t v___x_6353_; 
v___x_6353_ = lean_nat_dec_eq(v___x_6347_, v___x_6320_);
if (v___x_6353_ == 0)
{
if (v___y_6349_ == 0)
{
lean_object* v___x_6354_; 
v___x_6354_ = lean_unsigned_to_nat(1u);
v___y_6337_ = v___y_6352_;
v___y_6338_ = v___y_6350_;
v___y_6339_ = v___y_6351_;
v___y_6340_ = v___x_6354_;
goto v___jp_6336_;
}
else
{
v___y_6343_ = v___y_6352_;
v___y_6344_ = v___y_6350_;
v___y_6345_ = v___y_6351_;
goto v___jp_6342_;
}
}
else
{
v___y_6343_ = v___y_6352_;
v___y_6344_ = v___y_6350_;
v___y_6345_ = v___y_6351_;
goto v___jp_6342_;
}
}
else
{
uint8_t v___x_6355_; 
v___x_6355_ = lean_nat_dec_lt(v___x_6320_, v___x_6347_);
if (v___x_6355_ == 0)
{
v___y_6337_ = v___y_6352_;
v___y_6338_ = v___y_6350_;
v___y_6339_ = v___y_6351_;
v___y_6340_ = v___x_6320_;
goto v___jp_6336_;
}
else
{
lean_object* v___x_6356_; 
v___x_6356_ = lean_unsigned_to_nat(2u);
v___y_6337_ = v___y_6352_;
v___y_6338_ = v___y_6350_;
v___y_6339_ = v___y_6351_;
v___y_6340_ = v___x_6356_;
goto v___jp_6336_;
}
}
}
v___jp_6357_:
{
if (v___y_6358_ == 0)
{
v___y_6349_ = v___y_6358_;
v___y_6350_ = v___y_6359_;
v___y_6351_ = v___y_6360_;
v___y_6352_ = v___y_6361_;
goto v___jp_6348_;
}
else
{
lean_object* v___x_6362_; uint8_t v___x_6363_; 
v___x_6362_ = lean_unsigned_to_nat(1u);
v___x_6363_ = lean_nat_dec_le(v___y_6361_, v___x_6362_);
if (v___x_6363_ == 0)
{
v___y_6349_ = v___y_6358_;
v___y_6350_ = v___y_6359_;
v___y_6351_ = v___y_6360_;
v___y_6352_ = v___y_6361_;
goto v___jp_6348_;
}
else
{
lean_dec(v___y_6361_);
v___y_6349_ = v___y_6358_;
v___y_6350_ = v___y_6359_;
v___y_6351_ = v___y_6360_;
v___y_6352_ = v___x_6362_;
goto v___jp_6348_;
}
}
}
v___jp_6364_:
{
lean_object* v___x_6369_; 
v___x_6369_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v___y_6367_, v___x_6347_);
lean_dec_ref(v___y_6367_);
if (lean_obj_tag(v___x_6369_) == 0)
{
v___y_6358_ = v___y_6368_;
v___y_6359_ = v___y_6365_;
v___y_6360_ = v___y_6366_;
v___y_6361_ = v___x_6320_;
goto v___jp_6357_;
}
else
{
lean_object* v_val_6370_; 
v_val_6370_ = lean_ctor_get(v___x_6369_, 0);
lean_inc(v_val_6370_);
lean_dec_ref_known(v___x_6369_, 1);
v___y_6358_ = v___y_6368_;
v___y_6359_ = v___y_6365_;
v___y_6360_ = v___y_6366_;
v___y_6361_ = v_val_6370_;
goto v___jp_6357_;
}
}
v___jp_6371_:
{
lean_object* v_numNewlinesBeforeComments_6373_; uint8_t v_insertedAnyNewlines_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v_fst_6377_; lean_object* v_snd_6378_; uint8_t v___x_6379_; 
v_numNewlinesBeforeComments_6373_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v___y_6372_, v_whitespace_6317_);
lean_dec_ref(v___y_6372_);
v_insertedAnyNewlines_6374_ = 0;
v___x_6375_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0));
v___x_6376_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v___x_6347_, v_comments_6316_, v_numNewlinesBeforeComments_6373_, v___x_6320_, v___x_6375_);
v_fst_6377_ = lean_ctor_get(v___x_6376_, 0);
lean_inc(v_fst_6377_);
v_snd_6378_ = lean_ctor_get(v___x_6376_, 1);
lean_inc(v_snd_6378_);
lean_dec_ref(v___x_6376_);
v___x_6379_ = lean_nat_dec_eq(v___x_6347_, v___x_6320_);
if (v___x_6379_ == 0)
{
lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; uint8_t v_kind_6383_; 
v___x_6380_ = lean_unsigned_to_nat(1u);
v___x_6381_ = lean_nat_sub(v___x_6347_, v___x_6380_);
v___x_6382_ = lean_array_get_borrowed(v___x_6319_, v_comments_6316_, v___x_6381_);
lean_dec(v___x_6381_);
v_kind_6383_ = lean_ctor_get_uint8(v___x_6382_, sizeof(void*)*3);
if (v_kind_6383_ == 1)
{
uint8_t v___x_6384_; 
v___x_6384_ = 1;
v___y_6365_ = v_snd_6378_;
v___y_6366_ = v_fst_6377_;
v___y_6367_ = v_numNewlinesBeforeComments_6373_;
v___y_6368_ = v___x_6384_;
goto v___jp_6364_;
}
else
{
v___y_6365_ = v_snd_6378_;
v___y_6366_ = v_fst_6377_;
v___y_6367_ = v_numNewlinesBeforeComments_6373_;
v___y_6368_ = v_insertedAnyNewlines_6374_;
goto v___jp_6364_;
}
}
else
{
v___y_6365_ = v_snd_6378_;
v___y_6366_ = v_fst_6377_;
v___y_6367_ = v_numNewlinesBeforeComments_6373_;
v___y_6368_ = v_insertedAnyNewlines_6374_;
goto v___jp_6364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object* v_comments_6390_, lean_object* v_whitespace_6391_, lean_object* v_isLeading_6392_){
_start:
{
uint8_t v_isLeading_boxed_6393_; lean_object* v_res_6394_; 
v_isLeading_boxed_6393_ = lean_unbox(v_isLeading_6392_);
v_res_6394_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v_comments_6390_, v_whitespace_6391_, v_isLeading_boxed_6393_);
lean_dec_ref(v_whitespace_6391_);
lean_dec_ref(v_comments_6390_);
return v_res_6394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object* v_a_6395_, lean_object* v___x_6396_, lean_object* v___x_6397_, lean_object* v_inst_6398_, lean_object* v_R_6399_, lean_object* v_a_6400_, lean_object* v_b_6401_){
_start:
{
lean_object* v___x_6402_; 
v___x_6402_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6395_, v___x_6396_, v___x_6397_, v_a_6400_, v_b_6401_);
return v___x_6402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object* v_a_6403_, lean_object* v___x_6404_, lean_object* v___x_6405_, lean_object* v_inst_6406_, lean_object* v_R_6407_, lean_object* v_a_6408_, lean_object* v_b_6409_){
_start:
{
lean_object* v_res_6410_; 
v_res_6410_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(v_a_6403_, v___x_6404_, v___x_6405_, v_inst_6406_, v_R_6407_, v_a_6408_, v_b_6409_);
lean_dec_ref(v___x_6404_);
return v_res_6410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(lean_object* v_as_6411_, size_t v_sz_6412_, size_t v_i_6413_, lean_object* v_bs_6414_){
_start:
{
lean_object* v___x_6415_; 
v___x_6415_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6412_, v_i_6413_, v_bs_6414_);
return v___x_6415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object* v_as_6416_, lean_object* v_sz_6417_, lean_object* v_i_6418_, lean_object* v_bs_6419_){
_start:
{
size_t v_sz_boxed_6420_; size_t v_i_boxed_6421_; lean_object* v_res_6422_; 
v_sz_boxed_6420_ = lean_unbox_usize(v_sz_6417_);
lean_dec(v_sz_6417_);
v_i_boxed_6421_ = lean_unbox_usize(v_i_6418_);
lean_dec(v_i_6418_);
v_res_6422_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(v_as_6416_, v_sz_boxed_6420_, v_i_boxed_6421_, v_bs_6419_);
lean_dec_ref(v_as_6416_);
return v_res_6422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object* v_upperBound_6423_, lean_object* v_next_6424_, lean_object* v_upperBound_6425_, lean_object* v_inst_6426_, lean_object* v_R_6427_, lean_object* v_a_6428_, lean_object* v_b_6429_, lean_object* v_c_6430_){
_start:
{
lean_object* v___x_6431_; 
v___x_6431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6423_, v_next_6424_, v_upperBound_6425_, v_a_6428_, v_b_6429_);
return v___x_6431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object* v_upperBound_6432_, lean_object* v_next_6433_, lean_object* v_upperBound_6434_, lean_object* v_inst_6435_, lean_object* v_R_6436_, lean_object* v_a_6437_, lean_object* v_b_6438_, lean_object* v_c_6439_){
_start:
{
lean_object* v_res_6440_; 
v_res_6440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(v_upperBound_6432_, v_next_6433_, v_upperBound_6434_, v_inst_6435_, v_R_6436_, v_a_6437_, v_b_6438_, v_c_6439_);
lean_dec(v_upperBound_6434_);
lean_dec(v_next_6433_);
lean_dec(v_upperBound_6432_);
return v_res_6440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object* v_00_u03b2_6441_, lean_object* v_m_6442_, lean_object* v_a_6443_){
_start:
{
lean_object* v___x_6444_; 
v___x_6444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6442_, v_a_6443_);
return v___x_6444_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object* v_00_u03b2_6445_, lean_object* v_m_6446_, lean_object* v_a_6447_){
_start:
{
lean_object* v_res_6448_; 
v_res_6448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(v_00_u03b2_6445_, v_m_6446_, v_a_6447_);
lean_dec(v_a_6447_);
lean_dec_ref(v_m_6446_);
return v_res_6448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object* v_upperBound_6449_, lean_object* v_inst_6450_, lean_object* v_R_6451_, lean_object* v_a_6452_, lean_object* v_b_6453_, lean_object* v_c_6454_){
_start:
{
lean_object* v___x_6455_; 
v___x_6455_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6449_, v_a_6452_, v_b_6453_);
return v___x_6455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object* v_upperBound_6456_, lean_object* v_inst_6457_, lean_object* v_R_6458_, lean_object* v_a_6459_, lean_object* v_b_6460_, lean_object* v_c_6461_){
_start:
{
lean_object* v_res_6462_; 
v_res_6462_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(v_upperBound_6456_, v_inst_6457_, v_R_6458_, v_a_6459_, v_b_6460_, v_c_6461_);
lean_dec(v_upperBound_6456_);
return v_res_6462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object* v_upperBound_6463_, lean_object* v_comments_6464_, lean_object* v_numNewlinesBeforeComments_6465_, lean_object* v_inst_6466_, lean_object* v_R_6467_, lean_object* v_a_6468_, lean_object* v_b_6469_, lean_object* v_c_6470_){
_start:
{
lean_object* v___x_6471_; 
v___x_6471_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6463_, v_comments_6464_, v_numNewlinesBeforeComments_6465_, v_a_6468_, v_b_6469_);
return v___x_6471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object* v_upperBound_6472_, lean_object* v_comments_6473_, lean_object* v_numNewlinesBeforeComments_6474_, lean_object* v_inst_6475_, lean_object* v_R_6476_, lean_object* v_a_6477_, lean_object* v_b_6478_, lean_object* v_c_6479_){
_start:
{
lean_object* v_res_6480_; 
v_res_6480_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_upperBound_6472_, v_comments_6473_, v_numNewlinesBeforeComments_6474_, v_inst_6475_, v_R_6476_, v_a_6477_, v_b_6478_, v_c_6479_);
lean_dec_ref(v_numNewlinesBeforeComments_6474_);
lean_dec_ref(v_comments_6473_);
lean_dec(v_upperBound_6472_);
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object* v_00_u03b2_6481_, lean_object* v_a_6482_, lean_object* v_x_6483_){
_start:
{
lean_object* v___x_6484_; 
v___x_6484_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6482_, v_x_6483_);
return v___x_6484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object* v_00_u03b2_6485_, lean_object* v_a_6486_, lean_object* v_x_6487_){
_start:
{
lean_object* v_res_6488_; 
v_res_6488_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(v_00_u03b2_6485_, v_a_6486_, v_x_6487_);
lean_dec(v_x_6487_);
lean_dec(v_a_6486_);
return v_res_6488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object* v_leadingTk_6491_, lean_object* v_leading_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_){
_start:
{
uint8_t v___x_6501_; lean_object* v___x_6502_; 
v___x_6501_ = 0;
v___x_6502_ = l_Lean_Syntax_getRange_x3f(v_leadingTk_6491_, v___x_6501_);
if (lean_obj_tag(v___x_6502_) == 1)
{
lean_object* v_val_6503_; lean_object* v_str_6504_; lean_object* v_startPos_6505_; lean_object* v_stopPos_6506_; lean_object* v___x_6508_; uint8_t v_isShared_6509_; uint8_t v_isSharedCheck_6529_; 
v_val_6503_ = lean_ctor_get(v___x_6502_, 0);
lean_inc(v_val_6503_);
lean_dec_ref_known(v___x_6502_, 1);
v_str_6504_ = lean_ctor_get(v_leading_6492_, 0);
v_startPos_6505_ = lean_ctor_get(v_leading_6492_, 1);
v_stopPos_6506_ = lean_ctor_get(v_leading_6492_, 2);
v_isSharedCheck_6529_ = !lean_is_exclusive(v_leading_6492_);
if (v_isSharedCheck_6529_ == 0)
{
v___x_6508_ = v_leading_6492_;
v_isShared_6509_ = v_isSharedCheck_6529_;
goto v_resetjp_6507_;
}
else
{
lean_inc(v_stopPos_6506_);
lean_inc(v_startPos_6505_);
lean_inc(v_str_6504_);
lean_dec(v_leading_6492_);
v___x_6508_ = lean_box(0);
v_isShared_6509_ = v_isSharedCheck_6529_;
goto v_resetjp_6507_;
}
v_resetjp_6507_:
{
uint8_t v___x_6510_; 
v___x_6510_ = lean_string_is_valid_pos(v_str_6504_, v_startPos_6505_);
if (v___x_6510_ == 0)
{
lean_del_object(v___x_6508_);
lean_dec(v_stopPos_6506_);
lean_dec(v_startPos_6505_);
lean_dec_ref(v_str_6504_);
lean_dec(v_val_6503_);
goto v___jp_6495_;
}
else
{
uint8_t v___x_6511_; 
v___x_6511_ = lean_string_is_valid_pos(v_str_6504_, v_stopPos_6506_);
if (v___x_6511_ == 0)
{
lean_del_object(v___x_6508_);
lean_dec(v_stopPos_6506_);
lean_dec(v_startPos_6505_);
lean_dec_ref(v_str_6504_);
lean_dec(v_val_6503_);
goto v___jp_6495_;
}
else
{
uint8_t v___x_6512_; 
v___x_6512_ = lean_nat_dec_le(v_startPos_6505_, v_stopPos_6506_);
if (v___x_6512_ == 0)
{
lean_del_object(v___x_6508_);
lean_dec(v_stopPos_6506_);
lean_dec(v_startPos_6505_);
lean_dec_ref(v_str_6504_);
lean_dec(v_val_6503_);
goto v___jp_6495_;
}
else
{
lean_object* v_lineInfos_6513_; lean_object* v___x_6515_; 
lean_dec(v_leadingTk_6491_);
v_lineInfos_6513_ = lean_ctor_get(v___y_6493_, 4);
if (v_isShared_6509_ == 0)
{
v___x_6515_ = v___x_6508_;
goto v_reusejp_6514_;
}
else
{
lean_object* v_reuseFailAlloc_6528_; 
v_reuseFailAlloc_6528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_str_6504_);
lean_ctor_set(v_reuseFailAlloc_6528_, 1, v_startPos_6505_);
lean_ctor_set(v_reuseFailAlloc_6528_, 2, v_stopPos_6506_);
v___x_6515_ = v_reuseFailAlloc_6528_;
goto v_reusejp_6514_;
}
v_reusejp_6514_:
{
uint8_t v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v_fst_6519_; lean_object* v___x_6521_; uint8_t v_isShared_6522_; uint8_t v_isSharedCheck_6526_; 
v___x_6516_ = 0;
lean_inc_ref(v___x_6515_);
v___x_6517_ = l_Lean_Fmt_parseComments(v_lineInfos_6513_, v_val_6503_, v___x_6516_, v___x_6515_);
v___x_6518_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___x_6517_, v___x_6515_, v___x_6512_);
lean_dec_ref(v___x_6515_);
lean_dec_ref(v___x_6517_);
v_fst_6519_ = lean_ctor_get(v___x_6518_, 0);
v_isSharedCheck_6526_ = !lean_is_exclusive(v___x_6518_);
if (v_isSharedCheck_6526_ == 0)
{
lean_object* v_unused_6527_; 
v_unused_6527_ = lean_ctor_get(v___x_6518_, 1);
lean_dec(v_unused_6527_);
v___x_6521_ = v___x_6518_;
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
else
{
lean_inc(v_fst_6519_);
lean_dec(v___x_6518_);
v___x_6521_ = lean_box(0);
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
v_resetjp_6520_:
{
lean_object* v___x_6524_; 
if (v_isShared_6522_ == 0)
{
lean_ctor_set(v___x_6521_, 1, v___y_6494_);
v___x_6524_ = v___x_6521_;
goto v_reusejp_6523_;
}
else
{
lean_object* v_reuseFailAlloc_6525_; 
v_reuseFailAlloc_6525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6525_, 0, v_fst_6519_);
lean_ctor_set(v_reuseFailAlloc_6525_, 1, v___y_6494_);
v___x_6524_ = v_reuseFailAlloc_6525_;
goto v_reusejp_6523_;
}
v_reusejp_6523_:
{
return v___x_6524_;
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
lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; 
lean_dec(v___x_6502_);
lean_dec_ref(v_leading_6492_);
v___x_6530_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6531_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6532_, 0, v_leadingTk_6491_);
lean_ctor_set(v___x_6532_, 1, v___x_6530_);
lean_ctor_set(v___x_6532_, 2, v___x_6531_);
v___x_6533_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6533_, 0, v___x_6532_);
v___x_6534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6534_, 0, v___x_6533_);
lean_ctor_set(v___x_6534_, 1, v___y_6494_);
return v___x_6534_;
}
v___jp_6495_:
{
lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6496_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6497_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6498_, 0, v_leadingTk_6491_);
lean_ctor_set(v___x_6498_, 1, v___x_6496_);
lean_ctor_set(v___x_6498_, 2, v___x_6497_);
v___x_6499_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6499_, 0, v___x_6498_);
v___x_6500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6500_, 0, v___x_6499_);
lean_ctor_set(v___x_6500_, 1, v___y_6494_);
return v___x_6500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_leadingTk_6535_, lean_object* v_leading_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_){
_start:
{
lean_object* v_res_6539_; 
v_res_6539_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(v_leadingTk_6535_, v_leading_6536_, v___y_6537_, v___y_6538_);
lean_dec_ref(v___y_6537_);
return v_res_6539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object* v_stx_6541_, lean_object* v_a_6542_, lean_object* v_a_6543_){
_start:
{
lean_object* v___f_6544_; lean_object* v___x_6545_; 
v___f_6544_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0));
v___x_6545_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_6541_, v___f_6544_, v_a_6542_, v_a_6543_);
return v___x_6545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6546_, lean_object* v_a_6547_, lean_object* v_a_6548_){
_start:
{
lean_object* v_res_6549_; 
v_res_6549_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v_stx_6546_, v_a_6547_, v_a_6548_);
lean_dec_ref(v_a_6547_);
return v_res_6549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t v_atleastOneNewline_6550_, lean_object* v_trailingTk_6551_, lean_object* v_trailing_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_){
_start:
{
uint8_t v___x_6561_; lean_object* v___x_6562_; 
v___x_6561_ = 0;
v___x_6562_ = l_Lean_Syntax_getRange_x3f(v_trailingTk_6551_, v___x_6561_);
if (lean_obj_tag(v___x_6562_) == 1)
{
lean_object* v_val_6563_; lean_object* v_str_6564_; lean_object* v_startPos_6565_; lean_object* v_stopPos_6566_; lean_object* v___x_6568_; uint8_t v_isShared_6569_; uint8_t v_isSharedCheck_6620_; 
v_val_6563_ = lean_ctor_get(v___x_6562_, 0);
lean_inc(v_val_6563_);
lean_dec_ref_known(v___x_6562_, 1);
v_str_6564_ = lean_ctor_get(v_trailing_6552_, 0);
v_startPos_6565_ = lean_ctor_get(v_trailing_6552_, 1);
v_stopPos_6566_ = lean_ctor_get(v_trailing_6552_, 2);
v_isSharedCheck_6620_ = !lean_is_exclusive(v_trailing_6552_);
if (v_isSharedCheck_6620_ == 0)
{
v___x_6568_ = v_trailing_6552_;
v_isShared_6569_ = v_isSharedCheck_6620_;
goto v_resetjp_6567_;
}
else
{
lean_inc(v_stopPos_6566_);
lean_inc(v_startPos_6565_);
lean_inc(v_str_6564_);
lean_dec(v_trailing_6552_);
v___x_6568_ = lean_box(0);
v_isShared_6569_ = v_isSharedCheck_6620_;
goto v_resetjp_6567_;
}
v_resetjp_6567_:
{
uint8_t v___x_6570_; 
v___x_6570_ = lean_string_is_valid_pos(v_str_6564_, v_startPos_6565_);
if (v___x_6570_ == 0)
{
lean_del_object(v___x_6568_);
lean_dec(v_stopPos_6566_);
lean_dec(v_startPos_6565_);
lean_dec_ref(v_str_6564_);
lean_dec(v_val_6563_);
goto v___jp_6555_;
}
else
{
uint8_t v___x_6571_; 
v___x_6571_ = lean_string_is_valid_pos(v_str_6564_, v_stopPos_6566_);
if (v___x_6571_ == 0)
{
lean_del_object(v___x_6568_);
lean_dec(v_stopPos_6566_);
lean_dec(v_startPos_6565_);
lean_dec_ref(v_str_6564_);
lean_dec(v_val_6563_);
goto v___jp_6555_;
}
else
{
uint8_t v___x_6572_; 
v___x_6572_ = lean_nat_dec_le(v_startPos_6565_, v_stopPos_6566_);
if (v___x_6572_ == 0)
{
lean_del_object(v___x_6568_);
lean_dec(v_stopPos_6566_);
lean_dec(v_startPos_6565_);
lean_dec_ref(v_str_6564_);
lean_dec(v_val_6563_);
goto v___jp_6555_;
}
else
{
lean_object* v_lineInfos_6573_; lean_object* v___x_6575_; 
lean_dec(v_trailingTk_6551_);
v_lineInfos_6573_ = lean_ctor_get(v___y_6553_, 4);
if (v_isShared_6569_ == 0)
{
v___x_6575_ = v___x_6568_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6619_; 
v_reuseFailAlloc_6619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6619_, 0, v_str_6564_);
lean_ctor_set(v_reuseFailAlloc_6619_, 1, v_startPos_6565_);
lean_ctor_set(v_reuseFailAlloc_6619_, 2, v_stopPos_6566_);
v___x_6575_ = v_reuseFailAlloc_6619_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
lean_object* v___y_6577_; uint8_t v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; uint8_t v___x_6615_; 
v___x_6610_ = 1;
lean_inc_ref(v___x_6575_);
v___x_6611_ = l_Lean_Fmt_parseComments(v_lineInfos_6573_, v_val_6563_, v___x_6610_, v___x_6575_);
v___x_6612_ = lean_unsigned_to_nat(0u);
v___x_6613_ = lean_array_get_size(v___x_6611_);
v___x_6614_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6615_ = lean_nat_dec_lt(v___x_6612_, v___x_6613_);
if (v___x_6615_ == 0)
{
lean_dec_ref(v___x_6611_);
v___y_6577_ = v___x_6614_;
goto v___jp_6576_;
}
else
{
size_t v___x_6616_; size_t v___x_6617_; lean_object* v___x_6618_; 
v___x_6616_ = ((size_t)0ULL);
v___x_6617_ = lean_usize_of_nat(v___x_6613_);
v___x_6618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v___x_6611_, v___x_6616_, v___x_6617_, v___x_6614_);
lean_dec_ref(v___x_6611_);
v___y_6577_ = v___x_6618_;
goto v___jp_6576_;
}
v___jp_6576_:
{
lean_object* v___x_6578_; lean_object* v_snd_6579_; uint8_t v___x_6580_; 
v___x_6578_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___y_6577_, v___x_6575_, v___x_6561_);
lean_dec_ref(v___x_6575_);
lean_dec_ref(v___y_6577_);
v_snd_6579_ = lean_ctor_get(v___x_6578_, 1);
v___x_6580_ = lean_unbox(v_snd_6579_);
if (v___x_6580_ == 0)
{
if (v_atleastOneNewline_6550_ == 0)
{
lean_object* v_fst_6581_; lean_object* v___x_6583_; uint8_t v_isShared_6584_; uint8_t v_isSharedCheck_6588_; 
v_fst_6581_ = lean_ctor_get(v___x_6578_, 0);
v_isSharedCheck_6588_ = !lean_is_exclusive(v___x_6578_);
if (v_isSharedCheck_6588_ == 0)
{
lean_object* v_unused_6589_; 
v_unused_6589_ = lean_ctor_get(v___x_6578_, 1);
lean_dec(v_unused_6589_);
v___x_6583_ = v___x_6578_;
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
else
{
lean_inc(v_fst_6581_);
lean_dec(v___x_6578_);
v___x_6583_ = lean_box(0);
v_isShared_6584_ = v_isSharedCheck_6588_;
goto v_resetjp_6582_;
}
v_resetjp_6582_:
{
lean_object* v___x_6586_; 
if (v_isShared_6584_ == 0)
{
lean_ctor_set(v___x_6583_, 1, v___y_6554_);
v___x_6586_ = v___x_6583_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v_fst_6581_);
lean_ctor_set(v_reuseFailAlloc_6587_, 1, v___y_6554_);
v___x_6586_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
return v___x_6586_;
}
}
}
else
{
lean_object* v_fst_6590_; lean_object* v___x_6592_; uint8_t v_isShared_6593_; uint8_t v_isSharedCheck_6599_; 
v_fst_6590_ = lean_ctor_get(v___x_6578_, 0);
v_isSharedCheck_6599_ = !lean_is_exclusive(v___x_6578_);
if (v_isSharedCheck_6599_ == 0)
{
lean_object* v_unused_6600_; 
v_unused_6600_ = lean_ctor_get(v___x_6578_, 1);
lean_dec(v_unused_6600_);
v___x_6592_ = v___x_6578_;
v_isShared_6593_ = v_isSharedCheck_6599_;
goto v_resetjp_6591_;
}
else
{
lean_inc(v_fst_6590_);
lean_dec(v___x_6578_);
v___x_6592_ = lean_box(0);
v_isShared_6593_ = v_isSharedCheck_6599_;
goto v_resetjp_6591_;
}
v_resetjp_6591_:
{
lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6597_; 
v___x_6594_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6595_ = lean_array_push(v_fst_6590_, v___x_6594_);
if (v_isShared_6593_ == 0)
{
lean_ctor_set(v___x_6592_, 1, v___y_6554_);
lean_ctor_set(v___x_6592_, 0, v___x_6595_);
v___x_6597_ = v___x_6592_;
goto v_reusejp_6596_;
}
else
{
lean_object* v_reuseFailAlloc_6598_; 
v_reuseFailAlloc_6598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6595_);
lean_ctor_set(v_reuseFailAlloc_6598_, 1, v___y_6554_);
v___x_6597_ = v_reuseFailAlloc_6598_;
goto v_reusejp_6596_;
}
v_reusejp_6596_:
{
return v___x_6597_;
}
}
}
}
else
{
lean_object* v_fst_6601_; lean_object* v___x_6603_; uint8_t v_isShared_6604_; uint8_t v_isSharedCheck_6608_; 
v_fst_6601_ = lean_ctor_get(v___x_6578_, 0);
v_isSharedCheck_6608_ = !lean_is_exclusive(v___x_6578_);
if (v_isSharedCheck_6608_ == 0)
{
lean_object* v_unused_6609_; 
v_unused_6609_ = lean_ctor_get(v___x_6578_, 1);
lean_dec(v_unused_6609_);
v___x_6603_ = v___x_6578_;
v_isShared_6604_ = v_isSharedCheck_6608_;
goto v_resetjp_6602_;
}
else
{
lean_inc(v_fst_6601_);
lean_dec(v___x_6578_);
v___x_6603_ = lean_box(0);
v_isShared_6604_ = v_isSharedCheck_6608_;
goto v_resetjp_6602_;
}
v_resetjp_6602_:
{
lean_object* v___x_6606_; 
if (v_isShared_6604_ == 0)
{
lean_ctor_set(v___x_6603_, 1, v___y_6554_);
v___x_6606_ = v___x_6603_;
goto v_reusejp_6605_;
}
else
{
lean_object* v_reuseFailAlloc_6607_; 
v_reuseFailAlloc_6607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6607_, 0, v_fst_6601_);
lean_ctor_set(v_reuseFailAlloc_6607_, 1, v___y_6554_);
v___x_6606_ = v_reuseFailAlloc_6607_;
goto v_reusejp_6605_;
}
v_reusejp_6605_:
{
return v___x_6606_;
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
lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; 
lean_dec(v___x_6562_);
lean_dec_ref(v_trailing_6552_);
v___x_6621_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6622_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6623_, 0, v_trailingTk_6551_);
lean_ctor_set(v___x_6623_, 1, v___x_6621_);
lean_ctor_set(v___x_6623_, 2, v___x_6622_);
v___x_6624_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6624_, 0, v___x_6623_);
v___x_6625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6625_, 0, v___x_6624_);
lean_ctor_set(v___x_6625_, 1, v___y_6554_);
return v___x_6625_;
}
v___jp_6555_:
{
lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; 
v___x_6556_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6557_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
v___x_6558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6558_, 0, v_trailingTk_6551_);
lean_ctor_set(v___x_6558_, 1, v___x_6556_);
lean_ctor_set(v___x_6558_, 2, v___x_6557_);
v___x_6559_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6559_, 0, v___x_6558_);
v___x_6560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6560_, 0, v___x_6559_);
lean_ctor_set(v___x_6560_, 1, v___y_6554_);
return v___x_6560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_atleastOneNewline_6626_, lean_object* v_trailingTk_6627_, lean_object* v_trailing_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6631_; lean_object* v_res_6632_; 
v_atleastOneNewline_boxed_6631_ = lean_unbox(v_atleastOneNewline_6626_);
v_res_6632_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(v_atleastOneNewline_boxed_6631_, v_trailingTk_6627_, v_trailing_6628_, v___y_6629_, v___y_6630_);
lean_dec_ref(v___y_6629_);
return v_res_6632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object* v_stx_6633_, uint8_t v_atleastOneNewline_6634_, lean_object* v_a_6635_, lean_object* v_a_6636_){
_start:
{
lean_object* v___x_6637_; lean_object* v___f_6638_; lean_object* v___x_6639_; 
v___x_6637_ = lean_box(v_atleastOneNewline_6634_);
v___f_6638_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed), 5, 1);
lean_closure_set(v___f_6638_, 0, v___x_6637_);
v___x_6639_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_6633_, v___f_6638_, v_a_6635_, v_a_6636_);
return v___x_6639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6640_, lean_object* v_atleastOneNewline_6641_, lean_object* v_a_6642_, lean_object* v_a_6643_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6644_; lean_object* v_res_6645_; 
v_atleastOneNewline_boxed_6644_ = lean_unbox(v_atleastOneNewline_6641_);
v_res_6645_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_stx_6640_, v_atleastOneNewline_boxed_6644_, v_a_6642_, v_a_6643_);
lean_dec_ref(v_a_6642_);
return v_res_6645_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object* v_upperBound_6646_, lean_object* v_stxs_6647_, lean_object* v_f_6648_, lean_object* v___x_6649_, lean_object* v_a_6650_, lean_object* v_b_6651_, lean_object* v___y_6652_, lean_object* v___y_6653_){
_start:
{
uint8_t v___x_6654_; 
v___x_6654_ = lean_nat_dec_lt(v_a_6650_, v_upperBound_6646_);
if (v___x_6654_ == 0)
{
lean_object* v___x_6655_; 
lean_dec(v_a_6650_);
lean_dec_ref(v_f_6648_);
v___x_6655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6655_, 0, v_b_6651_);
lean_ctor_set(v___x_6655_, 1, v___y_6653_);
return v___x_6655_;
}
else
{
lean_object* v___x_6656_; lean_object* v___x_6657_; 
v___x_6656_ = lean_array_fget_borrowed(v_stxs_6647_, v_a_6650_);
lean_inc_ref(v_f_6648_);
lean_inc_ref(v___y_6652_);
lean_inc(v___x_6656_);
v___x_6657_ = lean_apply_3(v_f_6648_, v___x_6656_, v___y_6652_, v___y_6653_);
if (lean_obj_tag(v___x_6657_) == 0)
{
lean_object* v_a_6658_; lean_object* v_a_6659_; lean_object* v___x_6660_; lean_object* v___y_6662_; lean_object* v___x_6687_; uint8_t v___x_6688_; 
v_a_6658_ = lean_ctor_get(v___x_6657_, 0);
lean_inc(v_a_6658_);
v_a_6659_ = lean_ctor_get(v___x_6657_, 1);
lean_inc(v_a_6659_);
lean_dec_ref_known(v___x_6657_, 2);
v___x_6660_ = lean_unsigned_to_nat(1u);
v___x_6687_ = lean_nat_sub(v___x_6649_, v___x_6660_);
v___x_6688_ = lean_nat_dec_lt(v_a_6650_, v___x_6687_);
lean_dec(v___x_6687_);
if (v___x_6688_ == 0)
{
lean_object* v___x_6689_; lean_object* v___x_6690_; 
v___x_6689_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_6690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6651_, v_a_6658_, v___x_6689_, v___y_6652_, v_a_6659_);
v___y_6662_ = v___x_6690_;
goto v___jp_6661_;
}
else
{
lean_object* v___x_6691_; 
lean_inc(v___x_6656_);
v___x_6691_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_6656_, v___x_6688_, v___y_6652_, v_a_6659_);
if (lean_obj_tag(v___x_6691_) == 0)
{
lean_object* v_a_6692_; lean_object* v_a_6693_; lean_object* v___x_6694_; 
v_a_6692_ = lean_ctor_get(v___x_6691_, 0);
lean_inc(v_a_6692_);
v_a_6693_ = lean_ctor_get(v___x_6691_, 1);
lean_inc(v_a_6693_);
lean_dec_ref_known(v___x_6691_, 2);
v___x_6694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6651_, v_a_6658_, v_a_6692_, v___y_6652_, v_a_6693_);
v___y_6662_ = v___x_6694_;
goto v___jp_6661_;
}
else
{
lean_object* v_a_6695_; lean_object* v_a_6696_; lean_object* v___x_6698_; uint8_t v_isShared_6699_; uint8_t v_isSharedCheck_6703_; 
lean_dec(v_a_6658_);
lean_dec_ref(v_b_6651_);
lean_dec(v_a_6650_);
lean_dec_ref(v_f_6648_);
v_a_6695_ = lean_ctor_get(v___x_6691_, 0);
v_a_6696_ = lean_ctor_get(v___x_6691_, 1);
v_isSharedCheck_6703_ = !lean_is_exclusive(v___x_6691_);
if (v_isSharedCheck_6703_ == 0)
{
v___x_6698_ = v___x_6691_;
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
else
{
lean_inc(v_a_6696_);
lean_inc(v_a_6695_);
lean_dec(v___x_6691_);
v___x_6698_ = lean_box(0);
v_isShared_6699_ = v_isSharedCheck_6703_;
goto v_resetjp_6697_;
}
v_resetjp_6697_:
{
lean_object* v___x_6701_; 
if (v_isShared_6699_ == 0)
{
v___x_6701_ = v___x_6698_;
goto v_reusejp_6700_;
}
else
{
lean_object* v_reuseFailAlloc_6702_; 
v_reuseFailAlloc_6702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6702_, 0, v_a_6695_);
lean_ctor_set(v_reuseFailAlloc_6702_, 1, v_a_6696_);
v___x_6701_ = v_reuseFailAlloc_6702_;
goto v_reusejp_6700_;
}
v_reusejp_6700_:
{
return v___x_6701_;
}
}
}
}
v___jp_6661_:
{
if (lean_obj_tag(v___y_6662_) == 0)
{
lean_object* v_a_6663_; 
v_a_6663_ = lean_ctor_get(v___y_6662_, 0);
lean_inc(v_a_6663_);
if (lean_obj_tag(v_a_6663_) == 0)
{
lean_object* v_a_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6672_; 
lean_dec(v_a_6650_);
lean_dec_ref(v_f_6648_);
v_a_6664_ = lean_ctor_get(v___y_6662_, 1);
v_isSharedCheck_6672_ = !lean_is_exclusive(v___y_6662_);
if (v_isSharedCheck_6672_ == 0)
{
lean_object* v_unused_6673_; 
v_unused_6673_ = lean_ctor_get(v___y_6662_, 0);
lean_dec(v_unused_6673_);
v___x_6666_ = v___y_6662_;
v_isShared_6667_ = v_isSharedCheck_6672_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_a_6664_);
lean_dec(v___y_6662_);
v___x_6666_ = lean_box(0);
v_isShared_6667_ = v_isSharedCheck_6672_;
goto v_resetjp_6665_;
}
v_resetjp_6665_:
{
lean_object* v_a_6668_; lean_object* v___x_6670_; 
v_a_6668_ = lean_ctor_get(v_a_6663_, 0);
lean_inc(v_a_6668_);
lean_dec_ref_known(v_a_6663_, 1);
if (v_isShared_6667_ == 0)
{
lean_ctor_set(v___x_6666_, 0, v_a_6668_);
v___x_6670_ = v___x_6666_;
goto v_reusejp_6669_;
}
else
{
lean_object* v_reuseFailAlloc_6671_; 
v_reuseFailAlloc_6671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6671_, 0, v_a_6668_);
lean_ctor_set(v_reuseFailAlloc_6671_, 1, v_a_6664_);
v___x_6670_ = v_reuseFailAlloc_6671_;
goto v_reusejp_6669_;
}
v_reusejp_6669_:
{
return v___x_6670_;
}
}
}
else
{
lean_object* v_a_6674_; lean_object* v_a_6675_; lean_object* v___x_6676_; 
v_a_6674_ = lean_ctor_get(v___y_6662_, 1);
lean_inc(v_a_6674_);
lean_dec_ref_known(v___y_6662_, 2);
v_a_6675_ = lean_ctor_get(v_a_6663_, 0);
lean_inc(v_a_6675_);
lean_dec_ref_known(v_a_6663_, 1);
v___x_6676_ = lean_nat_add(v_a_6650_, v___x_6660_);
lean_dec(v_a_6650_);
v_a_6650_ = v___x_6676_;
v_b_6651_ = v_a_6675_;
v___y_6653_ = v_a_6674_;
goto _start;
}
}
else
{
lean_object* v_a_6678_; lean_object* v_a_6679_; lean_object* v___x_6681_; uint8_t v_isShared_6682_; uint8_t v_isSharedCheck_6686_; 
lean_dec(v_a_6650_);
lean_dec_ref(v_f_6648_);
v_a_6678_ = lean_ctor_get(v___y_6662_, 0);
v_a_6679_ = lean_ctor_get(v___y_6662_, 1);
v_isSharedCheck_6686_ = !lean_is_exclusive(v___y_6662_);
if (v_isSharedCheck_6686_ == 0)
{
v___x_6681_ = v___y_6662_;
v_isShared_6682_ = v_isSharedCheck_6686_;
goto v_resetjp_6680_;
}
else
{
lean_inc(v_a_6679_);
lean_inc(v_a_6678_);
lean_dec(v___y_6662_);
v___x_6681_ = lean_box(0);
v_isShared_6682_ = v_isSharedCheck_6686_;
goto v_resetjp_6680_;
}
v_resetjp_6680_:
{
lean_object* v___x_6684_; 
if (v_isShared_6682_ == 0)
{
v___x_6684_ = v___x_6681_;
goto v_reusejp_6683_;
}
else
{
lean_object* v_reuseFailAlloc_6685_; 
v_reuseFailAlloc_6685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6685_, 0, v_a_6678_);
lean_ctor_set(v_reuseFailAlloc_6685_, 1, v_a_6679_);
v___x_6684_ = v_reuseFailAlloc_6685_;
goto v_reusejp_6683_;
}
v_reusejp_6683_:
{
return v___x_6684_;
}
}
}
}
}
else
{
lean_object* v_a_6704_; lean_object* v_a_6705_; lean_object* v___x_6707_; uint8_t v_isShared_6708_; uint8_t v_isSharedCheck_6712_; 
lean_dec_ref(v_b_6651_);
lean_dec(v_a_6650_);
lean_dec_ref(v_f_6648_);
v_a_6704_ = lean_ctor_get(v___x_6657_, 0);
v_a_6705_ = lean_ctor_get(v___x_6657_, 1);
v_isSharedCheck_6712_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6712_ == 0)
{
v___x_6707_ = v___x_6657_;
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
else
{
lean_inc(v_a_6705_);
lean_inc(v_a_6704_);
lean_dec(v___x_6657_);
v___x_6707_ = lean_box(0);
v_isShared_6708_ = v_isSharedCheck_6712_;
goto v_resetjp_6706_;
}
v_resetjp_6706_:
{
lean_object* v___x_6710_; 
if (v_isShared_6708_ == 0)
{
v___x_6710_ = v___x_6707_;
goto v_reusejp_6709_;
}
else
{
lean_object* v_reuseFailAlloc_6711_; 
v_reuseFailAlloc_6711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6711_, 0, v_a_6704_);
lean_ctor_set(v_reuseFailAlloc_6711_, 1, v_a_6705_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object* v_upperBound_6713_, lean_object* v_stxs_6714_, lean_object* v_f_6715_, lean_object* v___x_6716_, lean_object* v_a_6717_, lean_object* v_b_6718_, lean_object* v___y_6719_, lean_object* v___y_6720_){
_start:
{
lean_object* v_res_6721_; 
v_res_6721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6713_, v_stxs_6714_, v_f_6715_, v___x_6716_, v_a_6717_, v_b_6718_, v___y_6719_, v___y_6720_);
lean_dec_ref(v___y_6719_);
lean_dec(v___x_6716_);
lean_dec_ref(v_stxs_6714_);
lean_dec(v_upperBound_6713_);
return v_res_6721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object* v_f_6722_, lean_object* v_stxs_6723_, lean_object* v_a_6724_, lean_object* v_a_6725_){
_start:
{
lean_object* v___x_6726_; lean_object* v___x_6727_; uint8_t v___x_6728_; 
v___x_6726_ = lean_array_get_size(v_stxs_6723_);
v___x_6727_ = lean_unsigned_to_nat(1u);
v___x_6728_ = lean_nat_dec_eq(v___x_6726_, v___x_6727_);
if (v___x_6728_ == 0)
{
lean_object* v___x_6729_; lean_object* v_acc_6730_; lean_object* v___x_6731_; 
v___x_6729_ = lean_unsigned_to_nat(0u);
v_acc_6730_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_6731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v___x_6726_, v_stxs_6723_, v_f_6722_, v___x_6726_, v___x_6729_, v_acc_6730_, v_a_6724_, v_a_6725_);
if (lean_obj_tag(v___x_6731_) == 0)
{
lean_object* v_a_6732_; lean_object* v_a_6733_; lean_object* v___x_6735_; uint8_t v_isShared_6736_; uint8_t v_isSharedCheck_6741_; 
v_a_6732_ = lean_ctor_get(v___x_6731_, 0);
v_a_6733_ = lean_ctor_get(v___x_6731_, 1);
v_isSharedCheck_6741_ = !lean_is_exclusive(v___x_6731_);
if (v_isSharedCheck_6741_ == 0)
{
v___x_6735_ = v___x_6731_;
v_isShared_6736_ = v_isSharedCheck_6741_;
goto v_resetjp_6734_;
}
else
{
lean_inc(v_a_6733_);
lean_inc(v_a_6732_);
lean_dec(v___x_6731_);
v___x_6735_ = lean_box(0);
v_isShared_6736_ = v_isSharedCheck_6741_;
goto v_resetjp_6734_;
}
v_resetjp_6734_:
{
lean_object* v___x_6737_; lean_object* v___x_6739_; 
v___x_6737_ = l_Lean_Fmt_TaggedDoc_join(v_a_6732_);
if (v_isShared_6736_ == 0)
{
lean_ctor_set(v___x_6735_, 0, v___x_6737_);
v___x_6739_ = v___x_6735_;
goto v_reusejp_6738_;
}
else
{
lean_object* v_reuseFailAlloc_6740_; 
v_reuseFailAlloc_6740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6740_, 0, v___x_6737_);
lean_ctor_set(v_reuseFailAlloc_6740_, 1, v_a_6733_);
v___x_6739_ = v_reuseFailAlloc_6740_;
goto v_reusejp_6738_;
}
v_reusejp_6738_:
{
return v___x_6739_;
}
}
}
else
{
lean_object* v_a_6742_; lean_object* v_a_6743_; lean_object* v___x_6745_; uint8_t v_isShared_6746_; uint8_t v_isSharedCheck_6750_; 
v_a_6742_ = lean_ctor_get(v___x_6731_, 0);
v_a_6743_ = lean_ctor_get(v___x_6731_, 1);
v_isSharedCheck_6750_ = !lean_is_exclusive(v___x_6731_);
if (v_isSharedCheck_6750_ == 0)
{
v___x_6745_ = v___x_6731_;
v_isShared_6746_ = v_isSharedCheck_6750_;
goto v_resetjp_6744_;
}
else
{
lean_inc(v_a_6743_);
lean_inc(v_a_6742_);
lean_dec(v___x_6731_);
v___x_6745_ = lean_box(0);
v_isShared_6746_ = v_isSharedCheck_6750_;
goto v_resetjp_6744_;
}
v_resetjp_6744_:
{
lean_object* v___x_6748_; 
if (v_isShared_6746_ == 0)
{
v___x_6748_ = v___x_6745_;
goto v_reusejp_6747_;
}
else
{
lean_object* v_reuseFailAlloc_6749_; 
v_reuseFailAlloc_6749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6749_, 0, v_a_6742_);
lean_ctor_set(v_reuseFailAlloc_6749_, 1, v_a_6743_);
v___x_6748_ = v_reuseFailAlloc_6749_;
goto v_reusejp_6747_;
}
v_reusejp_6747_:
{
return v___x_6748_;
}
}
}
}
else
{
lean_object* v___x_6751_; lean_object* v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; 
v___x_6751_ = lean_box(0);
v___x_6752_ = lean_unsigned_to_nat(0u);
v___x_6753_ = lean_array_get_borrowed(v___x_6751_, v_stxs_6723_, v___x_6752_);
lean_inc_ref(v_a_6724_);
lean_inc(v___x_6753_);
v___x_6754_ = lean_apply_3(v_f_6722_, v___x_6753_, v_a_6724_, v_a_6725_);
return v___x_6754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object* v_f_6755_, lean_object* v_stxs_6756_, lean_object* v_a_6757_, lean_object* v_a_6758_){
_start:
{
lean_object* v_res_6759_; 
v_res_6759_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v_f_6755_, v_stxs_6756_, v_a_6757_, v_a_6758_);
lean_dec_ref(v_a_6757_);
lean_dec_ref(v_stxs_6756_);
return v_res_6759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object* v_upperBound_6760_, lean_object* v_stxs_6761_, lean_object* v_f_6762_, lean_object* v___x_6763_, lean_object* v_inst_6764_, lean_object* v_R_6765_, lean_object* v_a_6766_, lean_object* v_b_6767_, lean_object* v_c_6768_, lean_object* v___y_6769_, lean_object* v___y_6770_){
_start:
{
lean_object* v___x_6771_; 
v___x_6771_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6760_, v_stxs_6761_, v_f_6762_, v___x_6763_, v_a_6766_, v_b_6767_, v___y_6769_, v___y_6770_);
return v___x_6771_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object* v_upperBound_6772_, lean_object* v_stxs_6773_, lean_object* v_f_6774_, lean_object* v___x_6775_, lean_object* v_inst_6776_, lean_object* v_R_6777_, lean_object* v_a_6778_, lean_object* v_b_6779_, lean_object* v_c_6780_, lean_object* v___y_6781_, lean_object* v___y_6782_){
_start:
{
lean_object* v_res_6783_; 
v_res_6783_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(v_upperBound_6772_, v_stxs_6773_, v_f_6774_, v___x_6775_, v_inst_6776_, v_R_6777_, v_a_6778_, v_b_6779_, v_c_6780_, v___y_6781_, v___y_6782_);
lean_dec_ref(v___y_6781_);
lean_dec(v___x_6775_);
lean_dec_ref(v_stxs_6773_);
lean_dec(v_upperBound_6772_);
return v_res_6783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_stxs_6784_, lean_object* v_a_6785_, lean_object* v_a_6786_){
_start:
{
lean_object* v___x_6787_; lean_object* v___x_6788_; 
v___x_6787_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 0);
v___x_6788_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v___x_6787_, v_stxs_6784_, v_a_6785_, v_a_6786_);
return v___x_6788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_stxs_6789_, lean_object* v_a_6790_, lean_object* v_a_6791_){
_start:
{
lean_object* v_res_6792_; 
v_res_6792_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_stxs_6789_, v_a_6790_, v_a_6791_);
lean_dec_ref(v_a_6790_);
lean_dec_ref(v_stxs_6789_);
return v_res_6792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(lean_object* v_x_6793_){
_start:
{
lean_object* v___x_6794_; 
v___x_6794_ = lean_obj_tag_nat(v_x_6793_);
return v___x_6794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg___boxed(lean_object* v_x_6795_){
_start:
{
lean_object* v_res_6796_; 
v_res_6796_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl___redArg(v_x_6795_);
lean_dec_ref(v_x_6795_);
return v_res_6796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl(lean_object* v_sep_6797_, lean_object* v_x_6798_){
_start:
{
lean_object* v___x_6799_; 
v___x_6799_ = lean_obj_tag_nat(v_x_6798_);
return v___x_6799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___impl___boxed(lean_object* v_sep_6800_, lean_object* v_x_6801_){
_start:
{
lean_object* v_res_6802_; 
v_res_6802_ = l_Lean_Fmt_TrailingGroup_ctorIdx___impl(v_sep_6800_, v_x_6801_);
lean_dec_ref(v_x_6801_);
lean_dec_ref(v_sep_6800_);
return v_res_6802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object* v_t_6803_, lean_object* v_k_6804_){
_start:
{
lean_object* v_g_6805_; lean_object* v___x_6806_; 
v_g_6805_ = lean_ctor_get(v_t_6803_, 0);
lean_inc_ref(v_g_6805_);
lean_dec_ref(v_t_6803_);
v___x_6806_ = lean_apply_1(v_k_6804_, v_g_6805_);
return v___x_6806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim(lean_object* v_sep_6807_, lean_object* v_motive_6808_, lean_object* v_ctorIdx_6809_, lean_object* v_t_6810_, lean_object* v_h_6811_, lean_object* v_k_6812_){
_start:
{
lean_object* v___x_6813_; 
v___x_6813_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6810_, v_k_6812_);
return v___x_6813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object* v_sep_6814_, lean_object* v_motive_6815_, lean_object* v_ctorIdx_6816_, lean_object* v_t_6817_, lean_object* v_h_6818_, lean_object* v_k_6819_){
_start:
{
lean_object* v_res_6820_; 
v_res_6820_ = l_Lean_Fmt_TrailingGroup_ctorElim(v_sep_6814_, v_motive_6815_, v_ctorIdx_6816_, v_t_6817_, v_h_6818_, v_k_6819_);
lean_dec(v_ctorIdx_6816_);
lean_dec_ref(v_sep_6814_);
return v_res_6820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object* v_t_6821_, lean_object* v_group_6822_){
_start:
{
lean_object* v___x_6823_; 
v___x_6823_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6821_, v_group_6822_);
return v___x_6823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim(lean_object* v_sep_6824_, lean_object* v_motive_6825_, lean_object* v_t_6826_, lean_object* v_h_6827_, lean_object* v_group_6828_){
_start:
{
lean_object* v___x_6829_; 
v___x_6829_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6826_, v_group_6828_);
return v___x_6829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object* v_sep_6830_, lean_object* v_motive_6831_, lean_object* v_t_6832_, lean_object* v_h_6833_, lean_object* v_group_6834_){
_start:
{
lean_object* v_res_6835_; 
v_res_6835_ = l_Lean_Fmt_TrailingGroup_group_elim(v_sep_6830_, v_motive_6831_, v_t_6832_, v_h_6833_, v_group_6834_);
lean_dec_ref(v_sep_6830_);
return v_res_6835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object* v_t_6836_, lean_object* v_trailing_6837_){
_start:
{
lean_object* v___x_6838_; 
v___x_6838_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6836_, v_trailing_6837_);
return v___x_6838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim(lean_object* v_sep_6839_, lean_object* v_motive_6840_, lean_object* v_t_6841_, lean_object* v_h_6842_, lean_object* v_trailing_6843_){
_start:
{
lean_object* v___x_6844_; 
v___x_6844_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6841_, v_trailing_6843_);
return v___x_6844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object* v_sep_6845_, lean_object* v_motive_6846_, lean_object* v_t_6847_, lean_object* v_h_6848_, lean_object* v_trailing_6849_){
_start:
{
lean_object* v_res_6850_; 
v_res_6850_ = l_Lean_Fmt_TrailingGroup_trailing_elim(v_sep_6845_, v_motive_6846_, v_t_6847_, v_h_6848_, v_trailing_6849_);
lean_dec_ref(v_sep_6845_);
return v_res_6850_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_6851_; lean_object* v___x_6852_; 
v___x_6851_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_6852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6852_, 0, v___x_6851_);
return v___x_6852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg(){
_start:
{
lean_object* v___x_6854_; 
v___x_6854_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0);
return v___x_6854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___boxed(lean_object* v___dummy_6855_){
_start:
{
lean_object* v_res_6856_; 
v_res_6856_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v_res_6856_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0(void){
_start:
{
lean_object* v___x_6857_; 
v___x_6857_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v___x_6857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object* v_sep_6858_){
_start:
{
lean_object* v___x_6859_; 
v___x_6859_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object* v_sep_6860_){
_start:
{
lean_object* v_res_6861_; 
v_res_6861_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6860_);
lean_dec_ref(v_sep_6860_);
return v_res_6861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg(){
_start:
{
lean_object* v___x_6863_; 
v___x_6863_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg___boxed(lean_object* v___dummy_6864_){
_start:
{
lean_object* v_res_6865_; 
v_res_6865_ = l_Lean_Fmt_instInhabitedTrailingGroup___redArg();
return v_res_6865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup(lean_object* v_a_6866_){
_start:
{
lean_object* v___x_6867_; 
v___x_6867_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object* v_a_6868_){
_start:
{
lean_object* v_res_6869_; 
v_res_6869_ = l_Lean_Fmt_instInhabitedTrailingGroup(v_a_6868_);
lean_dec_ref(v_a_6868_);
return v_res_6869_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object* v_upperBound_6870_, lean_object* v_elemsAndSeps_6871_, lean_object* v_pendingGroup_6872_, lean_object* v___x_6873_, lean_object* v_a_6874_, lean_object* v_b_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_){
_start:
{
lean_object* v_a_6879_; lean_object* v_a_6880_; uint8_t v___x_6884_; 
v___x_6884_ = lean_nat_dec_lt(v_a_6874_, v_upperBound_6870_);
if (v___x_6884_ == 0)
{
lean_object* v___x_6885_; 
lean_dec(v_a_6874_);
lean_dec_ref(v_pendingGroup_6872_);
v___x_6885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6885_, 0, v_b_6875_);
lean_ctor_set(v___x_6885_, 1, v___y_6877_);
return v___x_6885_;
}
else
{
lean_object* v___x_6886_; lean_object* v___x_6887_; 
v___x_6886_ = lean_array_fget_borrowed(v_elemsAndSeps_6871_, v_a_6874_);
lean_inc(v___x_6886_);
v___x_6887_ = l_Lean_Fmt_fmt(v___x_6886_, v___y_6876_, v___y_6877_);
if (lean_obj_tag(v___x_6887_) == 0)
{
lean_object* v_a_6888_; lean_object* v_a_6889_; lean_object* v_fst_6890_; lean_object* v_snd_6891_; lean_object* v___x_6893_; uint8_t v_isShared_6894_; uint8_t v_isSharedCheck_6938_; 
v_a_6888_ = lean_ctor_get(v___x_6887_, 0);
lean_inc(v_a_6888_);
v_a_6889_ = lean_ctor_get(v___x_6887_, 1);
lean_inc(v_a_6889_);
lean_dec_ref_known(v___x_6887_, 2);
v_fst_6890_ = lean_ctor_get(v_b_6875_, 0);
v_snd_6891_ = lean_ctor_get(v_b_6875_, 1);
v_isSharedCheck_6938_ = !lean_is_exclusive(v_b_6875_);
if (v_isSharedCheck_6938_ == 0)
{
v___x_6893_ = v_b_6875_;
v_isShared_6894_ = v_isSharedCheck_6938_;
goto v_resetjp_6892_;
}
else
{
lean_inc(v_snd_6891_);
lean_inc(v_fst_6890_);
lean_dec(v_b_6875_);
v___x_6893_ = lean_box(0);
v_isShared_6894_ = v_isSharedCheck_6938_;
goto v_resetjp_6892_;
}
v_resetjp_6892_:
{
lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6897_; lean_object* v___y_6899_; uint8_t v___y_6927_; lean_object* v___x_6934_; lean_object* v___x_6935_; uint8_t v___x_6936_; 
v___x_6895_ = lean_unsigned_to_nat(0u);
v___x_6896_ = lean_box(0);
v___x_6897_ = lean_array_push(v_snd_6891_, v_a_6888_);
v___x_6934_ = lean_unsigned_to_nat(2u);
v___x_6935_ = lean_nat_mod(v_a_6874_, v___x_6934_);
v___x_6936_ = lean_nat_dec_eq(v___x_6935_, v___x_6895_);
lean_dec(v___x_6935_);
if (v___x_6936_ == 0)
{
v___y_6927_ = v___x_6884_;
goto v___jp_6926_;
}
else
{
uint8_t v___x_6937_; 
v___x_6937_ = 0;
v___y_6927_ = v___x_6937_;
goto v___jp_6926_;
}
v___jp_6898_:
{
uint8_t v___x_6900_; lean_object* v___x_6901_; 
v___x_6900_ = 0;
v___x_6901_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___y_6899_, v___x_6900_, v___y_6876_, v_a_6889_);
if (lean_obj_tag(v___x_6901_) == 0)
{
lean_object* v_a_6902_; lean_object* v_a_6903_; uint8_t v___x_6904_; 
v_a_6902_ = lean_ctor_get(v___x_6901_, 0);
lean_inc(v_a_6902_);
v_a_6903_ = lean_ctor_get(v___x_6901_, 1);
lean_inc(v_a_6903_);
lean_dec_ref_known(v___x_6901_, 2);
v___x_6904_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_6902_);
if (v___x_6904_ == 0)
{
lean_object* v___x_6905_; lean_object* v___x_6906_; lean_object* v___x_6907_; lean_object* v___x_6908_; lean_object* v___x_6910_; 
v___x_6905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6905_, 0, v___x_6897_);
v___x_6906_ = lean_array_push(v_fst_6890_, v___x_6905_);
v___x_6907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6907_, 0, v_a_6902_);
v___x_6908_ = lean_array_push(v___x_6906_, v___x_6907_);
lean_inc_ref(v_pendingGroup_6872_);
if (v_isShared_6894_ == 0)
{
lean_ctor_set(v___x_6893_, 1, v_pendingGroup_6872_);
lean_ctor_set(v___x_6893_, 0, v___x_6908_);
v___x_6910_ = v___x_6893_;
goto v_reusejp_6909_;
}
else
{
lean_object* v_reuseFailAlloc_6911_; 
v_reuseFailAlloc_6911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6911_, 0, v___x_6908_);
lean_ctor_set(v_reuseFailAlloc_6911_, 1, v_pendingGroup_6872_);
v___x_6910_ = v_reuseFailAlloc_6911_;
goto v_reusejp_6909_;
}
v_reusejp_6909_:
{
v_a_6879_ = v___x_6910_;
v_a_6880_ = v_a_6903_;
goto v___jp_6878_;
}
}
else
{
lean_object* v___x_6913_; 
lean_dec(v_a_6902_);
if (v_isShared_6894_ == 0)
{
lean_ctor_set(v___x_6893_, 1, v___x_6897_);
v___x_6913_ = v___x_6893_;
goto v_reusejp_6912_;
}
else
{
lean_object* v_reuseFailAlloc_6914_; 
v_reuseFailAlloc_6914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6914_, 0, v_fst_6890_);
lean_ctor_set(v_reuseFailAlloc_6914_, 1, v___x_6897_);
v___x_6913_ = v_reuseFailAlloc_6914_;
goto v_reusejp_6912_;
}
v_reusejp_6912_:
{
v_a_6879_ = v___x_6913_;
v_a_6880_ = v_a_6903_;
goto v___jp_6878_;
}
}
}
else
{
lean_object* v_a_6915_; lean_object* v_a_6916_; lean_object* v___x_6918_; uint8_t v_isShared_6919_; uint8_t v_isSharedCheck_6923_; 
lean_dec_ref(v___x_6897_);
lean_del_object(v___x_6893_);
lean_dec(v_fst_6890_);
lean_dec(v_a_6874_);
lean_dec_ref(v_pendingGroup_6872_);
v_a_6915_ = lean_ctor_get(v___x_6901_, 0);
v_a_6916_ = lean_ctor_get(v___x_6901_, 1);
v_isSharedCheck_6923_ = !lean_is_exclusive(v___x_6901_);
if (v_isSharedCheck_6923_ == 0)
{
v___x_6918_ = v___x_6901_;
v_isShared_6919_ = v_isSharedCheck_6923_;
goto v_resetjp_6917_;
}
else
{
lean_inc(v_a_6916_);
lean_inc(v_a_6915_);
lean_dec(v___x_6901_);
v___x_6918_ = lean_box(0);
v_isShared_6919_ = v_isSharedCheck_6923_;
goto v_resetjp_6917_;
}
v_resetjp_6917_:
{
lean_object* v___x_6921_; 
if (v_isShared_6919_ == 0)
{
v___x_6921_ = v___x_6918_;
goto v_reusejp_6920_;
}
else
{
lean_object* v_reuseFailAlloc_6922_; 
v_reuseFailAlloc_6922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_a_6915_);
lean_ctor_set(v_reuseFailAlloc_6922_, 1, v_a_6916_);
v___x_6921_ = v_reuseFailAlloc_6922_;
goto v_reusejp_6920_;
}
v_reusejp_6920_:
{
return v___x_6921_;
}
}
}
}
v___jp_6924_:
{
lean_object* v___x_6925_; 
v___x_6925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6925_, 0, v_fst_6890_);
lean_ctor_set(v___x_6925_, 1, v___x_6897_);
v_a_6879_ = v___x_6925_;
v_a_6880_ = v_a_6889_;
goto v___jp_6878_;
}
v___jp_6926_:
{
lean_object* v___x_6928_; lean_object* v___x_6929_; uint8_t v___x_6930_; 
v___x_6928_ = lean_unsigned_to_nat(1u);
v___x_6929_ = lean_nat_sub(v___x_6873_, v___x_6928_);
v___x_6930_ = lean_nat_dec_lt(v_a_6874_, v___x_6929_);
lean_dec(v___x_6929_);
if (v___x_6930_ == 0)
{
lean_del_object(v___x_6893_);
goto v___jp_6924_;
}
else
{
if (v___y_6927_ == 0)
{
lean_del_object(v___x_6893_);
goto v___jp_6924_;
}
else
{
uint8_t v___x_6931_; 
lean_inc(v___x_6886_);
v___x_6931_ = l_Lean_Syntax_matchesNull(v___x_6886_, v___x_6895_);
if (v___x_6931_ == 0)
{
lean_inc(v___x_6886_);
v___y_6899_ = v___x_6886_;
goto v___jp_6898_;
}
else
{
lean_object* v___x_6932_; lean_object* v___x_6933_; 
v___x_6932_ = lean_nat_sub(v_a_6874_, v___x_6928_);
v___x_6933_ = lean_array_get_borrowed(v___x_6896_, v_elemsAndSeps_6871_, v___x_6932_);
lean_dec(v___x_6932_);
lean_inc(v___x_6933_);
v___y_6899_ = v___x_6933_;
goto v___jp_6898_;
}
}
}
}
}
}
else
{
lean_object* v_a_6939_; lean_object* v_a_6940_; lean_object* v___x_6942_; uint8_t v_isShared_6943_; uint8_t v_isSharedCheck_6947_; 
lean_dec_ref(v_b_6875_);
lean_dec(v_a_6874_);
lean_dec_ref(v_pendingGroup_6872_);
v_a_6939_ = lean_ctor_get(v___x_6887_, 0);
v_a_6940_ = lean_ctor_get(v___x_6887_, 1);
v_isSharedCheck_6947_ = !lean_is_exclusive(v___x_6887_);
if (v_isSharedCheck_6947_ == 0)
{
v___x_6942_ = v___x_6887_;
v_isShared_6943_ = v_isSharedCheck_6947_;
goto v_resetjp_6941_;
}
else
{
lean_inc(v_a_6940_);
lean_inc(v_a_6939_);
lean_dec(v___x_6887_);
v___x_6942_ = lean_box(0);
v_isShared_6943_ = v_isSharedCheck_6947_;
goto v_resetjp_6941_;
}
v_resetjp_6941_:
{
lean_object* v___x_6945_; 
if (v_isShared_6943_ == 0)
{
v___x_6945_ = v___x_6942_;
goto v_reusejp_6944_;
}
else
{
lean_object* v_reuseFailAlloc_6946_; 
v_reuseFailAlloc_6946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6946_, 0, v_a_6939_);
lean_ctor_set(v_reuseFailAlloc_6946_, 1, v_a_6940_);
v___x_6945_ = v_reuseFailAlloc_6946_;
goto v_reusejp_6944_;
}
v_reusejp_6944_:
{
return v___x_6945_;
}
}
}
}
v___jp_6878_:
{
lean_object* v___x_6881_; lean_object* v___x_6882_; 
v___x_6881_ = lean_unsigned_to_nat(1u);
v___x_6882_ = lean_nat_add(v_a_6874_, v___x_6881_);
lean_dec(v_a_6874_);
v_a_6874_ = v___x_6882_;
v_b_6875_ = v_a_6879_;
v___y_6877_ = v_a_6880_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object* v_upperBound_6948_, lean_object* v_elemsAndSeps_6949_, lean_object* v_pendingGroup_6950_, lean_object* v___x_6951_, lean_object* v_a_6952_, lean_object* v_b_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_){
_start:
{
lean_object* v_res_6956_; 
v_res_6956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_6948_, v_elemsAndSeps_6949_, v_pendingGroup_6950_, v___x_6951_, v_a_6952_, v_b_6953_, v___y_6954_, v___y_6955_);
lean_dec_ref(v___y_6954_);
lean_dec(v___x_6951_);
lean_dec_ref(v_elemsAndSeps_6949_);
lean_dec(v_upperBound_6948_);
return v_res_6956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object* v_sep_6961_, lean_object* v_stxs_6962_, lean_object* v_a_6963_, lean_object* v_a_6964_){
_start:
{
lean_object* v___x_6965_; lean_object* v___x_6966_; lean_object* v_acc_6967_; lean_object* v___x_6968_; lean_object* v___x_6969_; 
v___x_6965_ = lean_unsigned_to_nat(0u);
v___x_6966_ = lean_array_get_size(v_stxs_6962_);
v_acc_6967_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0));
v___x_6968_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1));
v___x_6969_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v___x_6966_, v_stxs_6962_, v_acc_6967_, v___x_6966_, v___x_6965_, v___x_6968_, v_a_6963_, v_a_6964_);
if (lean_obj_tag(v___x_6969_) == 0)
{
lean_object* v_a_6970_; lean_object* v_a_6971_; lean_object* v___x_6973_; uint8_t v_isShared_6974_; uint8_t v_isSharedCheck_6987_; 
v_a_6970_ = lean_ctor_get(v___x_6969_, 0);
v_a_6971_ = lean_ctor_get(v___x_6969_, 1);
v_isSharedCheck_6987_ = !lean_is_exclusive(v___x_6969_);
if (v_isSharedCheck_6987_ == 0)
{
v___x_6973_ = v___x_6969_;
v_isShared_6974_ = v_isSharedCheck_6987_;
goto v_resetjp_6972_;
}
else
{
lean_inc(v_a_6971_);
lean_inc(v_a_6970_);
lean_dec(v___x_6969_);
v___x_6973_ = lean_box(0);
v_isShared_6974_ = v_isSharedCheck_6987_;
goto v_resetjp_6972_;
}
v_resetjp_6972_:
{
lean_object* v_fst_6975_; lean_object* v_snd_6976_; lean_object* v___x_6977_; uint8_t v___x_6978_; 
v_fst_6975_ = lean_ctor_get(v_a_6970_, 0);
lean_inc(v_fst_6975_);
v_snd_6976_ = lean_ctor_get(v_a_6970_, 1);
lean_inc(v_snd_6976_);
lean_dec(v_a_6970_);
v___x_6977_ = lean_array_get_size(v_snd_6976_);
v___x_6978_ = lean_nat_dec_eq(v___x_6977_, v___x_6965_);
if (v___x_6978_ == 0)
{
lean_object* v___x_6979_; lean_object* v___x_6980_; lean_object* v___x_6982_; 
v___x_6979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6979_, 0, v_snd_6976_);
v___x_6980_ = lean_array_push(v_fst_6975_, v___x_6979_);
if (v_isShared_6974_ == 0)
{
lean_ctor_set(v___x_6973_, 0, v___x_6980_);
v___x_6982_ = v___x_6973_;
goto v_reusejp_6981_;
}
else
{
lean_object* v_reuseFailAlloc_6983_; 
v_reuseFailAlloc_6983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6983_, 0, v___x_6980_);
lean_ctor_set(v_reuseFailAlloc_6983_, 1, v_a_6971_);
v___x_6982_ = v_reuseFailAlloc_6983_;
goto v_reusejp_6981_;
}
v_reusejp_6981_:
{
return v___x_6982_;
}
}
else
{
lean_object* v___x_6985_; 
lean_dec(v_snd_6976_);
if (v_isShared_6974_ == 0)
{
lean_ctor_set(v___x_6973_, 0, v_fst_6975_);
v___x_6985_ = v___x_6973_;
goto v_reusejp_6984_;
}
else
{
lean_object* v_reuseFailAlloc_6986_; 
v_reuseFailAlloc_6986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6986_, 0, v_fst_6975_);
lean_ctor_set(v_reuseFailAlloc_6986_, 1, v_a_6971_);
v___x_6985_ = v_reuseFailAlloc_6986_;
goto v_reusejp_6984_;
}
v_reusejp_6984_:
{
return v___x_6985_;
}
}
}
}
else
{
lean_object* v_a_6988_; lean_object* v_a_6989_; lean_object* v___x_6991_; uint8_t v_isShared_6992_; uint8_t v_isSharedCheck_6996_; 
v_a_6988_ = lean_ctor_get(v___x_6969_, 0);
v_a_6989_ = lean_ctor_get(v___x_6969_, 1);
v_isSharedCheck_6996_ = !lean_is_exclusive(v___x_6969_);
if (v_isSharedCheck_6996_ == 0)
{
v___x_6991_ = v___x_6969_;
v_isShared_6992_ = v_isSharedCheck_6996_;
goto v_resetjp_6990_;
}
else
{
lean_inc(v_a_6989_);
lean_inc(v_a_6988_);
lean_dec(v___x_6969_);
v___x_6991_ = lean_box(0);
v_isShared_6992_ = v_isSharedCheck_6996_;
goto v_resetjp_6990_;
}
v_resetjp_6990_:
{
lean_object* v___x_6994_; 
if (v_isShared_6992_ == 0)
{
v___x_6994_ = v___x_6991_;
goto v_reusejp_6993_;
}
else
{
lean_object* v_reuseFailAlloc_6995_; 
v_reuseFailAlloc_6995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6995_, 0, v_a_6988_);
lean_ctor_set(v_reuseFailAlloc_6995_, 1, v_a_6989_);
v___x_6994_ = v_reuseFailAlloc_6995_;
goto v_reusejp_6993_;
}
v_reusejp_6993_:
{
return v___x_6994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object* v_sep_6997_, lean_object* v_stxs_6998_, lean_object* v_a_6999_, lean_object* v_a_7000_){
_start:
{
lean_object* v_res_7001_; 
v_res_7001_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_6997_, v_stxs_6998_, v_a_6999_, v_a_7000_);
lean_dec_ref(v_a_6999_);
lean_dec_ref(v_stxs_6998_);
lean_dec_ref(v_sep_6997_);
return v_res_7001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object* v_ks_7002_, lean_object* v_sep_7003_, lean_object* v_stxs_7004_, lean_object* v_a_7005_, lean_object* v_a_7006_){
_start:
{
lean_object* v___x_7007_; 
v___x_7007_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7003_, v_stxs_7004_, v_a_7005_, v_a_7006_);
return v___x_7007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object* v_ks_7008_, lean_object* v_sep_7009_, lean_object* v_stxs_7010_, lean_object* v_a_7011_, lean_object* v_a_7012_){
_start:
{
lean_object* v_res_7013_; 
v_res_7013_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups(v_ks_7008_, v_sep_7009_, v_stxs_7010_, v_a_7011_, v_a_7012_);
lean_dec_ref(v_a_7011_);
lean_dec_ref(v_stxs_7010_);
lean_dec_ref(v_sep_7009_);
lean_dec(v_ks_7008_);
return v_res_7013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object* v_upperBound_7014_, lean_object* v_elemsAndSeps_7015_, lean_object* v_sep_7016_, lean_object* v_pendingGroup_7017_, lean_object* v___x_7018_, lean_object* v_inst_7019_, lean_object* v_R_7020_, lean_object* v_a_7021_, lean_object* v_b_7022_, lean_object* v_c_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_){
_start:
{
lean_object* v___x_7026_; 
v___x_7026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7014_, v_elemsAndSeps_7015_, v_pendingGroup_7017_, v___x_7018_, v_a_7021_, v_b_7022_, v___y_7024_, v___y_7025_);
return v___x_7026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object* v_upperBound_7027_, lean_object* v_elemsAndSeps_7028_, lean_object* v_sep_7029_, lean_object* v_pendingGroup_7030_, lean_object* v___x_7031_, lean_object* v_inst_7032_, lean_object* v_R_7033_, lean_object* v_a_7034_, lean_object* v_b_7035_, lean_object* v_c_7036_, lean_object* v___y_7037_, lean_object* v___y_7038_){
_start:
{
lean_object* v_res_7039_; 
v_res_7039_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(v_upperBound_7027_, v_elemsAndSeps_7028_, v_sep_7029_, v_pendingGroup_7030_, v___x_7031_, v_inst_7032_, v_R_7033_, v_a_7034_, v_b_7035_, v_c_7036_, v___y_7037_, v___y_7038_);
lean_dec_ref(v___y_7037_);
lean_dec(v___x_7031_);
lean_dec_ref(v_sep_7029_);
lean_dec_ref(v_elemsAndSeps_7028_);
lean_dec(v_upperBound_7027_);
return v_res_7039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object* v_sep_7043_, size_t v_sz_7044_, size_t v_i_7045_, lean_object* v_bs_7046_){
_start:
{
uint8_t v___x_7047_; 
v___x_7047_ = lean_usize_dec_lt(v_i_7045_, v_sz_7044_);
if (v___x_7047_ == 0)
{
lean_dec_ref(v_sep_7043_);
return v_bs_7046_;
}
else
{
lean_object* v_v_7048_; lean_object* v___x_7049_; lean_object* v_bs_x27_7050_; lean_object* v___y_7052_; 
v_v_7048_ = lean_array_uget(v_bs_7046_, v_i_7045_);
v___x_7049_ = lean_unsigned_to_nat(0u);
v_bs_x27_7050_ = lean_array_uset(v_bs_7046_, v_i_7045_, v___x_7049_);
if (lean_obj_tag(v_v_7048_) == 0)
{
lean_object* v_g_7057_; lean_object* v___x_7058_; lean_object* v___x_7059_; 
v_g_7057_ = lean_ctor_get(v_v_7048_, 0);
lean_inc_ref(v_g_7057_);
lean_dec_ref_known(v_v_7048_, 1);
v___x_7058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0));
lean_inc_ref(v_sep_7043_);
v___x_7059_ = l_Lean_Fmt_Layouts_sepArray(v_sep_7043_, v_g_7057_, v___x_7058_);
lean_dec_ref(v_g_7057_);
v___y_7052_ = v___x_7059_;
goto v___jp_7051_;
}
else
{
lean_object* v_t_7060_; 
v_t_7060_ = lean_ctor_get(v_v_7048_, 0);
lean_inc_ref(v_t_7060_);
lean_dec_ref_known(v_v_7048_, 1);
v___y_7052_ = v_t_7060_;
goto v___jp_7051_;
}
v___jp_7051_:
{
size_t v___x_7053_; size_t v___x_7054_; lean_object* v___x_7055_; 
v___x_7053_ = ((size_t)1ULL);
v___x_7054_ = lean_usize_add(v_i_7045_, v___x_7053_);
v___x_7055_ = lean_array_uset(v_bs_x27_7050_, v_i_7045_, v___y_7052_);
v_i_7045_ = v___x_7054_;
v_bs_7046_ = v___x_7055_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object* v_sep_7061_, lean_object* v_sz_7062_, lean_object* v_i_7063_, lean_object* v_bs_7064_){
_start:
{
size_t v_sz_boxed_7065_; size_t v_i_boxed_7066_; lean_object* v_res_7067_; 
v_sz_boxed_7065_ = lean_unbox_usize(v_sz_7062_);
lean_dec(v_sz_7062_);
v_i_boxed_7066_ = lean_unbox_usize(v_i_7063_);
lean_dec(v_i_7063_);
v_res_7067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7061_, v_sz_boxed_7065_, v_i_boxed_7066_, v_bs_7064_);
return v_res_7067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object* v_sep_7068_, lean_object* v_stxs_7069_, lean_object* v_a_7070_, lean_object* v_a_7071_){
_start:
{
lean_object* v___x_7072_; 
v___x_7072_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7068_, v_stxs_7069_, v_a_7070_, v_a_7071_);
if (lean_obj_tag(v___x_7072_) == 0)
{
lean_object* v_a_7073_; lean_object* v_a_7074_; lean_object* v___x_7076_; uint8_t v_isShared_7077_; uint8_t v_isSharedCheck_7085_; 
v_a_7073_ = lean_ctor_get(v___x_7072_, 0);
v_a_7074_ = lean_ctor_get(v___x_7072_, 1);
v_isSharedCheck_7085_ = !lean_is_exclusive(v___x_7072_);
if (v_isSharedCheck_7085_ == 0)
{
v___x_7076_ = v___x_7072_;
v_isShared_7077_ = v_isSharedCheck_7085_;
goto v_resetjp_7075_;
}
else
{
lean_inc(v_a_7074_);
lean_inc(v_a_7073_);
lean_dec(v___x_7072_);
v___x_7076_ = lean_box(0);
v_isShared_7077_ = v_isSharedCheck_7085_;
goto v_resetjp_7075_;
}
v_resetjp_7075_:
{
size_t v_sz_7078_; size_t v___x_7079_; lean_object* v___x_7080_; lean_object* v___x_7081_; lean_object* v___x_7083_; 
v_sz_7078_ = lean_array_size(v_a_7073_);
v___x_7079_ = ((size_t)0ULL);
v___x_7080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7068_, v_sz_7078_, v___x_7079_, v_a_7073_);
v___x_7081_ = l_Lean_Fmt_TaggedDoc_join(v___x_7080_);
if (v_isShared_7077_ == 0)
{
lean_ctor_set(v___x_7076_, 0, v___x_7081_);
v___x_7083_ = v___x_7076_;
goto v_reusejp_7082_;
}
else
{
lean_object* v_reuseFailAlloc_7084_; 
v_reuseFailAlloc_7084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7084_, 0, v___x_7081_);
lean_ctor_set(v_reuseFailAlloc_7084_, 1, v_a_7074_);
v___x_7083_ = v_reuseFailAlloc_7084_;
goto v_reusejp_7082_;
}
v_reusejp_7082_:
{
return v___x_7083_;
}
}
}
else
{
lean_object* v_a_7086_; lean_object* v_a_7087_; lean_object* v___x_7089_; uint8_t v_isShared_7090_; uint8_t v_isSharedCheck_7094_; 
lean_dec_ref(v_sep_7068_);
v_a_7086_ = lean_ctor_get(v___x_7072_, 0);
v_a_7087_ = lean_ctor_get(v___x_7072_, 1);
v_isSharedCheck_7094_ = !lean_is_exclusive(v___x_7072_);
if (v_isSharedCheck_7094_ == 0)
{
v___x_7089_ = v___x_7072_;
v_isShared_7090_ = v_isSharedCheck_7094_;
goto v_resetjp_7088_;
}
else
{
lean_inc(v_a_7087_);
lean_inc(v_a_7086_);
lean_dec(v___x_7072_);
v___x_7089_ = lean_box(0);
v_isShared_7090_ = v_isSharedCheck_7094_;
goto v_resetjp_7088_;
}
v_resetjp_7088_:
{
lean_object* v___x_7092_; 
if (v_isShared_7090_ == 0)
{
v___x_7092_ = v___x_7089_;
goto v_reusejp_7091_;
}
else
{
lean_object* v_reuseFailAlloc_7093_; 
v_reuseFailAlloc_7093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7093_, 0, v_a_7086_);
lean_ctor_set(v_reuseFailAlloc_7093_, 1, v_a_7087_);
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
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object* v_sep_7095_, lean_object* v_stxs_7096_, lean_object* v_a_7097_, lean_object* v_a_7098_){
_start:
{
lean_object* v_res_7099_; 
v_res_7099_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7095_, v_stxs_7096_, v_a_7097_, v_a_7098_);
lean_dec_ref(v_a_7097_);
lean_dec_ref(v_stxs_7096_);
return v_res_7099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_ks_7100_, lean_object* v_sep_7101_, lean_object* v_stxs_7102_, lean_object* v_a_7103_, lean_object* v_a_7104_){
_start:
{
lean_object* v___x_7105_; 
v___x_7105_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7101_, v_stxs_7102_, v_a_7103_, v_a_7104_);
return v___x_7105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_ks_7106_, lean_object* v_sep_7107_, lean_object* v_stxs_7108_, lean_object* v_a_7109_, lean_object* v_a_7110_){
_start:
{
lean_object* v_res_7111_; 
v_res_7111_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(v_ks_7106_, v_sep_7107_, v_stxs_7108_, v_a_7109_, v_a_7110_);
lean_dec_ref(v_a_7109_);
lean_dec_ref(v_stxs_7108_);
lean_dec(v_ks_7106_);
return v_res_7111_;
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
