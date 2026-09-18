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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_parseComments(lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_ShareCommon_objectFactory;
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
extern uint32_t l_Lean_idBeginEscape;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
uint8_t l_Lean_isLetterLike(uint32_t);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
extern lean_object* l_String_instInhabitedSlice;
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Fmt_instBEqInfixOperationPrecs_beq(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t l_Lean_Fmt_instBEqDefaultCost_beq___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedState_default;
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Layouts_quantified(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
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
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__5;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__6;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__7_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__7_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__8 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__8_value;
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
LEAN_EXPORT uint8_t l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.FmtM.Basic"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__0 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__0_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Fmt.getLineInfo!"};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__1 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__1_value;
static const lean_string_object l_Lean_Fmt_getLineInfo_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "assertion violation: lineInfo.startPos <= pos && pos <= lineInfo.endPos\n  "};
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__2 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__2_value;
static lean_once_cell_t l_Lean_Fmt_getLineInfo_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_getLineInfo_x21___closed__3;
static const lean_closure_object l_Lean_Fmt_getLineInfo_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_getLineInfo_x21___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_getLineInfo_x21___closed__4 = (const lean_object*)&l_Lean_Fmt_getLineInfo_x21___closed__4_value;
static const lean_closure_object l_Lean_Fmt_getLineInfo_x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_getLineInfo_x21___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Fmt_fmtPrefixOperator___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Fmt_fmtPrefixOperator___closed__2;
static lean_once_cell_t l_Lean_Fmt_fmtPrefixOperator___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Fmt_fmtPrefixOperator___closed__3;
static lean_once_cell_t l_Lean_Fmt_fmtPrefixOperator___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Fmt_fmtPrefixOperator___closed__4;
static lean_once_cell_t l_Lean_Fmt_fmtPrefixOperator___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Fmt_fmtPrefixOperator___closed__5;
static lean_once_cell_t l_Lean_Fmt_fmtPrefixOperator___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Fmt_fmtPrefixOperator___closed__6;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "substring is invalid and cannot be converted to a slice"};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "Input syntax to the formatter is malformed: substring is invalid and cannot be converted to a slice."};
static const lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___boxed(lean_object*, lean_object*);
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
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
v___x_116_ = lean_string_utf8_byte_size(v___x_115_);
return v___x_116_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1);
v___x_119_ = lean_nat_dec_eq(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__1);
v___x_121_ = lean_unsigned_to_nat(0u);
v___x_122_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
v___x_123_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_120_);
return v___x_123_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3);
v___x_125_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__4);
v___x_128_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__3);
v___x_129_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_127_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
lean_ctor_set(v___x_129_, 3, v___x_126_);
return v___x_129_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__5, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__5);
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg(){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__2);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__6, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__6_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__6);
return v___x_140_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__8));
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___boxed(lean_object* v___dummy_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg();
return v_res_143_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0(void){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg();
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(lean_object* v_s_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___boxed(lean_object* v_s_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0(v_s_147_);
lean_dec_ref(v_s_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(lean_object* v_numSpaces_149_, lean_object* v_s_150_, lean_object* v___x_151_, lean_object* v___x_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
lean_object* v_it_156_; lean_object* v_startInclusive_157_; lean_object* v_endExclusive_158_; 
if (lean_obj_tag(v_a_153_) == 0)
{
lean_object* v_currPos_164_; lean_object* v_searcher_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_271_; 
v_currPos_164_ = lean_ctor_get(v_a_153_, 0);
v_searcher_165_ = lean_ctor_get(v_a_153_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_a_153_);
if (v_isSharedCheck_271_ == 0)
{
v___x_167_ = v_a_153_;
v_isShared_168_ = v_isSharedCheck_271_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_searcher_165_);
lean_inc(v_currPos_164_);
lean_dec(v_a_153_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_271_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_it_170_; lean_object* v_it_176_; lean_object* v_startPos_177_; lean_object* v_endPos_178_; 
switch(lean_obj_tag(v_searcher_165_))
{
case 0:
{
lean_object* v_pos_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_203_; 
lean_del_object(v___x_167_);
v_pos_191_ = lean_ctor_get(v_searcher_165_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_searcher_165_);
if (v_isSharedCheck_203_ == 0)
{
v___x_193_ = v_searcher_165_;
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_pos_191_);
lean_dec(v_searcher_165_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v_startInclusive_195_; lean_object* v_endExclusive_196_; lean_object* v___x_197_; uint8_t v_decide_198_; 
v_startInclusive_195_ = lean_ctor_get(v___x_151_, 1);
v_endExclusive_196_ = lean_ctor_get(v___x_151_, 2);
v___x_197_ = lean_nat_sub(v_endExclusive_196_, v_startInclusive_195_);
v_decide_198_ = lean_nat_dec_eq(v_pos_191_, v___x_197_);
lean_dec(v___x_197_);
if (v_decide_198_ == 0)
{
lean_object* v___x_200_; 
lean_inc(v_pos_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 1);
v___x_200_ = v___x_193_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_pos_191_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_inc(v_pos_191_);
v_it_176_ = v___x_200_;
v_startPos_177_ = v_pos_191_;
v_endPos_178_ = v_pos_191_;
goto v___jp_175_;
}
}
else
{
lean_object* v___x_202_; 
lean_del_object(v___x_193_);
v___x_202_ = lean_box(3);
lean_inc(v_pos_191_);
v_it_176_ = v___x_202_;
v_startPos_177_ = v_pos_191_;
v_endPos_178_ = v_pos_191_;
goto v___jp_175_;
}
}
}
case 1:
{
lean_object* v_pos_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_pos_204_ = lean_ctor_get(v_searcher_165_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_searcher_165_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v_searcher_165_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_pos_204_);
lean_dec(v_searcher_165_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_string_utf8_next_fast(v_s_150_, v_pos_204_);
lean_dec(v_pos_204_);
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 0);
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_it_170_ = v___x_210_;
goto v___jp_169_;
}
}
}
case 2:
{
lean_object* v_needle_213_; lean_object* v_table_214_; lean_object* v_stackPos_215_; lean_object* v_needlePos_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_270_; 
v_needle_213_ = lean_ctor_get(v_searcher_165_, 0);
v_table_214_ = lean_ctor_get(v_searcher_165_, 1);
v_stackPos_215_ = lean_ctor_get(v_searcher_165_, 2);
v_needlePos_216_ = lean_ctor_get(v_searcher_165_, 3);
v_isSharedCheck_270_ = !lean_is_exclusive(v_searcher_165_);
if (v_isSharedCheck_270_ == 0)
{
v___x_218_ = v_searcher_165_;
v_isShared_219_ = v_isSharedCheck_270_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_needlePos_216_);
lean_inc(v_stackPos_215_);
lean_inc(v_table_214_);
lean_inc(v_needle_213_);
lean_dec(v_searcher_165_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_270_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_str_220_; lean_object* v_startInclusive_221_; lean_object* v_endExclusive_222_; lean_object* v_basePos_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_str_220_ = lean_ctor_get(v_needle_213_, 0);
v_startInclusive_221_ = lean_ctor_get(v_needle_213_, 1);
v_endExclusive_222_ = lean_ctor_get(v_needle_213_, 2);
v_basePos_223_ = lean_nat_sub(v_stackPos_215_, v_needlePos_216_);
v___x_224_ = lean_nat_sub(v_endExclusive_222_, v_startInclusive_221_);
v___x_225_ = lean_nat_add(v_basePos_223_, v___x_224_);
v___x_226_ = lean_nat_dec_le(v___x_225_, v___x_152_);
lean_dec(v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
lean_dec(v___x_224_);
lean_del_object(v___x_218_);
lean_dec(v_needlePos_216_);
lean_dec(v_stackPos_215_);
lean_dec_ref(v_table_214_);
lean_dec_ref(v_needle_213_);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_basePos_223_, v___x_227_);
lean_dec(v_basePos_223_);
v___x_229_ = lean_nat_dec_le(v___x_228_, v___x_152_);
lean_dec(v___x_228_);
if (v___x_229_ == 0)
{
lean_del_object(v___x_167_);
goto v___jp_189_;
}
else
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(3);
v_it_170_ = v___x_230_;
goto v___jp_169_;
}
}
else
{
uint8_t v_stackByte_231_; lean_object* v___x_232_; uint8_t v_patByte_233_; uint8_t v___x_234_; 
lean_dec(v_basePos_223_);
lean_inc(v_stackPos_215_);
v_stackByte_231_ = lean_string_get_byte_fast(v_s_150_, v_stackPos_215_);
v___x_232_ = lean_nat_add(v_startInclusive_221_, v_needlePos_216_);
v_patByte_233_ = lean_string_get_byte_fast(v_str_220_, v___x_232_);
v___x_234_ = lean_uint8_dec_eq(v_stackByte_231_, v_patByte_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; uint8_t v_decide_236_; 
lean_dec(v___x_224_);
v___x_235_ = lean_unsigned_to_nat(0u);
v_decide_236_ = lean_nat_dec_eq(v_needlePos_216_, v___x_235_);
if (v_decide_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_newNeedlePos_239_; uint8_t v___x_240_; 
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_sub(v_needlePos_216_, v___x_237_);
lean_dec(v_needlePos_216_);
v_newNeedlePos_239_ = lean_array_fget_borrowed(v_table_214_, v___x_238_);
lean_dec(v___x_238_);
v___x_240_ = lean_nat_dec_eq(v_newNeedlePos_239_, v___x_235_);
if (v___x_240_ == 0)
{
lean_object* v___x_242_; 
lean_inc(v_newNeedlePos_239_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 3, v_newNeedlePos_239_);
v___x_242_ = v___x_218_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_needle_213_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_table_214_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_stackPos_215_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_newNeedlePos_239_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v_it_170_ = v___x_242_;
goto v___jp_169_;
}
}
else
{
lean_object* v_nextStackPos_244_; lean_object* v___x_246_; 
v_nextStackPos_244_ = l_String_Slice_posGE___redArg(v___x_151_, v_stackPos_215_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 3, v___x_235_);
lean_ctor_set(v___x_218_, 2, v_nextStackPos_244_);
v___x_246_ = v___x_218_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_needle_213_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_table_214_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_nextStackPos_244_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v___x_235_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v_it_170_ = v___x_246_;
goto v___jp_169_;
}
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_nextStackPos_250_; lean_object* v___x_252_; 
lean_dec(v_needlePos_216_);
v___x_248_ = lean_unsigned_to_nat(1u);
v___x_249_ = lean_nat_add(v_stackPos_215_, v___x_248_);
lean_dec(v_stackPos_215_);
v_nextStackPos_250_ = l_String_Slice_posGE___redArg(v___x_151_, v___x_249_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 3, v___x_235_);
lean_ctor_set(v___x_218_, 2, v_nextStackPos_250_);
v___x_252_ = v___x_218_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_needle_213_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_table_214_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_nextStackPos_250_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v___x_235_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
v_it_170_ = v___x_252_;
goto v___jp_169_;
}
}
}
else
{
lean_object* v___x_254_; lean_object* v_nextStackPos_255_; lean_object* v_nextNeedlePos_256_; uint8_t v_decide_257_; 
lean_del_object(v___x_167_);
v___x_254_ = lean_unsigned_to_nat(1u);
v_nextStackPos_255_ = lean_nat_add(v_stackPos_215_, v___x_254_);
lean_dec(v_stackPos_215_);
v_nextNeedlePos_256_ = lean_nat_add(v_needlePos_216_, v___x_254_);
lean_dec(v_needlePos_216_);
v_decide_257_ = lean_nat_dec_eq(v_nextNeedlePos_256_, v___x_224_);
lean_dec(v___x_224_);
if (v_decide_257_ == 0)
{
lean_object* v___x_259_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 3, v_nextNeedlePos_256_);
lean_ctor_set(v___x_218_, 2, v_nextStackPos_255_);
v___x_259_ = v___x_218_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_needle_213_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_table_214_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_nextStackPos_255_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_nextNeedlePos_256_);
v___x_259_ = v_reuseFailAlloc_262_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; 
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_currPos_164_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v_a_153_ = v___x_260_;
goto _start;
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_263_ = lean_nat_sub(v_nextStackPos_255_, v_nextNeedlePos_256_);
lean_dec(v_nextNeedlePos_256_);
v___x_264_ = l_String_Slice_pos_x21(v___x_151_, v___x_263_);
lean_dec(v___x_263_);
v___x_265_ = l_String_Slice_pos_x21(v___x_151_, v_nextStackPos_255_);
v___x_266_ = lean_unsigned_to_nat(0u);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 3, v___x_266_);
lean_ctor_set(v___x_218_, 2, v_nextStackPos_255_);
v___x_268_ = v___x_218_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_needle_213_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_table_214_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_nextStackPos_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
v_it_176_ = v___x_268_;
v_startPos_177_ = v___x_264_;
v_endPos_178_ = v___x_265_;
goto v___jp_175_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_167_);
goto v___jp_189_;
}
}
v___jp_169_:
{
lean_object* v___x_172_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v_it_170_);
v___x_172_ = v___x_167_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_currPos_164_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v_it_170_);
v___x_172_ = v_reuseFailAlloc_174_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
v_a_153_ = v___x_172_;
goto _start;
}
}
v___jp_175_:
{
lean_object* v_slice_179_; lean_object* v_startInclusive_180_; lean_object* v_endExclusive_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_slice_179_ = l_String_Slice_subslice_x21(v___x_151_, v_currPos_164_, v_startPos_177_);
v_startInclusive_180_ = lean_ctor_get(v_slice_179_, 0);
v_endExclusive_181_ = lean_ctor_get(v_slice_179_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_slice_179_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v_slice_179_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_endExclusive_181_);
lean_inc(v_startInclusive_180_);
lean_dec(v_slice_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_nextIt_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v_it_176_);
lean_ctor_set(v___x_183_, 0, v_endPos_178_);
v_nextIt_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_endPos_178_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_it_176_);
v_nextIt_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
v_it_156_ = v_nextIt_186_;
v_startInclusive_157_ = v_startInclusive_180_;
v_endExclusive_158_ = v_endExclusive_181_;
goto v___jp_155_;
}
}
}
v___jp_189_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(1);
lean_inc(v___x_152_);
v_it_156_ = v___x_190_;
v_startInclusive_157_ = v_currPos_164_;
v_endExclusive_158_ = v___x_152_;
goto v___jp_155_;
}
}
}
else
{
lean_dec(v___x_152_);
lean_dec_ref(v_s_150_);
lean_dec(v_numSpaces_149_);
return v_b_154_;
}
v___jp_155_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_inc_ref(v_s_150_);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v_s_150_);
lean_ctor_set(v___x_159_, 1, v_startInclusive_157_);
lean_ctor_set(v___x_159_, 2, v_endExclusive_158_);
lean_inc(v_numSpaces_149_);
v___x_160_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent_dropSpaces(v___x_159_, v_numSpaces_149_);
v___x_161_ = l_String_Slice_toString(v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = lean_array_push(v_b_154_, v___x_161_);
v_a_153_ = v_it_156_;
v_b_154_ = v___x_162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg___boxed(lean_object* v_numSpaces_272_, lean_object* v_s_273_, lean_object* v___x_274_, lean_object* v___x_275_, lean_object* v_a_276_, lean_object* v_b_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_272_, v_s_273_, v___x_274_, v___x_275_, v_a_276_, v_b_277_);
lean_dec_ref(v___x_274_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(lean_object* v_s_281_, lean_object* v_numSpaces_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_283_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_string_utf8_byte_size(v_s_281_);
lean_inc_ref(v_s_281_);
v___x_286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_286_, 0, v_s_281_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
lean_ctor_set(v___x_286_, 2, v___x_285_);
v___x_287_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_288_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__String_deindent___closed__0));
v___x_289_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_282_, v_s_281_, v___x_286_, v___x_285_, v___x_287_, v___x_288_);
lean_dec_ref_known(v___x_286_, 3);
v___x_290_ = lean_array_to_list(v___x_289_);
v___x_291_ = l_String_intercalate(v___x_283_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(lean_object* v_numSpaces_292_, lean_object* v_s_293_, lean_object* v___x_294_, lean_object* v___x_295_, lean_object* v_inst_296_, lean_object* v_R_297_, lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___redArg(v_numSpaces_292_, v_s_293_, v___x_294_, v___x_295_, v_a_298_, v_b_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1___boxed(lean_object* v_numSpaces_301_, lean_object* v_s_302_, lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v_inst_305_, lean_object* v_R_306_, lean_object* v_a_307_, lean_object* v_b_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__1(v_numSpaces_301_, v_s_302_, v___x_303_, v___x_304_, v_inst_305_, v_R_306_, v_a_307_, v_b_308_);
lean_dec_ref(v___x_303_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState___redArg(lean_object* v_value_310_, lean_object* v_s_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_s_311_);
lean_ctor_set(v___x_312_, 1, v_value_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_Result_ofFinalState(lean_object* v_00_u03b1_313_, lean_object* v_value_314_, lean_object* v_s_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_s_315_);
lean_ctor_set(v___x_316_, 1, v_value_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_box(0);
v___x_318_ = lean_unsigned_to_nat(16u);
v___x_319_ = lean_mk_array(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__0, &l_Lean_FmtM_run___redArg___closed__0_once, _init_l_Lean_FmtM_run___redArg___closed__0);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = l_Lean_ShareCommon_objectFactory;
v___x_324_ = l_ShareCommon_mkStateImpl(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_FmtM_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__2, &l_Lean_FmtM_run___redArg___closed__2_once, _init_l_Lean_FmtM_run___redArg___closed__2);
v___x_327_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__1, &l_Lean_FmtM_run___redArg___closed__1_once, _init_l_Lean_FmtM_run___redArg___closed__1);
v___x_328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_ctor_set(v___x_328_, 2, v___x_325_);
lean_ctor_set(v___x_328_, 3, v___x_327_);
lean_ctor_set(v___x_328_, 4, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run___redArg(lean_object* v_ctx_329_, lean_object* v_act_330_){
_start:
{
lean_object* v___x_331_; lean_object* v_r_332_; 
v___x_331_ = lean_obj_once(&l_Lean_FmtM_run___redArg___closed__3, &l_Lean_FmtM_run___redArg___closed__3_once, _init_l_Lean_FmtM_run___redArg___closed__3);
v_r_332_ = lean_apply_2(v_act_330_, v_ctx_329_, v___x_331_);
if (lean_obj_tag(v_r_332_) == 0)
{
lean_object* v_a_333_; lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_342_; 
v_a_333_ = lean_ctor_get(v_r_332_, 0);
v_a_334_ = lean_ctor_get(v_r_332_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_r_332_);
if (v_isSharedCheck_342_ == 0)
{
v___x_336_ = v_r_332_;
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_inc(v_a_333_);
lean_dec(v_r_332_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_342_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v_a_333_);
lean_ctor_set(v___x_336_, 0, v_a_334_);
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_334_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_a_333_);
v___x_339_ = v_reuseFailAlloc_341_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; 
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_344_; 
v_a_343_ = lean_ctor_get(v_r_332_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v_r_332_, 2);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v_a_343_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FmtM_run(lean_object* v_00_u03b1_345_, lean_object* v_ctx_346_, lean_object* v_act_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_FmtM_run___redArg(v_ctx_346_, v_act_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(lean_object* v_00_u03b1_349_, lean_object* v_v_350_, lean_object* v_x_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_toBacktrackableState_353_; lean_object* v_shareCommonState_354_; lean_object* v_freshTagId_355_; lean_object* v_missingFormatters_356_; lean_object* v_partialFormatters_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_375_; 
v_toBacktrackableState_353_ = lean_ctor_get(v___y_352_, 0);
v_shareCommonState_354_ = lean_ctor_get(v___y_352_, 1);
v_freshTagId_355_ = lean_ctor_get(v___y_352_, 2);
v_missingFormatters_356_ = lean_ctor_get(v___y_352_, 3);
v_partialFormatters_357_ = lean_ctor_get(v___y_352_, 4);
v_isSharedCheck_375_ = !lean_is_exclusive(v___y_352_);
if (v_isSharedCheck_375_ == 0)
{
v___x_359_ = v___y_352_;
v_isShared_360_ = v_isSharedCheck_375_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_partialFormatters_357_);
lean_inc(v_missingFormatters_356_);
lean_inc(v_freshTagId_355_);
lean_inc(v_shareCommonState_354_);
lean_inc(v_toBacktrackableState_353_);
lean_dec(v___y_352_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_375_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_374_; 
v___x_361_ = l_Lean_ShareCommon_objectFactory;
v___x_362_ = lean_state_sharecommon(v___x_361_, v_shareCommonState_354_, v_v_350_);
v_fst_363_ = lean_ctor_get(v___x_362_, 0);
v_snd_364_ = lean_ctor_get(v___x_362_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_374_ == 0)
{
v___x_366_ = v___x_362_;
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_snd_364_);
lean_inc(v_fst_363_);
lean_dec(v___x_362_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 1, v_snd_364_);
v___x_369_ = v___x_359_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_toBacktrackableState_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_snd_364_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_freshTagId_355_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_missingFormatters_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_partialFormatters_357_);
v___x_369_ = v_reuseFailAlloc_373_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_fst_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v_v_377_, lean_object* v_x_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Fmt_FmtM_Basic_0__instMonadShareCommonFmtM___lam__0(v_00_u03b1_376_, v_v_377_, v_x_378_, v___y_379_);
lean_dec_ref(v_x_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_FormattedWhitespace_merge(lean_object* v_t1_383_, lean_object* v_t2_384_){
_start:
{
lean_object* v_formattedLeadingRanges_385_; lean_object* v_formattedTrailingRanges_386_; lean_object* v_formattedLeadingRanges_387_; lean_object* v_formattedTrailingRanges_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_397_; 
v_formattedLeadingRanges_385_ = lean_ctor_get(v_t1_383_, 0);
lean_inc_ref(v_formattedLeadingRanges_385_);
v_formattedTrailingRanges_386_ = lean_ctor_get(v_t1_383_, 1);
lean_inc_ref(v_formattedTrailingRanges_386_);
lean_dec_ref(v_t1_383_);
v_formattedLeadingRanges_387_ = lean_ctor_get(v_t2_384_, 0);
v_formattedTrailingRanges_388_ = lean_ctor_get(v_t2_384_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_t2_384_);
if (v_isSharedCheck_397_ == 0)
{
v___x_390_ = v_t2_384_;
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_formattedTrailingRanges_388_);
lean_inc(v_formattedLeadingRanges_387_);
lean_dec(v_t2_384_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_392_ = l_Array_append___redArg(v_formattedLeadingRanges_385_, v_formattedLeadingRanges_387_);
lean_dec_ref(v_formattedLeadingRanges_387_);
v___x_393_ = l_Array_append___redArg(v_formattedTrailingRanges_386_, v_formattedTrailingRanges_388_);
lean_dec_ref(v_formattedTrailingRanges_388_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v___x_393_);
lean_ctor_set(v___x_390_, 0, v___x_392_);
v___x_395_ = v___x_390_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg(lean_object* v_stx_398_, lean_object* v_i_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_arg_401_; uint8_t v___x_402_; 
v_arg_401_ = l_Lean_Syntax_getArg(v_stx_398_, v_i_399_);
v___x_402_ = l_Lean_Syntax_isMissing(v_arg_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_arg_401_);
lean_ctor_set(v___x_403_, 1, v_a_400_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_arg_401_);
v___x_404_ = l_Lean_Fmt_Error_partialFormatter;
v___x_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_a_400_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___redArg___boxed(lean_object* v_stx_406_, lean_object* v_i_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_406_, v_i_407_, v_a_408_);
lean_dec(v_i_407_);
lean_dec(v_stx_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21(lean_object* v_stx_410_, lean_object* v_i_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_410_, v_i_411_, v_a_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getStxArg_x21___boxed(lean_object* v_stx_415_, lean_object* v_i_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Fmt_getStxArg_x21(v_stx_415_, v_i_416_, v_a_417_, v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_i_416_);
lean_dec(v_stx_415_);
return v_res_419_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0(void){
_start:
{
lean_object* v___x_420_; lean_object* v___f_421_; 
v___x_420_ = l_Lean_Fmt_instInhabitedError_default;
v___f_421_ = lean_alloc_closure((void*)(l_EStateM_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_421_, 0, v___x_420_);
return v___f_421_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___f_425_; lean_object* v___f_426_; lean_object* v___x_684__overap_427_; lean_object* v___x_428_; 
v___f_425_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___closed__0);
v___f_426_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_426_, 0, v___f_425_);
v___x_684__overap_427_ = lean_panic_fn_borrowed(v___f_426_, v_msg_422_);
lean_dec_ref(v___f_426_);
lean_inc_ref(v___y_423_);
v___x_428_ = lean_apply_2(v___x_684__overap_427_, v___y_423_, v___y_424_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0___boxed(lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v_msg_429_, v___y_430_, v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_432_;
}
}
static lean_object* _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = l_Lean_Fmt_instInhabitedSyntaxLineInfo_default;
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(lean_object* v_msg_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0, &l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0_once, _init_l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1___closed__0);
v___x_438_ = lean_panic_fn_borrowed(v___x_437_, v_msg_436_);
return v___x_438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_getLineInfo_x21___lam__0(lean_object* v_x1_439_, lean_object* v_x2_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = lean_nat_add(v_x1_439_, v___x_441_);
v___x_443_ = lean_nat_dec_le(v___x_442_, v_x2_440_);
lean_dec(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__0___boxed(lean_object* v_x1_444_, lean_object* v_x2_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lean_Fmt_getLineInfo_x21___lam__0(v_x1_444_, v_x2_445_);
lean_dec(v_x2_445_);
lean_dec(v_x1_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1(lean_object* v_x_448_){
_start:
{
lean_object* v_startPos_449_; 
v_startPos_449_ = lean_ctor_get(v_x_448_, 4);
lean_inc(v_startPos_449_);
return v_startPos_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21___lam__1___boxed(lean_object* v_x_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Fmt_getLineInfo_x21___lam__1(v_x_450_);
lean_dec_ref(v_x_450_);
return v_res_451_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__3(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_455_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__2));
v___x_456_ = lean_unsigned_to_nat(2u);
v___x_457_ = lean_unsigned_to_nat(84u);
v___x_458_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__1));
v___x_459_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_460_ = l_mkPanicMessageWithDecl(v___x_459_, v___x_458_, v___x_457_, v___x_456_, v___x_455_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Fmt_getLineInfo_x21___closed__9(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_466_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__8));
v___x_467_ = lean_unsigned_to_nat(14u);
v___x_468_ = lean_unsigned_to_nat(22u);
v___x_469_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__7));
v___x_470_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__6));
v___x_471_ = l_mkPanicMessageWithDecl(v___x_470_, v___x_469_, v___x_468_, v___x_467_, v___x_466_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getLineInfo_x21(lean_object* v_pos_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___y_476_; uint8_t v___y_477_; lean_object* v___y_482_; lean_object* v_lineInfos_488_; lean_object* v___f_489_; lean_object* v___f_490_; lean_object* v___x_491_; 
v_lineInfos_488_ = lean_ctor_get(v_a_473_, 4);
v___f_489_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___f_490_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
lean_inc(v_pos_472_);
v___x_491_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_488_, v_pos_472_, v___f_490_, v___f_489_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_493_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__1(v___x_492_);
v___y_482_ = v___x_493_;
goto v___jp_481_;
}
else
{
lean_object* v_val_494_; 
v_val_494_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_494_);
lean_dec_ref_known(v___x_491_, 1);
v___y_482_ = v_val_494_;
goto v___jp_481_;
}
v___jp_475_:
{
if (v___y_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec_ref(v___y_476_);
v___x_478_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__3, &l_Lean_Fmt_getLineInfo_x21___closed__3_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__3);
v___x_479_ = l_panic___at___00Lean_Fmt_getLineInfo_x21_spec__0(v___x_478_, v_a_473_, v_a_474_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v___y_476_);
lean_ctor_set(v___x_480_, 1, v_a_474_);
return v___x_480_;
}
}
v___jp_481_:
{
lean_object* v_snd_483_; lean_object* v_startPos_484_; lean_object* v_endPos_485_; uint8_t v___x_486_; 
v_snd_483_ = lean_ctor_get(v___y_482_, 1);
lean_inc(v_snd_483_);
lean_dec_ref(v___y_482_);
v_startPos_484_ = lean_ctor_get(v_snd_483_, 4);
v_endPos_485_ = lean_ctor_get(v_snd_483_, 5);
v___x_486_ = lean_nat_dec_le(v_startPos_484_, v_pos_472_);
if (v___x_486_ == 0)
{
lean_dec(v_pos_472_);
v___y_476_ = v_snd_483_;
v___y_477_ = v___x_486_;
goto v___jp_475_;
}
else
{
uint8_t v___x_487_; 
v___x_487_ = lean_nat_dec_le(v_pos_472_, v_endPos_485_);
lean_dec(v_pos_472_);
v___y_476_ = v_snd_483_;
v___y_477_ = v___x_487_;
goto v___jp_475_;
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
v___f_503_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
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
v___x_534_ = lean_unsigned_to_nat(92u);
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
v___f_565_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___f_566_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
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
v___f_613_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___f_614_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
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
lean_dec(v_metaData_643_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_656_; lean_object* v_a_657_; 
v_a_656_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_656_);
v_a_657_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_644_, 2);
v_a_635_ = v_a_656_;
v_a_636_ = v_a_657_;
goto v___jp_634_;
}
else
{
lean_object* v_a_658_; lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v_bs_x27_633_);
v_a_658_ = lean_ctor_get(v___x_644_, 0);
v_a_659_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_644_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_inc(v_a_658_);
lean_dec(v___x_644_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_658_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg___boxed(lean_object* v_sz_667_, lean_object* v_i_668_, lean_object* v_bs_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v_i_boxed_672_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_boxed_671_, v_i_boxed_672_, v_bs_669_, v___y_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace(lean_object* v_stx_674_, lean_object* v_fmtLeading_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getHeadToken_x3f(v_stx_674_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_680_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_678_, 1);
v___x_680_ = l_Lean_Syntax_getLeading_x3f(v_val_679_);
if (lean_obj_tag(v___x_680_) == 1)
{
lean_object* v_val_681_; lean_object* v___x_682_; 
v_val_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_val_681_);
lean_dec_ref_known(v___x_680_, 1);
lean_inc_ref(v_a_676_);
v___x_682_ = lean_apply_4(v_fmtLeading_675_, v_val_679_, v_val_681_, v_a_676_, v_a_677_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v_a_684_; size_t v_sz_685_; size_t v___x_686_; lean_object* v___x_687_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
v_a_684_ = lean_ctor_get(v___x_682_, 1);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_682_, 2);
v_sz_685_ = lean_array_size(v_a_683_);
v___x_686_ = ((size_t)0ULL);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_685_, v___x_686_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_697_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_a_689_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_697_ == 0)
{
v___x_691_ = v___x_687_;
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_697_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_Fmt_TaggedDoc_join(v_a_688_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_693_);
v___x_695_ = v___x_691_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_a_689_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_698_ = lean_ctor_get(v___x_687_, 0);
v_a_699_ = lean_ctor_get(v___x_687_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_687_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_inc(v_a_698_);
lean_dec(v___x_687_);
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
lean_object* v_a_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_a_707_ = lean_ctor_get(v___x_682_, 0);
v_a_708_ = lean_ctor_get(v___x_682_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_682_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_inc(v_a_707_);
lean_dec(v___x_682_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_707_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v___x_680_);
lean_dec(v_val_679_);
lean_dec_ref(v_fmtLeading_675_);
v___x_716_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_a_677_);
return v___x_717_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v___x_678_);
lean_dec_ref(v_fmtLeading_675_);
v___x_718_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_a_677_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWhitespace___boxed(lean_object* v_stx_720_, lean_object* v_fmtLeading_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_720_, v_fmtLeading_721_, v_a_722_, v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(size_t v_sz_725_, size_t v_i_726_, lean_object* v_bs_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_725_, v_i_726_, v_bs_727_, v___y_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___boxed(lean_object* v_sz_731_, lean_object* v_i_732_, lean_object* v_bs_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
size_t v_sz_boxed_736_; size_t v_i_boxed_737_; lean_object* v_res_738_; 
v_sz_boxed_736_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_737_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0(v_sz_boxed_736_, v_i_boxed_737_, v_bs_733_, v___y_734_, v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace(lean_object* v_stx_739_, lean_object* v_fmtTrailing_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Syntax_getTailToken_x3f(v_stx_739_);
if (lean_obj_tag(v___x_743_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_745_; 
v_val_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = l_Lean_Syntax_getTrailing_x3f(v_val_744_);
if (lean_obj_tag(v___x_745_) == 1)
{
lean_object* v_val_746_; lean_object* v___x_747_; 
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v___x_745_, 1);
lean_inc_ref(v_a_741_);
v___x_747_ = lean_apply_4(v_fmtTrailing_740_, v_val_744_, v_val_746_, v_a_741_, v_a_742_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_a_749_; size_t v_sz_750_; size_t v___x_751_; lean_object* v___x_752_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
v_a_749_ = lean_ctor_get(v___x_747_, 1);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_747_, 2);
v_sz_750_ = lean_array_size(v_a_748_);
v___x_751_ = ((size_t)0ULL);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtLeadingWhitespace_spec__0___redArg(v_sz_750_, v___x_751_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_a_754_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v___x_752_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = l_Lean_Fmt_TaggedDoc_join(v_a_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_a_754_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
else
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
v_a_763_ = lean_ctor_get(v___x_752_, 0);
v_a_764_ = lean_ctor_get(v___x_752_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_752_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_inc(v_a_763_);
lean_dec(v___x_752_);
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
lean_object* v_a_772_; lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_a_772_ = lean_ctor_get(v___x_747_, 0);
v_a_773_ = lean_ctor_get(v___x_747_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_747_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_inc(v_a_772_);
lean_dec(v___x_747_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_772_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v___x_745_);
lean_dec(v_val_744_);
lean_dec_ref(v_fmtTrailing_740_);
v___x_781_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_a_742_);
return v___x_782_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec(v___x_743_);
lean_dec_ref(v_fmtTrailing_740_);
v___x_783_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v_a_742_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWhitespace___boxed(lean_object* v_stx_785_, lean_object* v_fmtTrailing_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_785_, v_fmtTrailing_786_, v_a_787_, v_a_788_);
lean_dec_ref(v_a_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(lean_object* v_env_790_, lean_object* v_opts_791_, lean_object* v_kind_792_){
_start:
{
uint8_t v___x_793_; lean_object* v___x_794_; 
v___x_793_ = 1;
v___x_794_ = l_Lean_Environment_evalConst___redArg(v_env_790_, v_opts_791_, v_kind_792_, v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; 
lean_dec_ref_known(v___x_794_, 1);
v___x_795_ = lean_box(0);
return v___x_795_;
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_794_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_794_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1___boxed(lean_object* v_env_804_, lean_object* v_opts_805_, lean_object* v_kind_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f_unsafe__1(v_env_804_, v_opts_805_, v_kind_806_);
lean_dec(v_kind_806_);
lean_dec_ref(v_opts_805_);
lean_dec_ref(v_env_804_);
return v_res_807_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_box(0);
v___x_809_ = lean_unsigned_to_nat(16u);
v___x_810_ = lean_mk_array(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__0);
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(lean_object* v_env_825_, lean_object* v_opts_826_, lean_object* v_kind_827_){
_start:
{
uint8_t v___x_828_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_834_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; uint8_t v___y_848_; uint8_t v___y_849_; uint8_t v___y_863_; lean_object* v___x_898_; 
v___x_828_ = 0;
lean_inc(v_kind_827_);
lean_inc_ref(v_env_825_);
v___x_898_ = l_Lean_Environment_find_x3f(v_env_825_, v_kind_827_, v___x_828_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v___x_899_; 
lean_dec(v_kind_827_);
lean_dec_ref(v_env_825_);
v___x_899_ = lean_box(0);
return v___x_899_;
}
else
{
lean_object* v_val_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_val_900_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v___x_898_, 1);
v___x_901_ = l_Lean_ConstantInfo_type(v_val_900_);
lean_dec(v_val_900_);
v___x_902_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_903_ = l_Lean_Expr_isConstOf(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_905_ = l_Lean_Expr_isConstOf(v___x_901_, v___x_904_);
lean_dec_ref(v___x_901_);
v___y_863_ = v___x_905_;
goto v___jp_862_;
}
else
{
lean_dec_ref(v___x_901_);
v___y_863_ = v___x_903_;
goto v___jp_862_;
}
}
v___jp_829_:
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_add(v___y_831_, v___x_835_);
lean_dec(v___y_831_);
v___x_837_ = lean_nat_dec_eq(v___x_836_, v___y_833_);
lean_dec(v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_830_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
else
{
uint8_t v___x_839_; 
v___x_839_ = lean_nat_dec_eq(v___y_833_, v___y_832_);
lean_dec(v___y_832_);
lean_dec(v___y_833_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_dec(v___y_830_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_842_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_842_, 0, v___y_830_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*2, v___y_834_);
lean_ctor_set_uint8(v___x_842_, sizeof(void*)*2 + 1, v___x_828_);
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
}
v___jp_844_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_inc(v___y_846_);
lean_inc(v___y_847_);
lean_inc(v___y_845_);
v___x_850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_850_, 0, v___y_845_);
lean_ctor_set(v___x_850_, 1, v___y_847_);
lean_ctor_set(v___x_850_, 2, v___y_846_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
if (v___y_849_ == 0)
{
uint8_t v___x_852_; 
v___x_852_ = lean_nat_dec_eq(v___y_845_, v___y_846_);
if (v___x_852_ == 0)
{
v___y_830_ = v___x_851_;
v___y_831_ = v___y_845_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_847_;
v___y_834_ = v___y_848_;
goto v___jp_829_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v___y_846_, v___x_853_);
v___x_855_ = lean_nat_dec_eq(v___y_847_, v___x_854_);
lean_dec(v___x_854_);
if (v___x_855_ == 0)
{
v___y_830_ = v___x_851_;
v___y_831_ = v___y_845_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_847_;
v___y_834_ = v___y_848_;
goto v___jp_829_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v___y_847_);
lean_dec(v___y_846_);
lean_dec(v___y_845_);
v___x_856_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_857_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_857_, 0, v___x_851_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*2, v___x_828_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*2 + 1, v___x_828_);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
return v___x_858_;
}
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v___y_847_);
lean_dec(v___y_846_);
lean_dec(v___y_845_);
v___x_859_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__1);
v___x_860_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_860_, 0, v___x_851_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*2, v___x_828_);
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*2 + 1, v___x_828_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
v___jp_862_:
{
if (v___y_863_ == 0)
{
lean_object* v___x_864_; 
lean_dec(v_kind_827_);
lean_dec_ref(v_env_825_);
v___x_864_ = lean_box(0);
return v___x_864_;
}
else
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Environment_evalConst___redArg(v_env_825_, v_opts_826_, v_kind_827_, v___y_863_);
lean_dec(v_kind_827_);
lean_dec_ref(v_env_825_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_866_; 
lean_dec_ref_known(v___x_865_, 1);
v___x_866_ = lean_box(0);
return v___x_866_;
}
else
{
lean_object* v_a_867_; 
v_a_867_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_865_, 1);
if (lean_obj_tag(v_a_867_) == 4)
{
lean_object* v_p_868_; 
v_p_868_ = lean_ctor_get(v_a_867_, 3);
lean_inc_ref(v_p_868_);
if (lean_obj_tag(v_p_868_) == 2)
{
lean_object* v_name_869_; 
v_name_869_ = lean_ctor_get(v_p_868_, 0);
lean_inc(v_name_869_);
if (lean_obj_tag(v_name_869_) == 1)
{
lean_object* v_pre_870_; 
v_pre_870_ = lean_ctor_get(v_name_869_, 0);
if (lean_obj_tag(v_pre_870_) == 0)
{
lean_object* v_prec_871_; lean_object* v_lhsPrec_872_; lean_object* v_p_u2081_873_; lean_object* v_p_u2082_874_; lean_object* v_str_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_prec_871_ = lean_ctor_get(v_a_867_, 1);
lean_inc(v_prec_871_);
v_lhsPrec_872_ = lean_ctor_get(v_a_867_, 2);
lean_inc(v_lhsPrec_872_);
lean_dec_ref_known(v_a_867_, 4);
v_p_u2081_873_ = lean_ctor_get(v_p_868_, 1);
lean_inc_ref(v_p_u2081_873_);
v_p_u2082_874_ = lean_ctor_get(v_p_868_, 2);
lean_inc_ref(v_p_u2082_874_);
lean_dec_ref_known(v_p_868_, 3);
v_str_875_ = lean_ctor_get(v_name_869_, 1);
lean_inc_ref(v_str_875_);
lean_dec_ref_known(v_name_869_, 2);
v___x_876_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_877_ = lean_string_dec_eq(v_str_875_, v___x_876_);
lean_dec_ref(v_str_875_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec_ref(v_p_u2082_874_);
lean_dec_ref(v_p_u2081_873_);
lean_dec(v_lhsPrec_872_);
lean_dec(v_prec_871_);
v___x_878_ = lean_box(0);
return v___x_878_;
}
else
{
if (lean_obj_tag(v_p_u2081_873_) == 5)
{
lean_dec_ref_known(v_p_u2081_873_, 1);
if (lean_obj_tag(v_p_u2082_874_) == 7)
{
lean_object* v_catName_879_; 
v_catName_879_ = lean_ctor_get(v_p_u2082_874_, 0);
lean_inc(v_catName_879_);
if (lean_obj_tag(v_catName_879_) == 1)
{
lean_object* v_pre_880_; 
v_pre_880_ = lean_ctor_get(v_catName_879_, 0);
if (lean_obj_tag(v_pre_880_) == 0)
{
lean_object* v_rbp_881_; lean_object* v_str_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_rbp_881_ = lean_ctor_get(v_p_u2082_874_, 1);
lean_inc(v_rbp_881_);
lean_dec_ref_known(v_p_u2082_874_, 2);
v_str_882_ = lean_ctor_get(v_catName_879_, 1);
lean_inc_ref(v_str_882_);
lean_dec_ref_known(v_catName_879_, 2);
v___x_883_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_884_ = lean_string_dec_eq(v_str_882_, v___x_883_);
lean_dec_ref(v_str_882_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
lean_dec(v_rbp_881_);
lean_dec(v_lhsPrec_872_);
lean_dec(v_prec_871_);
v___x_885_ = lean_box(0);
return v___x_885_;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = lean_nat_dec_eq(v_prec_871_, v_lhsPrec_872_);
if (v___x_886_ == 0)
{
v___y_845_ = v_prec_871_;
v___y_846_ = v_rbp_881_;
v___y_847_ = v_lhsPrec_872_;
v___y_848_ = v___x_884_;
v___y_849_ = v___x_828_;
goto v___jp_844_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_nat_add(v_lhsPrec_872_, v___x_887_);
v___x_889_ = lean_nat_dec_eq(v___x_888_, v_rbp_881_);
lean_dec(v___x_888_);
v___y_845_ = v_prec_871_;
v___y_846_ = v_rbp_881_;
v___y_847_ = v_lhsPrec_872_;
v___y_848_ = v___x_884_;
v___y_849_ = v___x_889_;
goto v___jp_844_;
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec_ref_known(v_catName_879_, 2);
lean_dec_ref_known(v_p_u2082_874_, 2);
lean_dec(v_lhsPrec_872_);
lean_dec(v_prec_871_);
v___x_890_ = lean_box(0);
return v___x_890_;
}
}
else
{
lean_object* v___x_891_; 
lean_dec_ref_known(v_p_u2082_874_, 2);
lean_dec(v_catName_879_);
lean_dec(v_lhsPrec_872_);
lean_dec(v_prec_871_);
v___x_891_ = lean_box(0);
return v___x_891_;
}
}
else
{
lean_object* v___x_892_; 
lean_dec_ref(v_p_u2082_874_);
lean_dec(v_lhsPrec_872_);
lean_dec(v_prec_871_);
v___x_892_ = lean_box(0);
return v___x_892_;
}
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v_p_u2082_874_);
lean_dec_ref(v_p_u2081_873_);
lean_dec(v_lhsPrec_872_);
lean_dec(v_prec_871_);
v___x_893_ = lean_box(0);
return v___x_893_;
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec_ref_known(v_name_869_, 2);
lean_dec_ref_known(v_p_868_, 3);
lean_dec_ref_known(v_a_867_, 4);
v___x_894_ = lean_box(0);
return v___x_894_;
}
}
else
{
lean_object* v___x_895_; 
lean_dec(v_name_869_);
lean_dec_ref_known(v_p_868_, 3);
lean_dec_ref_known(v_a_867_, 4);
v___x_895_ = lean_box(0);
return v___x_895_;
}
}
else
{
lean_object* v___x_896_; 
lean_dec_ref_known(v_a_867_, 4);
lean_dec_ref(v_p_868_);
v___x_896_ = lean_box(0);
return v___x_896_;
}
}
else
{
lean_object* v___x_897_; 
lean_dec(v_a_867_);
v___x_897_ = lean_box(0);
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___boxed(lean_object* v_env_906_, lean_object* v_opts_907_, lean_object* v_kind_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_906_, v_opts_907_, v_kind_908_);
lean_dec_ref(v_opts_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(lean_object* v_env_910_, lean_object* v_opts_911_, lean_object* v_kind_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = l_Lean_Fmt_infixFmtAttribute;
lean_inc_ref(v_env_910_);
v___x_914_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_913_, v_env_910_, v_kind_912_);
v___x_915_ = l_List_head_x3f___redArg(v___x_914_);
lean_dec(v___x_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; 
v___x_916_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_910_, v_opts_911_, v_kind_912_);
return v___x_916_;
}
else
{
lean_dec(v_kind_912_);
lean_dec_ref(v_env_910_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f___boxed(lean_object* v_env_917_, lean_object* v_opts_918_, lean_object* v_kind_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_917_, v_opts_918_, v_kind_919_);
lean_dec_ref(v_opts_918_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(lean_object* v_env_921_, lean_object* v_opts_922_, lean_object* v_kind_923_){
_start:
{
uint8_t v___x_924_; lean_object* v___x_925_; 
v___x_924_ = 1;
v___x_925_ = l_Lean_Environment_evalConst___redArg(v_env_921_, v_opts_922_, v_kind_923_, v___x_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; 
lean_dec_ref_known(v___x_925_, 1);
v___x_926_ = lean_box(0);
return v___x_926_;
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
v_a_927_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_925_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1___boxed(lean_object* v_env_935_, lean_object* v_opts_936_, lean_object* v_kind_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter_unsafe__1(v_env_935_, v_opts_936_, v_kind_937_);
lean_dec(v_kind_937_);
lean_dec_ref(v_opts_936_);
lean_dec_ref(v_env_935_);
return v_res_938_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(lean_object* v_env_939_, lean_object* v_opts_940_, lean_object* v_kind_941_){
_start:
{
uint8_t v___x_942_; lean_object* v___x_943_; 
v___x_942_ = 0;
lean_inc(v_kind_941_);
lean_inc_ref(v_env_939_);
v___x_943_ = l_Lean_Environment_find_x3f(v_env_939_, v_kind_941_, v___x_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_dec(v_kind_941_);
lean_dec_ref(v_env_939_);
return v___x_942_;
}
else
{
lean_object* v_val_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_val_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_val_944_);
lean_dec_ref_known(v___x_943_, 1);
v___x_945_ = l_Lean_ConstantInfo_type(v_val_944_);
lean_dec(v_val_944_);
v___x_946_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_947_ = l_Lean_Expr_isConstOf(v___x_945_, v___x_946_);
lean_dec_ref(v___x_945_);
if (v___x_947_ == 0)
{
lean_dec(v_kind_941_);
lean_dec_ref(v_env_939_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Environment_evalConst___redArg(v_env_939_, v_opts_940_, v_kind_941_, v___x_947_);
lean_dec(v_kind_941_);
lean_dec_ref(v_env_939_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_dec_ref_known(v___x_948_, 1);
return v___x_942_;
}
else
{
lean_object* v_a_949_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
if (lean_obj_tag(v_a_949_) == 3)
{
lean_object* v_p_950_; 
v_p_950_ = lean_ctor_get(v_a_949_, 2);
lean_inc_ref(v_p_950_);
if (lean_obj_tag(v_p_950_) == 2)
{
lean_object* v_name_951_; 
v_name_951_ = lean_ctor_get(v_p_950_, 0);
lean_inc(v_name_951_);
if (lean_obj_tag(v_name_951_) == 1)
{
lean_object* v_pre_952_; 
v_pre_952_ = lean_ctor_get(v_name_951_, 0);
if (lean_obj_tag(v_pre_952_) == 0)
{
lean_object* v_prec_953_; lean_object* v_p_u2081_954_; lean_object* v_p_u2082_955_; lean_object* v_str_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_prec_953_ = lean_ctor_get(v_a_949_, 1);
lean_inc(v_prec_953_);
lean_dec_ref_known(v_a_949_, 3);
v_p_u2081_954_ = lean_ctor_get(v_p_950_, 1);
lean_inc_ref(v_p_u2081_954_);
v_p_u2082_955_ = lean_ctor_get(v_p_950_, 2);
lean_inc_ref(v_p_u2082_955_);
lean_dec_ref_known(v_p_950_, 3);
v_str_956_ = lean_ctor_get(v_name_951_, 1);
lean_inc_ref(v_str_956_);
lean_dec_ref_known(v_name_951_, 2);
v___x_957_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__2));
v___x_958_ = lean_string_dec_eq(v_str_956_, v___x_957_);
lean_dec_ref(v_str_956_);
if (v___x_958_ == 0)
{
lean_dec_ref(v_p_u2082_955_);
lean_dec_ref(v_p_u2081_954_);
lean_dec(v_prec_953_);
return v___x_958_;
}
else
{
if (lean_obj_tag(v_p_u2081_954_) == 5)
{
lean_dec_ref_known(v_p_u2081_954_, 1);
if (lean_obj_tag(v_p_u2082_955_) == 7)
{
lean_object* v_catName_959_; 
v_catName_959_ = lean_ctor_get(v_p_u2082_955_, 0);
lean_inc(v_catName_959_);
if (lean_obj_tag(v_catName_959_) == 1)
{
lean_object* v_pre_960_; 
v_pre_960_ = lean_ctor_get(v_catName_959_, 0);
if (lean_obj_tag(v_pre_960_) == 0)
{
lean_object* v_rbp_961_; lean_object* v_str_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_rbp_961_ = lean_ctor_get(v_p_u2082_955_, 1);
lean_inc(v_rbp_961_);
lean_dec_ref_known(v_p_u2082_955_, 2);
v_str_962_ = lean_ctor_get(v_catName_959_, 1);
lean_inc_ref(v_str_962_);
lean_dec_ref_known(v_catName_959_, 2);
v___x_963_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__3));
v___x_964_ = lean_string_dec_eq(v_str_962_, v___x_963_);
lean_dec_ref(v_str_962_);
if (v___x_964_ == 0)
{
lean_dec(v_rbp_961_);
lean_dec(v_prec_953_);
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_eq(v_prec_953_, v_rbp_961_);
lean_dec(v_rbp_961_);
lean_dec(v_prec_953_);
return v___x_965_;
}
}
else
{
lean_dec_ref_known(v_catName_959_, 2);
lean_dec_ref_known(v_p_u2082_955_, 2);
lean_dec(v_prec_953_);
return v___x_942_;
}
}
else
{
lean_dec(v_catName_959_);
lean_dec_ref_known(v_p_u2082_955_, 2);
lean_dec(v_prec_953_);
return v___x_942_;
}
}
else
{
lean_dec_ref(v_p_u2082_955_);
lean_dec(v_prec_953_);
return v___x_942_;
}
}
else
{
lean_dec_ref(v_p_u2082_955_);
lean_dec_ref(v_p_u2081_954_);
lean_dec(v_prec_953_);
return v___x_942_;
}
}
}
else
{
lean_dec_ref_known(v_name_951_, 2);
lean_dec_ref_known(v_p_950_, 3);
lean_dec_ref_known(v_a_949_, 3);
return v___x_942_;
}
}
else
{
lean_dec_ref_known(v_p_950_, 3);
lean_dec(v_name_951_);
lean_dec_ref_known(v_a_949_, 3);
return v___x_942_;
}
}
else
{
lean_dec_ref(v_p_950_);
lean_dec_ref_known(v_a_949_, 3);
return v___x_942_;
}
}
else
{
lean_dec(v_a_949_);
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter___boxed(lean_object* v_env_966_, lean_object* v_opts_967_, lean_object* v_kind_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_966_, v_opts_967_, v_kind_968_);
lean_dec_ref(v_opts_967_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(lean_object* v_env_971_, lean_object* v_opts_972_, lean_object* v_kind_973_){
_start:
{
uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_974_ = 1;
v___x_975_ = l_Lean_Environment_evalConst___redArg(v_env_971_, v_opts_972_, v_kind_973_, v___x_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_976_; 
lean_dec_ref_known(v___x_975_, 1);
v___x_976_ = lean_box(0);
return v___x_976_;
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_a_977_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_975_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1___boxed(lean_object* v_env_985_, lean_object* v_opts_986_, lean_object* v_kind_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter_unsafe__1(v_env_985_, v_opts_986_, v_kind_987_);
lean_dec(v_kind_987_);
lean_dec_ref(v_opts_986_);
lean_dec_ref(v_env_985_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(lean_object* v_env_989_, lean_object* v_opts_990_, lean_object* v_kind_991_){
_start:
{
uint8_t v___x_992_; lean_object* v___x_993_; 
v___x_992_ = 0;
lean_inc(v_kind_991_);
lean_inc_ref(v_env_989_);
v___x_993_ = l_Lean_Environment_find_x3f(v_env_989_, v_kind_991_, v___x_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_dec(v_kind_991_);
lean_dec_ref(v_env_989_);
return v___x_992_;
}
else
{
lean_object* v_val_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_val_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = l_Lean_ConstantInfo_type(v_val_994_);
lean_dec(v_val_994_);
v___x_996_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__8));
v___x_997_ = l_Lean_Expr_isConstOf(v___x_995_, v___x_996_);
lean_dec_ref(v___x_995_);
if (v___x_997_ == 0)
{
lean_dec(v_kind_991_);
lean_dec_ref(v_env_989_);
return v___x_997_;
}
else
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_Environment_evalConst___redArg(v_env_989_, v_opts_990_, v_kind_991_, v___x_997_);
lean_dec(v_kind_991_);
lean_dec_ref(v_env_989_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_dec_ref_known(v___x_998_, 1);
return v___x_992_;
}
else
{
lean_object* v_a_999_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
if (lean_obj_tag(v_a_999_) == 4)
{
lean_object* v_p_1000_; 
v_p_1000_ = lean_ctor_get(v_a_999_, 3);
if (lean_obj_tag(v_p_1000_) == 5)
{
lean_object* v_prec_1001_; lean_object* v_lhsPrec_1002_; uint8_t v___x_1003_; 
v_prec_1001_ = lean_ctor_get(v_a_999_, 1);
lean_inc(v_prec_1001_);
v_lhsPrec_1002_ = lean_ctor_get(v_a_999_, 2);
lean_inc(v_lhsPrec_1002_);
lean_dec_ref_known(v_a_999_, 4);
v___x_1003_ = lean_nat_dec_eq(v_prec_1001_, v_lhsPrec_1002_);
lean_dec(v_lhsPrec_1002_);
lean_dec(v_prec_1001_);
return v___x_1003_;
}
else
{
lean_dec_ref_known(v_a_999_, 4);
return v___x_992_;
}
}
else
{
lean_dec(v_a_999_);
return v___x_992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter___boxed(lean_object* v_env_1004_, lean_object* v_opts_1005_, lean_object* v_kind_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_1004_, v_opts_1005_, v_kind_1006_);
lean_dec_ref(v_opts_1005_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(lean_object* v_a_1135_, lean_object* v_as_1136_, size_t v_i_1137_, size_t v_stop_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_usize_dec_eq(v_i_1137_, v_stop_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_array_uget_borrowed(v_as_1136_, v_i_1137_);
v___x_1141_ = lean_name_eq(v_a_1135_, v___x_1140_);
if (v___x_1141_ == 0)
{
size_t v___x_1142_; size_t v___x_1143_; 
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_add(v_i_1137_, v___x_1142_);
v_i_1137_ = v___x_1143_;
goto _start;
}
else
{
return v___x_1141_;
}
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = 0;
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0___boxed(lean_object* v_a_1146_, lean_object* v_as_1147_, lean_object* v_i_1148_, lean_object* v_stop_1149_){
_start:
{
size_t v_i_boxed_1150_; size_t v_stop_boxed_1151_; uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_i_boxed_1150_ = lean_unbox_usize(v_i_1148_);
lean_dec(v_i_1148_);
v_stop_boxed_1151_ = lean_unbox_usize(v_stop_1149_);
lean_dec(v_stop_1149_);
v_res_1152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1146_, v_as_1147_, v_i_boxed_1150_, v_stop_boxed_1151_);
lean_dec_ref(v_as_1147_);
lean_dec(v_a_1146_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(lean_object* v_as_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_array_get_size(v_as_1154_);
v___x_1158_ = lean_nat_dec_lt(v___x_1156_, v___x_1157_);
if (v___x_1158_ == 0)
{
return v___x_1158_;
}
else
{
if (v___x_1158_ == 0)
{
return v___x_1158_;
}
else
{
size_t v___x_1159_; size_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = lean_usize_of_nat(v___x_1157_);
v___x_1161_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0_spec__0(v_a_1155_, v_as_1154_, v___x_1159_, v___x_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0___boxed(lean_object* v_as_1162_, lean_object* v_a_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v_as_1162_, v_a_1163_);
lean_dec(v_a_1163_);
lean_dec_ref(v_as_1162_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(lean_object* v_x_1171_){
_start:
{
switch(lean_obj_tag(v_x_1171_))
{
case 5:
{
uint8_t v___x_1172_; 
v___x_1172_ = 1;
return v___x_1172_;
}
case 6:
{
uint8_t v___x_1173_; 
v___x_1173_ = 1;
return v___x_1173_;
}
case 12:
{
uint8_t v___x_1174_; 
v___x_1174_ = 1;
return v___x_1174_;
}
case 0:
{
lean_object* v_name_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_name_1175_ = lean_ctor_get(v_x_1171_, 0);
v___x_1176_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_emptyParserAliases));
v___x_1177_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1176_, v_name_1175_);
return v___x_1177_;
}
case 1:
{
lean_object* v_name_1178_; lean_object* v_p_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_name_1178_ = lean_ctor_get(v_x_1171_, 0);
v_p_1179_ = lean_ctor_get(v_x_1171_, 1);
v___x_1180_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_transparentParserAliases));
v___x_1181_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr_spec__0(v___x_1180_, v_name_1178_);
if (v___x_1181_ == 0)
{
return v___x_1181_;
}
else
{
v_x_1171_ = v_p_1179_;
goto _start;
}
}
case 2:
{
lean_object* v_name_1183_; lean_object* v_p_u2081_1184_; lean_object* v_p_u2082_1185_; uint8_t v___y_1187_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v_name_1183_ = lean_ctor_get(v_x_1171_, 0);
v_p_u2081_1184_ = lean_ctor_get(v_x_1171_, 1);
v_p_u2082_1185_ = lean_ctor_get(v_x_1171_, 2);
v___x_1190_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__0));
v___x_1191_ = lean_name_eq(v_name_1183_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___closed__2));
v___x_1193_ = lean_name_eq(v_name_1183_, v___x_1192_);
v___y_1187_ = v___x_1193_;
goto v___jp_1186_;
}
else
{
v___y_1187_ = v___x_1191_;
goto v___jp_1186_;
}
v___jp_1186_:
{
if (v___y_1187_ == 0)
{
return v___y_1187_;
}
else
{
uint8_t v___x_1188_; 
v___x_1188_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_p_u2081_1184_);
if (v___x_1188_ == 0)
{
return v___x_1188_;
}
else
{
v_x_1171_ = v_p_u2082_1185_;
goto _start;
}
}
}
}
case 3:
{
lean_object* v_p_1194_; 
v_p_1194_ = lean_ctor_get(v_x_1171_, 2);
v_x_1171_ = v_p_1194_;
goto _start;
}
case 9:
{
lean_object* v_p_1196_; 
v_p_1196_ = lean_ctor_get(v_x_1171_, 2);
v_x_1171_ = v_p_1196_;
goto _start;
}
default: 
{
uint8_t v___x_1198_; 
v___x_1198_ = 0;
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr___boxed(lean_object* v_x_1199_){
_start:
{
uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_res_1200_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_x_1199_);
lean_dec_ref(v_x_1199_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(lean_object* v_env_1202_, lean_object* v_opts_1203_, lean_object* v_kind_1204_){
_start:
{
uint8_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = 1;
v___x_1206_ = l_Lean_Environment_evalConst___redArg(v_env_1202_, v_opts_1203_, v_kind_1204_, v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; 
lean_dec_ref_known(v___x_1206_, 1);
v___x_1207_ = lean_box(0);
return v___x_1207_;
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1206_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1___boxed(lean_object* v_env_1216_, lean_object* v_opts_1217_, lean_object* v_kind_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter_unsafe__1(v_env_1216_, v_opts_1217_, v_kind_1218_);
lean_dec(v_kind_1218_);
lean_dec_ref(v_opts_1217_);
lean_dec_ref(v_env_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(lean_object* v_env_1220_, lean_object* v_opts_1221_, lean_object* v_kind_1222_){
_start:
{
uint8_t v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = 0;
lean_inc(v_kind_1222_);
lean_inc_ref(v_env_1220_);
v___x_1224_ = l_Lean_Environment_find_x3f(v_env_1220_, v_kind_1222_, v___x_1223_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_dec(v_kind_1222_);
lean_dec_ref(v_env_1220_);
return v___x_1223_;
}
else
{
lean_object* v_val_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_val_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_val_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v___x_1226_ = l_Lean_ConstantInfo_type(v_val_1225_);
lean_dec(v_val_1225_);
v___x_1227_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f___closed__6));
v___x_1228_ = l_Lean_Expr_isConstOf(v___x_1226_, v___x_1227_);
lean_dec_ref(v___x_1226_);
if (v___x_1228_ == 0)
{
lean_dec(v_kind_1222_);
lean_dec_ref(v_env_1220_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Environment_evalConst___redArg(v_env_1220_, v_opts_1221_, v_kind_1222_, v___x_1228_);
lean_dec(v_kind_1222_);
lean_dec_ref(v_env_1220_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_dec_ref_known(v___x_1229_, 1);
return v___x_1223_;
}
else
{
lean_object* v_a_1230_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
if (lean_obj_tag(v_a_1230_) == 4)
{
lean_dec_ref_known(v_a_1230_, 4);
return v___x_1223_;
}
else
{
uint8_t v___x_1231_; 
v___x_1231_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAtomicParserDescr(v_a_1230_);
lean_dec(v_a_1230_);
return v___x_1231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter___boxed(lean_object* v_env_1232_, lean_object* v_opts_1233_, lean_object* v_kind_1234_){
_start:
{
uint8_t v_res_1235_; lean_object* v_r_1236_; 
v_res_1235_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_1232_, v_opts_1233_, v_kind_1234_);
lean_dec_ref(v_opts_1233_);
v_r_1236_ = lean_box(v_res_1235_);
return v_r_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f(lean_object* v_env_1237_, lean_object* v_kind_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_1240_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1239_, v_env_1237_, v_kind_1238_);
v___x_1241_ = l_List_head_x3f___redArg(v___x_1240_);
lean_dec(v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getConditionalFormatter_x3f___boxed(lean_object* v_env_1242_, lean_object* v_kind_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Fmt_getConditionalFormatter_x3f(v_env_1242_, v_kind_1243_);
lean_dec(v_kind_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f(lean_object* v_env_1245_, lean_object* v_kind_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_1248_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(v___x_1247_, v_env_1245_, v_kind_1246_);
v___x_1249_ = l_List_head_x3f___redArg(v___x_1248_);
lean_dec(v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getQuantifierFormatter_x3f___boxed(lean_object* v_env_1250_, lean_object* v_kind_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1250_, v_kind_1251_);
lean_dec(v_kind_1251_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(lean_object* v_msg_1267_){
_start:
{
lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___f_1268_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__0));
v___f_1269_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__1));
v___f_1270_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__2));
v___f_1271_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__3));
v___f_1272_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__4));
v___f_1273_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__5));
v___f_1274_ = ((lean_object*)(l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1___closed__6));
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___f_1268_);
lean_ctor_set(v___x_1275_, 1, v___f_1269_);
v___x_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v___f_1270_);
lean_ctor_set(v___x_1276_, 2, v___f_1271_);
lean_ctor_set(v___x_1276_, 3, v___f_1272_);
lean_ctor_set(v___x_1276_, 4, v___f_1273_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___f_1274_);
v___x_1278_ = ((lean_object*)(l_Lean_Fmt_instInhabitedQuantifierChain_default));
v___x_1279_ = l_instInhabitedOfMonad___redArg(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_panic_fn_borrowed(v___x_1279_, v_msg_1267_);
lean_dec(v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(lean_object* v_env_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1346_; 
v_snd_1283_ = lean_ctor_get(v_a_1282_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_a_1282_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v_a_1282_, 0);
lean_dec(v_unused_1347_);
v___x_1285_ = v_a_1282_;
v_isShared_1286_ = v_isSharedCheck_1346_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_dec(v_a_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1346_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_snd_1287_; lean_object* v_fst_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1345_; 
v_snd_1287_ = lean_ctor_get(v_snd_1283_, 1);
v_fst_1288_ = lean_ctor_get(v_snd_1283_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_snd_1283_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1290_ = v_snd_1283_;
v_isShared_1291_ = v_isSharedCheck_1345_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_snd_1287_);
lean_inc(v_fst_1288_);
lean_dec(v_snd_1283_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1345_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
if (lean_obj_tag(v_fst_1288_) == 1)
{
lean_object* v_fst_1292_; lean_object* v_snd_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1327_; 
v_fst_1292_ = lean_ctor_get(v_snd_1287_, 0);
v_snd_1293_ = lean_ctor_get(v_snd_1287_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_snd_1287_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1295_ = v_snd_1287_;
v_isShared_1296_ = v_isSharedCheck_1327_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_snd_1293_);
lean_inc(v_fst_1292_);
lean_dec(v_snd_1287_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1327_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_val_1297_; lean_object* v___x_1298_; 
v_val_1297_ = lean_ctor_get(v_fst_1288_, 0);
lean_inc(v_val_1297_);
lean_inc(v_fst_1292_);
v___x_1298_ = lean_apply_1(v_val_1297_, v_fst_1292_);
if (lean_obj_tag(v___x_1298_) == 1)
{
lean_object* v_val_1299_; lean_object* v_toQuantifierHeadComponents_1300_; lean_object* v_body_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_dec(v_fst_1292_);
lean_dec_ref_known(v_fst_1288_, 1);
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v_toQuantifierHeadComponents_1300_ = lean_ctor_get(v_val_1299_, 0);
lean_inc_ref(v_toQuantifierHeadComponents_1300_);
v_body_1301_ = lean_ctor_get(v_val_1299_, 1);
lean_inc_n(v_body_1301_, 2);
lean_dec(v_val_1299_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_array_push(v_snd_1293_, v_toQuantifierHeadComponents_1300_);
v___x_1304_ = l_Lean_Syntax_getKind(v_body_1301_);
lean_inc_ref(v_env_1281_);
v___x_1305_ = l_Lean_Fmt_getQuantifierFormatter_x3f(v_env_1281_, v___x_1304_);
lean_dec(v___x_1304_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 1, v___x_1303_);
lean_ctor_set(v___x_1295_, 0, v_body_1301_);
v___x_1307_ = v___x_1295_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_body_1301_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___x_1303_);
v___x_1307_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1307_);
lean_ctor_set(v___x_1290_, 0, v___x_1305_);
v___x_1309_ = v___x_1290_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1311_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1309_);
lean_ctor_set(v___x_1285_, 0, v___x_1302_);
v___x_1311_ = v___x_1285_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
v_a_1282_ = v___x_1311_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_dec(v___x_1298_);
lean_dec_ref(v_env_1281_);
lean_inc(v_fst_1292_);
lean_inc(v_snd_1293_);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v_snd_1293_);
lean_ctor_set(v___x_1316_, 1, v_fst_1292_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
if (v_isShared_1296_ == 0)
{
v___x_1319_ = v___x_1295_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_fst_1292_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_snd_1293_);
v___x_1319_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1319_);
v___x_1321_ = v___x_1290_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_fst_1288_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1321_);
lean_ctor_set(v___x_1285_, 0, v___x_1317_);
v___x_1323_ = v___x_1285_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
}
else
{
lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v_env_1281_);
v_fst_1328_ = lean_ctor_get(v_snd_1287_, 0);
v_snd_1329_ = lean_ctor_get(v_snd_1287_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_snd_1287_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1331_ = v_snd_1287_;
v_isShared_1332_ = v_isSharedCheck_1344_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_snd_1329_);
lean_inc(v_fst_1328_);
lean_dec(v_snd_1287_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1344_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
lean_inc(v_fst_1328_);
lean_inc(v_snd_1329_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_snd_1329_);
lean_ctor_set(v___x_1333_, 1, v_fst_1328_);
v___x_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
if (v_isShared_1332_ == 0)
{
v___x_1336_ = v___x_1331_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_fst_1328_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_snd_1329_);
v___x_1336_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1336_);
v___x_1338_ = v___x_1290_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_fst_1288_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1338_);
lean_ctor_set(v___x_1285_, 0, v___x_1334_);
v___x_1340_ = v___x_1285_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
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
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1352_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__2));
v___x_1353_ = lean_unsigned_to_nat(2u);
v___x_1354_ = lean_unsigned_to_nat(250u);
v___x_1355_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__1));
v___x_1356_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__0));
v___x_1357_ = l_mkPanicMessageWithDecl(v___x_1356_, v___x_1355_, v___x_1354_, v___x_1353_, v___x_1352_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(lean_object* v_env_1358_, lean_object* v_deconstructQuantifier_x3f_1359_, lean_object* v_stx_1360_){
_start:
{
lean_object* v_deconstructQuantifier_x3f_1361_; lean_object* v_quantifiers_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_fst_1368_; 
v_deconstructQuantifier_x3f_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_deconstructQuantifier_x3f_1361_, 0, v_deconstructQuantifier_x3f_1359_);
v_quantifiers_1362_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__0));
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_stx_1360_);
lean_ctor_set(v___x_1364_, 1, v_quantifiers_1362_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_deconstructQuantifier_x3f_1361_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1363_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1358_, v___x_1366_);
v_fst_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_fst_1368_);
lean_dec_ref(v___x_1367_);
if (lean_obj_tag(v_fst_1368_) == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain___closed__3);
v___x_1370_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__1(v___x_1369_);
return v___x_1370_;
}
else
{
lean_object* v_val_1371_; 
v_val_1371_ = lean_ctor_get(v_fst_1368_, 0);
lean_inc(v_val_1371_);
lean_dec_ref_known(v_fst_1368_, 1);
return v_val_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0(lean_object* v_env_1372_, lean_object* v_inst_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain_spec__0___redArg(v_env_1372_, v_a_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(lean_object* v_x_1376_, lean_object* v_x_1377_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
if (lean_obj_tag(v_x_1377_) == 0)
{
uint8_t v___x_1378_; 
v___x_1378_ = 1;
return v___x_1378_;
}
else
{
uint8_t v___x_1379_; 
v___x_1379_ = 0;
return v___x_1379_;
}
}
else
{
if (lean_obj_tag(v_x_1377_) == 0)
{
uint8_t v___x_1380_; 
v___x_1380_ = 0;
return v___x_1380_;
}
else
{
lean_object* v_val_1381_; lean_object* v_val_1382_; uint8_t v___x_1383_; 
v_val_1381_ = lean_ctor_get(v_x_1376_, 0);
v_val_1382_ = lean_ctor_get(v_x_1377_, 0);
v___x_1383_ = l_Lean_Fmt_instBEqInfixOperationPrecs_beq(v_val_1381_, v_val_1382_);
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1___boxed(lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_x_1384_, v_x_1385_);
lean_dec(v_x_1385_);
lean_dec(v_x_1384_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(lean_object* v_a_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
uint8_t v___x_1390_; 
v___x_1390_ = 0;
return v___x_1390_;
}
else
{
lean_object* v_key_1391_; lean_object* v_tail_1392_; uint8_t v___x_1393_; 
v_key_1391_ = lean_ctor_get(v_x_1389_, 0);
v_tail_1392_ = lean_ctor_get(v_x_1389_, 2);
v___x_1393_ = lean_name_eq(v_key_1391_, v_a_1388_);
if (v___x_1393_ == 0)
{
v_x_1389_ = v_tail_1392_;
goto _start;
}
else
{
return v___x_1393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg___boxed(lean_object* v_a_1395_, lean_object* v_x_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1395_, v_x_1396_);
lean_dec(v_x_1396_);
lean_dec(v_a_1395_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(lean_object* v_m_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_buckets_1401_; lean_object* v___x_1402_; uint64_t v___y_1404_; 
v_buckets_1401_ = lean_ctor_get(v_m_1399_, 1);
v___x_1402_ = lean_array_get_size(v_buckets_1401_);
if (lean_obj_tag(v_a_1400_) == 0)
{
uint64_t v___x_1418_; 
v___x_1418_ = 1723ULL;
v___y_1404_ = v___x_1418_;
goto v___jp_1403_;
}
else
{
uint64_t v_hash_1419_; 
v_hash_1419_ = lean_ctor_get_uint64(v_a_1400_, sizeof(void*)*2);
v___y_1404_ = v_hash_1419_;
goto v___jp_1403_;
}
v___jp_1403_:
{
uint64_t v___x_1405_; uint64_t v___x_1406_; uint64_t v_fold_1407_; uint64_t v___x_1408_; uint64_t v___x_1409_; uint64_t v___x_1410_; size_t v___x_1411_; size_t v___x_1412_; size_t v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1405_ = 32ULL;
v___x_1406_ = lean_uint64_shift_right(v___y_1404_, v___x_1405_);
v_fold_1407_ = lean_uint64_xor(v___y_1404_, v___x_1406_);
v___x_1408_ = 16ULL;
v___x_1409_ = lean_uint64_shift_right(v_fold_1407_, v___x_1408_);
v___x_1410_ = lean_uint64_xor(v_fold_1407_, v___x_1409_);
v___x_1411_ = lean_uint64_to_usize(v___x_1410_);
v___x_1412_ = lean_usize_of_nat(v___x_1402_);
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_sub(v___x_1412_, v___x_1413_);
v___x_1415_ = lean_usize_land(v___x_1411_, v___x_1414_);
v___x_1416_ = lean_array_uget_borrowed(v_buckets_1401_, v___x_1415_);
v___x_1417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1400_, v___x_1416_);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg___boxed(lean_object* v_m_1420_, lean_object* v_a_1421_){
_start:
{
uint8_t v_res_1422_; lean_object* v_r_1423_; 
v_res_1422_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_m_1420_);
v_r_1423_ = lean_box(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(lean_object* v_env_1424_, lean_object* v_opts_1425_, lean_object* v_op_1426_, lean_object* v_stx_1427_){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1444_ = l_Lean_Syntax_getNumArgs(v_stx_1427_);
v___x_1445_ = lean_unsigned_to_nat(3u);
v___x_1446_ = lean_nat_dec_eq(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_env_1424_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_mk_empty_array_with_capacity(v___x_1447_);
v___x_1449_ = lean_array_push(v___x_1448_, v_stx_1427_);
return v___x_1449_;
}
else
{
lean_object* v_precs_x3f_1450_; lean_object* v_extendedChainKinds_1451_; lean_object* v___x_1452_; 
v_precs_x3f_1450_ = lean_ctor_get(v_op_1426_, 0);
v_extendedChainKinds_1451_ = lean_ctor_get(v_op_1426_, 1);
lean_inc(v_stx_1427_);
v___x_1452_ = l_Lean_Syntax_getKind(v_stx_1427_);
if (lean_obj_tag(v_precs_x3f_1450_) == 0)
{
goto v___jp_1453_;
}
else
{
lean_object* v_op_x27_x3f_1458_; 
lean_inc(v___x_1452_);
lean_inc_ref(v_env_1424_);
v_op_x27_x3f_1458_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_1424_, v_opts_1425_, v___x_1452_);
if (lean_obj_tag(v_op_x27_x3f_1458_) == 0)
{
goto v___jp_1453_;
}
else
{
lean_object* v_val_1459_; lean_object* v_precs_x3f_1460_; uint8_t v___x_1461_; 
v_val_1459_ = lean_ctor_get(v_op_x27_x3f_1458_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v_op_x27_x3f_1458_, 1);
v_precs_x3f_1460_ = lean_ctor_get(v_val_1459_, 0);
lean_inc(v_precs_x3f_1460_);
lean_dec(v_val_1459_);
v___x_1461_ = l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__1(v_precs_x3f_1460_, v_precs_x3f_1450_);
lean_dec(v_precs_x3f_1460_);
if (v___x_1461_ == 0)
{
goto v___jp_1453_;
}
else
{
lean_dec(v___x_1452_);
goto v___jp_1428_;
}
}
}
v___jp_1453_:
{
uint8_t v___x_1454_; 
v___x_1454_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_extendedChainKinds_1451_, v___x_1452_);
lean_dec(v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v_env_1424_);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_mk_empty_array_with_capacity(v___x_1455_);
v___x_1457_ = lean_array_push(v___x_1456_, v_stx_1427_);
return v___x_1457_;
}
else
{
goto v___jp_1428_;
}
}
}
v___jp_1428_:
{
lean_object* v___x_1429_; lean_object* v_op_1430_; uint8_t v___x_1431_; 
v___x_1429_ = lean_unsigned_to_nat(1u);
v_op_1430_ = l_Lean_Syntax_getArg(v_stx_1427_, v___x_1429_);
v___x_1431_ = l_Lean_Syntax_isAtom(v_op_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_op_1430_);
lean_dec_ref(v_env_1424_);
v___x_1432_ = lean_mk_empty_array_with_capacity(v___x_1429_);
v___x_1433_ = lean_array_push(v___x_1432_, v_stx_1427_);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v_left_1435_; lean_object* v___x_1436_; lean_object* v_right_1437_; lean_object* v_leftChain_1438_; lean_object* v_rightChain_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v_left_1435_ = l_Lean_Syntax_getArg(v_stx_1427_, v___x_1434_);
v___x_1436_ = lean_unsigned_to_nat(2u);
v_right_1437_ = l_Lean_Syntax_getArg(v_stx_1427_, v___x_1436_);
lean_dec(v_stx_1427_);
lean_inc_ref(v_env_1424_);
v_leftChain_1438_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1424_, v_opts_1425_, v_op_1426_, v_left_1435_);
v_rightChain_1439_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1424_, v_opts_1425_, v_op_1426_, v_right_1437_);
v___x_1440_ = lean_mk_empty_array_with_capacity(v___x_1429_);
v___x_1441_ = lean_array_push(v___x_1440_, v_op_1430_);
v___x_1442_ = l_Array_append___redArg(v_leftChain_1438_, v___x_1441_);
lean_dec_ref(v___x_1441_);
v___x_1443_ = l_Array_append___redArg(v___x_1442_, v_rightChain_1439_);
lean_dec_ref(v_rightChain_1439_);
return v___x_1443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain___boxed(lean_object* v_env_1462_, lean_object* v_opts_1463_, lean_object* v_op_1464_, lean_object* v_stx_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_1462_, v_opts_1463_, v_op_1464_, v_stx_1465_);
lean_dec_ref(v_op_1464_);
lean_dec_ref(v_opts_1463_);
return v_res_1466_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_a_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___redArg(v_m_1468_, v_a_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0___boxed(lean_object* v_00_u03b2_1471_, lean_object* v_m_1472_, lean_object* v_a_1473_){
_start:
{
uint8_t v_res_1474_; lean_object* v_r_1475_; 
v_res_1474_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0(v_00_u03b2_1471_, v_m_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_m_1472_);
v_r_1475_ = lean_box(v_res_1474_);
return v_r_1475_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(lean_object* v_00_u03b2_1476_, lean_object* v_a_1477_, lean_object* v_x_1478_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_1477_, v_x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1480_, lean_object* v_a_1481_, lean_object* v_x_1482_){
_start:
{
uint8_t v_res_1483_; lean_object* v_r_1484_; 
v_res_1483_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0(v_00_u03b2_1480_, v_a_1481_, v_x_1482_);
lean_dec(v_x_1482_);
lean_dec(v_a_1481_);
v_r_1484_ = lean_box(v_res_1483_);
return v_r_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(lean_object* v___x_1485_, lean_object* v___x_1486_, lean_object* v___x_1487_, lean_object* v_a_1488_, lean_object* v_b_1489_){
_start:
{
lean_object* v_it_1491_; lean_object* v_startInclusive_1492_; lean_object* v_endExclusive_1493_; 
if (lean_obj_tag(v_a_1488_) == 0)
{
lean_object* v_currPos_1499_; lean_object* v_searcher_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1606_; 
v_currPos_1499_ = lean_ctor_get(v_a_1488_, 0);
v_searcher_1500_ = lean_ctor_get(v_a_1488_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_a_1488_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1502_ = v_a_1488_;
v_isShared_1503_ = v_isSharedCheck_1606_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_searcher_1500_);
lean_inc(v_currPos_1499_);
lean_dec(v_a_1488_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1606_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_it_1505_; lean_object* v_it_1511_; lean_object* v_startPos_1512_; lean_object* v_endPos_1513_; 
switch(lean_obj_tag(v_searcher_1500_))
{
case 0:
{
lean_object* v_pos_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1538_; 
lean_del_object(v___x_1502_);
v_pos_1526_ = lean_ctor_get(v_searcher_1500_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_searcher_1500_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1528_ = v_searcher_1500_;
v_isShared_1529_ = v_isSharedCheck_1538_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_pos_1526_);
lean_dec(v_searcher_1500_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1538_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_startInclusive_1530_; lean_object* v_endExclusive_1531_; lean_object* v___x_1532_; uint8_t v_decide_1533_; 
v_startInclusive_1530_ = lean_ctor_get(v___x_1486_, 1);
v_endExclusive_1531_ = lean_ctor_get(v___x_1486_, 2);
v___x_1532_ = lean_nat_sub(v_endExclusive_1531_, v_startInclusive_1530_);
v_decide_1533_ = lean_nat_dec_eq(v_pos_1526_, v___x_1532_);
lean_dec(v___x_1532_);
if (v_decide_1533_ == 0)
{
lean_object* v___x_1535_; 
lean_inc(v_pos_1526_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 1);
v___x_1535_ = v___x_1528_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_pos_1526_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_inc(v_pos_1526_);
v_it_1511_ = v___x_1535_;
v_startPos_1512_ = v_pos_1526_;
v_endPos_1513_ = v_pos_1526_;
goto v___jp_1510_;
}
}
else
{
lean_object* v___x_1537_; 
lean_del_object(v___x_1528_);
v___x_1537_ = lean_box(3);
lean_inc(v_pos_1526_);
v_it_1511_ = v___x_1537_;
v_startPos_1512_ = v_pos_1526_;
v_endPos_1513_ = v_pos_1526_;
goto v___jp_1510_;
}
}
}
case 1:
{
lean_object* v_pos_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
v_pos_1539_ = lean_ctor_get(v_searcher_1500_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_searcher_1500_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1541_ = v_searcher_1500_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_pos_1539_);
lean_dec(v_searcher_1500_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = lean_string_utf8_next_fast(v___x_1485_, v_pos_1539_);
lean_dec(v_pos_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set_tag(v___x_1541_, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
v_it_1505_ = v___x_1545_;
goto v___jp_1504_;
}
}
}
case 2:
{
lean_object* v_needle_1548_; lean_object* v_table_1549_; lean_object* v_stackPos_1550_; lean_object* v_needlePos_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1605_; 
v_needle_1548_ = lean_ctor_get(v_searcher_1500_, 0);
v_table_1549_ = lean_ctor_get(v_searcher_1500_, 1);
v_stackPos_1550_ = lean_ctor_get(v_searcher_1500_, 2);
v_needlePos_1551_ = lean_ctor_get(v_searcher_1500_, 3);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_searcher_1500_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1553_ = v_searcher_1500_;
v_isShared_1554_ = v_isSharedCheck_1605_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_needlePos_1551_);
lean_inc(v_stackPos_1550_);
lean_inc(v_table_1549_);
lean_inc(v_needle_1548_);
lean_dec(v_searcher_1500_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1605_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_str_1555_; lean_object* v_startInclusive_1556_; lean_object* v_endExclusive_1557_; lean_object* v_basePos_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v_str_1555_ = lean_ctor_get(v_needle_1548_, 0);
v_startInclusive_1556_ = lean_ctor_get(v_needle_1548_, 1);
v_endExclusive_1557_ = lean_ctor_get(v_needle_1548_, 2);
v_basePos_1558_ = lean_nat_sub(v_stackPos_1550_, v_needlePos_1551_);
v___x_1559_ = lean_nat_sub(v_endExclusive_1557_, v_startInclusive_1556_);
v___x_1560_ = lean_nat_add(v_basePos_1558_, v___x_1559_);
v___x_1561_ = lean_nat_dec_le(v___x_1560_, v___x_1487_);
lean_dec(v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
lean_dec(v___x_1559_);
lean_del_object(v___x_1553_);
lean_dec(v_needlePos_1551_);
lean_dec(v_stackPos_1550_);
lean_dec_ref(v_table_1549_);
lean_dec_ref(v_needle_1548_);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = lean_nat_add(v_basePos_1558_, v___x_1562_);
lean_dec(v_basePos_1558_);
v___x_1564_ = lean_nat_dec_le(v___x_1563_, v___x_1487_);
lean_dec(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_del_object(v___x_1502_);
goto v___jp_1524_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_box(3);
v_it_1505_ = v___x_1565_;
goto v___jp_1504_;
}
}
else
{
uint8_t v_stackByte_1566_; lean_object* v___x_1567_; uint8_t v_patByte_1568_; uint8_t v___x_1569_; 
lean_dec(v_basePos_1558_);
lean_inc(v_stackPos_1550_);
v_stackByte_1566_ = lean_string_get_byte_fast(v___x_1485_, v_stackPos_1550_);
v___x_1567_ = lean_nat_add(v_startInclusive_1556_, v_needlePos_1551_);
v_patByte_1568_ = lean_string_get_byte_fast(v_str_1555_, v___x_1567_);
v___x_1569_ = lean_uint8_dec_eq(v_stackByte_1566_, v_patByte_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; uint8_t v_decide_1571_; 
lean_dec(v___x_1559_);
v___x_1570_ = lean_unsigned_to_nat(0u);
v_decide_1571_ = lean_nat_dec_eq(v_needlePos_1551_, v___x_1570_);
if (v_decide_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_newNeedlePos_1574_; uint8_t v___x_1575_; 
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_sub(v_needlePos_1551_, v___x_1572_);
lean_dec(v_needlePos_1551_);
v_newNeedlePos_1574_ = lean_array_fget_borrowed(v_table_1549_, v___x_1573_);
lean_dec(v___x_1573_);
v___x_1575_ = lean_nat_dec_eq(v_newNeedlePos_1574_, v___x_1570_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1577_; 
lean_inc(v_newNeedlePos_1574_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v_newNeedlePos_1574_);
v___x_1577_ = v___x_1553_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_needle_1548_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_table_1549_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_stackPos_1550_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_newNeedlePos_1574_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
v_it_1505_ = v___x_1577_;
goto v___jp_1504_;
}
}
else
{
lean_object* v_nextStackPos_1579_; lean_object* v___x_1581_; 
v_nextStackPos_1579_ = l_String_Slice_posGE___redArg(v___x_1486_, v_stackPos_1550_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v___x_1570_);
lean_ctor_set(v___x_1553_, 2, v_nextStackPos_1579_);
v___x_1581_ = v___x_1553_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_needle_1548_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_table_1549_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_nextStackPos_1579_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v___x_1570_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
v_it_1505_ = v___x_1581_;
goto v___jp_1504_;
}
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_nextStackPos_1585_; lean_object* v___x_1587_; 
lean_dec(v_needlePos_1551_);
v___x_1583_ = lean_unsigned_to_nat(1u);
v___x_1584_ = lean_nat_add(v_stackPos_1550_, v___x_1583_);
lean_dec(v_stackPos_1550_);
v_nextStackPos_1585_ = l_String_Slice_posGE___redArg(v___x_1486_, v___x_1584_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v___x_1570_);
lean_ctor_set(v___x_1553_, 2, v_nextStackPos_1585_);
v___x_1587_ = v___x_1553_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_needle_1548_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_table_1549_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_nextStackPos_1585_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v___x_1570_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v_it_1505_ = v___x_1587_;
goto v___jp_1504_;
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v_nextStackPos_1590_; lean_object* v_nextNeedlePos_1591_; uint8_t v_decide_1592_; 
lean_del_object(v___x_1502_);
v___x_1589_ = lean_unsigned_to_nat(1u);
v_nextStackPos_1590_ = lean_nat_add(v_stackPos_1550_, v___x_1589_);
lean_dec(v_stackPos_1550_);
v_nextNeedlePos_1591_ = lean_nat_add(v_needlePos_1551_, v___x_1589_);
lean_dec(v_needlePos_1551_);
v_decide_1592_ = lean_nat_dec_eq(v_nextNeedlePos_1591_, v___x_1559_);
lean_dec(v___x_1559_);
if (v_decide_1592_ == 0)
{
lean_object* v___x_1594_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v_nextNeedlePos_1591_);
lean_ctor_set(v___x_1553_, 2, v_nextStackPos_1590_);
v___x_1594_ = v___x_1553_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_needle_1548_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_table_1549_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_nextStackPos_1590_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_nextNeedlePos_1591_);
v___x_1594_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_currPos_1499_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v_a_1488_ = v___x_1595_;
goto _start;
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1598_ = lean_nat_sub(v_nextStackPos_1590_, v_nextNeedlePos_1591_);
lean_dec(v_nextNeedlePos_1591_);
v___x_1599_ = l_String_Slice_pos_x21(v___x_1486_, v___x_1598_);
lean_dec(v___x_1598_);
v___x_1600_ = l_String_Slice_pos_x21(v___x_1486_, v_nextStackPos_1590_);
v___x_1601_ = lean_unsigned_to_nat(0u);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 3, v___x_1601_);
lean_ctor_set(v___x_1553_, 2, v_nextStackPos_1590_);
v___x_1603_ = v___x_1553_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_needle_1548_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_table_1549_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_nextStackPos_1590_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
v_it_1511_ = v___x_1603_;
v_startPos_1512_ = v___x_1599_;
v_endPos_1513_ = v___x_1600_;
goto v___jp_1510_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_1502_);
goto v___jp_1524_;
}
}
v___jp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v_it_1505_);
v___x_1507_ = v___x_1502_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_currPos_1499_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_it_1505_);
v___x_1507_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
v_a_1488_ = v___x_1507_;
goto _start;
}
}
v___jp_1510_:
{
lean_object* v_slice_1514_; lean_object* v_startInclusive_1515_; lean_object* v_endExclusive_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_slice_1514_ = l_String_Slice_subslice_x21(v___x_1486_, v_currPos_1499_, v_startPos_1512_);
v_startInclusive_1515_ = lean_ctor_get(v_slice_1514_, 0);
v_endExclusive_1516_ = lean_ctor_get(v_slice_1514_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_slice_1514_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v_slice_1514_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_endExclusive_1516_);
lean_inc(v_startInclusive_1515_);
lean_dec(v_slice_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_nextIt_1521_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 1, v_it_1511_);
lean_ctor_set(v___x_1518_, 0, v_endPos_1513_);
v_nextIt_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_endPos_1513_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_it_1511_);
v_nextIt_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
v_it_1491_ = v_nextIt_1521_;
v_startInclusive_1492_ = v_startInclusive_1515_;
v_endExclusive_1493_ = v_endExclusive_1516_;
goto v___jp_1490_;
}
}
}
v___jp_1524_:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_box(1);
lean_inc(v___x_1487_);
v_it_1491_ = v___x_1525_;
v_startInclusive_1492_ = v_currPos_1499_;
v_endExclusive_1493_ = v___x_1487_;
goto v___jp_1490_;
}
}
}
else
{
lean_dec(v___x_1487_);
lean_dec_ref(v___x_1485_);
return v_b_1489_;
}
v___jp_1490_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_inc_ref(v___x_1485_);
v___x_1494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1485_);
lean_ctor_set(v___x_1494_, 1, v_startInclusive_1492_);
lean_ctor_set(v___x_1494_, 2, v_endExclusive_1493_);
v___x_1495_ = l_String_Slice_toString(v___x_1494_);
lean_dec_ref_known(v___x_1494_, 3);
v___x_1496_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_1495_);
v___x_1497_ = lean_array_push(v_b_1489_, v___x_1496_);
v_a_1488_ = v_it_1491_;
v_b_1489_ = v___x_1497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg___boxed(lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_a_1610_, lean_object* v_b_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1607_, v___x_1608_, v___x_1609_, v_a_1610_, v_b_1611_);
lean_dec_ref(v___x_1608_);
return v_res_1612_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtRawAsInSource___closed__3(void){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource(uint8_t v_isFallback_1619_, lean_object* v_stx_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = 0;
v___x_1624_ = l_Lean_Syntax_getPos_x3f(v_stx_1620_, v___x_1623_);
if (lean_obj_tag(v___x_1624_) == 1)
{
lean_object* v_val_1625_; lean_object* v___x_1626_; 
v_val_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1620_, v___x_1623_);
if (lean_obj_tag(v___x_1626_) == 1)
{
lean_object* v_text_1627_; lean_object* v_val_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1678_; 
v_text_1627_ = lean_ctor_get(v_a_1621_, 1);
v_val_1628_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1630_ = v___x_1626_;
v_isShared_1631_ = v_isSharedCheck_1678_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_val_1628_);
lean_dec(v___x_1626_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1678_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_source_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_source_1632_ = lean_ctor_get(v_text_1627_, 0);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = lean_string_utf8_byte_size(v_source_1632_);
lean_inc_ref(v_source_1632_);
v___x_1635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1635_, 0, v_source_1632_);
lean_ctor_set(v___x_1635_, 1, v___x_1633_);
lean_ctor_set(v___x_1635_, 2, v___x_1634_);
v___x_1636_ = l_String_Slice_pos_x3f(v___x_1635_, v_val_1625_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_dec_ref_known(v___x_1635_, 3);
lean_dec(v_val_1628_);
v___x_1637_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1638_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v_stx_1620_);
lean_ctor_set(v___x_1639_, 1, v___x_1637_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 2);
lean_ctor_set(v___x_1630_, 0, v___x_1639_);
v___x_1641_ = v___x_1630_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_a_1622_);
return v___x_1642_;
}
}
else
{
lean_object* v_val_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1630_);
v_val_1644_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1646_ = v___x_1636_;
v_isShared_1647_ = v_isSharedCheck_1677_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_val_1644_);
lean_dec(v___x_1636_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1677_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_String_Slice_pos_x3f(v___x_1635_, v_val_1628_);
lean_dec_ref_known(v___x_1635_, 3);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_dec(v_val_1644_);
v___x_1649_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__0));
v___x_1650_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__1));
v___x_1651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1651_, 0, v_stx_1620_);
lean_ctor_set(v___x_1651_, 1, v___x_1649_);
lean_ctor_set(v___x_1651_, 2, v___x_1650_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set_tag(v___x_1646_, 2);
lean_ctor_set(v___x_1646_, 0, v___x_1651_);
v___x_1653_ = v___x_1646_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
lean_ctor_set(v___x_1654_, 1, v_a_1622_);
return v___x_1654_;
}
}
else
{
lean_object* v_val_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_del_object(v___x_1646_);
v_val_1656_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1657_ = lean_string_utf8_extract_fast(v_source_1632_, v_val_1644_, v_val_1656_);
lean_dec(v_val_1656_);
lean_dec(v_val_1644_);
v___x_1658_ = lean_string_utf8_byte_size(v___x_1657_);
lean_inc_ref(v___x_1657_);
v___x_1659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1633_);
lean_ctor_set(v___x_1659_, 2, v___x_1658_);
v___x_1660_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1661_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1662_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1657_, v___x_1659_, v___x_1658_, v___x_1660_, v___x_1661_);
lean_dec_ref_known(v___x_1659_, 3);
v___x_1663_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1664_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1663_, v___x_1662_);
v___x_1665_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1623_, v___x_1664_);
v___x_1666_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___x_1665_, v_stx_1620_, v_a_1622_);
lean_dec(v_stx_1620_);
if (lean_obj_tag(v___x_1666_) == 0)
{
if (v_isFallback_1619_ == 0)
{
return v___x_1666_;
}
else
{
lean_object* v_a_1667_; lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_a_1668_ = lean_ctor_get(v___x_1666_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1670_ = v___x_1666_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_1667_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_a_1668_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
return v___x_1666_;
}
}
}
}
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___x_1626_);
lean_dec(v_val_1625_);
v___x_1679_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1680_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1679_, v_stx_1620_, v_a_1622_);
lean_dec(v_stx_1620_);
return v___x_1680_;
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec(v___x_1624_);
v___x_1681_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_1682_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_1681_, v_stx_1620_, v_a_1622_);
lean_dec(v_stx_1620_);
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRawAsInSource___boxed(lean_object* v_isFallback_1683_, lean_object* v_stx_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v_isFallback_boxed_1687_; lean_object* v_res_1688_; 
v_isFallback_boxed_1687_ = lean_unbox(v_isFallback_1683_);
v_res_1688_ = l_Lean_Fmt_fmtRawAsInSource(v_isFallback_boxed_1687_, v_stx_1684_, v_a_1685_, v_a_1686_);
lean_dec_ref(v_a_1685_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(lean_object* v___x_1689_, lean_object* v___x_1690_, lean_object* v___x_1691_, lean_object* v_inst_1692_, lean_object* v_R_1693_, lean_object* v_a_1694_, lean_object* v_b_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_1689_, v___x_1690_, v___x_1691_, v_a_1694_, v_b_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___boxed(lean_object* v___x_1697_, lean_object* v___x_1698_, lean_object* v___x_1699_, lean_object* v_inst_1700_, lean_object* v_R_1701_, lean_object* v_a_1702_, lean_object* v_b_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0(v___x_1697_, v___x_1698_, v___x_1699_, v_inst_1700_, v_R_1701_, v_a_1702_, v_b_1703_);
lean_dec_ref(v___x_1698_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_bs_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1708_ == 0)
{
return v_bs_1707_;
}
else
{
lean_object* v_v_1709_; lean_object* v___x_1710_; lean_object* v_bs_x27_1711_; lean_object* v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v_v_1709_ = lean_array_uget(v_bs_1707_, v_i_1706_);
v___x_1710_ = lean_unsigned_to_nat(0u);
v_bs_x27_1711_ = lean_array_uset(v_bs_1707_, v_i_1706_, v___x_1710_);
v___x_1712_ = l_Lean_Fmt_Doc_text___override___redArg(v_v_1709_);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1706_, v___x_1713_);
v___x_1715_ = lean_array_uset(v_bs_x27_1711_, v_i_1706_, v___x_1712_);
v_i_1706_ = v___x_1714_;
v_bs_1707_ = v___x_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2___boxed(lean_object* v_sz_1717_, lean_object* v_i_1718_, lean_object* v_bs_1719_){
_start:
{
size_t v_sz_boxed_1720_; size_t v_i_boxed_1721_; lean_object* v_res_1722_; 
v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1717_);
lean_dec(v_sz_1717_);
v_i_boxed_1721_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_boxed_1720_, v_i_boxed_1721_, v_bs_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(lean_object* v_ctx_1723_, size_t v_sz_1724_, size_t v_i_1725_, lean_object* v_bs_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
if (v___x_1727_ == 0)
{
lean_dec_ref(v_ctx_1723_);
return v_bs_1726_;
}
else
{
lean_object* v_v_1728_; lean_object* v_str_1729_; lean_object* v_startPos_1730_; lean_object* v_stopPos_1731_; lean_object* v_anchorColumnPos_1732_; lean_object* v___x_1733_; lean_object* v_bs_x27_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; size_t v___x_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
v_v_1728_ = lean_array_uget_borrowed(v_bs_1726_, v_i_1725_);
v_str_1729_ = lean_ctor_get(v_v_1728_, 0);
lean_inc_ref(v_str_1729_);
v_startPos_1730_ = lean_ctor_get(v_v_1728_, 1);
lean_inc(v_startPos_1730_);
v_stopPos_1731_ = lean_ctor_get(v_v_1728_, 2);
lean_inc(v_stopPos_1731_);
v_anchorColumnPos_1732_ = lean_ctor_get(v_ctx_1723_, 0);
v___x_1733_ = lean_unsigned_to_nat(0u);
v_bs_x27_1734_ = lean_array_uset(v_bs_1726_, v_i_1725_, v___x_1733_);
v___x_1735_ = lean_string_utf8_extract(v_str_1729_, v_startPos_1730_, v_stopPos_1731_);
lean_dec(v_stopPos_1731_);
lean_dec(v_startPos_1730_);
lean_dec_ref(v_str_1729_);
lean_inc(v_anchorColumnPos_1732_);
v___x_1736_ = l___private_Lean_Fmt_FmtM_Basic_0__String_deindent(v___x_1735_, v_anchorColumnPos_1732_);
v___x_1737_ = ((size_t)1ULL);
v___x_1738_ = lean_usize_add(v_i_1725_, v___x_1737_);
v___x_1739_ = lean_array_uset(v_bs_x27_1734_, v_i_1725_, v___x_1736_);
v_i_1725_ = v___x_1738_;
v_bs_1726_ = v___x_1739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1___boxed(lean_object* v_ctx_1741_, lean_object* v_sz_1742_, lean_object* v_i_1743_, lean_object* v_bs_1744_){
_start:
{
size_t v_sz_boxed_1745_; size_t v_i_boxed_1746_; lean_object* v_res_1747_; 
v_sz_boxed_1745_ = lean_unbox_usize(v_sz_1742_);
lean_dec(v_sz_1742_);
v_i_boxed_1746_ = lean_unbox_usize(v_i_1743_);
lean_dec(v_i_1743_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1741_, v_sz_boxed_1745_, v_i_boxed_1746_, v_bs_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(lean_object* v_a_1748_, lean_object* v_b_1749_){
_start:
{
lean_object* v_array_1750_; lean_object* v_start_1751_; lean_object* v_stop_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1765_; 
v_array_1750_ = lean_ctor_get(v_a_1748_, 0);
v_start_1751_ = lean_ctor_get(v_a_1748_, 1);
v_stop_1752_ = lean_ctor_get(v_a_1748_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_a_1748_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1754_ = v_a_1748_;
v_isShared_1755_ = v_isSharedCheck_1765_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_stop_1752_);
lean_inc(v_start_1751_);
lean_inc(v_array_1750_);
lean_dec(v_a_1748_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1765_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_nat_dec_lt(v_start_1751_, v_stop_1752_);
if (v___x_1756_ == 0)
{
lean_del_object(v___x_1754_);
lean_dec(v_stop_1752_);
lean_dec(v_start_1751_);
lean_dec_ref(v_array_1750_);
return v_b_1749_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; 
v___x_1757_ = lean_unsigned_to_nat(1u);
v___x_1758_ = lean_nat_add(v_start_1751_, v___x_1757_);
lean_inc_ref(v_array_1750_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v___x_1758_);
v___x_1760_ = v___x_1754_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_array_1750_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1758_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_stop_1752_);
v___x_1760_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_array_fget(v_array_1750_, v_start_1751_);
lean_dec(v_start_1751_);
lean_dec_ref(v_array_1750_);
v___x_1762_ = lean_array_push(v_b_1749_, v___x_1761_);
v_a_1748_ = v___x_1760_;
v_b_1749_ = v___x_1762_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(lean_object* v_ctx_1770_, lean_object* v_trailing_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_lastTokenTailPos_1773_; lean_object* v_startPos_1774_; uint8_t v___x_1775_; 
v_lastTokenTailPos_1773_ = lean_ctor_get(v_ctx_1770_, 2);
v_startPos_1774_ = lean_ctor_get(v_trailing_1771_, 1);
v___x_1775_ = lean_nat_dec_le(v_lastTokenTailPos_1773_, v_startPos_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v_lines_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_str_1782_; lean_object* v_startPos_1783_; lean_object* v_stopPos_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; size_t v_sz_1793_; size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v_newLines_1796_; size_t v_sz_1797_; lean_object* v_formatted_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1776_ = l_instInhabitedRaw__1;
v___x_1777_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_trailing_1771_);
v___x_1778_ = l_Substring_Raw_splitOn(v_trailing_1771_, v___x_1777_);
v_lines_1779_ = lean_array_mk(v___x_1778_);
v___x_1780_ = lean_unsigned_to_nat(0u);
v___x_1781_ = lean_array_get(v___x_1776_, v_lines_1779_, v___x_1780_);
v_str_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc_ref(v_str_1782_);
v_startPos_1783_ = lean_ctor_get(v___x_1781_, 1);
lean_inc(v_startPos_1783_);
v_stopPos_1784_ = lean_ctor_get(v___x_1781_, 2);
lean_inc(v_stopPos_1784_);
lean_dec(v___x_1781_);
v___x_1785_ = lean_string_utf8_extract(v_str_1782_, v_startPos_1783_, v_stopPos_1784_);
lean_dec(v_stopPos_1784_);
lean_dec(v_startPos_1783_);
lean_dec_ref(v_str_1782_);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = lean_mk_empty_array_with_capacity(v___x_1786_);
lean_inc_ref(v___x_1787_);
v___x_1788_ = lean_array_push(v___x_1787_, v___x_1785_);
v___x_1789_ = lean_array_get_size(v_lines_1779_);
v___x_1790_ = l_Array_toSubarray___redArg(v_lines_1779_, v___x_1786_, v___x_1789_);
v___x_1791_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__0));
v___x_1792_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v___x_1790_, v___x_1791_);
v_sz_1793_ = lean_array_size(v___x_1792_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1770_, v_sz_1793_, v___x_1794_, v___x_1792_);
v_newLines_1796_ = l_Array_append___redArg(v___x_1788_, v___x_1795_);
lean_dec_ref(v___x_1795_);
v_sz_1797_ = lean_array_size(v_newLines_1796_);
v_formatted_1798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1797_, v___x_1794_, v_newLines_1796_);
v___x_1799_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1800_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1799_, v_formatted_1798_);
v___x_1801_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1800_);
v___x_1802_ = l_Lean_Syntax_Range_ofSubstring(v_trailing_1771_);
lean_dec_ref(v_trailing_1771_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1801_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_array_push(v___x_1787_, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v_a_1772_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec_ref(v_trailing_1771_);
lean_dec_ref(v_ctx_1770_);
v___x_1807_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v_a_1772_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(lean_object* v_ctx_1809_, lean_object* v___trailingTk_1810_, lean_object* v_trailing_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg(v_ctx_1809_, v_trailing_1811_, v_a_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed(lean_object* v_ctx_1815_, lean_object* v___trailingTk_1816_, lean_object* v_trailing_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing(v_ctx_1815_, v___trailingTk_1816_, v_trailing_1817_, v_a_1818_, v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v___trailingTk_1816_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0(lean_object* v_inst_1821_, lean_object* v_R_1822_, lean_object* v_a_1823_, lean_object* v_b_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__0___redArg(v_a_1823_, v_b_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(lean_object* v_ctx_1826_, lean_object* v_leading_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_stopPos_1829_; lean_object* v_firstTokenPos_1830_; uint8_t v___x_1831_; 
v_stopPos_1829_ = lean_ctor_get(v_leading_1827_, 2);
v_firstTokenPos_1830_ = lean_ctor_get(v_ctx_1826_, 1);
v___x_1831_ = lean_nat_dec_le(v_stopPos_1829_, v_firstTokenPos_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_lines_1834_; size_t v_sz_1835_; size_t v___x_1836_; lean_object* v_newLines_1837_; size_t v_sz_1838_; lean_object* v_formatted_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1832_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___redArg___closed__0));
lean_inc_ref(v_leading_1827_);
v___x_1833_ = l_Substring_Raw_splitOn(v_leading_1827_, v___x_1832_);
v_lines_1834_ = lean_array_mk(v___x_1833_);
v_sz_1835_ = lean_array_size(v_lines_1834_);
v___x_1836_ = ((size_t)0ULL);
v_newLines_1837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__1(v_ctx_1826_, v_sz_1835_, v___x_1836_, v_lines_1834_);
v_sz_1838_ = lean_array_size(v_newLines_1837_);
v_formatted_1839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing_spec__2(v_sz_1838_, v___x_1836_, v_newLines_1837_);
v___x_1840_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1841_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1840_, v_formatted_1839_);
v___x_1842_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1841_);
v___x_1843_ = l_Lean_Syntax_Range_ofSubstring(v_leading_1827_);
lean_dec_ref(v_leading_1827_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1842_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = lean_mk_empty_array_with_capacity(v___x_1846_);
v___x_1848_ = lean_array_push(v___x_1847_, v___x_1845_);
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
lean_ctor_set(v___x_1849_, 1, v_a_1828_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_dec_ref(v_leading_1827_);
lean_dec_ref(v_ctx_1826_);
v___x_1850_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___redArg___closed__1));
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v_a_1828_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(lean_object* v_ctx_1852_, lean_object* v___leadingTk_1853_, lean_object* v_leading_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___redArg(v_ctx_1852_, v_leading_1854_, v_a_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed(lean_object* v_ctx_1858_, lean_object* v___leadingTk_1859_, lean_object* v_leading_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading(v_ctx_1858_, v___leadingTk_1859_, v_leading_1860_, v_a_1861_, v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v___leadingTk_1859_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(lean_object* v_stx_1864_, lean_object* v_token_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_inc_ref(v_a_1866_);
v___x_1869_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtLeading___boxed), 5, 1);
lean_closure_set(v___x_1869_, 0, v_a_1866_);
lean_inc(v_stx_1864_);
v___x_1870_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_1864_, v___x_1869_, v_a_1867_, v_a_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v_a_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
v_a_1872_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1870_, 2);
lean_inc_ref(v_a_1866_);
v___x_1873_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtTrailing___boxed), 5, 1);
lean_closure_set(v___x_1873_, 0, v_a_1866_);
lean_inc(v_stx_1864_);
v___x_1874_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_1864_, v___x_1873_, v_a_1867_, v_a_1872_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1937_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_a_1876_ = lean_ctor_get(v___x_1874_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1878_ = v___x_1874_;
v_isShared_1879_ = v_isSharedCheck_1937_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1937_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1909_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_string_utf8_byte_size(v_token_1865_);
lean_inc_ref(v_token_1865_);
v___x_1925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1925_, 0, v_token_1865_);
lean_ctor_set(v___x_1925_, 1, v___x_1923_);
lean_ctor_set(v___x_1925_, 2, v___x_1924_);
v___x_1926_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_1927_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_1928_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_token_1865_, v___x_1925_, v___x_1924_, v___x_1926_, v___x_1927_);
lean_dec_ref_known(v___x_1925_, 3);
v___x_1929_ = lean_array_get_size(v___x_1928_);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_nat_dec_eq(v___x_1929_, v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1932_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_1933_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_1932_, v___x_1928_);
v___x_1934_ = l_Lean_Fmt_Doc_unindented___override___redArg(v___x_1931_, v___x_1933_);
v___y_1909_ = v___x_1934_;
goto v___jp_1908_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_array_get(v___x_1935_, v___x_1928_, v___x_1923_);
lean_dec_ref(v___x_1928_);
v___y_1909_ = v___x_1936_;
goto v___jp_1908_;
}
v___jp_1880_:
{
uint8_t v___x_1883_; 
v___x_1883_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1882_);
if (v___x_1883_ == 0)
{
uint8_t v___x_1884_; 
v___x_1884_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1875_);
if (v___x_1884_ == 0)
{
lean_object* v_doc_1885_; lean_object* v_doc_1886_; uint8_t v___x_1887_; 
v_doc_1885_ = lean_ctor_get(v___y_1882_, 0);
lean_inc(v_doc_1885_);
lean_dec_ref(v___y_1882_);
v_doc_1886_ = lean_ctor_get(v_a_1875_, 0);
lean_inc(v_doc_1886_);
lean_dec(v_a_1875_);
v___x_1887_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1885_);
if (v___x_1887_ == 0)
{
uint8_t v___x_1888_; 
v___x_1888_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1886_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1889_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1885_, v_doc_1886_);
v___x_1890_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1889_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___y_1881_);
lean_ctor_set(v___x_1878_, 0, v___x_1890_);
v___x_1892_ = v___x_1878_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___y_1881_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_dec(v_doc_1886_);
v___x_1894_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1885_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___y_1881_);
lean_ctor_set(v___x_1878_, 0, v___x_1894_);
v___x_1896_ = v___x_1878_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___y_1881_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
lean_dec(v_doc_1885_);
v___x_1898_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1886_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___y_1881_);
lean_ctor_set(v___x_1878_, 0, v___x_1898_);
v___x_1900_ = v___x_1878_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___y_1881_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_object* v___x_1903_; 
lean_dec(v_a_1875_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___y_1881_);
lean_ctor_set(v___x_1878_, 0, v___y_1882_);
v___x_1903_ = v___x_1878_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___y_1882_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___y_1881_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_object* v___x_1906_; 
lean_dec_ref(v___y_1882_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___y_1881_);
v___x_1906_ = v___x_1878_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1875_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___y_1881_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
v___jp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v___y_1909_, v_stx_1864_, v_a_1876_);
lean_dec(v_stx_1864_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v_a_1912_; uint8_t v___x_1913_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
v_a_1912_ = lean_ctor_get(v___x_1910_, 1);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1910_, 2);
v___x_1913_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1871_);
if (v___x_1913_ == 0)
{
uint8_t v___x_1914_; 
v___x_1914_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_1911_);
if (v___x_1914_ == 0)
{
lean_object* v_doc_1915_; lean_object* v_doc_1916_; uint8_t v___x_1917_; 
v_doc_1915_ = lean_ctor_get(v_a_1871_, 0);
lean_inc(v_doc_1915_);
lean_dec(v_a_1871_);
v_doc_1916_ = lean_ctor_get(v_a_1911_, 0);
lean_inc(v_doc_1916_);
lean_dec(v_a_1911_);
v___x_1917_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1915_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1916_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1915_, v_doc_1916_);
v___x_1920_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1919_);
v___y_1881_ = v_a_1912_;
v___y_1882_ = v___x_1920_;
goto v___jp_1880_;
}
else
{
lean_object* v___x_1921_; 
lean_dec(v_doc_1916_);
v___x_1921_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1915_);
v___y_1881_ = v_a_1912_;
v___y_1882_ = v___x_1921_;
goto v___jp_1880_;
}
}
else
{
lean_object* v___x_1922_; 
lean_dec(v_doc_1915_);
v___x_1922_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1916_);
v___y_1881_ = v_a_1912_;
v___y_1882_ = v___x_1922_;
goto v___jp_1880_;
}
}
else
{
lean_dec(v_a_1911_);
v___y_1881_ = v_a_1912_;
v___y_1882_ = v_a_1871_;
goto v___jp_1880_;
}
}
else
{
lean_dec(v_a_1871_);
v___y_1881_ = v_a_1912_;
v___y_1882_ = v_a_1911_;
goto v___jp_1880_;
}
}
else
{
lean_del_object(v___x_1878_);
lean_dec(v_a_1875_);
lean_dec(v_a_1871_);
return v___x_1910_;
}
}
}
}
else
{
lean_dec(v_a_1871_);
lean_dec_ref(v_token_1865_);
lean_dec(v_stx_1864_);
return v___x_1874_;
}
}
else
{
lean_dec_ref(v_token_1865_);
lean_dec(v_stx_1864_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken___boxed(lean_object* v_stx_1938_, lean_object* v_token_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1938_, v_token_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
lean_dec_ref(v_a_1941_);
lean_dec_ref(v_a_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(lean_object* v_stx_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
switch(lean_obj_tag(v_stx_1947_))
{
case 0:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v_a_1950_);
return v___x_1952_;
}
case 1:
{
lean_object* v_kind_1953_; lean_object* v_args_1954_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v_kind_1953_ = lean_ctor_get(v_stx_1947_, 1);
lean_inc(v_kind_1953_);
v_args_1954_ = lean_ctor_get(v_stx_1947_, 2);
lean_inc_ref(v_args_1954_);
lean_dec_ref_known(v_stx_1947_, 3);
v___x_1981_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_1982_ = lean_name_eq(v_kind_1953_, v___x_1981_);
lean_dec(v_kind_1953_);
if (v___x_1982_ == 0)
{
v___y_1956_ = v_a_1948_;
v___y_1957_ = v_a_1949_;
v___y_1958_ = v_a_1950_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = lean_array_get_size(v_args_1954_);
v___x_1985_ = lean_nat_dec_lt(v___x_1983_, v___x_1984_);
if (v___x_1985_ == 0)
{
v___y_1956_ = v_a_1948_;
v___y_1957_ = v_a_1949_;
v___y_1958_ = v_a_1950_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_array_fget(v_args_1954_, v___x_1983_);
lean_dec_ref(v_args_1954_);
v_stx_1947_ = v___x_1986_;
goto _start;
}
}
v___jp_1955_:
{
size_t v_sz_1959_; size_t v___x_1960_; lean_object* v___x_1961_; 
v_sz_1959_ = lean_array_size(v_args_1954_);
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_1959_, v___x_1960_, v_args_1954_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1971_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
v_a_1963_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1971_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = l_Lean_Fmt_TaggedDoc_join(v_a_1962_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1967_);
v___x_1969_ = v___x_1965_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_a_1963_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_a_1972_ = lean_ctor_get(v___x_1961_, 0);
v_a_1973_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1961_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_inc(v_a_1972_);
lean_dec(v___x_1961_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1972_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
case 2:
{
lean_object* v_val_1988_; lean_object* v___x_1989_; 
v_val_1988_ = lean_ctor_get(v_stx_1947_, 1);
lean_inc_ref(v_val_1988_);
v___x_1989_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1947_, v_val_1988_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1989_;
}
default: 
{
lean_object* v_rawVal_1990_; lean_object* v_str_1991_; lean_object* v_startPos_1992_; lean_object* v_stopPos_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_rawVal_1990_ = lean_ctor_get(v_stx_1947_, 1);
v_str_1991_ = lean_ctor_get(v_rawVal_1990_, 0);
v_startPos_1992_ = lean_ctor_get(v_rawVal_1990_, 1);
v_stopPos_1993_ = lean_ctor_get(v_rawVal_1990_, 2);
v___x_1994_ = lean_string_utf8_extract(v_str_1991_, v_startPos_1992_, v_stopPos_1993_);
v___x_1995_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_fmtToken(v_stx_1947_, v___x_1994_, v_a_1948_, v_a_1949_, v_a_1950_);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(size_t v_sz_1996_, size_t v_i_1997_, lean_object* v_bs_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_usize_dec_lt(v_i_1997_, v_sz_1996_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_bs_1998_);
lean_ctor_set(v___x_2003_, 1, v___y_2001_);
return v___x_2003_;
}
else
{
lean_object* v_v_2004_; lean_object* v___x_2005_; 
v_v_2004_ = lean_array_uget_borrowed(v_bs_1998_, v_i_1997_);
lean_inc(v_v_2004_);
v___x_2005_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_v_2004_, v___y_1999_, v___y_2000_, v___y_2001_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v_a_2007_; lean_object* v___x_2008_; lean_object* v_bs_x27_2009_; size_t v___x_2010_; size_t v___x_2011_; lean_object* v___x_2012_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
v_a_2007_ = lean_ctor_get(v___x_2005_, 1);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2005_, 2);
v___x_2008_ = lean_unsigned_to_nat(0u);
v_bs_x27_2009_ = lean_array_uset(v_bs_1998_, v_i_1997_, v___x_2008_);
v___x_2010_ = ((size_t)1ULL);
v___x_2011_ = lean_usize_add(v_i_1997_, v___x_2010_);
v___x_2012_ = lean_array_uset(v_bs_x27_2009_, v_i_1997_, v_a_2006_);
v_i_1997_ = v___x_2011_;
v_bs_1998_ = v___x_2012_;
v___y_2001_ = v_a_2007_;
goto _start;
}
else
{
lean_object* v_a_2014_; lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v_bs_1998_);
v_a_2014_ = lean_ctor_get(v___x_2005_, 0);
v_a_2015_ = lean_ctor_get(v___x_2005_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2005_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_inc(v_a_2014_);
lean_dec(v___x_2005_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0___boxed(lean_object* v_sz_2023_, lean_object* v_i_2024_, lean_object* v_bs_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
size_t v_sz_boxed_2029_; size_t v_i_boxed_2030_; lean_object* v_res_2031_; 
v_sz_boxed_2029_ = lean_unbox_usize(v_sz_2023_);
lean_dec(v_sz_2023_);
v_i_boxed_2030_ = lean_unbox_usize(v_i_2024_);
lean_dec(v_i_2024_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go_spec__0(v_sz_boxed_2029_, v_i_boxed_2030_, v_bs_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___boxed(lean_object* v_stx_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec_ref(v_a_2033_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(lean_object* v_stx_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
uint8_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2040_ = 0;
v___x_2041_ = l_Lean_Syntax_getPos_x3f(v_stx_2037_, v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 1)
{
lean_object* v_val_2042_; lean_object* v___x_2043_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2037_, v___x_2040_);
if (lean_obj_tag(v___x_2043_) == 1)
{
lean_object* v_val_2044_; lean_object* v___x_2045_; 
v_val_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_val_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = l_Lean_Fmt_getLineInfos(v_val_2042_, v_val_2044_, v_a_2038_, v_a_2039_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2058_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_a_2047_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2049_ = v___x_2045_;
v_isShared_2050_ = v_isSharedCheck_2058_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2058_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2051_ = lean_unsigned_to_nat(1u);
v___x_2052_ = lean_array_get_size(v_a_2046_);
lean_dec(v_a_2046_);
v___x_2053_ = lean_nat_dec_lt(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_box(v___x_2053_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2054_);
v___x_2056_ = v___x_2049_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_a_2047_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_a_2059_ = lean_ctor_get(v___x_2045_, 0);
v_a_2060_ = lean_ctor_get(v___x_2045_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2045_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_inc(v_a_2059_);
lean_dec(v___x_2045_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2059_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v___x_2043_);
lean_dec(v_val_2042_);
v___x_2068_ = lean_box(v___x_2040_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v_a_2039_);
return v___x_2069_;
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
lean_dec(v___x_2041_);
v___x_2070_ = lean_box(v___x_2040_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v_a_2039_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline___boxed(lean_object* v_stx_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_2072_, v_a_2073_, v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_stx_2072_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtRaw_spec__4(lean_object* v_msg_2076_){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_panic_fn_borrowed(v___x_2077_, v_msg_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(lean_object* v_x2_2079_, lean_object* v_as_2080_, size_t v_i_2081_, size_t v_stop_2082_){
_start:
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_usize_dec_eq(v_i_2081_, v_stop_2082_);
if (v___x_2083_ == 0)
{
lean_object* v_startPos_2084_; lean_object* v___x_2085_; lean_object* v_start_2086_; uint8_t v___x_2087_; 
v_startPos_2084_ = lean_ctor_get(v_x2_2079_, 4);
v___x_2085_ = lean_array_uget_borrowed(v_as_2080_, v_i_2081_);
v_start_2086_ = lean_ctor_get(v___x_2085_, 0);
v___x_2087_ = lean_nat_dec_le(v_startPos_2084_, v_start_2086_);
if (v___x_2087_ == 0)
{
uint8_t v___x_2088_; 
v___x_2088_ = 1;
return v___x_2088_;
}
else
{
size_t v___x_2089_; size_t v___x_2090_; 
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_i_2081_, v___x_2089_);
v_i_2081_ = v___x_2090_;
goto _start;
}
}
else
{
uint8_t v___x_2092_; 
v___x_2092_ = 0;
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0___boxed(lean_object* v_x2_2093_, lean_object* v_as_2094_, lean_object* v_i_2095_, lean_object* v_stop_2096_){
_start:
{
size_t v_i_boxed_2097_; size_t v_stop_boxed_2098_; uint8_t v_res_2099_; lean_object* v_r_2100_; 
v_i_boxed_2097_ = lean_unbox_usize(v_i_2095_);
lean_dec(v_i_2095_);
v_stop_boxed_2098_ = lean_unbox_usize(v_stop_2096_);
lean_dec(v_stop_2096_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v_x2_2093_, v_as_2094_, v_i_boxed_2097_, v_stop_boxed_2098_);
lean_dec_ref(v_as_2094_);
lean_dec_ref(v_x2_2093_);
v_r_2100_ = lean_box(v_res_2099_);
return v_r_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(lean_object* v_as_2101_, size_t v_i_2102_, size_t v_stop_2103_, lean_object* v_b_2104_){
_start:
{
lean_object* v___y_2106_; uint8_t v___x_2110_; 
v___x_2110_ = lean_usize_dec_eq(v_i_2102_, v_stop_2103_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v_tokenRanges_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2111_ = lean_array_uget_borrowed(v_as_2101_, v_i_2102_);
v_tokenRanges_2117_ = lean_ctor_get(v___x_2111_, 3);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_array_get_size(v_tokenRanges_2117_);
v___x_2120_ = lean_nat_dec_lt(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
goto v___jp_2112_;
}
else
{
if (v___x_2120_ == 0)
{
goto v___jp_2112_;
}
else
{
size_t v___x_2121_; size_t v___x_2122_; uint8_t v___x_2123_; 
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = lean_usize_of_nat(v___x_2119_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__0(v___x_2111_, v_tokenRanges_2117_, v___x_2121_, v___x_2122_);
if (v___x_2123_ == 0)
{
goto v___jp_2112_;
}
else
{
v___y_2106_ = v_b_2104_;
goto v___jp_2105_;
}
}
}
v___jp_2112_:
{
lean_object* v_length_2113_; lean_object* v_indentation_2114_; uint8_t v___x_2115_; 
v_length_2113_ = lean_ctor_get(v___x_2111_, 0);
v_indentation_2114_ = lean_ctor_get(v___x_2111_, 1);
v___x_2115_ = lean_nat_dec_lt(v_indentation_2114_, v_length_2113_);
if (v___x_2115_ == 0)
{
v___y_2106_ = v_b_2104_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2116_; 
lean_inc(v___x_2111_);
v___x_2116_ = lean_array_push(v_b_2104_, v___x_2111_);
v___y_2106_ = v___x_2116_;
goto v___jp_2105_;
}
}
}
else
{
return v_b_2104_;
}
v___jp_2105_:
{
size_t v___x_2107_; size_t v___x_2108_; 
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_add(v_i_2102_, v___x_2107_);
v_i_2102_ = v___x_2108_;
v_b_2104_ = v___y_2106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5___boxed(lean_object* v_as_2124_, lean_object* v_i_2125_, lean_object* v_stop_2126_, lean_object* v_b_2127_){
_start:
{
size_t v_i_boxed_2128_; size_t v_stop_boxed_2129_; lean_object* v_res_2130_; 
v_i_boxed_2128_ = lean_unbox_usize(v_i_2125_);
lean_dec(v_i_2125_);
v_stop_boxed_2129_ = lean_unbox_usize(v_stop_2126_);
lean_dec(v_stop_2126_);
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v_as_2124_, v_i_boxed_2128_, v_stop_boxed_2129_, v_b_2127_);
lean_dec_ref(v_as_2124_);
return v_res_2130_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(lean_object* v___x_2131_, lean_object* v___x_2132_, lean_object* v_as_2133_, size_t v_i_2134_, size_t v_stop_2135_){
_start:
{
uint8_t v___x_2136_; 
v___x_2136_ = lean_usize_dec_eq(v_i_2134_, v_stop_2135_);
if (v___x_2136_ == 0)
{
uint8_t v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v___x_2137_ = 1;
v___x_2138_ = lean_array_uget_borrowed(v_as_2133_, v_i_2134_);
v___x_2139_ = lean_nat_dec_le(v___x_2131_, v___x_2138_);
if (v___x_2139_ == 0)
{
return v___x_2137_;
}
else
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_nat_dec_le(v___x_2131_, v___x_2132_);
if (v___x_2140_ == 0)
{
size_t v___x_2141_; size_t v___x_2142_; 
v___x_2141_ = ((size_t)1ULL);
v___x_2142_ = lean_usize_add(v_i_2134_, v___x_2141_);
v_i_2134_ = v___x_2142_;
goto _start;
}
else
{
return v___x_2137_;
}
}
}
else
{
uint8_t v___x_2144_; 
v___x_2144_ = 0;
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2___boxed(lean_object* v___x_2145_, lean_object* v___x_2146_, lean_object* v_as_2147_, lean_object* v_i_2148_, lean_object* v_stop_2149_){
_start:
{
size_t v_i_boxed_2150_; size_t v_stop_boxed_2151_; uint8_t v_res_2152_; lean_object* v_r_2153_; 
v_i_boxed_2150_ = lean_unbox_usize(v_i_2148_);
lean_dec(v_i_2148_);
v_stop_boxed_2151_ = lean_unbox_usize(v_stop_2149_);
lean_dec(v_stop_2149_);
v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2145_, v___x_2146_, v_as_2147_, v_i_boxed_2150_, v_stop_boxed_2151_);
lean_dec_ref(v_as_2147_);
lean_dec(v___x_2146_);
lean_dec(v___x_2145_);
v_r_2153_ = lean_box(v_res_2152_);
return v_r_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(size_t v_sz_2154_, size_t v_i_2155_, lean_object* v_bs_2156_){
_start:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_usize_dec_lt(v_i_2155_, v_sz_2154_);
if (v___x_2157_ == 0)
{
return v_bs_2156_;
}
else
{
lean_object* v_v_2158_; lean_object* v_indentation_2159_; lean_object* v___x_2160_; lean_object* v_bs_x27_2161_; size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v_v_2158_ = lean_array_uget_borrowed(v_bs_2156_, v_i_2155_);
v_indentation_2159_ = lean_ctor_get(v_v_2158_, 1);
lean_inc(v_indentation_2159_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v_bs_x27_2161_ = lean_array_uset(v_bs_2156_, v_i_2155_, v___x_2160_);
v___x_2162_ = ((size_t)1ULL);
v___x_2163_ = lean_usize_add(v_i_2155_, v___x_2162_);
v___x_2164_ = lean_array_uset(v_bs_x27_2161_, v_i_2155_, v_indentation_2159_);
v_i_2155_ = v___x_2163_;
v_bs_2156_ = v___x_2164_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1___boxed(lean_object* v_sz_2166_, lean_object* v_i_2167_, lean_object* v_bs_2168_){
_start:
{
size_t v_sz_boxed_2169_; size_t v_i_boxed_2170_; lean_object* v_res_2171_; 
v_sz_boxed_2169_ = lean_unbox_usize(v_sz_2166_);
lean_dec(v_sz_2166_);
v_i_boxed_2170_ = lean_unbox_usize(v_i_2167_);
lean_dec(v_i_2167_);
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_boxed_2169_, v_i_boxed_2170_, v_bs_2168_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(lean_object* v_as_2172_, size_t v_i_2173_, size_t v_stop_2174_, lean_object* v_b_2175_){
_start:
{
lean_object* v___y_2177_; uint8_t v___x_2181_; 
v___x_2181_ = lean_usize_dec_eq(v_i_2173_, v_stop_2174_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2182_ = lean_array_uget_borrowed(v_as_2172_, v_i_2173_);
v___x_2183_ = lean_nat_dec_le(v_b_2175_, v___x_2182_);
if (v___x_2183_ == 0)
{
v___y_2177_ = v___x_2182_;
goto v___jp_2176_;
}
else
{
v___y_2177_ = v_b_2175_;
goto v___jp_2176_;
}
}
else
{
lean_inc(v_b_2175_);
return v_b_2175_;
}
v___jp_2176_:
{
size_t v___x_2178_; size_t v___x_2179_; 
v___x_2178_ = ((size_t)1ULL);
v___x_2179_ = lean_usize_add(v_i_2173_, v___x_2178_);
v_i_2173_ = v___x_2179_;
v_b_2175_ = v___y_2177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5___boxed(lean_object* v_as_2184_, lean_object* v_i_2185_, lean_object* v_stop_2186_, lean_object* v_b_2187_){
_start:
{
size_t v_i_boxed_2188_; size_t v_stop_boxed_2189_; lean_object* v_res_2190_; 
v_i_boxed_2188_ = lean_unbox_usize(v_i_2185_);
lean_dec(v_i_2185_);
v_stop_boxed_2189_ = lean_unbox_usize(v_stop_2186_);
lean_dec(v_stop_2186_);
v_res_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_as_2184_, v_i_boxed_2188_, v_stop_boxed_2189_, v_b_2187_);
lean_dec(v_b_2187_);
lean_dec_ref(v_as_2184_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(lean_object* v_arr_2191_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_array_fget_borrowed(v_arr_2191_, v___x_2192_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_array_get_size(v_arr_2191_);
v___x_2196_ = lean_nat_dec_lt(v___x_2194_, v___x_2195_);
if (v___x_2196_ == 0)
{
lean_inc(v___x_2193_);
return v___x_2193_;
}
else
{
size_t v___x_2197_; size_t v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = ((size_t)1ULL);
v___x_2198_ = lean_usize_of_nat(v___x_2195_);
v___x_2199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3_spec__5(v_arr_2191_, v___x_2197_, v___x_2198_, v___x_2193_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg___boxed(lean_object* v_arr_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2200_);
lean_dec_ref(v_arr_2200_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(lean_object* v_arr_2202_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2203_ = lean_array_get_size(v_arr_2202_);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_nat_dec_eq(v___x_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2202_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_box(0);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3___boxed(lean_object* v_arr_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v_arr_2209_);
lean_dec_ref(v_arr_2209_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw(uint8_t v_isFallback_2211_, lean_object* v_stx_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_rawDoc_2216_; lean_object* v___y_2217_; lean_object* v___y_2230_; lean_object* v___y_2231_; uint8_t v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = 0;
v___x_2236_ = l_Lean_Syntax_getPos_x3f(v_stx_2212_, v___x_2235_);
if (lean_obj_tag(v___x_2236_) == 1)
{
lean_object* v_val_2237_; lean_object* v___x_2238_; 
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2212_, v___x_2235_);
if (lean_obj_tag(v___x_2238_) == 1)
{
lean_object* v_val_2239_; lean_object* v___x_2240_; 
v_val_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc_n(v_val_2239_, 2);
lean_dec_ref_known(v___x_2238_, 1);
lean_inc(v_val_2237_);
v___x_2240_ = l_Lean_Fmt_getLineInfos(v_val_2237_, v_val_2239_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_a_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v_indentation_2246_; lean_object* v_line_2247_; lean_object* v_startPos_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___y_2252_; size_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2266_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
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
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_array_get_size(v_a_2241_);
v___x_2280_ = l_Array_toSubarray___redArg(v_a_2241_, v___x_2278_, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_Fmt_getLineInfos___closed__0));
v___x_2282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_getLineInfos_spec__0___redArg(v___x_2280_, v___x_2281_);
v___x_2283_ = lean_array_get_size(v___x_2282_);
v___x_2284_ = lean_nat_dec_lt(v___x_2244_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_dec_ref(v___x_2282_);
v___y_2266_ = v___x_2281_;
goto v___jp_2265_;
}
else
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_nat_dec_le(v___x_2283_, v___x_2283_);
if (v___x_2285_ == 0)
{
if (v___x_2284_ == 0)
{
lean_dec_ref(v___x_2282_);
v___y_2266_ = v___x_2281_;
goto v___jp_2265_;
}
else
{
size_t v___x_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = ((size_t)0ULL);
v___x_2287_ = lean_usize_of_nat(v___x_2283_);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2282_, v___x_2286_, v___x_2287_, v___x_2281_);
lean_dec_ref(v___x_2282_);
v___y_2266_ = v___x_2288_;
goto v___jp_2265_;
}
}
else
{
size_t v___x_2289_; size_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = ((size_t)0ULL);
v___x_2290_ = lean_usize_of_nat(v___x_2283_);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_fmtRaw_spec__5(v___x_2282_, v___x_2289_, v___x_2290_, v___x_2281_);
lean_dec_ref(v___x_2282_);
v___y_2266_ = v___x_2291_;
goto v___jp_2265_;
}
}
v___jp_2251_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2255_, 0, v___y_2254_);
lean_ctor_set(v___x_2255_, 1, v_val_2237_);
lean_ctor_set(v___x_2255_, 2, v_val_2239_);
lean_inc(v_stx_2212_);
v___x_2256_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go(v_stx_2212_, v___x_2255_, v_a_2213_, v_a_2242_);
lean_dec_ref_known(v___x_2255_, 3);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v_a_2258_; uint8_t v___x_2259_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
v_a_2258_ = lean_ctor_get(v___x_2256_, 1);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2256_, 2);
v___x_2259_ = lean_nat_dec_le(v___x_2250_, v_indentation_2246_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_array_get_size(v___y_2252_);
v___x_2261_ = lean_nat_dec_lt(v___x_2244_, v___x_2260_);
if (v___x_2261_ == 0)
{
lean_dec_ref(v___y_2252_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
v___y_2230_ = v_a_2258_;
v___y_2231_ = v_a_2257_;
goto v___jp_2229_;
}
else
{
if (v___x_2261_ == 0)
{
lean_dec_ref(v___y_2252_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
v___y_2230_ = v_a_2258_;
v___y_2231_ = v_a_2257_;
goto v___jp_2229_;
}
else
{
size_t v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_usize_of_nat(v___x_2260_);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtRaw_spec__2(v___x_2250_, v_indentation_2246_, v___y_2252_, v___y_2253_, v___x_2262_);
lean_dec_ref(v___y_2252_);
lean_dec(v_indentation_2246_);
lean_dec(v___x_2250_);
if (v___x_2263_ == 0)
{
v___y_2230_ = v_a_2258_;
v___y_2231_ = v_a_2257_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Fmt_TaggedDoc_nested(v_a_2257_);
v_rawDoc_2216_ = v___x_2264_;
v___y_2217_ = v_a_2258_;
goto v___jp_2215_;
}
}
}
}
else
{
lean_dec_ref(v___y_2252_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
v___y_2230_ = v_a_2258_;
v___y_2231_ = v_a_2257_;
goto v___jp_2229_;
}
}
else
{
lean_dec_ref(v___y_2252_);
lean_dec(v___x_2250_);
lean_dec(v_indentation_2246_);
lean_dec(v_stx_2212_);
return v___x_2256_;
}
}
v___jp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; size_t v_sz_2270_; size_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_mk_empty_array_with_capacity(v___x_2267_);
lean_inc(v___x_2250_);
v___x_2269_ = lean_array_push(v___x_2268_, v___x_2250_);
v_sz_2270_ = lean_array_size(v___y_2266_);
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtRaw_spec__1(v_sz_2270_, v___x_2271_, v___y_2266_);
v___x_2273_ = l_Array_append___redArg(v___x_2269_, v___x_2272_);
v___x_2274_ = l_Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3(v___x_2273_);
lean_dec_ref(v___x_2273_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_2276_ = l_panic___at___00Lean_Fmt_fmtRaw_spec__4(v___x_2275_);
v___y_2252_ = v___x_2272_;
v___y_2253_ = v___x_2271_;
v___y_2254_ = v___x_2276_;
goto v___jp_2251_;
}
else
{
lean_object* v_val_2277_; 
v_val_2277_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_val_2277_);
lean_dec_ref_known(v___x_2274_, 1);
v___y_2252_ = v___x_2272_;
v___y_2253_ = v___x_2271_;
v___y_2254_ = v_val_2277_;
goto v___jp_2251_;
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_val_2239_);
lean_dec(v_val_2237_);
lean_dec(v_stx_2212_);
v_a_2292_ = lean_ctor_get(v___x_2240_, 0);
v_a_2293_ = lean_ctor_get(v___x_2240_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2240_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_inc(v_a_2292_);
lean_dec(v___x_2240_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2292_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_dec(v___x_2238_);
lean_dec(v_val_2237_);
v___x_2301_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2302_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2301_, v_stx_2212_, v_a_2214_);
lean_dec(v_stx_2212_);
return v___x_2302_;
}
}
else
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec(v___x_2236_);
v___x_2303_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_2304_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_2303_, v_stx_2212_, v_a_2214_);
lean_dec(v_stx_2212_);
return v___x_2304_;
}
v___jp_2215_:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_rawDoc_2216_, v_stx_2212_, v___y_2217_);
lean_dec(v_stx_2212_);
if (lean_obj_tag(v___x_2218_) == 0)
{
if (v_isFallback_2211_ == 0)
{
return v___x_2218_;
}
else
{
lean_object* v_a_2219_; lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2228_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_a_2220_ = lean_ctor_get(v___x_2218_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2222_ = v___x_2218_;
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = l_Lean_Fmt_TaggedDoc_mkRawFallback(v_a_2219_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_a_2220_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
return v___x_2218_;
}
}
v___jp_2229_:
{
lean_object* v_doc_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_doc_2232_ = lean_ctor_get(v___y_2231_, 0);
lean_inc(v_doc_2232_);
lean_dec_ref(v___y_2231_);
v___x_2233_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_2232_);
v___x_2234_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_2233_);
v_rawDoc_2216_ = v___x_2234_;
v___y_2217_ = v___y_2230_;
goto v___jp_2215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRaw___boxed(lean_object* v_isFallback_2305_, lean_object* v_stx_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
uint8_t v_isFallback_boxed_2309_; lean_object* v_res_2310_; 
v_isFallback_boxed_2309_ = lean_unbox(v_isFallback_2305_);
v_res_2310_ = l_Lean_Fmt_fmtRaw(v_isFallback_boxed_2309_, v_stx_2306_, v_a_2307_, v_a_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(lean_object* v_arr_2311_, lean_object* v_h_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___redArg(v_arr_2311_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3___boxed(lean_object* v_arr_2314_, lean_object* v_h_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Array_min___at___00Array_min_x3f___at___00Lean_Fmt_fmtRaw_spec__3_spec__3(v_arr_2314_, v_h_2315_);
lean_dec_ref(v_arr_2314_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0(lean_object* v_a_2317_, lean_object* v_____r_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_a_2317_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___lam__0___boxed(lean_object* v_a_2323_, lean_object* v_____r_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2323_, v_____r_2324_, v___y_2325_, v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(lean_object* v_a_2328_, lean_object* v_b_2329_, lean_object* v_x_2330_){
_start:
{
if (lean_obj_tag(v_x_2330_) == 0)
{
lean_dec(v_b_2329_);
lean_dec_ref(v_a_2328_);
return v_x_2330_;
}
else
{
lean_object* v_key_2331_; lean_object* v_value_2332_; lean_object* v_tail_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2345_; 
v_key_2331_ = lean_ctor_get(v_x_2330_, 0);
v_value_2332_ = lean_ctor_get(v_x_2330_, 1);
v_tail_2333_ = lean_ctor_get(v_x_2330_, 2);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_x_2330_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2335_ = v_x_2330_;
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_tail_2333_);
lean_inc(v_value_2332_);
lean_inc(v_key_2331_);
lean_dec(v_x_2330_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2345_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
uint8_t v___x_2337_; 
v___x_2337_ = l_Lean_Syntax_instBEqRange_beq(v_key_2331_, v_a_2328_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2328_, v_b_2329_, v_tail_2333_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 2, v___x_2338_);
v___x_2340_ = v___x_2335_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_key_2331_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_value_2332_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
else
{
lean_object* v___x_2343_; 
lean_dec(v_value_2332_);
lean_dec(v_key_2331_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 1, v_b_2329_);
lean_ctor_set(v___x_2335_, 0, v_a_2328_);
v___x_2343_ = v___x_2335_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2328_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_b_2329_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_tail_2333_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
if (lean_obj_tag(v_x_2347_) == 0)
{
return v_x_2346_;
}
else
{
lean_object* v_key_2348_; lean_object* v_value_2349_; lean_object* v_tail_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2373_; 
v_key_2348_ = lean_ctor_get(v_x_2347_, 0);
v_value_2349_ = lean_ctor_get(v_x_2347_, 1);
v_tail_2350_ = lean_ctor_get(v_x_2347_, 2);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2352_ = v_x_2347_;
v_isShared_2353_ = v_isSharedCheck_2373_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_tail_2350_);
lean_inc(v_value_2349_);
lean_inc(v_key_2348_);
lean_dec(v_x_2347_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2373_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; uint64_t v___x_2355_; uint64_t v___x_2356_; uint64_t v___x_2357_; uint64_t v_fold_2358_; uint64_t v___x_2359_; uint64_t v___x_2360_; uint64_t v___x_2361_; size_t v___x_2362_; size_t v___x_2363_; size_t v___x_2364_; size_t v___x_2365_; size_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2354_ = lean_array_get_size(v_x_2346_);
v___x_2355_ = l_Lean_Syntax_instHashableRange_hash(v_key_2348_);
v___x_2356_ = 32ULL;
v___x_2357_ = lean_uint64_shift_right(v___x_2355_, v___x_2356_);
v_fold_2358_ = lean_uint64_xor(v___x_2355_, v___x_2357_);
v___x_2359_ = 16ULL;
v___x_2360_ = lean_uint64_shift_right(v_fold_2358_, v___x_2359_);
v___x_2361_ = lean_uint64_xor(v_fold_2358_, v___x_2360_);
v___x_2362_ = lean_uint64_to_usize(v___x_2361_);
v___x_2363_ = lean_usize_of_nat(v___x_2354_);
v___x_2364_ = ((size_t)1ULL);
v___x_2365_ = lean_usize_sub(v___x_2363_, v___x_2364_);
v___x_2366_ = lean_usize_land(v___x_2362_, v___x_2365_);
v___x_2367_ = lean_array_uget_borrowed(v_x_2346_, v___x_2366_);
lean_inc(v___x_2367_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 2, v___x_2367_);
v___x_2369_ = v___x_2352_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_key_2348_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_value_2349_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_array_uset(v_x_2346_, v___x_2366_, v___x_2369_);
v_x_2346_ = v___x_2370_;
v_x_2347_ = v_tail_2350_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(lean_object* v_i_2374_, lean_object* v_source_2375_, lean_object* v_target_2376_){
_start:
{
lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = lean_array_get_size(v_source_2375_);
v___x_2378_ = lean_nat_dec_lt(v_i_2374_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_dec_ref(v_source_2375_);
lean_dec(v_i_2374_);
return v_target_2376_;
}
else
{
lean_object* v_es_2379_; lean_object* v___x_2380_; lean_object* v_source_2381_; lean_object* v_target_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_es_2379_ = lean_array_fget(v_source_2375_, v_i_2374_);
v___x_2380_ = lean_box(0);
v_source_2381_ = lean_array_fset(v_source_2375_, v_i_2374_, v___x_2380_);
v_target_2382_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2376_, v_es_2379_);
v___x_2383_ = lean_unsigned_to_nat(1u);
v___x_2384_ = lean_nat_add(v_i_2374_, v___x_2383_);
lean_dec(v_i_2374_);
v_i_2374_ = v___x_2384_;
v_source_2375_ = v_source_2381_;
v_target_2376_ = v_target_2382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(lean_object* v_data_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_nbuckets_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2387_ = lean_array_get_size(v_data_2386_);
v___x_2388_ = lean_unsigned_to_nat(2u);
v_nbuckets_2389_ = lean_nat_mul(v___x_2387_, v___x_2388_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_mk_array(v_nbuckets_2389_, v___x_2391_);
v___x_2393_ = lean_array_propagate_mark(v_data_2386_, v___x_2392_);
v___x_2394_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v___x_2390_, v_data_2386_, v___x_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(lean_object* v_a_2395_, lean_object* v_x_2396_){
_start:
{
if (lean_obj_tag(v_x_2396_) == 0)
{
uint8_t v___x_2397_; 
v___x_2397_ = 0;
return v___x_2397_;
}
else
{
lean_object* v_key_2398_; lean_object* v_tail_2399_; uint8_t v___x_2400_; 
v_key_2398_ = lean_ctor_get(v_x_2396_, 0);
v_tail_2399_ = lean_ctor_get(v_x_2396_, 2);
v___x_2400_ = l_Lean_Syntax_instBEqRange_beq(v_key_2398_, v_a_2395_);
if (v___x_2400_ == 0)
{
v_x_2396_ = v_tail_2399_;
goto _start;
}
else
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg___boxed(lean_object* v_a_2402_, lean_object* v_x_2403_){
_start:
{
uint8_t v_res_2404_; lean_object* v_r_2405_; 
v_res_2404_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2402_, v_x_2403_);
lean_dec(v_x_2403_);
lean_dec_ref(v_a_2402_);
v_r_2405_ = lean_box(v_res_2404_);
return v_r_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(lean_object* v_m_2406_, lean_object* v_a_2407_, lean_object* v_b_2408_){
_start:
{
lean_object* v_size_2409_; lean_object* v_buckets_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2453_; 
v_size_2409_ = lean_ctor_get(v_m_2406_, 0);
v_buckets_2410_ = lean_ctor_get(v_m_2406_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_m_2406_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2412_ = v_m_2406_;
v_isShared_2413_ = v_isSharedCheck_2453_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_buckets_2410_);
lean_inc(v_size_2409_);
lean_dec(v_m_2406_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2453_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; uint64_t v___x_2415_; uint64_t v___x_2416_; uint64_t v___x_2417_; uint64_t v_fold_2418_; uint64_t v___x_2419_; uint64_t v___x_2420_; uint64_t v___x_2421_; size_t v___x_2422_; size_t v___x_2423_; size_t v___x_2424_; size_t v___x_2425_; size_t v___x_2426_; lean_object* v_bkt_2427_; uint8_t v___x_2428_; 
v___x_2414_ = lean_array_get_size(v_buckets_2410_);
v___x_2415_ = l_Lean_Syntax_instHashableRange_hash(v_a_2407_);
v___x_2416_ = 32ULL;
v___x_2417_ = lean_uint64_shift_right(v___x_2415_, v___x_2416_);
v_fold_2418_ = lean_uint64_xor(v___x_2415_, v___x_2417_);
v___x_2419_ = 16ULL;
v___x_2420_ = lean_uint64_shift_right(v_fold_2418_, v___x_2419_);
v___x_2421_ = lean_uint64_xor(v_fold_2418_, v___x_2420_);
v___x_2422_ = lean_uint64_to_usize(v___x_2421_);
v___x_2423_ = lean_usize_of_nat(v___x_2414_);
v___x_2424_ = ((size_t)1ULL);
v___x_2425_ = lean_usize_sub(v___x_2423_, v___x_2424_);
v___x_2426_ = lean_usize_land(v___x_2422_, v___x_2425_);
v_bkt_2427_ = lean_array_uget_borrowed(v_buckets_2410_, v___x_2426_);
v___x_2428_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2407_, v_bkt_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v_size_x27_2430_; lean_object* v___x_2431_; lean_object* v_buckets_x27_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v___x_2429_ = lean_unsigned_to_nat(1u);
v_size_x27_2430_ = lean_nat_add(v_size_2409_, v___x_2429_);
lean_dec(v_size_2409_);
lean_inc(v_bkt_2427_);
v___x_2431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2431_, 0, v_a_2407_);
lean_ctor_set(v___x_2431_, 1, v_b_2408_);
lean_ctor_set(v___x_2431_, 2, v_bkt_2427_);
v_buckets_x27_2432_ = lean_array_uset(v_buckets_2410_, v___x_2426_, v___x_2431_);
v___x_2433_ = lean_unsigned_to_nat(4u);
v___x_2434_ = lean_nat_mul(v_size_x27_2430_, v___x_2433_);
v___x_2435_ = lean_unsigned_to_nat(3u);
v___x_2436_ = lean_nat_div(v___x_2434_, v___x_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_array_get_size(v_buckets_x27_2432_);
v___x_2438_ = lean_nat_dec_le(v___x_2436_, v___x_2437_);
lean_dec(v___x_2436_);
if (v___x_2438_ == 0)
{
lean_object* v_val_2439_; lean_object* v___x_2441_; 
v_val_2439_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_buckets_x27_2432_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v_val_2439_);
lean_ctor_set(v___x_2412_, 0, v_size_x27_2430_);
v___x_2441_ = v___x_2412_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_size_x27_2430_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_val_2439_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
else
{
lean_object* v___x_2444_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v_buckets_x27_2432_);
lean_ctor_set(v___x_2412_, 0, v_size_x27_2430_);
v___x_2444_ = v___x_2412_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_size_x27_2430_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_buckets_x27_2432_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
else
{
lean_object* v___x_2446_; lean_object* v_buckets_x27_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_inc(v_bkt_2427_);
v___x_2446_ = lean_box(0);
v_buckets_x27_2447_ = lean_array_uset(v_buckets_2410_, v___x_2426_, v___x_2446_);
v___x_2448_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2407_, v_b_2408_, v_bkt_2427_);
v___x_2449_ = lean_array_uset(v_buckets_x27_2447_, v___x_2426_, v___x_2448_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v___x_2449_);
v___x_2451_ = v___x_2412_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_size_2409_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith(lean_object* v_f_2454_, lean_object* v_formatterName_2455_, lean_object* v_stx_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___y_2460_; lean_object* v_a_2472_; lean_object* v_a_2473_; lean_object* v___x_2508_; 
lean_inc_ref(v_a_2457_);
lean_inc(v_stx_2456_);
v___x_2508_ = lean_apply_3(v_f_2454_, v_stx_2456_, v_a_2457_, v_a_2458_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v_a_2510_; lean_object* v___x_2511_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
v_a_2510_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2508_, 2);
v___x_2511_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_a_2509_, v_stx_2456_, v_a_2510_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_stx_2456_);
lean_dec(v_formatterName_2455_);
v_a_2512_ = lean_ctor_get(v___x_2511_, 1);
v_a_2513_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2515_ = v___x_2511_;
v_isShared_2516_ = v_isSharedCheck_2536_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2512_);
lean_inc(v_a_2513_);
lean_dec(v___x_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2536_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_toBacktrackableState_2517_; lean_object* v_shareCommonState_2518_; lean_object* v_freshTagId_2519_; lean_object* v_missingFormatters_2520_; lean_object* v_partialFormatters_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2535_; 
v_toBacktrackableState_2517_ = lean_ctor_get(v_a_2512_, 0);
v_shareCommonState_2518_ = lean_ctor_get(v_a_2512_, 1);
v_freshTagId_2519_ = lean_ctor_get(v_a_2512_, 2);
v_missingFormatters_2520_ = lean_ctor_get(v_a_2512_, 3);
v_partialFormatters_2521_ = lean_ctor_get(v_a_2512_, 4);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_a_2512_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2523_ = v_a_2512_;
v_isShared_2524_ = v_isSharedCheck_2535_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_partialFormatters_2521_);
lean_inc(v_missingFormatters_2520_);
lean_inc(v_freshTagId_2519_);
lean_inc(v_shareCommonState_2518_);
lean_inc(v_toBacktrackableState_2517_);
lean_dec(v_a_2512_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2535_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v_fst_2527_; lean_object* v_snd_2528_; lean_object* v___x_2530_; 
v___x_2525_ = l_Lean_ShareCommon_objectFactory;
v___x_2526_ = lean_state_sharecommon(v___x_2525_, v_shareCommonState_2518_, v_a_2513_);
v_fst_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_fst_2527_);
v_snd_2528_ = lean_ctor_get(v___x_2526_, 1);
lean_inc(v_snd_2528_);
lean_dec_ref(v___x_2526_);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v_snd_2528_);
v___x_2530_ = v___x_2523_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_toBacktrackableState_2517_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_snd_2528_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_freshTagId_2519_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_missingFormatters_2520_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v_partialFormatters_2521_);
v___x_2530_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2532_; 
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 1, v___x_2530_);
lean_ctor_set(v___x_2515_, 0, v_fst_2527_);
v___x_2532_ = v___x_2515_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_fst_2527_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v_a_2538_; 
v_a_2537_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2537_);
v_a_2538_ = lean_ctor_get(v___x_2511_, 1);
lean_inc(v_a_2538_);
lean_dec_ref_known(v___x_2511_, 2);
v_a_2472_ = v_a_2537_;
v_a_2473_ = v_a_2538_;
goto v___jp_2471_;
}
}
else
{
lean_object* v_a_2539_; lean_object* v_a_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2539_);
v_a_2540_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2508_, 2);
v_a_2472_ = v_a_2539_;
v_a_2473_ = v_a_2540_;
goto v___jp_2471_;
}
v___jp_2459_:
{
lean_object* v_a_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2470_; 
v_a_2461_ = lean_ctor_get(v___y_2460_, 0);
v_a_2462_ = lean_ctor_get(v___y_2460_, 1);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___y_2460_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2464_ = v___y_2460_;
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_inc(v_a_2461_);
lean_dec(v___y_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2470_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_a_2466_; lean_object* v___x_2468_; 
v_a_2466_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_a_2466_);
lean_dec(v_a_2461_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v_a_2466_);
v___x_2468_ = v___x_2464_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2466_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_a_2462_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
v___jp_2471_:
{
if (lean_obj_tag(v_a_2472_) == 0)
{
uint8_t v_err_2474_; 
v_err_2474_ = lean_ctor_get_uint8(v_a_2472_, 0);
if (v_err_2474_ == 0)
{
uint8_t v___x_2475_; lean_object* v___x_2476_; 
lean_dec_ref_known(v_a_2472_, 0);
v___x_2475_ = 1;
lean_inc(v_stx_2456_);
v___x_2476_ = l_Lean_Fmt_fmtRaw(v___x_2475_, v_stx_2456_, v_a_2457_, v_a_2473_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2505_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_a_2478_ = lean_ctor_get(v___x_2476_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2505_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2505_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
uint8_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = 0;
v___x_2483_ = l_Lean_Syntax_getRange_x3f(v_stx_2456_, v___x_2482_);
if (lean_obj_tag(v___x_2483_) == 1)
{
lean_object* v_val_2484_; lean_object* v_toBacktrackableState_2485_; lean_object* v_shareCommonState_2486_; lean_object* v_freshTagId_2487_; lean_object* v_missingFormatters_2488_; lean_object* v_partialFormatters_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2502_; 
v_val_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v_toBacktrackableState_2485_ = lean_ctor_get(v_a_2478_, 0);
v_shareCommonState_2486_ = lean_ctor_get(v_a_2478_, 1);
v_freshTagId_2487_ = lean_ctor_get(v_a_2478_, 2);
v_missingFormatters_2488_ = lean_ctor_get(v_a_2478_, 3);
v_partialFormatters_2489_ = lean_ctor_get(v_a_2478_, 4);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2478_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2491_ = v_a_2478_;
v_isShared_2492_ = v_isSharedCheck_2502_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_partialFormatters_2489_);
lean_inc(v_missingFormatters_2488_);
lean_inc(v_freshTagId_2487_);
lean_inc(v_shareCommonState_2486_);
lean_inc(v_toBacktrackableState_2485_);
lean_dec(v_a_2478_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2502_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_box(0);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_formatterName_2455_);
lean_ctor_set(v___x_2480_, 0, v_stx_2456_);
v___x_2495_ = v___x_2480_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_stx_2456_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v_formatterName_2455_);
v___x_2495_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2496_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_partialFormatters_2489_, v_val_2484_, v___x_2495_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 4, v___x_2496_);
v___x_2498_ = v___x_2491_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_toBacktrackableState_2485_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_shareCommonState_2486_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_freshTagId_2487_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_missingFormatters_2488_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2477_, v___x_2493_, v_a_2457_, v___x_2498_);
v___y_2460_ = v___x_2499_;
goto v___jp_2459_;
}
}
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v___x_2483_);
lean_del_object(v___x_2480_);
lean_dec(v_stx_2456_);
lean_dec(v_formatterName_2455_);
v___x_2503_ = lean_box(0);
v___x_2504_ = l_Lean_Fmt_fmtWith___lam__0(v_a_2477_, v___x_2503_, v_a_2457_, v_a_2478_);
v___y_2460_ = v___x_2504_;
goto v___jp_2459_;
}
}
}
else
{
lean_dec(v_stx_2456_);
lean_dec(v_formatterName_2455_);
return v___x_2476_;
}
}
else
{
lean_object* v___x_2506_; 
lean_dec(v_stx_2456_);
lean_dec(v_formatterName_2455_);
v___x_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2506_, 0, v_a_2472_);
lean_ctor_set(v___x_2506_, 1, v_a_2473_);
return v___x_2506_;
}
}
else
{
lean_object* v___x_2507_; 
lean_dec(v_stx_2456_);
lean_dec(v_formatterName_2455_);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_a_2472_);
lean_ctor_set(v___x_2507_, 1, v_a_2473_);
return v___x_2507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith___boxed(lean_object* v_f_2541_, lean_object* v_formatterName_2542_, lean_object* v_stx_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_Fmt_fmtWith(v_f_2541_, v_formatterName_2542_, v_stx_2543_, v_a_2544_, v_a_2545_);
lean_dec_ref(v_a_2544_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0(lean_object* v_00_u03b2_2547_, lean_object* v_m_2548_, lean_object* v_a_2549_, lean_object* v_b_2550_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_m_2548_, v_a_2549_, v_b_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(lean_object* v_00_u03b2_2552_, lean_object* v_a_2553_, lean_object* v_x_2554_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___redArg(v_a_2553_, v_x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2556_, lean_object* v_a_2557_, lean_object* v_x_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__0(v_00_u03b2_2556_, v_a_2557_, v_x_2558_);
lean_dec(v_x_2558_);
lean_dec_ref(v_a_2557_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1(lean_object* v_00_u03b2_2561_, lean_object* v_data_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1___redArg(v_data_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2(lean_object* v_00_u03b2_2564_, lean_object* v_a_2565_, lean_object* v_b_2566_, lean_object* v_x_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__2___redArg(v_a_2565_, v_b_2566_, v_x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2569_, lean_object* v_i_2570_, lean_object* v_source_2571_, lean_object* v_target_2572_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2___redArg(v_i_2570_, v_source_2571_, v_target_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2574_, lean_object* v_x_2575_, lean_object* v_x_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2575_, v_x_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(lean_object* v_a_2581_, lean_object* v_kind_2582_, lean_object* v_as_2583_, size_t v_sz_2584_, size_t v_i_2585_, lean_object* v_b_2586_){
_start:
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_usize_dec_lt(v_i_2585_, v_sz_2584_);
if (v___x_2587_ == 0)
{
lean_dec(v_kind_2582_);
lean_inc_ref(v_b_2586_);
return v_b_2586_;
}
else
{
lean_object* v_a_2588_; lean_object* v_provider_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2605_; 
v_a_2588_ = lean_array_uget(v_as_2583_, v_i_2585_);
v_provider_2589_ = lean_ctor_get(v_a_2588_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v_a_2588_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v_a_2588_, 0);
lean_dec(v_unused_2606_);
v___x_2591_ = v_a_2588_;
v_isShared_2592_ = v_isSharedCheck_2605_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_provider_2589_);
lean_dec(v_a_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2605_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v_env_2593_; lean_object* v_opts_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_env_2593_ = lean_ctor_get(v_a_2581_, 0);
v_opts_2594_ = lean_ctor_get(v_a_2581_, 3);
v___x_2595_ = lean_box(0);
lean_inc(v_kind_2582_);
lean_inc_ref(v_opts_2594_);
lean_inc_ref(v_env_2593_);
v___x_2596_ = lean_apply_3(v_provider_2589_, v_env_2593_, v_opts_2594_, v_kind_2582_);
if (lean_obj_tag(v___x_2596_) == 1)
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
lean_dec(v_kind_2582_);
v___x_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2595_);
lean_ctor_set(v___x_2591_, 0, v___x_2597_);
v___x_2599_ = v___x_2591_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2595_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
else
{
lean_object* v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; 
lean_dec(v___x_2596_);
lean_del_object(v___x_2591_);
v___x_2601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v___x_2602_ = ((size_t)1ULL);
v___x_2603_ = lean_usize_add(v_i_2585_, v___x_2602_);
v_i_2585_ = v___x_2603_;
v_b_2586_ = v___x_2601_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___boxed(lean_object* v_a_2607_, lean_object* v_kind_2608_, lean_object* v_as_2609_, lean_object* v_sz_2610_, lean_object* v_i_2611_, lean_object* v_b_2612_){
_start:
{
size_t v_sz_boxed_2613_; size_t v_i_boxed_2614_; lean_object* v_res_2615_; 
v_sz_boxed_2613_ = lean_unbox_usize(v_sz_2610_);
lean_dec(v_sz_2610_);
v_i_boxed_2614_ = lean_unbox_usize(v_i_2611_);
lean_dec(v_i_2611_);
v_res_2615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2607_, v_kind_2608_, v_as_2609_, v_sz_boxed_2613_, v_i_boxed_2614_, v_b_2612_);
lean_dec_ref(v_b_2612_);
lean_dec_ref(v_as_2609_);
lean_dec_ref(v_a_2607_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f(lean_object* v_kind_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_env_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; size_t v_sz_2623_; size_t v___x_2624_; lean_object* v___x_2625_; lean_object* v_fst_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2637_; 
v_env_2619_ = lean_ctor_get(v_a_2617_, 0);
lean_inc_ref(v_env_2619_);
v___x_2620_ = l_Lean_Fmt_getFmtProviders(v_env_2619_);
v___x_2621_ = lean_box(0);
v___x_2622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0___closed__0));
v_sz_2623_ = lean_array_size(v___x_2620_);
v___x_2624_ = ((size_t)0ULL);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_getFormatterForKind_x3f_spec__0(v_a_2617_, v_kind_2616_, v___x_2620_, v_sz_2623_, v___x_2624_, v___x_2622_);
lean_dec_ref(v___x_2620_);
v_fst_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2625_, 1);
lean_dec(v_unused_2638_);
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2637_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_fst_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2637_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
if (lean_obj_tag(v_fst_2626_) == 0)
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 1, v_a_2618_);
lean_ctor_set(v___x_2628_, 0, v___x_2621_);
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_a_2618_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
else
{
lean_object* v_val_2633_; lean_object* v___x_2635_; 
v_val_2633_ = lean_ctor_get(v_fst_2626_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v_fst_2626_, 1);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 1, v_a_2618_);
lean_ctor_set(v___x_2628_, 0, v_val_2633_);
v___x_2635_ = v___x_2628_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_val_2633_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_a_2618_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_getFormatterForKind_x3f___boxed(lean_object* v_kind_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2639_, v_a_2640_, v_a_2641_);
lean_dec_ref(v_a_2640_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt(lean_object* v_stx_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
switch(lean_obj_tag(v_stx_2643_))
{
case 0:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = l_Lean_Fmt_TaggedDoc_failure;
v___x_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
lean_ctor_set(v___x_2647_, 1, v_a_2645_);
return v___x_2647_;
}
case 1:
{
lean_object* v_kind_2648_; lean_object* v___x_2649_; lean_object* v_a_2650_; 
lean_inc_ref(v_stx_2643_);
v_kind_2648_ = l_Lean_Syntax_getKind(v_stx_2643_);
lean_inc(v_kind_2648_);
v___x_2649_ = l_Lean_Fmt_getFormatterForKind_x3f(v_kind_2648_, v_a_2644_, v_a_2645_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
if (lean_obj_tag(v_a_2650_) == 1)
{
lean_object* v_val_2651_; lean_object* v_a_2652_; lean_object* v_fst_2653_; lean_object* v_snd_2654_; lean_object* v___x_2655_; 
lean_dec(v_kind_2648_);
v_val_2651_ = lean_ctor_get(v_a_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v_a_2650_, 1);
v_a_2652_ = lean_ctor_get(v___x_2649_, 1);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2649_);
v_fst_2653_ = lean_ctor_get(v_val_2651_, 0);
lean_inc(v_fst_2653_);
v_snd_2654_ = lean_ctor_get(v_val_2651_, 1);
lean_inc(v_snd_2654_);
lean_dec(v_val_2651_);
v___x_2655_ = l_Lean_Fmt_fmtWith(v_snd_2654_, v_fst_2653_, v_stx_2643_, v_a_2644_, v_a_2652_);
return v___x_2655_;
}
else
{
lean_object* v_a_2656_; uint8_t v___x_2657_; lean_object* v___x_2658_; 
lean_dec(v_a_2650_);
v_a_2656_ = lean_ctor_get(v___x_2649_, 1);
lean_inc(v_a_2656_);
lean_dec_ref(v___x_2649_);
v___x_2657_ = 1;
lean_inc_ref(v_stx_2643_);
v___x_2658_ = l_Lean_Fmt_fmtRaw(v___x_2657_, v_stx_2643_, v_a_2644_, v_a_2656_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v_a_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
v_a_2660_ = lean_ctor_get(v___x_2658_, 1);
lean_inc(v_a_2660_);
v___x_2661_ = 0;
v___x_2662_ = l_Lean_Syntax_getRange_x3f(v_stx_2643_, v___x_2661_);
lean_dec_ref_known(v_stx_2643_, 3);
if (lean_obj_tag(v___x_2662_) == 1)
{
lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2683_; 
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; lean_object* v_unused_2685_; 
v_unused_2684_ = lean_ctor_get(v___x_2658_, 1);
lean_dec(v_unused_2684_);
v_unused_2685_ = lean_ctor_get(v___x_2658_, 0);
lean_dec(v_unused_2685_);
v___x_2664_ = v___x_2658_;
v_isShared_2665_ = v_isSharedCheck_2683_;
goto v_resetjp_2663_;
}
else
{
lean_dec(v___x_2658_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2683_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_val_2666_; lean_object* v_toBacktrackableState_2667_; lean_object* v_shareCommonState_2668_; lean_object* v_freshTagId_2669_; lean_object* v_missingFormatters_2670_; lean_object* v_partialFormatters_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2682_; 
v_val_2666_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_val_2666_);
lean_dec_ref_known(v___x_2662_, 1);
v_toBacktrackableState_2667_ = lean_ctor_get(v_a_2660_, 0);
v_shareCommonState_2668_ = lean_ctor_get(v_a_2660_, 1);
v_freshTagId_2669_ = lean_ctor_get(v_a_2660_, 2);
v_missingFormatters_2670_ = lean_ctor_get(v_a_2660_, 3);
v_partialFormatters_2671_ = lean_ctor_get(v_a_2660_, 4);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_a_2660_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2673_ = v_a_2660_;
v_isShared_2674_ = v_isSharedCheck_2682_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_partialFormatters_2671_);
lean_inc(v_missingFormatters_2670_);
lean_inc(v_freshTagId_2669_);
lean_inc(v_shareCommonState_2668_);
lean_inc(v_toBacktrackableState_2667_);
lean_dec(v_a_2660_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2682_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2675_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Fmt_fmtWith_spec__0___redArg(v_missingFormatters_2670_, v_val_2666_, v_kind_2648_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 3, v___x_2675_);
v___x_2677_ = v___x_2673_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_toBacktrackableState_2667_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_shareCommonState_2668_);
lean_ctor_set(v_reuseFailAlloc_2681_, 2, v_freshTagId_2669_);
lean_ctor_set(v_reuseFailAlloc_2681_, 3, v___x_2675_);
lean_ctor_set(v_reuseFailAlloc_2681_, 4, v_partialFormatters_2671_);
v___x_2677_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 1, v___x_2677_);
v___x_2679_ = v___x_2664_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2659_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_dec(v___x_2662_);
lean_dec(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_kind_2648_);
return v___x_2658_;
}
}
else
{
lean_dec_ref_known(v_stx_2643_, 3);
lean_dec(v_kind_2648_);
return v___x_2658_;
}
}
}
case 2:
{
lean_object* v_val_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v_valDocs_2692_; lean_object* v___x_2693_; lean_object* v_valDoc_2694_; lean_object* v___x_2695_; 
v_val_2686_ = lean_ctor_get(v_stx_2643_, 1);
v___x_2687_ = lean_unsigned_to_nat(0u);
v___x_2688_ = lean_string_utf8_byte_size(v_val_2686_);
lean_inc_ref_n(v_val_2686_, 2);
v___x_2689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2689_, 0, v_val_2686_);
lean_ctor_set(v___x_2689_, 1, v___x_2687_);
lean_ctor_set(v___x_2689_, 2, v___x_2688_);
v___x_2690_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_2691_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2692_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v_val_2686_, v___x_2689_, v___x_2688_, v___x_2690_, v___x_2691_);
lean_dec_ref_known(v___x_2689_, 3);
v___x_2693_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2694_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2693_, v_valDocs_2692_);
v___x_2695_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2694_, v_stx_2643_, v_a_2645_);
lean_dec_ref_known(v_stx_2643_, 2);
return v___x_2695_;
}
default: 
{
lean_object* v_rawVal_2696_; lean_object* v_str_2697_; lean_object* v_startPos_2698_; lean_object* v_stopPos_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2715_; 
v_rawVal_2696_ = lean_ctor_get(v_stx_2643_, 1);
lean_inc_ref(v_rawVal_2696_);
v_str_2697_ = lean_ctor_get(v_rawVal_2696_, 0);
v_startPos_2698_ = lean_ctor_get(v_rawVal_2696_, 1);
v_stopPos_2699_ = lean_ctor_get(v_rawVal_2696_, 2);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_rawVal_2696_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2701_ = v_rawVal_2696_;
v_isShared_2702_ = v_isSharedCheck_2715_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_stopPos_2699_);
lean_inc(v_startPos_2698_);
lean_inc(v_str_2697_);
lean_dec(v_rawVal_2696_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2715_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2703_ = lean_string_utf8_extract(v_str_2697_, v_startPos_2698_, v_stopPos_2699_);
lean_dec(v_stopPos_2699_);
lean_dec(v_startPos_2698_);
lean_dec_ref(v_str_2697_);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_string_utf8_byte_size(v___x_2703_);
lean_inc_ref(v___x_2703_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 2, v___x_2705_);
lean_ctor_set(v___x_2701_, 1, v___x_2704_);
lean_ctor_set(v___x_2701_, 0, v___x_2703_);
v___x_2707_ = v___x_2701_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v_valDocs_2710_; lean_object* v___x_2711_; lean_object* v_valDoc_2712_; lean_object* v___x_2713_; 
v___x_2708_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__String_deindent_spec__0___closed__0);
v___x_2709_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v_valDocs_2710_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtRawAsInSource_spec__0___redArg(v___x_2703_, v___x_2707_, v___x_2705_, v___x_2708_, v___x_2709_);
lean_dec_ref(v___x_2707_);
v___x_2711_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v_valDoc_2712_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2711_, v_valDocs_2710_);
v___x_2713_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_valDoc_2712_, v_stx_2643_, v_a_2645_);
lean_dec_ref_known(v_stx_2643_, 4);
return v___x_2713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt___boxed(lean_object* v_stx_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_Fmt_fmt(v_stx_2716_, v_a_2717_, v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
uint8_t v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = 0;
v___x_2725_ = l_Lean_Syntax_getRange_x3f(v_a_2721_, v___x_2724_);
if (lean_obj_tag(v___x_2725_) == 1)
{
lean_object* v_val_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2791_; 
v_val_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2791_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_val_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2791_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v_resolveChoiceNode_2730_; lean_object* v___x_2731_; 
v_resolveChoiceNode_2730_ = lean_ctor_get(v_a_2722_, 2);
lean_inc_ref(v_resolveChoiceNode_2730_);
v___x_2731_ = lean_apply_1(v_resolveChoiceNode_2730_, v_val_2726_);
if (lean_obj_tag(v___x_2731_) == 1)
{
lean_object* v_val_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2778_; 
lean_del_object(v___x_2728_);
v_val_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2778_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_val_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2778_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v_stx_2736_; lean_object* v_chosenAltIdx_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2777_; 
v_stx_2736_ = lean_ctor_get(v_val_2732_, 0);
v_chosenAltIdx_2737_ = lean_ctor_get(v_val_2732_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_val_2732_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2739_ = v_val_2732_;
v_isShared_2740_ = v_isSharedCheck_2777_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_chosenAltIdx_2737_);
lean_inc(v_stx_2736_);
lean_dec(v_val_2732_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2777_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2741_ = l_Lean_Syntax_getNumArgs(v_stx_2736_);
lean_dec(v_stx_2736_);
v___x_2742_ = l_Lean_Syntax_getNumArgs(v_a_2721_);
v___x_2743_ = lean_nat_dec_eq(v___x_2741_, v___x_2742_);
lean_dec(v___x_2742_);
lean_dec(v___x_2741_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_dec(v_chosenAltIdx_2737_);
v___x_2744_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2745_ = lean_box(0);
lean_inc(v_a_2721_);
v___x_2746_ = l_Lean_Syntax_formatStx(v_a_2721_, v___x_2745_, v___x_2743_);
v___x_2747_ = l_Std_Format_defWidth;
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = l_Std_Format_pretty(v___x_2746_, v___x_2747_, v___x_2748_, v___x_2748_);
v___x_2750_ = lean_string_append(v___x_2744_, v___x_2749_);
lean_dec_ref(v___x_2749_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 1);
lean_ctor_set(v___x_2739_, 1, v___x_2750_);
lean_ctor_set(v___x_2739_, 0, v_a_2721_);
v___x_2752_ = v___x_2739_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2721_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2754_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set_tag(v___x_2734_, 2);
lean_ctor_set(v___x_2734_, 0, v___x_2752_);
v___x_2754_ = v___x_2734_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v_a_2723_);
return v___x_2755_;
}
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2758_ = l_Lean_Syntax_getArgs(v_a_2721_);
v___x_2759_ = lean_array_get_size(v___x_2758_);
v___x_2760_ = lean_nat_dec_lt(v_chosenAltIdx_2737_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
lean_dec_ref(v___x_2758_);
lean_dec(v_chosenAltIdx_2737_);
v___x_2761_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2762_ = lean_box(0);
lean_inc(v_a_2721_);
v___x_2763_ = l_Lean_Syntax_formatStx(v_a_2721_, v___x_2762_, v___x_2760_);
v___x_2764_ = l_Std_Format_defWidth;
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = l_Std_Format_pretty(v___x_2763_, v___x_2764_, v___x_2765_, v___x_2765_);
v___x_2767_ = lean_string_append(v___x_2761_, v___x_2766_);
lean_dec_ref(v___x_2766_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 1);
lean_ctor_set(v___x_2739_, 1, v___x_2767_);
lean_ctor_set(v___x_2739_, 0, v_a_2721_);
v___x_2769_ = v___x_2739_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2721_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2771_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set_tag(v___x_2734_, 2);
lean_ctor_set(v___x_2734_, 0, v___x_2769_);
v___x_2771_ = v___x_2734_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v_a_2723_);
return v___x_2772_;
}
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
lean_del_object(v___x_2739_);
lean_del_object(v___x_2734_);
lean_dec(v_a_2721_);
v___x_2775_ = lean_array_fget(v___x_2758_, v_chosenAltIdx_2737_);
lean_dec(v_chosenAltIdx_2737_);
lean_dec_ref(v___x_2758_);
v___x_2776_ = l_Lean_Fmt_fmt(v___x_2775_, v_a_2722_, v_a_2723_);
return v___x_2776_;
}
}
}
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
lean_dec(v___x_2731_);
v___x_2779_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2780_ = lean_box(0);
lean_inc(v_a_2721_);
v___x_2781_ = l_Lean_Syntax_formatStx(v_a_2721_, v___x_2780_, v___x_2724_);
v___x_2782_ = l_Std_Format_defWidth;
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = l_Std_Format_pretty(v___x_2781_, v___x_2782_, v___x_2783_, v___x_2783_);
v___x_2785_ = lean_string_append(v___x_2779_, v___x_2784_);
lean_dec_ref(v___x_2784_);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v_a_2721_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set_tag(v___x_2728_, 2);
lean_ctor_set(v___x_2728_, 0, v___x_2786_);
v___x_2788_ = v___x_2728_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v_a_2723_);
return v___x_2789_;
}
}
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
lean_dec(v___x_2725_);
v___x_2792_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___closed__0));
v___x_2793_ = lean_box(0);
lean_inc(v_a_2721_);
v___x_2794_ = l_Lean_Syntax_formatStx(v_a_2721_, v___x_2793_, v___x_2724_);
v___x_2795_ = l_Std_Format_defWidth;
v___x_2796_ = lean_unsigned_to_nat(0u);
v___x_2797_ = l_Std_Format_pretty(v___x_2794_, v___x_2795_, v___x_2796_, v___x_2796_);
v___x_2798_ = lean_string_append(v___x_2792_, v___x_2797_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_a_2721_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v_a_2723_);
return v___x_2801_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode___boxed(lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2805_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = l_Lean_Fmt_instInhabitedState_default;
v___x_2807_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v___x_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(lean_object* v_msg_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_obj_once(&l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0, &l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2___closed__0);
v___x_2811_ = lean_panic_fn_borrowed(v___x_2810_, v_msg_2809_);
return v___x_2811_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_2812_){
_start:
{
lean_object* v_aPtr_2813_; lean_object* v_bPtr_2814_; size_t v_ptr_2815_; size_t v_ptr_2816_; uint64_t v___x_2817_; uint64_t v___x_2818_; uint64_t v___x_2819_; uint64_t v___x_2820_; uint64_t v___x_2821_; 
v_aPtr_2813_ = lean_ctor_get(v_x_2812_, 0);
v_bPtr_2814_ = lean_ctor_get(v_x_2812_, 1);
v_ptr_2815_ = lean_ctor_get_usize(v_aPtr_2813_, 1);
v_ptr_2816_ = lean_ctor_get_usize(v_bPtr_2814_, 1);
v___x_2817_ = 0ULL;
v___x_2818_ = lean_usize_to_uint64(v_ptr_2815_);
v___x_2819_ = lean_uint64_mix_hash(v___x_2817_, v___x_2818_);
v___x_2820_ = lean_usize_to_uint64(v_ptr_2816_);
v___x_2821_ = lean_uint64_mix_hash(v___x_2819_, v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_2822_){
_start:
{
uint64_t v_res_2823_; lean_object* v_r_2824_; 
v_res_2823_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_x_2822_);
lean_dec_ref(v_x_2822_);
v_r_2824_ = lean_box_uint64(v_res_2823_);
return v_r_2824_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_x_2825_, lean_object* v_x_2826_){
_start:
{
lean_object* v_aPtr_2827_; lean_object* v_aPtr_2828_; lean_object* v_bPtr_2829_; lean_object* v_bPtr_2830_; size_t v_ptr_2831_; size_t v_ptr_2832_; uint8_t v___x_2833_; 
v_aPtr_2827_ = lean_ctor_get(v_x_2825_, 0);
v_aPtr_2828_ = lean_ctor_get(v_x_2826_, 0);
v_bPtr_2829_ = lean_ctor_get(v_x_2825_, 1);
v_bPtr_2830_ = lean_ctor_get(v_x_2826_, 1);
v_ptr_2831_ = lean_ctor_get_usize(v_aPtr_2827_, 1);
v_ptr_2832_ = lean_ctor_get_usize(v_aPtr_2828_, 1);
v___x_2833_ = lean_usize_dec_eq(v_ptr_2831_, v_ptr_2832_);
if (v___x_2833_ == 0)
{
return v___x_2833_;
}
else
{
size_t v_ptr_2834_; size_t v_ptr_2835_; uint8_t v___x_2836_; 
v_ptr_2834_ = lean_ctor_get_usize(v_bPtr_2829_, 1);
v_ptr_2835_ = lean_ctor_get_usize(v_bPtr_2830_, 1);
v___x_2836_ = lean_usize_dec_eq(v_ptr_2834_, v_ptr_2835_);
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
uint8_t v_res_2839_; lean_object* v_r_2840_; 
v_res_2839_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_x_2837_, v_x_2838_);
lean_dec_ref(v_x_2838_);
lean_dec_ref(v_x_2837_);
v_r_2840_ = lean_box(v_res_2839_);
return v_r_2840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_a_2841_, lean_object* v_x_2842_){
_start:
{
if (lean_obj_tag(v_x_2842_) == 0)
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_box(0);
return v___x_2843_;
}
else
{
lean_object* v_key_2844_; lean_object* v_value_2845_; lean_object* v_tail_2846_; uint8_t v___x_2847_; 
v_key_2844_ = lean_ctor_get(v_x_2842_, 0);
v_value_2845_ = lean_ctor_get(v_x_2842_, 1);
v_tail_2846_ = lean_ctor_get(v_x_2842_, 2);
v___x_2847_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2844_, v_a_2841_);
if (v___x_2847_ == 0)
{
v_x_2842_ = v_tail_2846_;
goto _start;
}
else
{
lean_object* v___x_2849_; 
lean_inc(v_value_2845_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v_value_2845_);
return v___x_2849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_2850_, lean_object* v_x_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2850_, v_x_2851_);
lean_dec(v_x_2851_);
lean_dec_ref(v_a_2850_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(lean_object* v_m_2853_, lean_object* v_a_2854_){
_start:
{
lean_object* v_buckets_2855_; lean_object* v___x_2856_; uint64_t v___x_2857_; uint64_t v___x_2858_; uint64_t v___x_2859_; uint64_t v_fold_2860_; uint64_t v___x_2861_; uint64_t v___x_2862_; uint64_t v___x_2863_; size_t v___x_2864_; size_t v___x_2865_; size_t v___x_2866_; size_t v___x_2867_; size_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_buckets_2855_ = lean_ctor_get(v_m_2853_, 1);
v___x_2856_ = lean_array_get_size(v_buckets_2855_);
v___x_2857_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2854_);
v___x_2858_ = 32ULL;
v___x_2859_ = lean_uint64_shift_right(v___x_2857_, v___x_2858_);
v_fold_2860_ = lean_uint64_xor(v___x_2857_, v___x_2859_);
v___x_2861_ = 16ULL;
v___x_2862_ = lean_uint64_shift_right(v_fold_2860_, v___x_2861_);
v___x_2863_ = lean_uint64_xor(v_fold_2860_, v___x_2862_);
v___x_2864_ = lean_uint64_to_usize(v___x_2863_);
v___x_2865_ = lean_usize_of_nat(v___x_2856_);
v___x_2866_ = ((size_t)1ULL);
v___x_2867_ = lean_usize_sub(v___x_2865_, v___x_2866_);
v___x_2868_ = lean_usize_land(v___x_2864_, v___x_2867_);
v___x_2869_ = lean_array_uget_borrowed(v_buckets_2855_, v___x_2868_);
v___x_2870_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_2854_, v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_2871_, v_a_2872_);
lean_dec_ref(v_a_2872_);
lean_dec_ref(v_m_2871_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(lean_object* v_x_2874_, lean_object* v_x_2875_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
return v_x_2874_;
}
else
{
lean_object* v_key_2876_; lean_object* v_value_2877_; lean_object* v_tail_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2901_; 
v_key_2876_ = lean_ctor_get(v_x_2875_, 0);
v_value_2877_ = lean_ctor_get(v_x_2875_, 1);
v_tail_2878_ = lean_ctor_get(v_x_2875_, 2);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_x_2875_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2880_ = v_x_2875_;
v_isShared_2881_ = v_isSharedCheck_2901_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_tail_2878_);
lean_inc(v_value_2877_);
lean_inc(v_key_2876_);
lean_dec(v_x_2875_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2901_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; uint64_t v___x_2883_; uint64_t v___x_2884_; uint64_t v___x_2885_; uint64_t v_fold_2886_; uint64_t v___x_2887_; uint64_t v___x_2888_; uint64_t v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; size_t v___x_2892_; size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2882_ = lean_array_get_size(v_x_2874_);
v___x_2883_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_key_2876_);
v___x_2884_ = 32ULL;
v___x_2885_ = lean_uint64_shift_right(v___x_2883_, v___x_2884_);
v_fold_2886_ = lean_uint64_xor(v___x_2883_, v___x_2885_);
v___x_2887_ = 16ULL;
v___x_2888_ = lean_uint64_shift_right(v_fold_2886_, v___x_2887_);
v___x_2889_ = lean_uint64_xor(v_fold_2886_, v___x_2888_);
v___x_2890_ = lean_uint64_to_usize(v___x_2889_);
v___x_2891_ = lean_usize_of_nat(v___x_2882_);
v___x_2892_ = ((size_t)1ULL);
v___x_2893_ = lean_usize_sub(v___x_2891_, v___x_2892_);
v___x_2894_ = lean_usize_land(v___x_2890_, v___x_2893_);
v___x_2895_ = lean_array_uget_borrowed(v_x_2874_, v___x_2894_);
lean_inc(v___x_2895_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 2, v___x_2895_);
v___x_2897_ = v___x_2880_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_key_2876_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_value_2877_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_array_uset(v_x_2874_, v___x_2894_, v___x_2897_);
v_x_2874_ = v___x_2898_;
v_x_2875_ = v_tail_2878_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(lean_object* v_i_2902_, lean_object* v_source_2903_, lean_object* v_target_2904_){
_start:
{
lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = lean_array_get_size(v_source_2903_);
v___x_2906_ = lean_nat_dec_lt(v_i_2902_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_dec_ref(v_source_2903_);
lean_dec(v_i_2902_);
return v_target_2904_;
}
else
{
lean_object* v_es_2907_; lean_object* v___x_2908_; lean_object* v_source_2909_; lean_object* v_target_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v_es_2907_ = lean_array_fget(v_source_2903_, v_i_2902_);
v___x_2908_ = lean_box(0);
v_source_2909_ = lean_array_fset(v_source_2903_, v_i_2902_, v___x_2908_);
v_target_2910_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_target_2904_, v_es_2907_);
v___x_2911_ = lean_unsigned_to_nat(1u);
v___x_2912_ = lean_nat_add(v_i_2902_, v___x_2911_);
lean_dec(v_i_2902_);
v_i_2902_ = v___x_2912_;
v_source_2903_ = v_source_2909_;
v_target_2904_ = v_target_2910_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(lean_object* v_data_2914_){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v_nbuckets_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2915_ = lean_array_get_size(v_data_2914_);
v___x_2916_ = lean_unsigned_to_nat(2u);
v_nbuckets_2917_ = lean_nat_mul(v___x_2915_, v___x_2916_);
v___x_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = lean_box(0);
v___x_2920_ = lean_mk_array(v_nbuckets_2917_, v___x_2919_);
v___x_2921_ = lean_array_propagate_mark(v_data_2914_, v___x_2920_);
v___x_2922_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v___x_2918_, v_data_2914_, v___x_2921_);
return v___x_2922_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(lean_object* v_a_2923_, lean_object* v_x_2924_){
_start:
{
if (lean_obj_tag(v_x_2924_) == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = 0;
return v___x_2925_;
}
else
{
lean_object* v_key_2926_; lean_object* v_tail_2927_; uint8_t v___x_2928_; 
v_key_2926_ = lean_ctor_get(v_x_2924_, 0);
v_tail_2927_ = lean_ctor_get(v_x_2924_, 2);
v___x_2928_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2926_, v_a_2923_);
if (v___x_2928_ == 0)
{
v_x_2924_ = v_tail_2927_;
goto _start;
}
else
{
return v___x_2928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg___boxed(lean_object* v_a_2930_, lean_object* v_x_2931_){
_start:
{
uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_res_2932_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2930_, v_x_2931_);
lean_dec(v_x_2931_);
lean_dec_ref(v_a_2930_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(lean_object* v_a_2934_, lean_object* v_b_2935_, lean_object* v_x_2936_){
_start:
{
if (lean_obj_tag(v_x_2936_) == 0)
{
lean_dec(v_b_2935_);
lean_dec_ref(v_a_2934_);
return v_x_2936_;
}
else
{
lean_object* v_key_2937_; lean_object* v_value_2938_; lean_object* v_tail_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2951_; 
v_key_2937_ = lean_ctor_get(v_x_2936_, 0);
v_value_2938_ = lean_ctor_get(v_x_2936_, 1);
v_tail_2939_ = lean_ctor_get(v_x_2936_, 2);
v_isSharedCheck_2951_ = !lean_is_exclusive(v_x_2936_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2941_ = v_x_2936_;
v_isShared_2942_ = v_isSharedCheck_2951_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_tail_2939_);
lean_inc(v_value_2938_);
lean_inc(v_key_2937_);
lean_dec(v_x_2936_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2951_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
uint8_t v___x_2943_; 
v___x_2943_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5_spec__6(v_key_2937_, v_a_2934_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2934_, v_b_2935_, v_tail_2939_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 2, v___x_2944_);
v___x_2946_ = v___x_2941_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_key_2937_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_value_2938_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
else
{
lean_object* v___x_2949_; 
lean_dec(v_value_2938_);
lean_dec(v_key_2937_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_b_2935_);
lean_ctor_set(v___x_2941_, 0, v_a_2934_);
v___x_2949_ = v___x_2941_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2934_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_b_2935_);
lean_ctor_set(v_reuseFailAlloc_2950_, 2, v_tail_2939_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(lean_object* v_m_2952_, lean_object* v_a_2953_, lean_object* v_b_2954_){
_start:
{
lean_object* v_size_2955_; lean_object* v_buckets_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2999_; 
v_size_2955_ = lean_ctor_get(v_m_2952_, 0);
v_buckets_2956_ = lean_ctor_get(v_m_2952_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_m_2952_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2958_ = v_m_2952_;
v_isShared_2959_ = v_isSharedCheck_2999_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_buckets_2956_);
lean_inc(v_size_2955_);
lean_dec(v_m_2952_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2999_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; uint64_t v___x_2961_; uint64_t v___x_2962_; uint64_t v___x_2963_; uint64_t v_fold_2964_; uint64_t v___x_2965_; uint64_t v___x_2966_; uint64_t v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; lean_object* v_bkt_2973_; uint8_t v___x_2974_; 
v___x_2960_ = lean_array_get_size(v_buckets_2956_);
v___x_2961_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__4(v_a_2953_);
v___x_2962_ = 32ULL;
v___x_2963_ = lean_uint64_shift_right(v___x_2961_, v___x_2962_);
v_fold_2964_ = lean_uint64_xor(v___x_2961_, v___x_2963_);
v___x_2965_ = 16ULL;
v___x_2966_ = lean_uint64_shift_right(v_fold_2964_, v___x_2965_);
v___x_2967_ = lean_uint64_xor(v_fold_2964_, v___x_2966_);
v___x_2968_ = lean_uint64_to_usize(v___x_2967_);
v___x_2969_ = lean_usize_of_nat(v___x_2960_);
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_sub(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_usize_land(v___x_2968_, v___x_2971_);
v_bkt_2973_ = lean_array_uget_borrowed(v_buckets_2956_, v___x_2972_);
v___x_2974_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_2953_, v_bkt_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v_size_x27_2976_; lean_object* v___x_2977_; lean_object* v_buckets_x27_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2975_ = lean_unsigned_to_nat(1u);
v_size_x27_2976_ = lean_nat_add(v_size_2955_, v___x_2975_);
lean_dec(v_size_2955_);
lean_inc(v_bkt_2973_);
v___x_2977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2977_, 0, v_a_2953_);
lean_ctor_set(v___x_2977_, 1, v_b_2954_);
lean_ctor_set(v___x_2977_, 2, v_bkt_2973_);
v_buckets_x27_2978_ = lean_array_uset(v_buckets_2956_, v___x_2972_, v___x_2977_);
v___x_2979_ = lean_unsigned_to_nat(4u);
v___x_2980_ = lean_nat_mul(v_size_x27_2976_, v___x_2979_);
v___x_2981_ = lean_unsigned_to_nat(3u);
v___x_2982_ = lean_nat_div(v___x_2980_, v___x_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_array_get_size(v_buckets_x27_2978_);
v___x_2984_ = lean_nat_dec_le(v___x_2982_, v___x_2983_);
lean_dec(v___x_2982_);
if (v___x_2984_ == 0)
{
lean_object* v_val_2985_; lean_object* v___x_2987_; 
v_val_2985_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_buckets_x27_2978_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v_val_2985_);
lean_ctor_set(v___x_2958_, 0, v_size_x27_2976_);
v___x_2987_ = v___x_2958_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_size_x27_2976_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_val_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
else
{
lean_object* v___x_2990_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v_buckets_x27_2978_);
lean_ctor_set(v___x_2958_, 0, v_size_x27_2976_);
v___x_2990_ = v___x_2958_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_size_x27_2976_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_buckets_x27_2978_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
else
{
lean_object* v___x_2992_; lean_object* v_buckets_x27_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
lean_inc(v_bkt_2973_);
v___x_2992_ = lean_box(0);
v_buckets_x27_2993_ = lean_array_uset(v_buckets_2956_, v___x_2972_, v___x_2992_);
v___x_2994_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_2953_, v_b_2954_, v_bkt_2973_);
v___x_2995_ = lean_array_uset(v_buckets_x27_2993_, v___x_2972_, v___x_2994_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v___x_2995_);
v___x_2997_ = v___x_2958_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_size_2955_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(lean_object* v_a_3000_, lean_object* v_b_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v___y_3008_; lean_object* v_da1_3013_; lean_object* v_da2_3014_; lean_object* v_db1_3015_; lean_object* v_db2_3016_; lean_object* v___y_3017_; lean_object* v_sa_3024_; lean_object* v_sb_3025_; lean_object* v___y_3026_; 
switch(lean_obj_tag(v_a_3000_))
{
case 0:
{
if (lean_obj_tag(v_b_3001_) == 0)
{
uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = 1;
v___x_3031_ = lean_box(v___x_3030_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v_a_3002_);
return v___x_3032_;
}
else
{
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 1:
{
if (lean_obj_tag(v_b_3001_) == 1)
{
lean_object* v_f_3033_; lean_object* v_f_3034_; 
v_f_3033_ = lean_ctor_get(v_a_3000_, 1);
lean_inc_ref(v_f_3033_);
lean_dec_ref_known(v_a_3000_, 2);
v_f_3034_ = lean_ctor_get(v_b_3001_, 1);
lean_inc_ref(v_f_3034_);
lean_dec_ref_known(v_b_3001_, 2);
v_sa_3024_ = v_f_3033_;
v_sb_3025_ = v_f_3034_;
v___y_3026_ = v_a_3002_;
goto v___jp_3023_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 2:
{
if (lean_obj_tag(v_b_3001_) == 2)
{
lean_object* v_s_3035_; lean_object* v_s_3036_; 
v_s_3035_ = lean_ctor_get(v_a_3000_, 1);
lean_inc_ref(v_s_3035_);
lean_dec_ref_known(v_a_3000_, 2);
v_s_3036_ = lean_ctor_get(v_b_3001_, 1);
lean_inc_ref(v_s_3036_);
lean_dec_ref_known(v_b_3001_, 2);
v_sa_3024_ = v_s_3035_;
v_sb_3025_ = v_s_3036_;
v___y_3026_ = v_a_3002_;
goto v___jp_3023_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 3:
{
if (lean_obj_tag(v_b_3001_) == 3)
{
lean_object* v_id_3037_; lean_object* v_d_3038_; lean_object* v_id_3039_; lean_object* v_d_3040_; uint8_t v___x_3041_; 
v_id_3037_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_id_3037_);
v_d_3038_ = lean_ctor_get(v_a_3000_, 2);
lean_inc(v_d_3038_);
lean_dec_ref_known(v_a_3000_, 3);
v_id_3039_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_id_3039_);
v_d_3040_ = lean_ctor_get(v_b_3001_, 2);
lean_inc(v_d_3040_);
lean_dec_ref_known(v_b_3001_, 3);
v___x_3041_ = lean_nat_dec_eq(v_id_3037_, v_id_3039_);
lean_dec(v_id_3039_);
lean_dec(v_id_3037_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_dec(v_d_3040_);
lean_dec(v_d_3038_);
v___x_3042_ = lean_box(v___x_3041_);
v___x_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v_a_3002_);
return v___x_3043_;
}
else
{
lean_object* v___x_3044_; 
v___x_3044_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3038_, v_d_3040_, v_a_3002_);
return v___x_3044_;
}
}
else
{
lean_dec_ref_known(v_a_3000_, 3);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 4:
{
if (lean_obj_tag(v_b_3001_) == 4)
{
lean_object* v_d_3045_; lean_object* v_d_3046_; lean_object* v___x_3047_; 
v_d_3045_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3045_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3046_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3046_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3047_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3045_, v_d_3046_, v_a_3002_);
return v___x_3047_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 5:
{
if (lean_obj_tag(v_b_3001_) == 5)
{
lean_object* v_d_3048_; lean_object* v_d_3049_; lean_object* v___x_3050_; 
v_d_3048_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3048_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3049_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3049_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3050_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3048_, v_d_3049_, v_a_3002_);
return v___x_3050_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 6:
{
if (lean_obj_tag(v_b_3001_) == 6)
{
lean_object* v_n_3051_; uint8_t v_isCumulative_3052_; lean_object* v_d_3053_; lean_object* v_n_3054_; uint8_t v_isCumulative_3055_; lean_object* v_d_3056_; uint8_t v___y_3058_; uint8_t v___x_3060_; 
v_n_3051_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_n_3051_);
v_isCumulative_3052_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*3 + 7);
v_d_3053_ = lean_ctor_get(v_a_3000_, 2);
lean_inc(v_d_3053_);
lean_dec_ref_known(v_a_3000_, 3);
v_n_3054_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_n_3054_);
v_isCumulative_3055_ = lean_ctor_get_uint8(v_b_3001_, sizeof(void*)*3 + 7);
v_d_3056_ = lean_ctor_get(v_b_3001_, 2);
lean_inc(v_d_3056_);
lean_dec_ref_known(v_b_3001_, 3);
v___x_3060_ = lean_nat_dec_eq(v_n_3051_, v_n_3054_);
lean_dec(v_n_3054_);
lean_dec(v_n_3051_);
if (v___x_3060_ == 0)
{
lean_dec(v_d_3056_);
lean_dec(v_d_3053_);
goto v___jp_3003_;
}
else
{
if (v_isCumulative_3055_ == 0)
{
if (v_isCumulative_3052_ == 0)
{
v___y_3058_ = v___x_3060_;
goto v___jp_3057_;
}
else
{
lean_dec(v_d_3056_);
lean_dec(v_d_3053_);
goto v___jp_3003_;
}
}
else
{
v___y_3058_ = v_isCumulative_3052_;
goto v___jp_3057_;
}
}
v___jp_3057_:
{
if (v___y_3058_ == 0)
{
lean_dec(v_d_3056_);
lean_dec(v_d_3053_);
goto v___jp_3003_;
}
else
{
lean_object* v___x_3059_; 
v___x_3059_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3053_, v_d_3056_, v_a_3002_);
return v___x_3059_;
}
}
}
else
{
lean_dec_ref_known(v_a_3000_, 3);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 7:
{
if (lean_obj_tag(v_b_3001_) == 7)
{
lean_object* v_d_3061_; lean_object* v_d_3062_; lean_object* v___x_3063_; 
v_d_3061_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3061_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3062_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3062_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3063_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3061_, v_d_3062_, v_a_3002_);
return v___x_3063_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 8:
{
if (lean_obj_tag(v_b_3001_) == 8)
{
uint8_t v_onlyNonCumulative_3064_; 
v_onlyNonCumulative_3064_ = lean_ctor_get_uint8(v_b_3001_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_3064_ == 0)
{
uint8_t v_onlyNonCumulative_3065_; 
v_onlyNonCumulative_3065_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_3065_ == 0)
{
lean_object* v_d_3066_; lean_object* v_d_3067_; lean_object* v___x_3068_; 
v_d_3066_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3066_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3067_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3067_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3068_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3066_, v_d_3067_, v_a_3002_);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec_ref_known(v_b_3001_, 2);
lean_dec_ref_known(v_a_3000_, 2);
v___x_3069_ = lean_box(v_onlyNonCumulative_3064_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v_a_3002_);
return v___x_3070_;
}
}
else
{
uint8_t v_onlyNonCumulative_3071_; 
v_onlyNonCumulative_3071_ = lean_ctor_get_uint8(v_a_3000_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_3071_ == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec_ref_known(v_b_3001_, 2);
lean_dec_ref_known(v_a_3000_, 2);
v___x_3072_ = lean_box(v_onlyNonCumulative_3071_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v_a_3002_);
return v___x_3073_;
}
else
{
lean_object* v_d_3074_; lean_object* v_d_3075_; lean_object* v___x_3076_; 
v_d_3074_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3074_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3075_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3075_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3076_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3074_, v_d_3075_, v_a_3002_);
return v___x_3076_;
}
}
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 9:
{
if (lean_obj_tag(v_b_3001_) == 9)
{
lean_object* v_d_3077_; lean_object* v_d_3078_; lean_object* v___x_3079_; 
v_d_3077_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3077_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3078_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3078_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3079_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3077_, v_d_3078_, v_a_3002_);
return v___x_3079_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 10:
{
if (lean_obj_tag(v_b_3001_) == 10)
{
lean_object* v_d_3080_; lean_object* v_d_3081_; lean_object* v___x_3082_; 
v_d_3080_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3080_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3081_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3081_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3082_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3080_, v_d_3081_, v_a_3002_);
return v___x_3082_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 11:
{
if (lean_obj_tag(v_b_3001_) == 11)
{
lean_object* v_d_3083_; lean_object* v_d_3084_; lean_object* v___x_3085_; 
v_d_3083_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_d_3083_);
lean_dec_ref_known(v_a_3000_, 2);
v_d_3084_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_d_3084_);
lean_dec_ref_known(v_b_3001_, 2);
v___x_3085_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3083_, v_d_3084_, v_a_3002_);
return v___x_3085_;
}
else
{
lean_dec_ref_known(v_a_3000_, 2);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 12:
{
if (lean_obj_tag(v_b_3001_) == 12)
{
lean_object* v_p_3086_; lean_object* v_p_3087_; lean_object* v_d_3088_; lean_object* v_d_3089_; lean_object* v_id_3090_; lean_object* v_id_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3101_; 
v_p_3086_ = lean_ctor_get(v_a_3000_, 1);
lean_inc_ref(v_p_3086_);
v_p_3087_ = lean_ctor_get(v_b_3001_, 1);
lean_inc_ref(v_p_3087_);
v_d_3088_ = lean_ctor_get(v_a_3000_, 2);
lean_inc(v_d_3088_);
lean_dec_ref_known(v_a_3000_, 3);
v_d_3089_ = lean_ctor_get(v_b_3001_, 2);
lean_inc(v_d_3089_);
lean_dec_ref_known(v_b_3001_, 3);
v_id_3090_ = lean_ctor_get(v_p_3086_, 1);
lean_inc(v_id_3090_);
lean_dec_ref(v_p_3086_);
v_id_3091_ = lean_ctor_get(v_p_3087_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_p_3087_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v_p_3087_, 0);
lean_dec(v_unused_3102_);
v___x_3093_ = v_p_3087_;
v_isShared_3094_ = v_isSharedCheck_3101_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_id_3091_);
lean_dec(v_p_3087_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3101_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
uint8_t v___x_3095_; 
v___x_3095_ = lean_name_eq(v_id_3090_, v_id_3091_);
lean_dec(v_id_3091_);
lean_dec(v_id_3090_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
lean_dec(v_d_3089_);
lean_dec(v_d_3088_);
v___x_3096_ = lean_box(v___x_3095_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 1, v_a_3002_);
lean_ctor_set(v___x_3093_, 0, v___x_3096_);
v___x_3098_ = v___x_3093_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_a_3002_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
else
{
lean_object* v___x_3100_; 
lean_del_object(v___x_3093_);
v___x_3100_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3088_, v_d_3089_, v_a_3002_);
return v___x_3100_;
}
}
}
else
{
lean_dec_ref_known(v_a_3000_, 3);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 13:
{
if (lean_obj_tag(v_b_3001_) == 13)
{
lean_object* v_cost_3103_; lean_object* v_d_3104_; lean_object* v_cost_3105_; lean_object* v_d_3106_; uint8_t v___x_3107_; 
v_cost_3103_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_cost_3103_);
v_d_3104_ = lean_ctor_get(v_a_3000_, 2);
lean_inc(v_d_3104_);
lean_dec_ref_known(v_a_3000_, 3);
v_cost_3105_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_cost_3105_);
v_d_3106_ = lean_ctor_get(v_b_3001_, 2);
lean_inc(v_d_3106_);
lean_dec_ref_known(v_b_3001_, 3);
v___x_3107_ = l_Lean_Fmt_instBEqDefaultCost_beq___redArg(v_cost_3103_, v_cost_3105_);
lean_dec(v_cost_3105_);
lean_dec(v_cost_3103_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec(v_d_3106_);
lean_dec(v_d_3104_);
v___x_3108_ = lean_box(v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v_a_3002_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; 
v___x_3110_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_d_3104_, v_d_3106_, v_a_3002_);
return v___x_3110_;
}
}
else
{
lean_dec_ref_known(v_a_3000_, 3);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
case 14:
{
if (lean_obj_tag(v_b_3001_) == 14)
{
lean_object* v_a_3111_; lean_object* v_b_3112_; lean_object* v_a_3113_; lean_object* v_b_3114_; 
v_a_3111_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_a_3111_);
v_b_3112_ = lean_ctor_get(v_a_3000_, 2);
lean_inc(v_b_3112_);
lean_dec_ref_known(v_a_3000_, 3);
v_a_3113_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_a_3113_);
v_b_3114_ = lean_ctor_get(v_b_3001_, 2);
lean_inc(v_b_3114_);
lean_dec_ref_known(v_b_3001_, 3);
v_da1_3013_ = v_a_3111_;
v_da2_3014_ = v_b_3112_;
v_db1_3015_ = v_a_3113_;
v_db2_3016_ = v_b_3114_;
v___y_3017_ = v_a_3002_;
goto v___jp_3012_;
}
else
{
lean_dec_ref_known(v_a_3000_, 3);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
default: 
{
if (lean_obj_tag(v_b_3001_) == 15)
{
lean_object* v_a_3115_; lean_object* v_b_3116_; lean_object* v_a_3117_; lean_object* v_b_3118_; 
v_a_3115_ = lean_ctor_get(v_a_3000_, 1);
lean_inc(v_a_3115_);
v_b_3116_ = lean_ctor_get(v_a_3000_, 2);
lean_inc(v_b_3116_);
lean_dec_ref_known(v_a_3000_, 3);
v_a_3117_ = lean_ctor_get(v_b_3001_, 1);
lean_inc(v_a_3117_);
v_b_3118_ = lean_ctor_get(v_b_3001_, 2);
lean_inc(v_b_3118_);
lean_dec_ref_known(v_b_3001_, 3);
v_da1_3013_ = v_a_3115_;
v_da2_3014_ = v_b_3116_;
v_db1_3015_ = v_a_3117_;
v_db2_3016_ = v_b_3118_;
v___y_3017_ = v_a_3002_;
goto v___jp_3012_;
}
else
{
lean_dec_ref_known(v_a_3000_, 3);
lean_dec(v_b_3001_);
v___y_3008_ = v_a_3002_;
goto v___jp_3007_;
}
}
}
v___jp_3003_:
{
uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = 0;
v___x_3005_ = lean_box(v___x_3004_);
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
lean_ctor_set(v___x_3006_, 1, v_a_3002_);
return v___x_3006_;
}
v___jp_3007_:
{
uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = 0;
v___x_3010_ = lean_box(v___x_3009_);
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___y_3008_);
return v___x_3011_;
}
v___jp_3012_:
{
lean_object* v___x_3018_; lean_object* v_fst_3019_; uint8_t v___x_3020_; 
v___x_3018_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da1_3013_, v_db1_3015_, v___y_3017_);
v_fst_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_fst_3019_);
v___x_3020_ = lean_unbox(v_fst_3019_);
lean_dec(v_fst_3019_);
if (v___x_3020_ == 0)
{
lean_dec(v_db2_3016_);
lean_dec(v_da2_3014_);
return v___x_3018_;
}
else
{
lean_object* v_snd_3021_; lean_object* v___x_3022_; 
v_snd_3021_ = lean_ctor_get(v___x_3018_, 1);
lean_inc(v_snd_3021_);
lean_dec_ref(v___x_3018_);
v___x_3022_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_da2_3014_, v_db2_3016_, v_snd_3021_);
return v___x_3022_;
}
}
v___jp_3023_:
{
uint8_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_string_dec_eq(v_sa_3024_, v_sb_3025_);
lean_dec_ref(v_sb_3025_);
lean_dec_ref(v_sa_3024_);
v___x_3028_ = lean_box(v___x_3027_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___y_3026_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(lean_object* v_a_3119_, lean_object* v_b_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v_cacheKey_3124_; lean_object* v___x_3125_; 
lean_inc(v_a_3119_);
v___x_3122_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3119_);
lean_inc(v_b_3120_);
v___x_3123_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3120_);
v_cacheKey_3124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3124_, 0, v___x_3122_);
lean_ctor_set(v_cacheKey_3124_, 1, v___x_3123_);
v___x_3125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_a_3121_, v_cacheKey_3124_);
if (lean_obj_tag(v___x_3125_) == 1)
{
lean_object* v_val_3126_; lean_object* v___x_3127_; 
lean_dec_ref_known(v_cacheKey_3124_, 2);
lean_dec(v_b_3120_);
lean_dec(v_a_3119_);
v_val_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v_val_3126_);
lean_ctor_set(v___x_3127_, 1, v_a_3121_);
return v___x_3127_;
}
else
{
lean_object* v___x_3128_; lean_object* v_fst_3129_; lean_object* v_snd_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v___x_3125_);
v___x_3128_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__3(v_a_3119_, v_b_3120_, v_a_3121_);
v_fst_3129_ = lean_ctor_get(v___x_3128_, 0);
v_snd_3130_ = lean_ctor_get(v___x_3128_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3132_ = v___x_3128_;
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_snd_3130_);
lean_inc(v_fst_3129_);
lean_dec(v___x_3128_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_inc(v_fst_3129_);
v___x_3134_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_snd_3130_, v_cacheKey_3124_, v_fst_3129_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 1, v___x_3134_);
v___x_3136_ = v___x_3132_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_fst_3129_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = lean_box(0);
v___x_3140_ = lean_unsigned_to_nat(16u);
v___x_3141_ = lean_mk_array(v___x_3140_, v___x_3139_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3142_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__0);
v___x_3143_ = lean_unsigned_to_nat(0u);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___x_3142_);
return v___x_3144_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(lean_object* v_a_3145_, lean_object* v_b_3146_){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v_fst_3149_; uint8_t v___x_3150_; 
v___x_3147_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1, &l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1_once, _init_l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___closed__1);
v___x_3148_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0(v_a_3145_, v_b_3146_, v___x_3147_);
v_fst_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_fst_3149_);
lean_dec_ref(v___x_3148_);
v___x_3150_ = lean_unbox(v_fst_3149_);
lean_dec(v_fst_3149_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0___boxed(lean_object* v_a_3151_, lean_object* v_b_3152_){
_start:
{
uint8_t v_res_3153_; lean_object* v_r_3154_; 
v_res_3153_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_a_3151_, v_b_3152_);
v_r_3154_ = lean_box(v_res_3153_);
return v_r_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(lean_object* v_a_3155_, lean_object* v_choiceStx_3156_, lean_object* v_as_3157_, size_t v_sz_3158_, size_t v_i_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_a_3164_; lean_object* v_a_3165_; uint8_t v___x_3169_; 
v___x_3169_ = lean_usize_dec_lt(v_i_3159_, v_sz_3158_);
if (v___x_3169_ == 0)
{
lean_object* v___x_3170_; 
lean_dec(v_choiceStx_3156_);
lean_dec_ref(v_a_3155_);
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_b_3160_);
lean_ctor_set(v___x_3170_, 1, v___y_3162_);
return v___x_3170_;
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3172_; 
lean_dec_ref(v___y_3162_);
v_a_3171_ = lean_array_uget_borrowed(v_as_3157_, v_i_3159_);
lean_inc_ref(v_a_3155_);
lean_inc(v_a_3171_);
v___x_3172_ = l_Lean_Fmt_fmt(v_a_3171_, v___y_3161_, v_a_3155_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_snd_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3249_; 
v_snd_3173_ = lean_ctor_get(v_b_3160_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v_b_3160_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v_b_3160_, 0);
lean_dec(v_unused_3250_);
v___x_3175_ = v_b_3160_;
v_isShared_3176_ = v_isSharedCheck_3249_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_snd_3173_);
lean_dec(v_b_3160_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3249_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_a_3177_; lean_object* v_a_3178_; lean_object* v_fst_3179_; lean_object* v_snd_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3248_; 
v_a_3177_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3177_);
v_a_3178_ = lean_ctor_get(v___x_3172_, 1);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3172_, 2);
v_fst_3179_ = lean_ctor_get(v_snd_3173_, 0);
v_snd_3180_ = lean_ctor_get(v_snd_3173_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_snd_3173_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3182_ = v_snd_3173_;
v_isShared_3183_ = v_isSharedCheck_3248_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_snd_3180_);
lean_inc(v_fst_3179_);
lean_dec(v_snd_3173_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3248_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___x_3213_; lean_object* v_first_x3f_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; 
v___x_3213_ = lean_box(0);
if (lean_obj_tag(v_fst_3179_) == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_inc(v_a_3178_);
lean_inc(v_a_3177_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_a_3177_);
lean_ctor_set(v___x_3246_, 1, v_a_3178_);
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
v_first_x3f_3215_ = v___x_3247_;
v___y_3216_ = v___y_3161_;
v___y_3217_ = v_a_3178_;
goto v___jp_3214_;
}
else
{
v_first_x3f_3215_ = v_fst_3179_;
v___y_3216_ = v___y_3161_;
v___y_3217_ = v_a_3178_;
goto v___jp_3214_;
}
v___jp_3184_:
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_disambiguateChoiceNode(v_choiceStx_3156_, v___y_3186_, v_a_3155_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3203_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_a_3189_ = lean_ctor_get(v___x_3187_, 1);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3191_ = v___x_3187_;
v_isShared_3192_ = v_isSharedCheck_3203_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3203_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_a_3188_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___y_3185_);
v___x_3195_ = v___x_3182_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___y_3185_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_snd_3180_);
v___x_3195_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3197_; 
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 1, v___x_3195_);
lean_ctor_set(v___x_3175_, 0, v___x_3193_);
v___x_3197_ = v___x_3175_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3199_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3197_);
v___x_3199_ = v___x_3191_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_a_3189_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec(v___y_3185_);
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_del_object(v___x_3175_);
v_a_3204_ = lean_ctor_get(v___x_3187_, 0);
v_a_3205_ = lean_ctor_get(v___x_3187_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3187_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_inc(v_a_3204_);
lean_dec(v___x_3187_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3204_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
v___jp_3214_:
{
uint8_t v___x_3218_; 
lean_inc(v_a_3177_);
v___x_3218_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_a_3177_);
if (v___x_3218_ == 0)
{
if (lean_obj_tag(v_snd_3180_) == 1)
{
lean_object* v_val_3219_; lean_object* v_fst_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3238_; 
v_val_3219_ = lean_ctor_get(v_snd_3180_, 0);
lean_inc(v_val_3219_);
v_fst_3220_ = lean_ctor_get(v_val_3219_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_val_3219_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v_val_3219_, 1);
lean_dec(v_unused_3239_);
v___x_3222_ = v_val_3219_;
v_isShared_3223_ = v_isSharedCheck_3238_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_fst_3220_);
lean_dec(v_val_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3238_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_doc_3224_; lean_object* v_doc_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3236_; 
v_doc_3224_ = lean_ctor_get(v_a_3177_, 0);
lean_inc(v_doc_3224_);
lean_dec(v_a_3177_);
v_doc_3225_ = lean_ctor_get(v_fst_3220_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_fst_3220_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_fst_3220_, 1);
lean_dec(v_unused_3237_);
v___x_3227_ = v_fst_3220_;
v_isShared_3228_ = v_isSharedCheck_3236_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_doc_3225_);
lean_dec(v_fst_3220_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3236_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
uint8_t v___x_3229_; 
v___x_3229_ = l_Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0(v_doc_3224_, v_doc_3225_);
if (v___x_3229_ == 0)
{
lean_del_object(v___x_3227_);
lean_del_object(v___x_3222_);
lean_dec_ref(v___y_3217_);
v___y_3185_ = v_first_x3f_3215_;
v___y_3186_ = v___y_3216_;
goto v___jp_3184_;
}
else
{
if (v___x_3218_ == 0)
{
lean_object* v___x_3231_; 
lean_del_object(v___x_3182_);
lean_del_object(v___x_3175_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 1, v_snd_3180_);
lean_ctor_set(v___x_3222_, 0, v_first_x3f_3215_);
v___x_3231_ = v___x_3222_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_first_x3f_3215_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_snd_3180_);
v___x_3231_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3233_; 
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 1, v___x_3231_);
lean_ctor_set(v___x_3227_, 0, v___x_3213_);
v___x_3233_ = v___x_3227_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3231_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
v_a_3164_ = v___x_3233_;
v_a_3165_ = v___y_3217_;
goto v___jp_3163_;
}
}
}
else
{
lean_del_object(v___x_3227_);
lean_del_object(v___x_3222_);
lean_dec_ref(v___y_3217_);
v___y_3185_ = v_first_x3f_3215_;
v___y_3186_ = v___y_3216_;
goto v___jp_3184_;
}
}
}
}
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; 
lean_del_object(v___x_3182_);
lean_dec(v_snd_3180_);
lean_del_object(v___x_3175_);
lean_inc_ref(v___y_3217_);
v___x_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3240_, 0, v_a_3177_);
lean_ctor_set(v___x_3240_, 1, v___y_3217_);
v___x_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_first_x3f_3215_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3213_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v_a_3164_ = v___x_3243_;
v_a_3165_ = v___y_3217_;
goto v___jp_3163_;
}
}
else
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
lean_del_object(v___x_3182_);
lean_dec(v_a_3177_);
lean_del_object(v___x_3175_);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v_first_x3f_3215_);
lean_ctor_set(v___x_3244_, 1, v_snd_3180_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3213_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v_a_3164_ = v___x_3245_;
v_a_3165_ = v___y_3217_;
goto v___jp_3163_;
}
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v_b_3160_);
lean_dec(v_choiceStx_3156_);
lean_dec_ref(v_a_3155_);
v_a_3251_ = lean_ctor_get(v___x_3172_, 0);
v_a_3252_ = lean_ctor_get(v___x_3172_, 1);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3172_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_inc(v_a_3251_);
lean_dec(v___x_3172_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3251_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
v___jp_3163_:
{
size_t v___x_3166_; size_t v___x_3167_; 
v___x_3166_ = ((size_t)1ULL);
v___x_3167_ = lean_usize_add(v_i_3159_, v___x_3166_);
v_i_3159_ = v___x_3167_;
v_b_3160_ = v_a_3164_;
v___y_3162_ = v_a_3165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1___boxed(lean_object* v_a_3260_, lean_object* v_choiceStx_3261_, lean_object* v_as_3262_, lean_object* v_sz_3263_, lean_object* v_i_3264_, lean_object* v_b_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
size_t v_sz_boxed_3268_; size_t v_i_boxed_3269_; lean_object* v_res_3270_; 
v_sz_boxed_3268_ = lean_unbox_usize(v_sz_3263_);
lean_dec(v_sz_3263_);
v_i_boxed_3269_ = lean_unbox_usize(v_i_3264_);
lean_dec(v_i_3264_);
v_res_3270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3260_, v_choiceStx_3261_, v_as_3262_, v_sz_boxed_3268_, v_i_boxed_3269_, v_b_3265_, v___y_3266_, v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v_as_3262_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(lean_object* v_choiceStx_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v___y_3280_; lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3290_ = l_Lean_Syntax_getNumArgs(v_choiceStx_3276_);
v___x_3291_ = lean_unsigned_to_nat(0u);
v___x_3292_ = lean_nat_dec_eq(v___x_3290_, v___x_3291_);
lean_dec(v___x_3290_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; size_t v_sz_3295_; size_t v___x_3296_; lean_object* v___x_3297_; 
v___x_3293_ = l_Lean_Syntax_getArgs(v_choiceStx_3276_);
v___x_3294_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___closed__1));
v_sz_3295_ = lean_array_size(v___x_3293_);
v___x_3296_ = ((size_t)0ULL);
lean_inc_ref(v_a_3278_);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__1(v_a_3278_, v_choiceStx_3276_, v___x_3293_, v_sz_3295_, v___x_3296_, v___x_3294_, v_a_3277_, v_a_3278_);
lean_dec_ref(v___x_3293_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v_fst_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
v_fst_3299_ = lean_ctor_get(v_a_3298_, 0);
if (lean_obj_tag(v_fst_3299_) == 0)
{
lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3315_; 
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; lean_object* v_unused_3317_; 
v_unused_3316_ = lean_ctor_get(v___x_3297_, 1);
lean_dec(v_unused_3316_);
v_unused_3317_ = lean_ctor_get(v___x_3297_, 0);
lean_dec(v_unused_3317_);
v___x_3301_ = v___x_3297_;
v_isShared_3302_ = v_isSharedCheck_3315_;
goto v_resetjp_3300_;
}
else
{
lean_dec(v___x_3297_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3315_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v_snd_3303_; lean_object* v_snd_3304_; 
v_snd_3303_ = lean_ctor_get(v_a_3298_, 1);
lean_inc(v_snd_3303_);
lean_dec(v_a_3298_);
v_snd_3304_ = lean_ctor_get(v_snd_3303_, 1);
if (lean_obj_tag(v_snd_3304_) == 1)
{
lean_object* v_val_3305_; lean_object* v_fst_3306_; lean_object* v_snd_3307_; lean_object* v___x_3309_; 
lean_inc_ref(v_snd_3304_);
lean_dec(v_snd_3303_);
v_val_3305_ = lean_ctor_get(v_snd_3304_, 0);
lean_inc(v_val_3305_);
lean_dec_ref_known(v_snd_3304_, 1);
v_fst_3306_ = lean_ctor_get(v_val_3305_, 0);
lean_inc(v_fst_3306_);
v_snd_3307_ = lean_ctor_get(v_val_3305_, 1);
lean_inc(v_snd_3307_);
lean_dec(v_val_3305_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 1, v_snd_3307_);
lean_ctor_set(v___x_3301_, 0, v_fst_3306_);
v___x_3309_ = v___x_3301_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_fst_3306_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_snd_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
else
{
lean_object* v_fst_3311_; 
lean_del_object(v___x_3301_);
v_fst_3311_ = lean_ctor_get(v_snd_3303_, 0);
lean_inc(v_fst_3311_);
lean_dec(v_snd_3303_);
if (lean_obj_tag(v_fst_3311_) == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3313_ = l_panic___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__2(v___x_3312_);
v___y_3280_ = v___x_3313_;
goto v___jp_3279_;
}
else
{
lean_object* v_val_3314_; 
v_val_3314_ = lean_ctor_get(v_fst_3311_, 0);
lean_inc(v_val_3314_);
lean_dec_ref_known(v_fst_3311_, 1);
v___y_3280_ = v_val_3314_;
goto v___jp_3279_;
}
}
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3326_; 
lean_inc_ref(v_fst_3299_);
lean_dec(v_a_3298_);
v_a_3318_ = lean_ctor_get(v___x_3297_, 1);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3326_ == 0)
{
lean_object* v_unused_3327_; 
v_unused_3327_ = lean_ctor_get(v___x_3297_, 0);
lean_dec(v_unused_3327_);
v___x_3320_ = v___x_3297_;
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3297_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3326_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v_val_3322_; lean_object* v___x_3324_; 
v_val_3322_ = lean_ctor_get(v_fst_3299_, 0);
lean_inc(v_val_3322_);
lean_dec_ref_known(v_fst_3299_, 1);
if (v_isShared_3321_ == 0)
{
lean_ctor_set(v___x_3320_, 0, v_val_3322_);
v___x_3324_ = v___x_3320_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_val_3322_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_a_3318_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
v_a_3328_ = lean_ctor_get(v___x_3297_, 0);
v_a_3329_ = lean_ctor_get(v___x_3297_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3297_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_inc(v_a_3328_);
lean_dec(v___x_3297_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3328_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3338_ = l_Lean_Fmt_TaggedDoc_text___redArg(v___x_3337_, v_choiceStx_3276_, v_a_3278_);
lean_dec(v_choiceStx_3276_);
return v___x_3338_;
}
v___jp_3279_:
{
lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
v_fst_3281_ = lean_ctor_get(v___y_3280_, 0);
v_snd_3282_ = lean_ctor_get(v___y_3280_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___y_3280_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___y_3280_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_snd_3282_);
lean_inc(v_fst_3281_);
lean_dec(v___y_3280_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_fst_3281_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_snd_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed(lean_object* v_choiceStx_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode(v_choiceStx_3339_, v_a_3340_, v_a_3341_);
lean_dec_ref(v_a_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3343_, lean_object* v_m_3344_, lean_object* v_a_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___redArg(v_m_3344_, v_a_3345_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3347_, lean_object* v_m_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2(v_00_u03b2_3347_, v_m_3348_, v_a_3349_);
lean_dec_ref(v_a_3349_);
lean_dec_ref(v_m_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_3351_, lean_object* v_m_3352_, lean_object* v_a_3353_, lean_object* v_b_3354_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4___redArg(v_m_3352_, v_a_3353_, v_b_3354_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3356_, lean_object* v_a_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___redArg(v_a_3357_, v_x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3360_, lean_object* v_a_3361_, lean_object* v_x_3362_){
_start:
{
lean_object* v_res_3363_; 
v_res_3363_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_3360_, v_a_3361_, v_x_3362_);
lean_dec(v_x_3362_);
lean_dec_ref(v_a_3361_);
return v_res_3363_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_3364_, lean_object* v_a_3365_, lean_object* v_x_3366_){
_start:
{
uint8_t v___x_3367_; 
v___x_3367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___redArg(v_a_3365_, v_x_3366_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8___boxed(lean_object* v_00_u03b2_3368_, lean_object* v_a_3369_, lean_object* v_x_3370_){
_start:
{
uint8_t v_res_3371_; lean_object* v_r_3372_; 
v_res_3371_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__8(v_00_u03b2_3368_, v_a_3369_, v_x_3370_);
lean_dec(v_x_3370_);
lean_dec_ref(v_a_3369_);
v_r_3372_ = lean_box(v_res_3371_);
return v_r_3372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9(lean_object* v_00_u03b2_3373_, lean_object* v_data_3374_){
_start:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9___redArg(v_data_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10(lean_object* v_00_u03b2_3376_, lean_object* v_a_3377_, lean_object* v_b_3378_, lean_object* v_x_3379_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__10___redArg(v_a_3377_, v_b_3378_, v_x_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11(lean_object* v_00_u03b2_3381_, lean_object* v_i_3382_, lean_object* v_source_3383_, lean_object* v_target_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11___redArg(v_i_3382_, v_source_3383_, v_target_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12(lean_object* v_00_u03b2_3386_, lean_object* v_x_3387_, lean_object* v_x_3388_){
_start:
{
lean_object* v___x_3389_; 
v___x_3389_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___at___00Lean_Fmt_Doc_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode_spec__0_spec__0_spec__4_spec__9_spec__11_spec__12___redArg(v_x_3387_, v_x_3388_);
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(size_t v_sz_3390_, size_t v_i_3391_, lean_object* v_bs_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v___x_3395_; 
v___x_3395_ = lean_usize_dec_lt(v_i_3391_, v_sz_3390_);
if (v___x_3395_ == 0)
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v_bs_3392_);
lean_ctor_set(v___x_3396_, 1, v___y_3394_);
return v___x_3396_;
}
else
{
lean_object* v_v_3397_; lean_object* v___x_3398_; 
v_v_3397_ = lean_array_uget_borrowed(v_bs_3392_, v_i_3391_);
lean_inc(v_v_3397_);
v___x_3398_ = l_Lean_Fmt_fmt(v_v_3397_, v___y_3393_, v___y_3394_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v_a_3400_; lean_object* v___x_3401_; lean_object* v_bs_x27_3402_; size_t v___x_3403_; size_t v___x_3404_; lean_object* v___x_3405_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
v_a_3400_ = lean_ctor_get(v___x_3398_, 1);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3398_, 2);
v___x_3401_ = lean_unsigned_to_nat(0u);
v_bs_x27_3402_ = lean_array_uset(v_bs_3392_, v_i_3391_, v___x_3401_);
v___x_3403_ = ((size_t)1ULL);
v___x_3404_ = lean_usize_add(v_i_3391_, v___x_3403_);
v___x_3405_ = lean_array_uset(v_bs_x27_3402_, v_i_3391_, v_a_3399_);
v_i_3391_ = v___x_3404_;
v_bs_3392_ = v___x_3405_;
v___y_3394_ = v_a_3400_;
goto _start;
}
else
{
lean_object* v_a_3407_; lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec_ref(v_bs_3392_);
v_a_3407_ = lean_ctor_get(v___x_3398_, 0);
v_a_3408_ = lean_ctor_get(v___x_3398_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3398_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_inc(v_a_3407_);
lean_dec(v___x_3398_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3407_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1___boxed(lean_object* v_sz_3416_, lean_object* v_i_3417_, lean_object* v_bs_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
size_t v_sz_boxed_3421_; size_t v_i_boxed_3422_; lean_object* v_res_3423_; 
v_sz_boxed_3421_ = lean_unbox_usize(v_sz_3416_);
lean_dec(v_sz_3416_);
v_i_boxed_3422_ = lean_unbox_usize(v_i_3417_);
lean_dec(v_i_3417_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_boxed_3421_, v_i_boxed_3422_, v_bs_3418_, v___y_3419_, v___y_3420_);
lean_dec_ref(v___y_3419_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3424_, lean_object* v_x_3425_){
_start:
{
if (lean_obj_tag(v_x_3425_) == 0)
{
return v_x_3424_;
}
else
{
lean_object* v_key_3426_; lean_object* v_value_3427_; lean_object* v_tail_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3454_; 
v_key_3426_ = lean_ctor_get(v_x_3425_, 0);
v_value_3427_ = lean_ctor_get(v_x_3425_, 1);
v_tail_3428_ = lean_ctor_get(v_x_3425_, 2);
v_isSharedCheck_3454_ = !lean_is_exclusive(v_x_3425_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3430_ = v_x_3425_;
v_isShared_3431_ = v_isSharedCheck_3454_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_tail_3428_);
lean_inc(v_value_3427_);
lean_inc(v_key_3426_);
lean_dec(v_x_3425_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3454_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; uint64_t v___y_3434_; 
v___x_3432_ = lean_array_get_size(v_x_3424_);
if (lean_obj_tag(v_key_3426_) == 0)
{
uint64_t v___x_3452_; 
v___x_3452_ = 1723ULL;
v___y_3434_ = v___x_3452_;
goto v___jp_3433_;
}
else
{
uint64_t v_hash_3453_; 
v_hash_3453_ = lean_ctor_get_uint64(v_key_3426_, sizeof(void*)*2);
v___y_3434_ = v_hash_3453_;
goto v___jp_3433_;
}
v___jp_3433_:
{
uint64_t v___x_3435_; uint64_t v___x_3436_; uint64_t v_fold_3437_; uint64_t v___x_3438_; uint64_t v___x_3439_; uint64_t v___x_3440_; size_t v___x_3441_; size_t v___x_3442_; size_t v___x_3443_; size_t v___x_3444_; size_t v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v___x_3435_ = 32ULL;
v___x_3436_ = lean_uint64_shift_right(v___y_3434_, v___x_3435_);
v_fold_3437_ = lean_uint64_xor(v___y_3434_, v___x_3436_);
v___x_3438_ = 16ULL;
v___x_3439_ = lean_uint64_shift_right(v_fold_3437_, v___x_3438_);
v___x_3440_ = lean_uint64_xor(v_fold_3437_, v___x_3439_);
v___x_3441_ = lean_uint64_to_usize(v___x_3440_);
v___x_3442_ = lean_usize_of_nat(v___x_3432_);
v___x_3443_ = ((size_t)1ULL);
v___x_3444_ = lean_usize_sub(v___x_3442_, v___x_3443_);
v___x_3445_ = lean_usize_land(v___x_3441_, v___x_3444_);
v___x_3446_ = lean_array_uget_borrowed(v_x_3424_, v___x_3445_);
lean_inc(v___x_3446_);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 2, v___x_3446_);
v___x_3448_ = v___x_3430_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_key_3426_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_value_3427_);
lean_ctor_set(v_reuseFailAlloc_3451_, 2, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3449_; 
v___x_3449_ = lean_array_uset(v_x_3424_, v___x_3445_, v___x_3448_);
v_x_3424_ = v___x_3449_;
v_x_3425_ = v_tail_3428_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(lean_object* v_i_3455_, lean_object* v_source_3456_, lean_object* v_target_3457_){
_start:
{
lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = lean_array_get_size(v_source_3456_);
v___x_3459_ = lean_nat_dec_lt(v_i_3455_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_dec_ref(v_source_3456_);
lean_dec(v_i_3455_);
return v_target_3457_;
}
else
{
lean_object* v_es_3460_; lean_object* v___x_3461_; lean_object* v_source_3462_; lean_object* v_target_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_es_3460_ = lean_array_fget(v_source_3456_, v_i_3455_);
v___x_3461_ = lean_box(0);
v_source_3462_ = lean_array_fset(v_source_3456_, v_i_3455_, v___x_3461_);
v_target_3463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_target_3457_, v_es_3460_);
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = lean_nat_add(v_i_3455_, v___x_3464_);
lean_dec(v_i_3455_);
v_i_3455_ = v___x_3465_;
v_source_3456_ = v_source_3462_;
v_target_3457_ = v_target_3463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(lean_object* v_data_3467_){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v_nbuckets_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3468_ = lean_array_get_size(v_data_3467_);
v___x_3469_ = lean_unsigned_to_nat(2u);
v_nbuckets_3470_ = lean_nat_mul(v___x_3468_, v___x_3469_);
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = lean_box(0);
v___x_3473_ = lean_mk_array(v_nbuckets_3470_, v___x_3472_);
v___x_3474_ = lean_array_propagate_mark(v_data_3467_, v___x_3473_);
v___x_3475_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v___x_3471_, v_data_3467_, v___x_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(lean_object* v_m_3476_, lean_object* v_a_3477_, lean_object* v_b_3478_){
_start:
{
lean_object* v_size_3479_; lean_object* v_buckets_3480_; lean_object* v___x_3481_; uint64_t v___y_3483_; 
v_size_3479_ = lean_ctor_get(v_m_3476_, 0);
v_buckets_3480_ = lean_ctor_get(v_m_3476_, 1);
v___x_3481_ = lean_array_get_size(v_buckets_3480_);
if (lean_obj_tag(v_a_3477_) == 0)
{
uint64_t v___x_3520_; 
v___x_3520_ = 1723ULL;
v___y_3483_ = v___x_3520_;
goto v___jp_3482_;
}
else
{
uint64_t v_hash_3521_; 
v_hash_3521_ = lean_ctor_get_uint64(v_a_3477_, sizeof(void*)*2);
v___y_3483_ = v_hash_3521_;
goto v___jp_3482_;
}
v___jp_3482_:
{
uint64_t v___x_3484_; uint64_t v___x_3485_; uint64_t v_fold_3486_; uint64_t v___x_3487_; uint64_t v___x_3488_; uint64_t v___x_3489_; size_t v___x_3490_; size_t v___x_3491_; size_t v___x_3492_; size_t v___x_3493_; size_t v___x_3494_; lean_object* v_bkt_3495_; uint8_t v___x_3496_; 
v___x_3484_ = 32ULL;
v___x_3485_ = lean_uint64_shift_right(v___y_3483_, v___x_3484_);
v_fold_3486_ = lean_uint64_xor(v___y_3483_, v___x_3485_);
v___x_3487_ = 16ULL;
v___x_3488_ = lean_uint64_shift_right(v_fold_3486_, v___x_3487_);
v___x_3489_ = lean_uint64_xor(v_fold_3486_, v___x_3488_);
v___x_3490_ = lean_uint64_to_usize(v___x_3489_);
v___x_3491_ = lean_usize_of_nat(v___x_3481_);
v___x_3492_ = ((size_t)1ULL);
v___x_3493_ = lean_usize_sub(v___x_3491_, v___x_3492_);
v___x_3494_ = lean_usize_land(v___x_3490_, v___x_3493_);
v_bkt_3495_ = lean_array_uget_borrowed(v_buckets_3480_, v___x_3494_);
v___x_3496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain_spec__0_spec__0___redArg(v_a_3477_, v_bkt_3495_);
if (v___x_3496_ == 0)
{
lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3517_; 
lean_inc_ref(v_buckets_3480_);
lean_inc(v_size_3479_);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_m_3476_);
if (v_isSharedCheck_3517_ == 0)
{
lean_object* v_unused_3518_; lean_object* v_unused_3519_; 
v_unused_3518_ = lean_ctor_get(v_m_3476_, 1);
lean_dec(v_unused_3518_);
v_unused_3519_ = lean_ctor_get(v_m_3476_, 0);
lean_dec(v_unused_3519_);
v___x_3498_ = v_m_3476_;
v_isShared_3499_ = v_isSharedCheck_3517_;
goto v_resetjp_3497_;
}
else
{
lean_dec(v_m_3476_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3517_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v_size_x27_3501_; lean_object* v___x_3502_; lean_object* v_buckets_x27_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3500_ = lean_unsigned_to_nat(1u);
v_size_x27_3501_ = lean_nat_add(v_size_3479_, v___x_3500_);
lean_dec(v_size_3479_);
lean_inc(v_bkt_3495_);
v___x_3502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3502_, 0, v_a_3477_);
lean_ctor_set(v___x_3502_, 1, v_b_3478_);
lean_ctor_set(v___x_3502_, 2, v_bkt_3495_);
v_buckets_x27_3503_ = lean_array_uset(v_buckets_3480_, v___x_3494_, v___x_3502_);
v___x_3504_ = lean_unsigned_to_nat(4u);
v___x_3505_ = lean_nat_mul(v_size_x27_3501_, v___x_3504_);
v___x_3506_ = lean_unsigned_to_nat(3u);
v___x_3507_ = lean_nat_div(v___x_3505_, v___x_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_array_get_size(v_buckets_x27_3503_);
v___x_3509_ = lean_nat_dec_le(v___x_3507_, v___x_3508_);
lean_dec(v___x_3507_);
if (v___x_3509_ == 0)
{
lean_object* v_val_3510_; lean_object* v___x_3512_; 
v_val_3510_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_buckets_x27_3503_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v_val_3510_);
lean_ctor_set(v___x_3498_, 0, v_size_x27_3501_);
v___x_3512_ = v___x_3498_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_size_x27_3501_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_val_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
else
{
lean_object* v___x_3515_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 1, v_buckets_x27_3503_);
lean_ctor_set(v___x_3498_, 0, v_size_x27_3501_);
v___x_3515_ = v___x_3498_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_size_x27_3501_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_buckets_x27_3503_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_dec(v_b_3478_);
lean_dec(v_a_3477_);
return v_m_3476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator(lean_object* v_op_3522_, lean_object* v_stx_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
uint8_t v_sparse_3526_; uint8_t v_separateFinalOperand_3527_; lean_object* v_precs_x3f_3528_; lean_object* v_extendedChainKinds_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3570_; 
v_sparse_3526_ = lean_ctor_get_uint8(v_op_3522_, sizeof(void*)*2);
v_separateFinalOperand_3527_ = lean_ctor_get_uint8(v_op_3522_, sizeof(void*)*2 + 1);
v_precs_x3f_3528_ = lean_ctor_get(v_op_3522_, 0);
v_extendedChainKinds_3529_ = lean_ctor_get(v_op_3522_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_op_3522_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3531_ = v_op_3522_;
v_isShared_3532_ = v_isSharedCheck_3570_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_extendedChainKinds_3529_);
lean_inc(v_precs_x3f_3528_);
lean_dec(v_op_3522_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3570_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_env_3533_; lean_object* v_opts_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v_env_3533_ = lean_ctor_get(v_a_3524_, 0);
v_opts_3534_ = lean_ctor_get(v_a_3524_, 3);
lean_inc(v_stx_3523_);
v___x_3535_ = l_Lean_Syntax_getKind(v_stx_3523_);
v___x_3536_ = lean_box(0);
v___x_3537_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_extendedChainKinds_3529_, v___x_3535_, v___x_3536_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v___x_3537_);
v___x_3539_ = v___x_3531_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_precs_x3f_3528_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3537_);
lean_ctor_set_uint8(v_reuseFailAlloc_3569_, sizeof(void*)*2, v_sparse_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3569_, sizeof(void*)*2 + 1, v_separateFinalOperand_3527_);
v___x_3539_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; size_t v_sz_3541_; size_t v___x_3542_; lean_object* v___x_3543_; 
lean_inc_ref(v_env_3533_);
v___x_3540_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_collectInfixOperatorChain(v_env_3533_, v_opts_3534_, v___x_3539_, v_stx_3523_);
lean_dec_ref(v___x_3539_);
v_sz_3541_ = lean_array_size(v___x_3540_);
v___x_3542_ = ((size_t)0ULL);
v___x_3543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_3541_, v___x_3542_, v___x_3540_, v_a_3524_, v_a_3525_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3559_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_a_3545_ = lean_ctor_get(v___x_3543_, 1);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3547_ = v___x_3543_;
v_isShared_3548_ = v_isSharedCheck_3559_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3559_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___y_3550_; uint8_t v___x_3555_; 
v___x_3555_ = 1;
if (v_sparse_3526_ == 0)
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3556_, 0, v___x_3555_);
lean_ctor_set_uint8(v___x_3556_, 1, v_sparse_3526_);
lean_ctor_set_uint8(v___x_3556_, 2, v___x_3555_);
lean_ctor_set_uint8(v___x_3556_, 3, v___x_3555_);
v___y_3550_ = v___x_3556_;
goto v___jp_3549_;
}
else
{
uint8_t v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = 0;
v___x_3558_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_3558_, 0, v___x_3555_);
lean_ctor_set_uint8(v___x_3558_, 1, v___x_3557_);
lean_ctor_set_uint8(v___x_3558_, 2, v___x_3555_);
lean_ctor_set_uint8(v___x_3558_, 3, v___x_3557_);
lean_ctor_set_uint8(v___x_3558_, 4, v_separateFinalOperand_3527_);
v___y_3550_ = v___x_3558_;
goto v___jp_3549_;
}
v___jp_3549_:
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
v___x_3551_ = l_Lean_Fmt_Layouts_infixOperator(v_a_3544_, v___y_3550_);
lean_dec_ref(v___y_3550_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3551_);
v___x_3553_ = v___x_3547_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_a_3545_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
v_a_3560_ = lean_ctor_get(v___x_3543_, 0);
v_a_3561_ = lean_ctor_get(v___x_3543_, 1);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3543_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_inc(v_a_3560_);
lean_dec(v___x_3543_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3560_);
lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtInfixOperator___boxed(lean_object* v_op_3571_, lean_object* v_stx_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_Fmt_fmtInfixOperator(v_op_3571_, v_stx_3572_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_a_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0(lean_object* v_00_u03b2_3576_, lean_object* v_m_3577_, lean_object* v_a_3578_, lean_object* v_b_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0___redArg(v_m_3577_, v_a_3578_, v_b_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0(lean_object* v_00_u03b2_3581_, lean_object* v_data_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0___redArg(v_data_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3584_, lean_object* v_i_3585_, lean_object* v_source_3586_, lean_object* v_target_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1___redArg(v_i_3585_, v_source_3586_, v_target_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Fmt_fmtInfixOperator_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3590_, v_x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(lean_object* v_x_3593_, lean_object* v_x_3594_){
_start:
{
if (lean_obj_tag(v_x_3593_) == 0)
{
if (lean_obj_tag(v_x_3594_) == 0)
{
uint8_t v___x_3595_; 
v___x_3595_ = 1;
return v___x_3595_;
}
else
{
uint8_t v___x_3596_; 
v___x_3596_ = 0;
return v___x_3596_;
}
}
else
{
if (lean_obj_tag(v_x_3594_) == 0)
{
uint8_t v___x_3597_; 
v___x_3597_ = 0;
return v___x_3597_;
}
else
{
lean_object* v_val_3598_; lean_object* v_val_3599_; uint8_t v___x_3600_; 
v_val_3598_ = lean_ctor_get(v_x_3593_, 0);
v_val_3599_ = lean_ctor_get(v_x_3594_, 0);
v___x_3600_ = lean_string_dec_eq(v_val_3598_, v_val_3599_);
return v___x_3600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0___boxed(lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
uint8_t v_res_3603_; lean_object* v_r_3604_; 
v_res_3603_ = l_Option_instBEq_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v_x_3601_, v_x_3602_);
lean_dec(v_x_3602_);
lean_dec(v_x_3601_);
v_r_3604_ = lean_box(v_res_3603_);
return v_r_3604_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(lean_object* v_msg_3605_){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = l_String_instInhabitedSlice;
v___x_3607_ = lean_panic_fn_borrowed(v___x_3606_, v_msg_3605_);
return v___x_3607_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(lean_object* v_s_3608_, lean_object* v_a_3609_, uint8_t v_b_3610_){
_start:
{
lean_object* v_str_3611_; lean_object* v_startInclusive_3612_; lean_object* v_endExclusive_3613_; lean_object* v___x_3614_; uint8_t v_decide_3615_; 
v_str_3611_ = lean_ctor_get(v_s_3608_, 0);
v_startInclusive_3612_ = lean_ctor_get(v_s_3608_, 1);
v_endExclusive_3613_ = lean_ctor_get(v_s_3608_, 2);
v___x_3614_ = lean_nat_sub(v_endExclusive_3613_, v_startInclusive_3612_);
v_decide_3615_ = lean_nat_dec_eq(v_a_3609_, v___x_3614_);
lean_dec(v___x_3614_);
if (v_decide_3615_ == 0)
{
lean_object* v___x_3616_; uint32_t v___x_3617_; uint32_t v___x_3618_; uint8_t v___x_3619_; 
v___x_3616_ = lean_nat_add(v_startInclusive_3612_, v_a_3609_);
lean_dec(v_a_3609_);
v___x_3617_ = lean_string_utf8_get_fast(v_str_3611_, v___x_3616_);
v___x_3618_ = 187;
v___x_3619_ = lean_uint32_dec_eq(v___x_3617_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_string_utf8_next_fast(v_str_3611_, v___x_3616_);
lean_dec(v___x_3616_);
v___x_3621_ = lean_nat_sub(v___x_3620_, v_startInclusive_3612_);
v_a_3609_ = v___x_3621_;
v_b_3610_ = v___x_3619_;
goto _start;
}
else
{
lean_dec(v___x_3616_);
return v___x_3619_;
}
}
else
{
lean_dec(v_a_3609_);
return v_b_3610_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg___boxed(lean_object* v_s_3623_, lean_object* v_a_3624_, lean_object* v_b_3625_){
_start:
{
uint8_t v_b_boxed_3626_; uint8_t v_res_3627_; lean_object* v_r_3628_; 
v_b_boxed_3626_ = lean_unbox(v_b_3625_);
v_res_3627_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3623_, v_a_3624_, v_b_boxed_3626_);
lean_dec_ref(v_s_3623_);
v_r_3628_ = lean_box(v_res_3627_);
return v_r_3628_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(lean_object* v_s_3629_){
_start:
{
lean_object* v_searcher_3630_; uint8_t v___x_3631_; uint8_t v___x_3632_; 
v_searcher_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = 0;
v___x_3632_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3629_, v_searcher_3630_, v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1___boxed(lean_object* v_s_3633_){
_start:
{
uint8_t v_res_3634_; lean_object* v_r_3635_; 
v_res_3634_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v_s_3633_);
lean_dec_ref(v_s_3633_);
v_r_3635_ = lean_box(v_res_3634_);
return v_r_3635_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(lean_object* v_s_3636_, lean_object* v_pos_3637_){
_start:
{
lean_object* v_str_3638_; lean_object* v_startInclusive_3639_; lean_object* v_endExclusive_3640_; lean_object* v___x_3641_; uint8_t v___y_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; uint8_t v_decide_3654_; 
v_str_3638_ = lean_ctor_get(v_s_3636_, 0);
v_startInclusive_3639_ = lean_ctor_get(v_s_3636_, 1);
v_endExclusive_3640_ = lean_ctor_get(v_s_3636_, 2);
v___x_3641_ = lean_nat_add(v_startInclusive_3639_, v_pos_3637_);
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_nat_sub(v_endExclusive_3640_, v___x_3641_);
v_decide_3654_ = lean_nat_dec_eq(v___x_3652_, v___x_3653_);
lean_dec(v___x_3653_);
if (v_decide_3654_ == 0)
{
uint32_t v___x_3655_; uint8_t v___y_3673_; uint32_t v___x_3678_; uint8_t v___x_3679_; 
v___x_3655_ = lean_string_utf8_get_fast(v_str_3638_, v___x_3641_);
v___x_3678_ = 65;
v___x_3679_ = lean_uint32_dec_le(v___x_3678_, v___x_3655_);
if (v___x_3679_ == 0)
{
v___y_3673_ = v___x_3679_;
goto v___jp_3672_;
}
else
{
uint32_t v___x_3680_; uint8_t v___x_3681_; 
v___x_3680_ = 90;
v___x_3681_ = lean_uint32_dec_le(v___x_3655_, v___x_3680_);
v___y_3673_ = v___x_3681_;
goto v___jp_3672_;
}
v___jp_3656_:
{
uint32_t v___x_3657_; uint8_t v___x_3658_; 
v___x_3657_ = 95;
v___x_3658_ = lean_uint32_dec_eq(v___x_3655_, v___x_3657_);
if (v___x_3658_ == 0)
{
uint32_t v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = 39;
v___x_3660_ = lean_uint32_dec_eq(v___x_3655_, v___x_3659_);
if (v___x_3660_ == 0)
{
uint32_t v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = 33;
v___x_3662_ = lean_uint32_dec_eq(v___x_3655_, v___x_3661_);
if (v___x_3662_ == 0)
{
uint32_t v___x_3663_; uint8_t v___x_3664_; 
v___x_3663_ = 63;
v___x_3664_ = lean_uint32_dec_eq(v___x_3655_, v___x_3663_);
if (v___x_3664_ == 0)
{
uint8_t v___x_3665_; 
v___x_3665_ = l_Lean_isLetterLike(v___x_3655_);
if (v___x_3665_ == 0)
{
uint8_t v___x_3666_; 
v___x_3666_ = l_Lean_isSubScriptAlnum(v___x_3655_);
v___y_3651_ = v___x_3666_;
goto v___jp_3650_;
}
else
{
v___y_3651_ = v___x_3665_;
goto v___jp_3650_;
}
}
else
{
goto v___jp_3642_;
}
}
else
{
goto v___jp_3642_;
}
}
else
{
goto v___jp_3642_;
}
}
else
{
goto v___jp_3642_;
}
}
v___jp_3667_:
{
uint32_t v___x_3668_; uint8_t v___x_3669_; 
v___x_3668_ = 48;
v___x_3669_ = lean_uint32_dec_le(v___x_3668_, v___x_3655_);
if (v___x_3669_ == 0)
{
goto v___jp_3656_;
}
else
{
uint32_t v___x_3670_; uint8_t v___x_3671_; 
v___x_3670_ = 57;
v___x_3671_ = lean_uint32_dec_le(v___x_3655_, v___x_3670_);
if (v___x_3671_ == 0)
{
goto v___jp_3656_;
}
else
{
goto v___jp_3642_;
}
}
}
v___jp_3672_:
{
if (v___y_3673_ == 0)
{
uint32_t v___x_3674_; uint8_t v___x_3675_; 
v___x_3674_ = 97;
v___x_3675_ = lean_uint32_dec_le(v___x_3674_, v___x_3655_);
if (v___x_3675_ == 0)
{
goto v___jp_3667_;
}
else
{
uint32_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3676_ = 122;
v___x_3677_ = lean_uint32_dec_le(v___x_3655_, v___x_3676_);
if (v___x_3677_ == 0)
{
goto v___jp_3667_;
}
else
{
goto v___jp_3642_;
}
}
}
else
{
goto v___jp_3642_;
}
}
}
else
{
lean_dec(v___x_3641_);
return v_pos_3637_;
}
v___jp_3642_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3643_ = lean_string_utf8_next_fast(v_str_3638_, v___x_3641_);
v___x_3644_ = lean_nat_sub(v___x_3643_, v___x_3641_);
lean_dec(v___x_3641_);
v___x_3645_ = lean_nat_add(v_pos_3637_, v___x_3644_);
lean_dec(v___x_3644_);
v___x_3646_ = lean_unsigned_to_nat(1u);
v___x_3647_ = lean_nat_add(v_pos_3637_, v___x_3646_);
v___x_3648_ = lean_nat_dec_le(v___x_3647_, v___x_3645_);
lean_dec(v___x_3647_);
if (v___x_3648_ == 0)
{
lean_dec(v___x_3645_);
return v_pos_3637_;
}
else
{
lean_dec(v_pos_3637_);
v_pos_3637_ = v___x_3645_;
goto _start;
}
}
v___jp_3650_:
{
if (v___y_3651_ == 0)
{
lean_dec(v___x_3641_);
return v_pos_3637_;
}
else
{
goto v___jp_3642_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2___boxed(lean_object* v_s_3682_, lean_object* v_pos_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v_s_3682_, v_pos_3683_);
lean_dec_ref(v_s_3682_);
return v_res_3684_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__0(void){
_start:
{
uint32_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = l_Lean_idBeginEscape;
v___x_3686_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3687_ = lean_string_push(v___x_3686_, v___x_3685_);
return v___x_3687_;
}
}
static lean_object* _init_l_Lean_Fmt_fmtPrefixOperator___closed__1(void){
_start:
{
uint32_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3688_ = l_Lean_idEndEscape;
v___x_3689_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__4));
v___x_3690_ = lean_string_push(v___x_3689_, v___x_3688_);
return v___x_3690_;
}
}
static uint8_t _init_l_Lean_Fmt_fmtPrefixOperator___closed__2(void){
_start:
{
uint32_t v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = 95;
v___x_3692_ = lean_uint32_to_uint8(v___x_3691_);
return v___x_3692_;
}
}
static uint8_t _init_l_Lean_Fmt_fmtPrefixOperator___closed__3(void){
_start:
{
uint32_t v___x_3693_; uint8_t v___x_3694_; 
v___x_3693_ = 65;
v___x_3694_ = lean_uint32_to_uint8(v___x_3693_);
return v___x_3694_;
}
}
static uint8_t _init_l_Lean_Fmt_fmtPrefixOperator___closed__4(void){
_start:
{
uint32_t v___x_3695_; uint8_t v___x_3696_; 
v___x_3695_ = 90;
v___x_3696_ = lean_uint32_to_uint8(v___x_3695_);
return v___x_3696_;
}
}
static uint8_t _init_l_Lean_Fmt_fmtPrefixOperator___closed__5(void){
_start:
{
uint32_t v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = 97;
v___x_3698_ = lean_uint32_to_uint8(v___x_3697_);
return v___x_3698_;
}
}
static uint8_t _init_l_Lean_Fmt_fmtPrefixOperator___closed__6(void){
_start:
{
uint32_t v___x_3699_; uint8_t v___x_3700_; 
v___x_3699_ = 122;
v___x_3700_ = lean_uint32_to_uint8(v___x_3699_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator(lean_object* v_stx_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_){
_start:
{
lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; uint8_t v___y_3708_; lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3711_ = l_Lean_Syntax_getNumArgs(v_stx_3701_);
v___x_3712_ = lean_unsigned_to_nat(2u);
v___x_3713_ = lean_nat_dec_eq(v___x_3711_, v___x_3712_);
lean_dec(v___x_3711_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v_a_3703_);
return v___x_3715_;
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = lean_unsigned_to_nat(0u);
v___x_3717_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3701_, v___x_3716_, v_a_3703_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v_a_3719_; lean_object* v___x_3720_; lean_object* v___y_3722_; uint8_t v___y_3747_; lean_object* v___y_3759_; lean_object* v_startInclusive_3760_; lean_object* v_endExclusive_3761_; uint8_t v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; uint8_t v___y_3774_; uint32_t v___y_3785_; uint32_t v___y_3790_; uint8_t v___y_3791_; uint32_t v___y_3797_; lean_object* v___x_3812_; uint8_t v___x_3813_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
v_a_3719_ = lean_ctor_get(v___x_3717_, 1);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3717_, 2);
v___x_3720_ = l_Lean_Syntax_getAtomVal(v_a_3718_);
v___x_3812_ = lean_string_utf8_byte_size(v___x_3720_);
v___x_3813_ = lean_nat_dec_lt(v___x_3716_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3814_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3815_ = lean_string_append(v___x_3814_, v___x_3720_);
v___x_3816_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3817_ = lean_string_append(v___x_3815_, v___x_3816_);
v___x_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
v___y_3722_ = v___x_3818_;
goto v___jp_3721_;
}
else
{
uint8_t v_c_3819_; uint8_t v___x_3828_; uint8_t v___x_3829_; 
v_c_3819_ = lean_string_get_byte_fast(v___x_3720_, v___x_3716_);
v___x_3828_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__5, &l_Lean_Fmt_fmtPrefixOperator___closed__5_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__5);
v___x_3829_ = lean_uint8_dec_le(v___x_3828_, v_c_3819_);
if (v___x_3829_ == 0)
{
goto v___jp_3823_;
}
else
{
uint8_t v___x_3830_; uint8_t v___x_3831_; 
v___x_3830_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__6, &l_Lean_Fmt_fmtPrefixOperator___closed__6_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__6);
v___x_3831_ = lean_uint8_dec_le(v_c_3819_, v___x_3830_);
if (v___x_3831_ == 0)
{
goto v___jp_3823_;
}
else
{
goto v___jp_3809_;
}
}
v___jp_3820_:
{
uint8_t v___x_3821_; uint8_t v___x_3822_; 
v___x_3821_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__2, &l_Lean_Fmt_fmtPrefixOperator___closed__2_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__2);
v___x_3822_ = lean_uint8_dec_eq(v_c_3819_, v___x_3821_);
if (v___x_3822_ == 0)
{
goto v___jp_3802_;
}
else
{
goto v___jp_3809_;
}
}
v___jp_3823_:
{
uint8_t v___x_3824_; uint8_t v___x_3825_; 
v___x_3824_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__3, &l_Lean_Fmt_fmtPrefixOperator___closed__3_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__3);
v___x_3825_ = lean_uint8_dec_le(v___x_3824_, v_c_3819_);
if (v___x_3825_ == 0)
{
goto v___jp_3820_;
}
else
{
uint8_t v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__4, &l_Lean_Fmt_fmtPrefixOperator___closed__4_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__4);
v___x_3827_ = lean_uint8_dec_le(v_c_3819_, v___x_3826_);
if (v___x_3827_ == 0)
{
goto v___jp_3820_;
}
else
{
goto v___jp_3809_;
}
}
}
}
v___jp_3721_:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Lean_Fmt_fmt(v_a_3718_, v_a_3702_, v_a_3719_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v_a_3724_; lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_a_3724_ = lean_ctor_get(v___x_3723_, 0);
lean_inc(v_a_3724_);
v_a_3725_ = lean_ctor_get(v___x_3723_, 1);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3723_, 2);
v___x_3726_ = lean_unsigned_to_nat(1u);
v___x_3727_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3701_, v___x_3726_, v_a_3725_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v_a_3729_; lean_object* v___x_3730_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
v_a_3729_ = lean_ctor_get(v___x_3727_, 1);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___x_3727_, 2);
v___x_3730_ = l_Lean_Fmt_fmt(v_a_3728_, v_a_3702_, v_a_3729_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v_a_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
v_a_3732_ = lean_ctor_get(v___x_3730_, 1);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3730_, 2);
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3720_);
v___x_3734_ = l_Option_instBEq_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3722_, v___x_3733_);
lean_dec_ref_known(v___x_3733_, 1);
lean_dec(v___y_3722_);
if (v___x_3734_ == 0)
{
uint8_t v___x_3735_; 
v___x_3735_ = 1;
v___y_3705_ = v_a_3724_;
v___y_3706_ = v_a_3731_;
v___y_3707_ = v_a_3732_;
v___y_3708_ = v___x_3735_;
goto v___jp_3704_;
}
else
{
uint8_t v___x_3736_; 
v___x_3736_ = 2;
v___y_3705_ = v_a_3724_;
v___y_3706_ = v_a_3731_;
v___y_3707_ = v_a_3732_;
v___y_3708_ = v___x_3736_;
goto v___jp_3704_;
}
}
else
{
lean_dec(v_a_3724_);
lean_dec(v___y_3722_);
lean_dec_ref(v___x_3720_);
return v___x_3730_;
}
}
else
{
lean_object* v_a_3737_; lean_object* v_a_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
lean_dec(v_a_3724_);
lean_dec(v___y_3722_);
lean_dec_ref(v___x_3720_);
v_a_3737_ = lean_ctor_get(v___x_3727_, 0);
v_a_3738_ = lean_ctor_get(v___x_3727_, 1);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3740_ = v___x_3727_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_a_3738_);
lean_inc(v_a_3737_);
lean_dec(v___x_3727_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3737_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_a_3738_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
}
else
{
lean_dec(v___y_3722_);
lean_dec_ref(v___x_3720_);
return v___x_3723_;
}
}
v___jp_3746_:
{
if (v___y_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3748_ = lean_string_utf8_byte_size(v___x_3720_);
lean_inc_ref(v___x_3720_);
v___x_3749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3720_);
lean_ctor_set(v___x_3749_, 1, v___x_3716_);
lean_ctor_set(v___x_3749_, 2, v___x_3748_);
v___x_3750_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3749_);
lean_dec_ref_known(v___x_3749_, 3);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3751_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3752_ = lean_string_append(v___x_3751_, v___x_3720_);
v___x_3753_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3754_ = lean_string_append(v___x_3752_, v___x_3753_);
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
v___y_3722_ = v___x_3755_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_box(0);
v___y_3722_ = v___x_3756_;
goto v___jp_3721_;
}
}
else
{
lean_object* v___x_3757_; 
lean_inc_ref(v___x_3720_);
v___x_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3720_);
v___y_3722_ = v___x_3757_;
goto v___jp_3721_;
}
}
v___jp_3758_:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v_decide_3764_; 
v___x_3762_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3759_, v___x_3716_);
lean_dec_ref(v___y_3759_);
v___x_3763_ = lean_nat_sub(v_endExclusive_3761_, v_startInclusive_3760_);
lean_dec(v_startInclusive_3760_);
lean_dec(v_endExclusive_3761_);
v_decide_3764_ = lean_nat_dec_eq(v___x_3762_, v___x_3763_);
lean_dec(v___x_3763_);
lean_dec(v___x_3762_);
v___y_3747_ = v_decide_3764_;
goto v___jp_3746_;
}
v___jp_3765_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v_startInclusive_3768_; lean_object* v_endExclusive_3769_; 
v___x_3766_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3767_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3766_);
v_startInclusive_3768_ = lean_ctor_get(v___x_3767_, 1);
lean_inc(v_startInclusive_3768_);
v_endExclusive_3769_ = lean_ctor_get(v___x_3767_, 2);
lean_inc(v_endExclusive_3769_);
v___y_3759_ = v___x_3767_;
v_startInclusive_3760_ = v_startInclusive_3768_;
v_endExclusive_3761_ = v_endExclusive_3769_;
goto v___jp_3758_;
}
v___jp_3770_:
{
if (v___y_3771_ == 0)
{
lean_dec(v___y_3773_);
lean_dec(v___y_3772_);
goto v___jp_3765_;
}
else
{
if (v___y_3774_ == 0)
{
lean_dec(v___y_3773_);
lean_dec(v___y_3772_);
goto v___jp_3765_;
}
else
{
lean_object* v___x_3775_; 
lean_inc(v___y_3773_);
lean_inc(v___y_3772_);
lean_inc_ref(v___x_3720_);
v___x_3775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3720_);
lean_ctor_set(v___x_3775_, 1, v___y_3772_);
lean_ctor_set(v___x_3775_, 2, v___y_3773_);
v___y_3759_ = v___x_3775_;
v_startInclusive_3760_ = v___y_3772_;
v_endExclusive_3761_ = v___y_3773_;
goto v___jp_3758_;
}
}
}
v___jp_3776_:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; uint8_t v___x_3782_; 
v___x_3777_ = lean_string_utf8_byte_size(v___x_3720_);
lean_inc_ref(v___x_3720_);
v___x_3778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3720_);
lean_ctor_set(v___x_3778_, 1, v___x_3716_);
lean_ctor_set(v___x_3778_, 2, v___x_3777_);
v___x_3779_ = lean_unsigned_to_nat(1u);
v___x_3780_ = l_Substring_Raw_nextn(v___x_3778_, v___x_3779_, v___x_3716_);
lean_dec_ref_known(v___x_3778_, 3);
v___x_3781_ = lean_string_is_valid_pos(v___x_3720_, v___x_3780_);
v___x_3782_ = lean_string_is_valid_pos(v___x_3720_, v___x_3777_);
if (v___x_3782_ == 0)
{
v___y_3771_ = v___x_3781_;
v___y_3772_ = v___x_3780_;
v___y_3773_ = v___x_3777_;
v___y_3774_ = v___x_3782_;
goto v___jp_3770_;
}
else
{
uint8_t v___x_3783_; 
v___x_3783_ = lean_nat_dec_le(v___x_3780_, v___x_3777_);
v___y_3771_ = v___x_3781_;
v___y_3772_ = v___x_3780_;
v___y_3773_ = v___x_3777_;
v___y_3774_ = v___x_3783_;
goto v___jp_3770_;
}
}
v___jp_3784_:
{
uint32_t v___x_3786_; uint8_t v___x_3787_; 
v___x_3786_ = 95;
v___x_3787_ = lean_uint32_dec_eq(v___y_3785_, v___x_3786_);
if (v___x_3787_ == 0)
{
uint8_t v___x_3788_; 
v___x_3788_ = l_Lean_isLetterLike(v___y_3785_);
if (v___x_3788_ == 0)
{
v___y_3747_ = v___x_3788_;
goto v___jp_3746_;
}
else
{
goto v___jp_3776_;
}
}
else
{
goto v___jp_3776_;
}
}
v___jp_3789_:
{
if (v___y_3791_ == 0)
{
uint32_t v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = 97;
v___x_3793_ = lean_uint32_dec_le(v___x_3792_, v___y_3790_);
if (v___x_3793_ == 0)
{
v___y_3785_ = v___y_3790_;
goto v___jp_3784_;
}
else
{
uint32_t v___x_3794_; uint8_t v___x_3795_; 
v___x_3794_ = 122;
v___x_3795_ = lean_uint32_dec_le(v___y_3790_, v___x_3794_);
if (v___x_3795_ == 0)
{
v___y_3785_ = v___y_3790_;
goto v___jp_3784_;
}
else
{
goto v___jp_3776_;
}
}
}
else
{
goto v___jp_3776_;
}
}
v___jp_3796_:
{
uint32_t v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = 65;
v___x_3799_ = lean_uint32_dec_le(v___x_3798_, v___y_3797_);
if (v___x_3799_ == 0)
{
v___y_3790_ = v___y_3797_;
v___y_3791_ = v___x_3799_;
goto v___jp_3789_;
}
else
{
uint32_t v___x_3800_; uint8_t v___x_3801_; 
v___x_3800_ = 90;
v___x_3801_ = lean_uint32_dec_le(v___y_3797_, v___x_3800_);
v___y_3790_ = v___y_3797_;
v___y_3791_ = v___x_3801_;
goto v___jp_3789_;
}
}
v___jp_3802_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = lean_string_utf8_byte_size(v___x_3720_);
lean_inc_ref(v___x_3720_);
v___x_3804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3720_);
lean_ctor_set(v___x_3804_, 1, v___x_3716_);
lean_ctor_set(v___x_3804_, 2, v___x_3803_);
v___x_3805_ = l_String_Slice_Pos_get_x3f(v___x_3804_, v___x_3716_);
lean_dec_ref_known(v___x_3804_, 3);
if (lean_obj_tag(v___x_3805_) == 0)
{
uint32_t v___x_3806_; 
v___x_3806_ = 65;
v___y_3797_ = v___x_3806_;
goto v___jp_3796_;
}
else
{
lean_object* v_val_3807_; uint32_t v___x_3808_; 
v_val_3807_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_val_3807_);
lean_dec_ref_known(v___x_3805_, 1);
v___x_3808_ = lean_unbox_uint32(v_val_3807_);
lean_dec(v_val_3807_);
v___y_3797_ = v___x_3808_;
goto v___jp_3796_;
}
}
v___jp_3809_:
{
lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = lean_unsigned_to_nat(1u);
v___x_3811_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3720_, v___x_3810_);
if (v___x_3811_ == 0)
{
goto v___jp_3802_;
}
else
{
v___y_3747_ = v___x_3811_;
goto v___jp_3746_;
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
v_a_3832_ = lean_ctor_get(v___x_3717_, 0);
v_a_3833_ = lean_ctor_get(v___x_3717_, 1);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3717_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_inc(v_a_3832_);
lean_dec(v___x_3717_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3832_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
v___jp_3704_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = l_Lean_Fmt_Layouts_prefixOperator(v___y_3705_, v___y_3706_, v___y_3708_);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___y_3707_);
return v___x_3710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrefixOperator___boxed(lean_object* v_stx_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_Fmt_fmtPrefixOperator(v_stx_3841_, v_a_3842_, v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_stx_3841_);
return v_res_3844_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(lean_object* v_s_3845_, lean_object* v_inst_3846_, lean_object* v_R_3847_, lean_object* v_a_3848_, uint8_t v_b_3849_, lean_object* v_c_3850_){
_start:
{
uint8_t v___x_3851_; 
v___x_3851_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___redArg(v_s_3845_, v_a_3848_, v_b_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1___boxed(lean_object* v_s_3852_, lean_object* v_inst_3853_, lean_object* v_R_3854_, lean_object* v_a_3855_, lean_object* v_b_3856_, lean_object* v_c_3857_){
_start:
{
uint8_t v_b_boxed_3858_; uint8_t v_res_3859_; lean_object* v_r_3860_; 
v_b_boxed_3858_ = lean_unbox(v_b_3856_);
v_res_3859_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1_spec__1(v_s_3852_, v_inst_3853_, v_R_3854_, v_a_3855_, v_b_boxed_3858_, v_c_3857_);
lean_dec_ref(v_s_3852_);
v_r_3860_ = lean_box(v_res_3859_);
return v_r_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator(lean_object* v_stx_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3864_ = l_Lean_Syntax_getNumArgs(v_stx_3861_);
v___x_3865_ = lean_unsigned_to_nat(2u);
v___x_3866_ = lean_nat_dec_eq(v___x_3864_, v___x_3865_);
lean_dec(v___x_3864_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = l_Lean_Fmt_Error_partialFormatter;
v___x_3868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set(v___x_3868_, 1, v_a_3863_);
return v___x_3868_;
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_unsigned_to_nat(0u);
v___x_3870_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3861_, v___x_3869_, v_a_3863_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_a_3872_; lean_object* v___x_3873_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
v_a_3872_ = lean_ctor_get(v___x_3870_, 1);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3870_, 2);
v___x_3873_ = l_Lean_Fmt_fmt(v_a_3871_, v_a_3862_, v_a_3872_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3994_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_a_3875_ = lean_ctor_get(v___x_3873_, 1);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3877_ = v___x_3873_;
v_isShared_3878_ = v_isSharedCheck_3994_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3994_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___y_3880_; lean_object* v___y_3881_; uint8_t v___y_3882_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_unsigned_to_nat(1u);
v___x_3888_ = l_Lean_Fmt_getStxArg_x21___redArg(v_stx_3861_, v___x_3887_, v_a_3875_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v_a_3890_; lean_object* v___x_3891_; lean_object* v___y_3893_; uint8_t v___y_3902_; lean_object* v___y_3914_; lean_object* v_startInclusive_3915_; lean_object* v_endExclusive_3916_; lean_object* v___y_3926_; lean_object* v___y_3927_; uint8_t v___y_3928_; uint8_t v___y_3929_; uint32_t v___y_3939_; uint32_t v___y_3944_; uint8_t v___y_3945_; uint32_t v___y_3951_; lean_object* v___x_3965_; uint8_t v___x_3966_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
v_a_3890_ = lean_ctor_get(v___x_3888_, 1);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3888_, 2);
v___x_3891_ = l_Lean_Syntax_getAtomVal(v_a_3889_);
v___x_3965_ = lean_string_utf8_byte_size(v___x_3891_);
v___x_3966_ = lean_nat_dec_lt(v___x_3869_, v___x_3965_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3967_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3968_ = lean_string_append(v___x_3967_, v___x_3891_);
v___x_3969_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3970_ = lean_string_append(v___x_3968_, v___x_3969_);
v___x_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3970_);
v___y_3893_ = v___x_3971_;
goto v___jp_3892_;
}
else
{
uint8_t v_c_3972_; uint8_t v___x_3981_; uint8_t v___x_3982_; 
v_c_3972_ = lean_string_get_byte_fast(v___x_3891_, v___x_3869_);
v___x_3981_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__5, &l_Lean_Fmt_fmtPrefixOperator___closed__5_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__5);
v___x_3982_ = lean_uint8_dec_le(v___x_3981_, v_c_3972_);
if (v___x_3982_ == 0)
{
goto v___jp_3976_;
}
else
{
uint8_t v___x_3983_; uint8_t v___x_3984_; 
v___x_3983_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__6, &l_Lean_Fmt_fmtPrefixOperator___closed__6_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__6);
v___x_3984_ = lean_uint8_dec_le(v_c_3972_, v___x_3983_);
if (v___x_3984_ == 0)
{
goto v___jp_3976_;
}
else
{
goto v___jp_3963_;
}
}
v___jp_3973_:
{
uint8_t v___x_3974_; uint8_t v___x_3975_; 
v___x_3974_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__2, &l_Lean_Fmt_fmtPrefixOperator___closed__2_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__2);
v___x_3975_ = lean_uint8_dec_eq(v_c_3972_, v___x_3974_);
if (v___x_3975_ == 0)
{
goto v___jp_3956_;
}
else
{
goto v___jp_3963_;
}
}
v___jp_3976_:
{
uint8_t v___x_3977_; uint8_t v___x_3978_; 
v___x_3977_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__3, &l_Lean_Fmt_fmtPrefixOperator___closed__3_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__3);
v___x_3978_ = lean_uint8_dec_le(v___x_3977_, v_c_3972_);
if (v___x_3978_ == 0)
{
goto v___jp_3973_;
}
else
{
uint8_t v___x_3979_; uint8_t v___x_3980_; 
v___x_3979_ = lean_uint8_once(&l_Lean_Fmt_fmtPrefixOperator___closed__4, &l_Lean_Fmt_fmtPrefixOperator___closed__4_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__4);
v___x_3980_ = lean_uint8_dec_le(v_c_3972_, v___x_3979_);
if (v___x_3980_ == 0)
{
goto v___jp_3973_;
}
else
{
goto v___jp_3963_;
}
}
}
}
v___jp_3892_:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_Fmt_fmt(v_a_3889_, v_a_3862_, v_a_3890_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v_a_3896_; lean_object* v___x_3897_; uint8_t v___x_3898_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
v_a_3896_ = lean_ctor_get(v___x_3894_, 1);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3894_, 2);
v___x_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3891_);
v___x_3898_ = l_Option_instBEq_beq___at___00Lean_Fmt_fmtPrefixOperator_spec__0(v___y_3893_, v___x_3897_);
lean_dec_ref_known(v___x_3897_, 1);
lean_dec(v___y_3893_);
if (v___x_3898_ == 0)
{
uint8_t v___x_3899_; 
v___x_3899_ = 0;
v___y_3880_ = v_a_3895_;
v___y_3881_ = v_a_3896_;
v___y_3882_ = v___x_3899_;
goto v___jp_3879_;
}
else
{
uint8_t v___x_3900_; 
v___x_3900_ = 1;
v___y_3880_ = v_a_3895_;
v___y_3881_ = v_a_3896_;
v___y_3882_ = v___x_3900_;
goto v___jp_3879_;
}
}
else
{
lean_dec(v___y_3893_);
lean_dec_ref(v___x_3891_);
lean_del_object(v___x_3877_);
lean_dec(v_a_3874_);
return v___x_3894_;
}
}
v___jp_3901_:
{
if (v___y_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; 
v___x_3903_ = lean_string_utf8_byte_size(v___x_3891_);
lean_inc_ref(v___x_3891_);
v___x_3904_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3891_);
lean_ctor_set(v___x_3904_, 1, v___x_3869_);
lean_ctor_set(v___x_3904_, 2, v___x_3903_);
v___x_3905_ = l_String_Slice_contains___at___00Lean_Fmt_fmtPrefixOperator_spec__1(v___x_3904_);
lean_dec_ref_known(v___x_3904_, 3);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3906_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__0, &l_Lean_Fmt_fmtPrefixOperator___closed__0_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__0);
v___x_3907_ = lean_string_append(v___x_3906_, v___x_3891_);
v___x_3908_ = lean_obj_once(&l_Lean_Fmt_fmtPrefixOperator___closed__1, &l_Lean_Fmt_fmtPrefixOperator___closed__1_once, _init_l_Lean_Fmt_fmtPrefixOperator___closed__1);
v___x_3909_ = lean_string_append(v___x_3907_, v___x_3908_);
v___x_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
v___y_3893_ = v___x_3910_;
goto v___jp_3892_;
}
else
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_box(0);
v___y_3893_ = v___x_3911_;
goto v___jp_3892_;
}
}
else
{
lean_object* v___x_3912_; 
lean_inc_ref(v___x_3891_);
v___x_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3891_);
v___y_3893_ = v___x_3912_;
goto v___jp_3892_;
}
}
v___jp_3913_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; uint8_t v_decide_3919_; 
v___x_3917_ = l_String_Slice_Pos_skipWhile___at___00Lean_Fmt_fmtPrefixOperator_spec__2(v___y_3914_, v___x_3869_);
lean_dec_ref(v___y_3914_);
v___x_3918_ = lean_nat_sub(v_endExclusive_3916_, v_startInclusive_3915_);
lean_dec(v_startInclusive_3915_);
lean_dec(v_endExclusive_3916_);
v_decide_3919_ = lean_nat_dec_eq(v___x_3917_, v___x_3918_);
lean_dec(v___x_3918_);
lean_dec(v___x_3917_);
v___y_3902_ = v_decide_3919_;
goto v___jp_3901_;
}
v___jp_3920_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v_startInclusive_3923_; lean_object* v_endExclusive_3924_; 
v___x_3921_ = lean_obj_once(&l_Lean_Fmt_getLineInfo_x21___closed__9, &l_Lean_Fmt_getLineInfo_x21___closed__9_once, _init_l_Lean_Fmt_getLineInfo_x21___closed__9);
v___x_3922_ = l_panic___at___00Lean_Fmt_fmtPrefixOperator_spec__3(v___x_3921_);
v_startInclusive_3923_ = lean_ctor_get(v___x_3922_, 1);
lean_inc(v_startInclusive_3923_);
v_endExclusive_3924_ = lean_ctor_get(v___x_3922_, 2);
lean_inc(v_endExclusive_3924_);
v___y_3914_ = v___x_3922_;
v_startInclusive_3915_ = v_startInclusive_3923_;
v_endExclusive_3916_ = v_endExclusive_3924_;
goto v___jp_3913_;
}
v___jp_3925_:
{
if (v___y_3928_ == 0)
{
lean_dec(v___y_3927_);
lean_dec(v___y_3926_);
goto v___jp_3920_;
}
else
{
if (v___y_3929_ == 0)
{
lean_dec(v___y_3927_);
lean_dec(v___y_3926_);
goto v___jp_3920_;
}
else
{
lean_object* v___x_3930_; 
lean_inc(v___y_3927_);
lean_inc(v___y_3926_);
lean_inc_ref(v___x_3891_);
v___x_3930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3891_);
lean_ctor_set(v___x_3930_, 1, v___y_3926_);
lean_ctor_set(v___x_3930_, 2, v___y_3927_);
v___y_3914_ = v___x_3930_;
v_startInclusive_3915_ = v___y_3926_;
v_endExclusive_3916_ = v___y_3927_;
goto v___jp_3913_;
}
}
}
v___jp_3931_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; uint8_t v___x_3936_; 
v___x_3932_ = lean_string_utf8_byte_size(v___x_3891_);
lean_inc_ref(v___x_3891_);
v___x_3933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3891_);
lean_ctor_set(v___x_3933_, 1, v___x_3869_);
lean_ctor_set(v___x_3933_, 2, v___x_3932_);
v___x_3934_ = l_Substring_Raw_nextn(v___x_3933_, v___x_3887_, v___x_3869_);
lean_dec_ref_known(v___x_3933_, 3);
v___x_3935_ = lean_string_is_valid_pos(v___x_3891_, v___x_3934_);
v___x_3936_ = lean_string_is_valid_pos(v___x_3891_, v___x_3932_);
if (v___x_3936_ == 0)
{
v___y_3926_ = v___x_3934_;
v___y_3927_ = v___x_3932_;
v___y_3928_ = v___x_3935_;
v___y_3929_ = v___x_3936_;
goto v___jp_3925_;
}
else
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_nat_dec_le(v___x_3934_, v___x_3932_);
v___y_3926_ = v___x_3934_;
v___y_3927_ = v___x_3932_;
v___y_3928_ = v___x_3935_;
v___y_3929_ = v___x_3937_;
goto v___jp_3925_;
}
}
v___jp_3938_:
{
uint32_t v___x_3940_; uint8_t v___x_3941_; 
v___x_3940_ = 95;
v___x_3941_ = lean_uint32_dec_eq(v___y_3939_, v___x_3940_);
if (v___x_3941_ == 0)
{
uint8_t v___x_3942_; 
v___x_3942_ = l_Lean_isLetterLike(v___y_3939_);
if (v___x_3942_ == 0)
{
v___y_3902_ = v___x_3942_;
goto v___jp_3901_;
}
else
{
goto v___jp_3931_;
}
}
else
{
goto v___jp_3931_;
}
}
v___jp_3943_:
{
if (v___y_3945_ == 0)
{
uint32_t v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = 97;
v___x_3947_ = lean_uint32_dec_le(v___x_3946_, v___y_3944_);
if (v___x_3947_ == 0)
{
v___y_3939_ = v___y_3944_;
goto v___jp_3938_;
}
else
{
uint32_t v___x_3948_; uint8_t v___x_3949_; 
v___x_3948_ = 122;
v___x_3949_ = lean_uint32_dec_le(v___y_3944_, v___x_3948_);
if (v___x_3949_ == 0)
{
v___y_3939_ = v___y_3944_;
goto v___jp_3938_;
}
else
{
goto v___jp_3931_;
}
}
}
else
{
goto v___jp_3931_;
}
}
v___jp_3950_:
{
uint32_t v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = 65;
v___x_3953_ = lean_uint32_dec_le(v___x_3952_, v___y_3951_);
if (v___x_3953_ == 0)
{
v___y_3944_ = v___y_3951_;
v___y_3945_ = v___x_3953_;
goto v___jp_3943_;
}
else
{
uint32_t v___x_3954_; uint8_t v___x_3955_; 
v___x_3954_ = 90;
v___x_3955_ = lean_uint32_dec_le(v___y_3951_, v___x_3954_);
v___y_3944_ = v___y_3951_;
v___y_3945_ = v___x_3955_;
goto v___jp_3943_;
}
}
v___jp_3956_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = lean_string_utf8_byte_size(v___x_3891_);
lean_inc_ref(v___x_3891_);
v___x_3958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3891_);
lean_ctor_set(v___x_3958_, 1, v___x_3869_);
lean_ctor_set(v___x_3958_, 2, v___x_3957_);
v___x_3959_ = l_String_Slice_Pos_get_x3f(v___x_3958_, v___x_3869_);
lean_dec_ref_known(v___x_3958_, 3);
if (lean_obj_tag(v___x_3959_) == 0)
{
uint32_t v___x_3960_; 
v___x_3960_ = 65;
v___y_3951_ = v___x_3960_;
goto v___jp_3950_;
}
else
{
lean_object* v_val_3961_; uint32_t v___x_3962_; 
v_val_3961_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_val_3961_);
lean_dec_ref_known(v___x_3959_, 1);
v___x_3962_ = lean_unbox_uint32(v_val_3961_);
lean_dec(v_val_3961_);
v___y_3951_ = v___x_3962_;
goto v___jp_3950_;
}
}
v___jp_3963_:
{
uint8_t v___x_3964_; 
v___x_3964_ = l___private_Init_Data_ToString_Name_0__Lean_Name_needsNoEscapeAsciiRest(v___x_3891_, v___x_3887_);
if (v___x_3964_ == 0)
{
goto v___jp_3956_;
}
else
{
v___y_3902_ = v___x_3964_;
goto v___jp_3901_;
}
}
}
else
{
lean_object* v_a_3985_; lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_del_object(v___x_3877_);
lean_dec(v_a_3874_);
v_a_3985_ = lean_ctor_get(v___x_3888_, 0);
v_a_3986_ = lean_ctor_get(v___x_3888_, 1);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3888_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3888_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_inc(v_a_3985_);
lean_dec(v___x_3888_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3985_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
v___jp_3879_:
{
lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3883_ = l_Lean_Fmt_Layouts_postfixOperator(v_a_3874_, v___y_3880_, v___y_3882_);
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 1, v___y_3881_);
lean_ctor_set(v___x_3877_, 0, v___x_3883_);
v___x_3885_ = v___x_3877_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v___y_3881_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
return v___x_3873_;
}
}
else
{
lean_object* v_a_3995_; lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
v_a_3995_ = lean_ctor_get(v___x_3870_, 0);
v_a_3996_ = lean_ctor_get(v___x_3870_, 1);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3870_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_inc(v_a_3995_);
lean_dec(v___x_3870_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3995_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPostfixOperator___boxed(lean_object* v_stx_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_Fmt_fmtPostfixOperator(v_stx_4004_, v_a_4005_, v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_stx_4004_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(size_t v_sz_4008_, size_t v_i_4009_, lean_object* v_bs_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_usize_dec_lt(v_i_4009_, v_sz_4008_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4014_, 0, v_bs_4010_);
lean_ctor_set(v___x_4014_, 1, v___y_4012_);
return v___x_4014_;
}
else
{
lean_object* v_v_4015_; lean_object* v_elseTk_4016_; lean_object* v_ifTk_4017_; lean_object* v_cond_4018_; lean_object* v_thenTk_4019_; lean_object* v_body_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4081_; 
v_v_4015_ = lean_array_uget(v_bs_4010_, v_i_4009_);
v_elseTk_4016_ = lean_ctor_get(v_v_4015_, 0);
v_ifTk_4017_ = lean_ctor_get(v_v_4015_, 1);
v_cond_4018_ = lean_ctor_get(v_v_4015_, 2);
v_thenTk_4019_ = lean_ctor_get(v_v_4015_, 3);
v_body_4020_ = lean_ctor_get(v_v_4015_, 4);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_v_4015_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4022_ = v_v_4015_;
v_isShared_4023_ = v_isSharedCheck_4081_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_body_4020_);
lean_inc(v_thenTk_4019_);
lean_inc(v_cond_4018_);
lean_inc(v_ifTk_4017_);
lean_inc(v_elseTk_4016_);
lean_dec(v_v_4015_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4081_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_Fmt_fmt(v_elseTk_4016_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v_a_4026_; lean_object* v___x_4027_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
v_a_4026_ = lean_ctor_get(v___x_4024_, 1);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4024_, 2);
v___x_4027_ = l_Lean_Fmt_fmt(v_ifTk_4017_, v___y_4011_, v_a_4026_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v_a_4029_; lean_object* v___x_4030_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
v_a_4029_ = lean_ctor_get(v___x_4027_, 1);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4027_, 2);
v___x_4030_ = l_Lean_Fmt_fmt(v_thenTk_4019_, v___y_4011_, v_a_4029_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v_a_4032_; lean_object* v___x_4033_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
v_a_4032_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4030_, 2);
v___x_4033_ = l_Lean_Fmt_fmt(v_body_4020_, v___y_4011_, v_a_4032_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v_a_4035_; lean_object* v___x_4036_; lean_object* v_bs_x27_4037_; lean_object* v___x_4039_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
v_a_4035_ = lean_ctor_get(v___x_4033_, 1);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4033_, 2);
v___x_4036_ = lean_unsigned_to_nat(0u);
v_bs_x27_4037_ = lean_array_uset(v_bs_4010_, v_i_4009_, v___x_4036_);
if (v_isShared_4023_ == 0)
{
lean_ctor_set(v___x_4022_, 4, v_a_4034_);
lean_ctor_set(v___x_4022_, 3, v_a_4031_);
lean_ctor_set(v___x_4022_, 1, v_a_4028_);
lean_ctor_set(v___x_4022_, 0, v_a_4025_);
v___x_4039_ = v___x_4022_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4025_);
lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_a_4028_);
lean_ctor_set(v_reuseFailAlloc_4044_, 2, v_cond_4018_);
lean_ctor_set(v_reuseFailAlloc_4044_, 3, v_a_4031_);
lean_ctor_set(v_reuseFailAlloc_4044_, 4, v_a_4034_);
v___x_4039_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
size_t v___x_4040_; size_t v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = ((size_t)1ULL);
v___x_4041_ = lean_usize_add(v_i_4009_, v___x_4040_);
v___x_4042_ = lean_array_uset(v_bs_x27_4037_, v_i_4009_, v___x_4039_);
v_i_4009_ = v___x_4041_;
v_bs_4010_ = v___x_4042_;
v___y_4012_ = v_a_4035_;
goto _start;
}
}
else
{
lean_object* v_a_4045_; lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec(v_a_4031_);
lean_dec(v_a_4028_);
lean_dec(v_a_4025_);
lean_del_object(v___x_4022_);
lean_dec_ref(v_cond_4018_);
lean_dec_ref(v_bs_4010_);
v_a_4045_ = lean_ctor_get(v___x_4033_, 0);
v_a_4046_ = lean_ctor_get(v___x_4033_, 1);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4033_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_inc(v_a_4045_);
lean_dec(v___x_4033_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4045_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec(v_a_4028_);
lean_dec(v_a_4025_);
lean_del_object(v___x_4022_);
lean_dec(v_body_4020_);
lean_dec_ref(v_cond_4018_);
lean_dec_ref(v_bs_4010_);
v_a_4054_ = lean_ctor_get(v___x_4030_, 0);
v_a_4055_ = lean_ctor_get(v___x_4030_, 1);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4030_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_inc(v_a_4054_);
lean_dec(v___x_4030_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4054_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_a_4025_);
lean_del_object(v___x_4022_);
lean_dec(v_body_4020_);
lean_dec(v_thenTk_4019_);
lean_dec_ref(v_cond_4018_);
lean_dec_ref(v_bs_4010_);
v_a_4063_ = lean_ctor_get(v___x_4027_, 0);
v_a_4064_ = lean_ctor_get(v___x_4027_, 1);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4027_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_inc(v_a_4063_);
lean_dec(v___x_4027_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4063_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_del_object(v___x_4022_);
lean_dec(v_body_4020_);
lean_dec(v_thenTk_4019_);
lean_dec_ref(v_cond_4018_);
lean_dec(v_ifTk_4017_);
lean_dec_ref(v_bs_4010_);
v_a_4072_ = lean_ctor_get(v___x_4024_, 0);
v_a_4073_ = lean_ctor_get(v___x_4024_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4024_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_inc(v_a_4072_);
lean_dec(v___x_4024_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4072_);
lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1___boxed(lean_object* v_sz_4082_, lean_object* v_i_4083_, lean_object* v_bs_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
size_t v_sz_boxed_4087_; size_t v_i_boxed_4088_; lean_object* v_res_4089_; 
v_sz_boxed_4087_ = lean_unbox_usize(v_sz_4082_);
lean_dec(v_sz_4082_);
v_i_boxed_4088_ = lean_unbox_usize(v_i_4083_);
lean_dec(v_i_4083_);
v_res_4089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_boxed_4087_, v_i_boxed_4088_, v_bs_4084_, v___y_4085_, v___y_4086_);
lean_dec_ref(v___y_4085_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(lean_object* v_a_4090_, lean_object* v_x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4094_, 0, v_a_4090_);
v___x_4095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
lean_ctor_set(v___x_4095_, 1, v___y_4093_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0___boxed(lean_object* v_a_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4096_, v_x_4097_, v___y_4098_, v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec_ref(v_x_4097_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(lean_object* v___x_4101_, lean_object* v_val_4102_, lean_object* v_elseIfs_4103_, lean_object* v_ifTk_4104_, lean_object* v_cond_4105_, lean_object* v_thenTk_4106_, lean_object* v_thenBody_4107_, lean_object* v_a_4108_, lean_object* v_____r_4109_, lean_object* v_elseBody_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_inc(v_elseBody_4110_);
v___x_4113_ = l_Lean_Syntax_getKind(v_elseBody_4110_);
v___x_4114_ = l_Lean_Fmt_getConditionalFormatter_x3f(v___x_4101_, v___x_4113_);
lean_dec(v___x_4113_);
if (lean_obj_tag(v___x_4114_) == 1)
{
lean_object* v_val_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4175_; 
v_val_4115_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4117_ = v___x_4114_;
v_isShared_4118_ = v_isSharedCheck_4175_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_val_4115_);
lean_dec(v___x_4114_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4175_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4119_; 
lean_inc_ref(v___y_4111_);
v___x_4119_ = lean_apply_3(v_val_4115_, v_elseBody_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
if (lean_obj_tag(v_a_4120_) == 1)
{
lean_object* v_val_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4153_; 
lean_del_object(v___x_4117_);
lean_dec_ref(v_a_4108_);
v_val_4121_ = lean_ctor_get(v_a_4120_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_a_4120_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4123_ = v_a_4120_;
v_isShared_4124_ = v_isSharedCheck_4153_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_val_4121_);
lean_dec(v_a_4120_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4153_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4151_; 
v_a_4125_ = lean_ctor_get(v___x_4119_, 1);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4151_ == 0)
{
lean_object* v_unused_4152_; 
v_unused_4152_ = lean_ctor_get(v___x_4119_, 0);
lean_dec(v_unused_4152_);
v___x_4127_ = v___x_4119_;
v_isShared_4128_ = v_isSharedCheck_4151_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4119_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4151_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v_ifTk_4129_; lean_object* v_cond_4130_; lean_object* v_thenTk_4131_; lean_object* v_thenBody_4132_; lean_object* v_elseTk_x3f_4133_; lean_object* v_elseBody_x3f_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4149_; 
v_ifTk_4129_ = lean_ctor_get(v_val_4121_, 0);
v_cond_4130_ = lean_ctor_get(v_val_4121_, 1);
v_thenTk_4131_ = lean_ctor_get(v_val_4121_, 2);
v_thenBody_4132_ = lean_ctor_get(v_val_4121_, 3);
v_elseTk_x3f_4133_ = lean_ctor_get(v_val_4121_, 5);
v_elseBody_x3f_4134_ = lean_ctor_get(v_val_4121_, 6);
v_isSharedCheck_4149_ = !lean_is_exclusive(v_val_4121_);
if (v_isSharedCheck_4149_ == 0)
{
lean_object* v_unused_4150_; 
v_unused_4150_ = lean_ctor_get(v_val_4121_, 4);
lean_dec(v_unused_4150_);
v___x_4136_ = v_val_4121_;
v_isShared_4137_ = v_isSharedCheck_4149_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_elseBody_x3f_4134_);
lean_inc(v_elseTk_x3f_4133_);
lean_inc(v_thenBody_4132_);
lean_inc(v_thenTk_4131_);
lean_inc(v_cond_4130_);
lean_inc(v_ifTk_4129_);
lean_dec(v_val_4121_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4149_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4141_; 
v___x_4138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4138_, 0, v_val_4102_);
lean_ctor_set(v___x_4138_, 1, v_ifTk_4129_);
lean_ctor_set(v___x_4138_, 2, v_cond_4130_);
lean_ctor_set(v___x_4138_, 3, v_thenTk_4131_);
lean_ctor_set(v___x_4138_, 4, v_thenBody_4132_);
v___x_4139_ = lean_array_push(v_elseIfs_4103_, v___x_4138_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 4, v___x_4139_);
lean_ctor_set(v___x_4136_, 3, v_thenBody_4107_);
lean_ctor_set(v___x_4136_, 2, v_thenTk_4106_);
lean_ctor_set(v___x_4136_, 1, v_cond_4105_);
lean_ctor_set(v___x_4136_, 0, v_ifTk_4104_);
v___x_4141_ = v___x_4136_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_ifTk_4104_);
lean_ctor_set(v_reuseFailAlloc_4148_, 1, v_cond_4105_);
lean_ctor_set(v_reuseFailAlloc_4148_, 2, v_thenTk_4106_);
lean_ctor_set(v_reuseFailAlloc_4148_, 3, v_thenBody_4107_);
lean_ctor_set(v_reuseFailAlloc_4148_, 4, v___x_4139_);
lean_ctor_set(v_reuseFailAlloc_4148_, 5, v_elseTk_x3f_4133_);
lean_ctor_set(v_reuseFailAlloc_4148_, 6, v_elseBody_x3f_4134_);
v___x_4141_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
lean_object* v___x_4143_; 
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v___x_4141_);
v___x_4143_ = v___x_4123_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4141_);
v___x_4143_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
lean_object* v___x_4145_; 
if (v_isShared_4128_ == 0)
{
lean_ctor_set(v___x_4127_, 0, v___x_4143_);
v___x_4145_ = v___x_4127_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_a_4125_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v_a_4120_);
lean_dec(v_thenBody_4107_);
lean_dec(v_thenTk_4106_);
lean_dec_ref(v_cond_4105_);
lean_dec(v_ifTk_4104_);
lean_dec_ref(v_elseIfs_4103_);
lean_dec(v_val_4102_);
v_a_4154_ = lean_ctor_get(v___x_4119_, 1);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4164_ == 0)
{
lean_object* v_unused_4165_; 
v_unused_4165_ = lean_ctor_get(v___x_4119_, 0);
lean_dec(v_unused_4165_);
v___x_4156_ = v___x_4119_;
v_isShared_4157_ = v_isSharedCheck_4164_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4119_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4164_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4118_ == 0)
{
lean_ctor_set_tag(v___x_4117_, 0);
lean_ctor_set(v___x_4117_, 0, v_a_4108_);
v___x_4159_ = v___x_4117_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4108_);
v___x_4159_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
lean_object* v___x_4161_; 
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v___x_4159_);
v___x_4161_ = v___x_4156_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4162_, 1, v_a_4154_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_del_object(v___x_4117_);
lean_dec_ref(v_a_4108_);
lean_dec(v_thenBody_4107_);
lean_dec(v_thenTk_4106_);
lean_dec_ref(v_cond_4105_);
lean_dec(v_ifTk_4104_);
lean_dec_ref(v_elseIfs_4103_);
lean_dec(v_val_4102_);
v_a_4166_ = lean_ctor_get(v___x_4119_, 0);
v_a_4167_ = lean_ctor_get(v___x_4119_, 1);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4119_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_inc(v_a_4166_);
lean_dec(v___x_4119_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4166_);
lean_ctor_set(v_reuseFailAlloc_4173_, 1, v_a_4167_);
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
lean_object* v___x_4176_; lean_object* v___x_4177_; 
lean_dec(v___x_4114_);
lean_dec(v_elseBody_4110_);
lean_dec(v_thenBody_4107_);
lean_dec(v_thenTk_4106_);
lean_dec_ref(v_cond_4105_);
lean_dec(v_ifTk_4104_);
lean_dec_ref(v_elseIfs_4103_);
lean_dec(v_val_4102_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v_a_4108_);
v___x_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
lean_ctor_set(v___x_4177_, 1, v___y_4112_);
return v___x_4177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1___boxed(lean_object* v___x_4178_, lean_object* v_val_4179_, lean_object* v_elseIfs_4180_, lean_object* v_ifTk_4181_, lean_object* v_cond_4182_, lean_object* v_thenTk_4183_, lean_object* v_thenBody_4184_, lean_object* v_a_4185_, lean_object* v_____r_4186_, lean_object* v_elseBody_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4178_, v_val_4179_, v_elseIfs_4180_, v_ifTk_4181_, v_cond_4182_, v_thenTk_4183_, v_thenBody_4184_, v_a_4185_, v_____r_4186_, v_elseBody_4187_, v___y_4188_, v___y_4189_);
lean_dec_ref(v___y_4188_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(lean_object* v___x_4205_, lean_object* v_a_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v___y_4210_; lean_object* v_elseTk_x3f_4234_; 
v_elseTk_x3f_4234_ = lean_ctor_get(v_a_4206_, 5);
if (lean_obj_tag(v_elseTk_x3f_4234_) == 1)
{
lean_object* v_elseBody_x3f_4235_; 
v_elseBody_x3f_4235_ = lean_ctor_get(v_a_4206_, 6);
if (lean_obj_tag(v_elseBody_x3f_4235_) == 1)
{
lean_object* v_ifTk_4236_; lean_object* v_cond_4237_; lean_object* v_thenTk_4238_; lean_object* v_thenBody_4239_; lean_object* v_elseIfs_4240_; lean_object* v_val_4241_; lean_object* v_val_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; 
v_ifTk_4236_ = lean_ctor_get(v_a_4206_, 0);
lean_inc(v_ifTk_4236_);
v_cond_4237_ = lean_ctor_get(v_a_4206_, 1);
lean_inc_ref(v_cond_4237_);
v_thenTk_4238_ = lean_ctor_get(v_a_4206_, 2);
lean_inc(v_thenTk_4238_);
v_thenBody_4239_ = lean_ctor_get(v_a_4206_, 3);
lean_inc(v_thenBody_4239_);
v_elseIfs_4240_ = lean_ctor_get(v_a_4206_, 4);
lean_inc_ref(v_elseIfs_4240_);
v_val_4241_ = lean_ctor_get(v_elseTk_x3f_4234_, 0);
lean_inc(v_val_4241_);
v_val_4242_ = lean_ctor_get(v_elseBody_x3f_4235_, 0);
v___x_4243_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__3));
lean_inc(v_val_4242_);
v___x_4244_ = l_Lean_Syntax_isOfKind(v_val_4242_, v___x_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_inc(v_val_4242_);
v___x_4245_ = lean_box(0);
lean_inc_ref(v___x_4205_);
v___x_4246_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4205_, v_val_4241_, v_elseIfs_4240_, v_ifTk_4236_, v_cond_4237_, v_thenTk_4238_, v_thenBody_4239_, v_a_4206_, v___x_4245_, v_val_4242_, v___y_4207_, v___y_4208_);
v___y_4210_ = v___x_4246_;
goto v___jp_4209_;
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; 
v___x_4247_ = lean_unsigned_to_nat(0u);
v___x_4248_ = l_Lean_Syntax_getArg(v_val_4242_, v___x_4247_);
v___x_4249_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___closed__5));
lean_inc(v___x_4248_);
v___x_4250_ = l_Lean_Syntax_isOfKind(v___x_4248_, v___x_4249_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
lean_inc(v_val_4242_);
lean_dec(v___x_4248_);
v___x_4251_ = lean_box(0);
lean_inc_ref(v___x_4205_);
v___x_4252_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4205_, v_val_4241_, v_elseIfs_4240_, v_ifTk_4236_, v_cond_4237_, v_thenTk_4238_, v_thenBody_4239_, v_a_4206_, v___x_4251_, v_val_4242_, v___y_4207_, v___y_4208_);
v___y_4210_ = v___x_4252_;
goto v___jp_4209_;
}
else
{
lean_object* v___x_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v___x_4253_ = l_Lean_Syntax_getArg(v___x_4248_, v___x_4247_);
lean_dec(v___x_4248_);
v___x_4254_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_4253_);
v___x_4255_ = l_Lean_Syntax_matchesNull(v___x_4253_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_inc(v_val_4242_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
lean_inc_ref(v___x_4205_);
v___x_4257_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4205_, v_val_4241_, v_elseIfs_4240_, v_ifTk_4236_, v_cond_4237_, v_thenTk_4238_, v_thenBody_4239_, v_a_4206_, v___x_4256_, v_val_4242_, v___y_4207_, v___y_4208_);
v___y_4210_ = v___x_4257_;
goto v___jp_4209_;
}
else
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4258_ = l_Lean_Syntax_getArg(v___x_4253_, v___x_4247_);
lean_dec(v___x_4253_);
v___x_4259_ = lean_box(0);
lean_inc_ref(v___x_4205_);
v___x_4260_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__1(v___x_4205_, v_val_4241_, v_elseIfs_4240_, v_ifTk_4236_, v_cond_4237_, v_thenTk_4238_, v_thenBody_4239_, v_a_4206_, v___x_4259_, v___x_4258_, v___y_4207_, v___y_4208_);
v___y_4210_ = v___x_4260_;
goto v___jp_4209_;
}
}
}
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
lean_inc(v_elseBody_x3f_4235_);
lean_inc_ref(v_elseTk_x3f_4234_);
v___x_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4261_, 0, v_elseTk_x3f_4234_);
lean_ctor_set(v___x_4261_, 1, v_elseBody_x3f_4235_);
v___x_4262_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4206_, v___x_4261_, v___y_4207_, v___y_4208_);
lean_dec_ref_known(v___x_4261_, 2);
v___y_4210_ = v___x_4262_;
goto v___jp_4209_;
}
}
else
{
lean_object* v_elseBody_x3f_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v_elseBody_x3f_4263_ = lean_ctor_get(v_a_4206_, 6);
lean_inc(v_elseBody_x3f_4263_);
lean_inc(v_elseTk_x3f_4234_);
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v_elseTk_x3f_4234_);
lean_ctor_set(v___x_4264_, 1, v_elseBody_x3f_4263_);
v___x_4265_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___lam__0(v_a_4206_, v___x_4264_, v___y_4207_, v___y_4208_);
lean_dec_ref_known(v___x_4264_, 2);
v___y_4210_ = v___x_4265_;
goto v___jp_4209_;
}
v___jp_4209_:
{
if (lean_obj_tag(v___y_4210_) == 0)
{
lean_object* v_a_4211_; 
v_a_4211_ = lean_ctor_get(v___y_4210_, 0);
lean_inc(v_a_4211_);
if (lean_obj_tag(v_a_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref(v___x_4205_);
v_a_4212_ = lean_ctor_get(v___y_4210_, 1);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___y_4210_);
if (v_isSharedCheck_4220_ == 0)
{
lean_object* v_unused_4221_; 
v_unused_4221_ = lean_ctor_get(v___y_4210_, 0);
lean_dec(v_unused_4221_);
v___x_4214_ = v___y_4210_;
v_isShared_4215_ = v_isSharedCheck_4220_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___y_4210_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4220_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v_a_4216_; lean_object* v___x_4218_; 
v_a_4216_ = lean_ctor_get(v_a_4211_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v_a_4211_, 1);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v_a_4216_);
v___x_4218_ = v___x_4214_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4216_);
lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_a_4212_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v_a_4223_; 
v_a_4222_ = lean_ctor_get(v___y_4210_, 1);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___y_4210_, 2);
v_a_4223_ = lean_ctor_get(v_a_4211_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v_a_4211_, 1);
v_a_4206_ = v_a_4223_;
v___y_4208_ = v_a_4222_;
goto _start;
}
}
else
{
lean_object* v_a_4225_; lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v___x_4205_);
v_a_4225_ = lean_ctor_get(v___y_4210_, 0);
v_a_4226_ = lean_ctor_get(v___y_4210_, 1);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___y_4210_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___y_4210_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_inc(v_a_4225_);
lean_dec(v___y_4210_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4225_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg___boxed(lean_object* v___x_4266_, lean_object* v_a_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4266_, v_a_4267_, v___y_4268_, v___y_4269_);
lean_dec_ref(v___y_4268_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional(lean_object* v_initialFmt_4271_, lean_object* v_stx_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; uint8_t v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; uint8_t v___y_4295_; lean_object* v___y_4296_; lean_object* v_env_4302_; lean_object* v___x_4303_; 
v_env_4302_ = lean_ctor_get(v_a_4273_, 0);
lean_inc_ref(v_a_4273_);
lean_inc(v_stx_4272_);
v___x_4303_ = lean_apply_3(v_initialFmt_4271_, v_stx_4272_, v_a_4273_, v_a_4274_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
if (lean_obj_tag(v_a_4304_) == 1)
{
lean_object* v_a_4305_; lean_object* v_val_4306_; lean_object* v___x_4307_; 
v_a_4305_ = lean_ctor_get(v___x_4303_, 1);
lean_inc(v_a_4305_);
lean_dec_ref_known(v___x_4303_, 2);
v_val_4306_ = lean_ctor_get(v_a_4304_, 0);
lean_inc(v_val_4306_);
lean_dec_ref_known(v_a_4304_, 1);
v___x_4307_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtConditional_hasNewline(v_stx_4272_, v_a_4273_, v_a_4305_);
lean_dec(v_stx_4272_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v_a_4309_; uint8_t v___y_4311_; uint8_t v___x_4361_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
v_a_4309_ = lean_ctor_get(v___x_4307_, 1);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4307_, 2);
v___x_4361_ = lean_unbox(v_a_4308_);
lean_dec(v_a_4308_);
if (v___x_4361_ == 0)
{
uint8_t v___x_4362_; 
v___x_4362_ = 1;
v___y_4311_ = v___x_4362_;
goto v___jp_4310_;
}
else
{
uint8_t v___x_4363_; 
v___x_4363_ = 0;
v___y_4311_ = v___x_4363_;
goto v___jp_4310_;
}
v___jp_4310_:
{
lean_object* v___x_4312_; 
lean_inc_ref(v_env_4302_);
v___x_4312_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v_env_4302_, v_val_4306_, v_a_4273_, v_a_4309_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v_a_4314_; lean_object* v_ifTk_4315_; lean_object* v_cond_4316_; lean_object* v_thenTk_4317_; lean_object* v_thenBody_4318_; lean_object* v_elseIfs_4319_; lean_object* v_elseTk_x3f_4320_; lean_object* v_elseBody_x3f_4321_; lean_object* v___x_4322_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
v_a_4314_ = lean_ctor_get(v___x_4312_, 1);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4312_, 2);
v_ifTk_4315_ = lean_ctor_get(v_a_4313_, 0);
lean_inc(v_ifTk_4315_);
v_cond_4316_ = lean_ctor_get(v_a_4313_, 1);
lean_inc_ref(v_cond_4316_);
v_thenTk_4317_ = lean_ctor_get(v_a_4313_, 2);
lean_inc(v_thenTk_4317_);
v_thenBody_4318_ = lean_ctor_get(v_a_4313_, 3);
lean_inc(v_thenBody_4318_);
v_elseIfs_4319_ = lean_ctor_get(v_a_4313_, 4);
lean_inc_ref(v_elseIfs_4319_);
v_elseTk_x3f_4320_ = lean_ctor_get(v_a_4313_, 5);
lean_inc(v_elseTk_x3f_4320_);
v_elseBody_x3f_4321_ = lean_ctor_get(v_a_4313_, 6);
lean_inc(v_elseBody_x3f_4321_);
lean_dec(v_a_4313_);
v___x_4322_ = l_Lean_Fmt_fmt(v_ifTk_4315_, v_a_4273_, v_a_4314_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v_a_4324_; lean_object* v___x_4325_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
v_a_4324_ = lean_ctor_get(v___x_4322_, 1);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4322_, 2);
v___x_4325_ = l_Lean_Fmt_fmt(v_thenTk_4317_, v_a_4273_, v_a_4324_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v_a_4327_; lean_object* v___x_4328_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc(v_a_4326_);
v_a_4327_ = lean_ctor_get(v___x_4325_, 1);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4325_, 2);
v___x_4328_ = l_Lean_Fmt_fmt(v_thenBody_4318_, v_a_4273_, v_a_4327_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v_a_4330_; size_t v_sz_4331_; size_t v___x_4332_; lean_object* v___x_4333_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
v_a_4330_ = lean_ctor_get(v___x_4328_, 1);
lean_inc(v_a_4330_);
lean_dec_ref_known(v___x_4328_, 2);
v_sz_4331_ = lean_array_size(v_elseIfs_4319_);
v___x_4332_ = ((size_t)0ULL);
v___x_4333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtConditional_spec__1(v_sz_4331_, v___x_4332_, v_elseIfs_4319_, v_a_4273_, v_a_4330_);
if (lean_obj_tag(v___x_4333_) == 0)
{
if (lean_obj_tag(v_elseTk_x3f_4320_) == 0)
{
lean_object* v_a_4334_; lean_object* v_a_4335_; lean_object* v___x_4336_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
v_a_4335_ = lean_ctor_get(v___x_4333_, 1);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4333_, 2);
v___x_4336_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4288_ = v_a_4323_;
v___y_4289_ = v_a_4329_;
v___y_4290_ = v_a_4334_;
v___y_4291_ = v_a_4335_;
v___y_4292_ = v_elseBody_x3f_4321_;
v___y_4293_ = v_a_4326_;
v___y_4294_ = v_cond_4316_;
v___y_4295_ = v___y_4311_;
v___y_4296_ = v___x_4336_;
goto v___jp_4287_;
}
else
{
lean_object* v_a_4337_; lean_object* v_a_4338_; lean_object* v_val_4339_; lean_object* v___x_4340_; 
v_a_4337_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4337_);
v_a_4338_ = lean_ctor_get(v___x_4333_, 1);
lean_inc(v_a_4338_);
lean_dec_ref_known(v___x_4333_, 2);
v_val_4339_ = lean_ctor_get(v_elseTk_x3f_4320_, 0);
lean_inc(v_val_4339_);
lean_dec_ref_known(v_elseTk_x3f_4320_, 1);
v___x_4340_ = l_Lean_Fmt_fmt(v_val_4339_, v_a_4273_, v_a_4338_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v_a_4341_; lean_object* v_a_4342_; 
v_a_4341_ = lean_ctor_get(v___x_4340_, 0);
lean_inc(v_a_4341_);
v_a_4342_ = lean_ctor_get(v___x_4340_, 1);
lean_inc(v_a_4342_);
lean_dec_ref_known(v___x_4340_, 2);
v___y_4288_ = v_a_4323_;
v___y_4289_ = v_a_4329_;
v___y_4290_ = v_a_4337_;
v___y_4291_ = v_a_4342_;
v___y_4292_ = v_elseBody_x3f_4321_;
v___y_4293_ = v_a_4326_;
v___y_4294_ = v_cond_4316_;
v___y_4295_ = v___y_4311_;
v___y_4296_ = v_a_4341_;
goto v___jp_4287_;
}
else
{
lean_dec(v_a_4337_);
lean_dec(v_a_4329_);
lean_dec(v_a_4326_);
lean_dec(v_a_4323_);
lean_dec(v_elseBody_x3f_4321_);
lean_dec_ref(v_cond_4316_);
return v___x_4340_;
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_a_4329_);
lean_dec(v_a_4326_);
lean_dec(v_a_4323_);
lean_dec(v_elseBody_x3f_4321_);
lean_dec(v_elseTk_x3f_4320_);
lean_dec_ref(v_cond_4316_);
v_a_4343_ = lean_ctor_get(v___x_4333_, 0);
v_a_4344_ = lean_ctor_get(v___x_4333_, 1);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4333_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_inc(v_a_4343_);
lean_dec(v___x_4333_);
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
}
else
{
lean_dec(v_a_4326_);
lean_dec(v_a_4323_);
lean_dec(v_elseBody_x3f_4321_);
lean_dec(v_elseTk_x3f_4320_);
lean_dec_ref(v_elseIfs_4319_);
lean_dec_ref(v_cond_4316_);
return v___x_4328_;
}
}
else
{
lean_dec(v_a_4323_);
lean_dec(v_elseBody_x3f_4321_);
lean_dec(v_elseTk_x3f_4320_);
lean_dec_ref(v_elseIfs_4319_);
lean_dec(v_thenBody_4318_);
lean_dec_ref(v_cond_4316_);
return v___x_4325_;
}
}
else
{
lean_dec(v_elseBody_x3f_4321_);
lean_dec(v_elseTk_x3f_4320_);
lean_dec_ref(v_elseIfs_4319_);
lean_dec(v_thenBody_4318_);
lean_dec(v_thenTk_4317_);
lean_dec_ref(v_cond_4316_);
return v___x_4322_;
}
}
else
{
lean_object* v_a_4352_; lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
v_a_4352_ = lean_ctor_get(v___x_4312_, 0);
v_a_4353_ = lean_ctor_get(v___x_4312_, 1);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4312_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_inc(v_a_4352_);
lean_dec(v___x_4312_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4352_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_dec(v_val_4306_);
v_a_4364_ = lean_ctor_get(v___x_4307_, 0);
v_a_4365_ = lean_ctor_get(v___x_4307_, 1);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4307_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_inc(v_a_4364_);
lean_dec(v___x_4307_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4364_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4381_; 
lean_dec(v_a_4304_);
lean_dec(v_stx_4272_);
v_a_4373_ = lean_ctor_get(v___x_4303_, 1);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4381_ == 0)
{
lean_object* v_unused_4382_; 
v_unused_4382_ = lean_ctor_get(v___x_4303_, 0);
lean_dec(v_unused_4382_);
v___x_4375_ = v___x_4303_;
v_isShared_4376_ = v_isSharedCheck_4381_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4303_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4381_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4379_; 
v___x_4377_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4376_ == 0)
{
lean_ctor_set_tag(v___x_4375_, 1);
lean_ctor_set(v___x_4375_, 0, v___x_4377_);
v___x_4379_ = v___x_4375_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4377_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v_a_4373_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4391_; 
lean_dec(v_stx_4272_);
v_a_4383_ = lean_ctor_get(v___x_4303_, 0);
v_a_4384_ = lean_ctor_get(v___x_4303_, 1);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4386_ = v___x_4303_;
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_inc(v_a_4383_);
lean_dec(v___x_4303_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4391_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
lean_object* v___x_4389_; 
if (v_isShared_4387_ == 0)
{
v___x_4389_ = v___x_4386_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4390_; 
v_reuseFailAlloc_4390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4390_, 0, v_a_4383_);
lean_ctor_set(v_reuseFailAlloc_4390_, 1, v_a_4384_);
v___x_4389_ = v_reuseFailAlloc_4390_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
return v___x_4389_;
}
}
}
v___jp_4275_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = l_Lean_Fmt_Layouts_conditional(v___y_4276_, v___y_4281_, v___y_4280_, v___y_4277_, v___y_4278_, v___y_4283_, v___y_4284_, v___y_4282_);
lean_dec_ref(v___y_4278_);
v___x_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
lean_ctor_set(v___x_4286_, 1, v___y_4279_);
return v___x_4286_;
}
v___jp_4287_:
{
if (lean_obj_tag(v___y_4292_) == 0)
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4276_ = v___y_4288_;
v___y_4277_ = v___y_4289_;
v___y_4278_ = v___y_4290_;
v___y_4279_ = v___y_4291_;
v___y_4280_ = v___y_4293_;
v___y_4281_ = v___y_4294_;
v___y_4282_ = v___y_4295_;
v___y_4283_ = v___y_4296_;
v___y_4284_ = v___x_4297_;
goto v___jp_4275_;
}
else
{
lean_object* v_val_4298_; lean_object* v___x_4299_; 
v_val_4298_ = lean_ctor_get(v___y_4292_, 0);
lean_inc(v_val_4298_);
lean_dec_ref_known(v___y_4292_, 1);
v___x_4299_ = l_Lean_Fmt_fmt(v_val_4298_, v_a_4273_, v___y_4291_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v_a_4301_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
v_a_4301_ = lean_ctor_get(v___x_4299_, 1);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4299_, 2);
v___y_4276_ = v___y_4288_;
v___y_4277_ = v___y_4289_;
v___y_4278_ = v___y_4290_;
v___y_4279_ = v_a_4301_;
v___y_4280_ = v___y_4293_;
v___y_4281_ = v___y_4294_;
v___y_4282_ = v___y_4295_;
v___y_4283_ = v___y_4296_;
v___y_4284_ = v_a_4300_;
goto v___jp_4275_;
}
else
{
lean_dec_ref(v___y_4296_);
lean_dec_ref(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec_ref(v___y_4288_);
return v___x_4299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtConditional___boxed(lean_object* v_initialFmt_4392_, lean_object* v_stx_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Fmt_fmtConditional(v_initialFmt_4392_, v_stx_4393_, v_a_4394_, v_a_4395_);
lean_dec_ref(v_a_4394_);
return v_res_4396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(lean_object* v___x_4397_, lean_object* v_inst_4398_, lean_object* v_a_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v___x_4402_; 
v___x_4402_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___redArg(v___x_4397_, v_a_4399_, v___y_4400_, v___y_4401_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0___boxed(lean_object* v___x_4403_, lean_object* v_inst_4404_, lean_object* v_a_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_fmtConditional_spec__0(v___x_4403_, v_inst_4404_, v_a_4405_, v___y_4406_, v___y_4407_);
lean_dec_ref(v___y_4406_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(size_t v_sz_4409_, size_t v_i_4410_, lean_object* v_bs_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v___x_4414_; 
v___x_4414_ = lean_usize_dec_lt(v_i_4410_, v_sz_4409_);
if (v___x_4414_ == 0)
{
lean_object* v___x_4415_; 
v___x_4415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4415_, 0, v_bs_4411_);
lean_ctor_set(v___x_4415_, 1, v___y_4413_);
return v___x_4415_;
}
else
{
lean_object* v_v_4416_; size_t v_sz_4417_; size_t v___x_4418_; lean_object* v___x_4419_; 
v_v_4416_ = lean_array_uget_borrowed(v_bs_4411_, v_i_4410_);
v_sz_4417_ = lean_array_size(v_v_4416_);
v___x_4418_ = ((size_t)0ULL);
lean_inc(v_v_4416_);
v___x_4419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_4417_, v___x_4418_, v_v_4416_, v___y_4412_, v___y_4413_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v_a_4421_; lean_object* v___x_4422_; lean_object* v_bs_x27_4423_; size_t v___x_4424_; size_t v___x_4425_; lean_object* v___x_4426_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
v_a_4421_ = lean_ctor_get(v___x_4419_, 1);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4419_, 2);
v___x_4422_ = lean_unsigned_to_nat(0u);
v_bs_x27_4423_ = lean_array_uset(v_bs_4411_, v_i_4410_, v___x_4422_);
v___x_4424_ = ((size_t)1ULL);
v___x_4425_ = lean_usize_add(v_i_4410_, v___x_4424_);
v___x_4426_ = lean_array_uset(v_bs_x27_4423_, v_i_4410_, v_a_4420_);
v_i_4410_ = v___x_4425_;
v_bs_4411_ = v___x_4426_;
v___y_4413_ = v_a_4421_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4411_);
return v___x_4419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0___boxed(lean_object* v_sz_4428_, lean_object* v_i_4429_, lean_object* v_bs_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
size_t v_sz_boxed_4433_; size_t v_i_boxed_4434_; lean_object* v_res_4435_; 
v_sz_boxed_4433_ = lean_unbox_usize(v_sz_4428_);
lean_dec(v_sz_4428_);
v_i_boxed_4434_ = lean_unbox_usize(v_i_4429_);
lean_dec(v_i_4429_);
v_res_4435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_boxed_4433_, v_i_boxed_4434_, v_bs_4430_, v___y_4431_, v___y_4432_);
lean_dec_ref(v___y_4431_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(size_t v_sz_4436_, size_t v_i_4437_, lean_object* v_bs_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
uint8_t v___x_4441_; 
v___x_4441_ = lean_usize_dec_lt(v_i_4437_, v_sz_4436_);
if (v___x_4441_ == 0)
{
lean_object* v___x_4442_; 
v___x_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4442_, 0, v_bs_4438_);
lean_ctor_set(v___x_4442_, 1, v___y_4440_);
return v___x_4442_;
}
else
{
lean_object* v_v_4443_; size_t v_sz_4444_; size_t v___x_4445_; lean_object* v___x_4446_; 
v_v_4443_ = lean_array_uget_borrowed(v_bs_4438_, v_i_4437_);
v_sz_4444_ = lean_array_size(v_v_4443_);
v___x_4445_ = ((size_t)0ULL);
lean_inc(v_v_4443_);
v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__0(v_sz_4444_, v___x_4445_, v_v_4443_, v___y_4439_, v___y_4440_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v_a_4448_; lean_object* v___x_4449_; lean_object* v_bs_x27_4450_; size_t v___x_4451_; size_t v___x_4452_; lean_object* v___x_4453_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
v_a_4448_ = lean_ctor_get(v___x_4446_, 1);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4446_, 2);
v___x_4449_ = lean_unsigned_to_nat(0u);
v_bs_x27_4450_ = lean_array_uset(v_bs_4438_, v_i_4437_, v___x_4449_);
v___x_4451_ = ((size_t)1ULL);
v___x_4452_ = lean_usize_add(v_i_4437_, v___x_4451_);
v___x_4453_ = lean_array_uset(v_bs_x27_4450_, v_i_4437_, v_a_4447_);
v_i_4437_ = v___x_4452_;
v_bs_4438_ = v___x_4453_;
v___y_4440_ = v_a_4448_;
goto _start;
}
else
{
lean_dec_ref(v_bs_4438_);
return v___x_4446_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1___boxed(lean_object* v_sz_4455_, lean_object* v_i_4456_, lean_object* v_bs_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
size_t v_sz_boxed_4460_; size_t v_i_boxed_4461_; lean_object* v_res_4462_; 
v_sz_boxed_4460_ = lean_unbox_usize(v_sz_4455_);
lean_dec(v_sz_4455_);
v_i_boxed_4461_ = lean_unbox_usize(v_i_4456_);
lean_dec(v_i_4456_);
v_res_4462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_boxed_4460_, v_i_boxed_4461_, v_bs_4457_, v___y_4458_, v___y_4459_);
lean_dec_ref(v___y_4458_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups(lean_object* v_bgs_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
size_t v_sz_4466_; size_t v___x_4467_; lean_object* v___x_4468_; 
v_sz_4466_ = lean_array_size(v_bgs_4463_);
v___x_4467_ = ((size_t)0ULL);
v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtBinderGroups_spec__1(v_sz_4466_, v___x_4467_, v_bgs_4463_, v_a_4464_, v_a_4465_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtBinderGroups___boxed(lean_object* v_bgs_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_Fmt_fmtBinderGroups(v_bgs_4469_, v_a_4470_, v_a_4471_);
lean_dec_ref(v_a_4470_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred(lean_object* v_lhs_4473_, lean_object* v_rhs_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_Lean_Fmt_fmt(v_lhs_4473_, v_a_4475_, v_a_4476_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v_a_4479_; lean_object* v___x_4480_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
v_a_4479_ = lean_ctor_get(v___x_4477_, 1);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4477_, 2);
v___x_4480_ = l_Lean_Fmt_fmt(v_rhs_4474_, v_a_4475_, v_a_4479_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4496_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
v_a_4482_ = lean_ctor_get(v___x_4480_, 1);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4484_ = v___x_4480_;
v_isShared_4485_ = v_isSharedCheck_4496_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_inc(v_a_4481_);
lean_dec(v___x_4480_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4496_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; uint8_t v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4494_; 
v___x_4486_ = lean_unsigned_to_nat(2u);
v___x_4487_ = lean_mk_empty_array_with_capacity(v___x_4486_);
v___x_4488_ = lean_array_push(v___x_4487_, v_a_4478_);
v___x_4489_ = lean_array_push(v___x_4488_, v_a_4481_);
v___x_4490_ = 1;
v___x_4491_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4489_, v___x_4490_);
lean_dec_ref(v___x_4489_);
v___x_4492_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4491_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v___x_4492_);
v___x_4494_ = v___x_4484_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4492_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_a_4482_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
else
{
lean_dec(v_a_4478_);
return v___x_4480_;
}
}
else
{
lean_dec(v_rhs_4474_);
return v___x_4477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWithBinderPred___boxed(lean_object* v_lhs_4497_, lean_object* v_rhs_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4497_, v_rhs_4498_, v_a_4499_, v_a_4500_);
lean_dec_ref(v_a_4499_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead(lean_object* v_head_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v_quantifier_4505_; lean_object* v_binders_4506_; lean_object* v_typeAscriptionTk_x3f_4507_; lean_object* v_type_x3f_4508_; lean_object* v_commaTk_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4622_; 
v_quantifier_4505_ = lean_ctor_get(v_head_4502_, 0);
v_binders_4506_ = lean_ctor_get(v_head_4502_, 1);
v_typeAscriptionTk_x3f_4507_ = lean_ctor_get(v_head_4502_, 2);
v_type_x3f_4508_ = lean_ctor_get(v_head_4502_, 3);
v_commaTk_4509_ = lean_ctor_get(v_head_4502_, 4);
v_isSharedCheck_4622_ = !lean_is_exclusive(v_head_4502_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4511_ = v_head_4502_;
v_isShared_4512_ = v_isSharedCheck_4622_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_commaTk_4509_);
lean_inc(v_type_x3f_4508_);
lean_inc(v_typeAscriptionTk_x3f_4507_);
lean_inc(v_binders_4506_);
lean_inc(v_quantifier_4505_);
lean_dec(v_head_4502_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4622_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_Fmt_fmt(v_quantifier_4505_, v_a_4503_, v_a_4504_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v_a_4515_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v_binderGroups_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
v_a_4515_ = lean_ctor_get(v___x_4513_, 1);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4513_, 2);
if (lean_obj_tag(v_binders_4506_) == 0)
{
lean_object* v_group_4581_; lean_object* v___x_4582_; 
v_group_4581_ = lean_ctor_get(v_binders_4506_, 0);
lean_inc_ref(v_group_4581_);
lean_dec_ref_known(v_binders_4506_, 1);
v___x_4582_ = l_Lean_Fmt_fmtBinderGroups(v_group_4581_, v_a_4503_, v_a_4515_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v_a_4584_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
v_a_4584_ = lean_ctor_get(v___x_4582_, 1);
lean_inc(v_a_4584_);
lean_dec_ref_known(v___x_4582_, 2);
v_binderGroups_4564_ = v_a_4583_;
v___y_4565_ = v_a_4503_;
v___y_4566_ = v_a_4584_;
goto v___jp_4563_;
}
else
{
lean_object* v_a_4585_; lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_dec(v_a_4514_);
lean_del_object(v___x_4511_);
lean_dec(v_commaTk_4509_);
lean_dec(v_type_x3f_4508_);
lean_dec(v_typeAscriptionTk_x3f_4507_);
v_a_4585_ = lean_ctor_get(v___x_4582_, 0);
v_a_4586_ = lean_ctor_get(v___x_4582_, 1);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4582_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_inc(v_a_4585_);
lean_dec(v___x_4582_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4585_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
else
{
lean_object* v_lhs_4594_; lean_object* v_rhs_4595_; lean_object* v___x_4596_; 
v_lhs_4594_ = lean_ctor_get(v_binders_4506_, 0);
lean_inc(v_lhs_4594_);
v_rhs_4595_ = lean_ctor_get(v_binders_4506_, 1);
lean_inc(v_rhs_4595_);
lean_dec_ref_known(v_binders_4506_, 2);
v___x_4596_ = l_Lean_Fmt_fmtWithBinderPred(v_lhs_4594_, v_rhs_4595_, v_a_4503_, v_a_4515_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v_a_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
v_a_4598_ = lean_ctor_get(v___x_4596_, 1);
lean_inc(v_a_4598_);
lean_dec_ref_known(v___x_4596_, 2);
v___x_4599_ = lean_unsigned_to_nat(1u);
v___x_4600_ = lean_mk_empty_array_with_capacity(v___x_4599_);
lean_inc_ref_n(v___x_4600_, 2);
v___x_4601_ = lean_array_push(v___x_4600_, v_a_4597_);
v___x_4602_ = lean_array_push(v___x_4600_, v___x_4601_);
v___x_4603_ = lean_array_push(v___x_4600_, v___x_4602_);
v_binderGroups_4564_ = v___x_4603_;
v___y_4565_ = v_a_4503_;
v___y_4566_ = v_a_4598_;
goto v___jp_4563_;
}
else
{
lean_object* v_a_4604_; lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
lean_dec(v_a_4514_);
lean_del_object(v___x_4511_);
lean_dec(v_commaTk_4509_);
lean_dec(v_type_x3f_4508_);
lean_dec(v_typeAscriptionTk_x3f_4507_);
v_a_4604_ = lean_ctor_get(v___x_4596_, 0);
v_a_4605_ = lean_ctor_get(v___x_4596_, 1);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4596_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_inc(v_a_4604_);
lean_dec(v___x_4596_);
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
v___jp_4516_:
{
lean_object* v___x_4522_; 
v___x_4522_ = l_Lean_Fmt_fmt(v_commaTk_4509_, v___y_4517_, v___y_4518_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4534_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
v_a_4524_ = lean_ctor_get(v___x_4522_, 1);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4526_ = v___x_4522_;
v_isShared_4527_ = v_isSharedCheck_4534_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_inc(v_a_4523_);
lean_dec(v___x_4522_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4534_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 4, v_a_4523_);
lean_ctor_set(v___x_4511_, 3, v___y_4521_);
lean_ctor_set(v___x_4511_, 2, v___y_4519_);
lean_ctor_set(v___x_4511_, 1, v___y_4520_);
lean_ctor_set(v___x_4511_, 0, v_a_4514_);
v___x_4529_ = v___x_4511_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4514_);
lean_ctor_set(v_reuseFailAlloc_4533_, 1, v___y_4520_);
lean_ctor_set(v_reuseFailAlloc_4533_, 2, v___y_4519_);
lean_ctor_set(v_reuseFailAlloc_4533_, 3, v___y_4521_);
lean_ctor_set(v_reuseFailAlloc_4533_, 4, v_a_4523_);
v___x_4529_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
lean_object* v___x_4531_; 
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v___x_4529_);
v___x_4531_ = v___x_4526_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4529_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_a_4524_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
else
{
lean_object* v_a_4535_; lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec_ref(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v_a_4514_);
lean_del_object(v___x_4511_);
v_a_4535_ = lean_ctor_get(v___x_4522_, 0);
v_a_4536_ = lean_ctor_get(v___x_4522_, 1);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4522_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_inc(v_a_4535_);
lean_dec(v___x_4522_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4535_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
v___jp_4544_:
{
if (lean_obj_tag(v_type_x3f_4508_) == 0)
{
lean_object* v___x_4549_; 
v___x_4549_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4517_ = v___y_4545_;
v___y_4518_ = v___y_4546_;
v___y_4519_ = v___y_4548_;
v___y_4520_ = v___y_4547_;
v___y_4521_ = v___x_4549_;
goto v___jp_4516_;
}
else
{
lean_object* v_val_4550_; lean_object* v___x_4551_; 
v_val_4550_ = lean_ctor_get(v_type_x3f_4508_, 0);
lean_inc(v_val_4550_);
lean_dec_ref_known(v_type_x3f_4508_, 1);
v___x_4551_ = l_Lean_Fmt_fmt(v_val_4550_, v___y_4545_, v___y_4546_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v_a_4553_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
v_a_4553_ = lean_ctor_get(v___x_4551_, 1);
lean_inc(v_a_4553_);
lean_dec_ref_known(v___x_4551_, 2);
v___y_4517_ = v___y_4545_;
v___y_4518_ = v_a_4553_;
v___y_4519_ = v___y_4548_;
v___y_4520_ = v___y_4547_;
v___y_4521_ = v_a_4552_;
goto v___jp_4516_;
}
else
{
lean_object* v_a_4554_; lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec_ref(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v_a_4514_);
lean_del_object(v___x_4511_);
lean_dec(v_commaTk_4509_);
v_a_4554_ = lean_ctor_get(v___x_4551_, 0);
v_a_4555_ = lean_ctor_get(v___x_4551_, 1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4551_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_inc(v_a_4554_);
lean_dec(v___x_4551_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4554_);
lean_ctor_set(v_reuseFailAlloc_4561_, 1, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
v___jp_4563_:
{
if (lean_obj_tag(v_typeAscriptionTk_x3f_4507_) == 0)
{
lean_object* v___x_4567_; 
v___x_4567_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_4545_ = v___y_4565_;
v___y_4546_ = v___y_4566_;
v___y_4547_ = v_binderGroups_4564_;
v___y_4548_ = v___x_4567_;
goto v___jp_4544_;
}
else
{
lean_object* v_val_4568_; lean_object* v___x_4569_; 
v_val_4568_ = lean_ctor_get(v_typeAscriptionTk_x3f_4507_, 0);
lean_inc(v_val_4568_);
lean_dec_ref_known(v_typeAscriptionTk_x3f_4507_, 1);
v___x_4569_ = l_Lean_Fmt_fmt(v_val_4568_, v___y_4565_, v___y_4566_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v_a_4571_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
v_a_4571_ = lean_ctor_get(v___x_4569_, 1);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4569_, 2);
v___y_4545_ = v___y_4565_;
v___y_4546_ = v_a_4571_;
v___y_4547_ = v_binderGroups_4564_;
v___y_4548_ = v_a_4570_;
goto v___jp_4544_;
}
else
{
lean_object* v_a_4572_; lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref(v_binderGroups_4564_);
lean_dec(v_a_4514_);
lean_del_object(v___x_4511_);
lean_dec(v_commaTk_4509_);
lean_dec(v_type_x3f_4508_);
v_a_4572_ = lean_ctor_get(v___x_4569_, 0);
v_a_4573_ = lean_ctor_get(v___x_4569_, 1);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4569_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_inc(v_a_4572_);
lean_dec(v___x_4569_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4572_);
lean_ctor_set(v_reuseFailAlloc_4579_, 1, v_a_4573_);
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
else
{
lean_object* v_a_4613_; lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
lean_del_object(v___x_4511_);
lean_dec(v_commaTk_4509_);
lean_dec(v_type_x3f_4508_);
lean_dec(v_typeAscriptionTk_x3f_4507_);
lean_dec_ref(v_binders_4506_);
v_a_4613_ = lean_ctor_get(v___x_4513_, 0);
v_a_4614_ = lean_ctor_get(v___x_4513_, 1);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4513_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_inc(v_a_4613_);
lean_dec(v___x_4513_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4613_);
lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_a_4614_);
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
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifierHead___boxed(lean_object* v_head_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_Fmt_fmtQuantifierHead(v_head_4623_, v_a_4624_, v_a_4625_);
lean_dec_ref(v_a_4624_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(size_t v_sz_4627_, size_t v_i_4628_, lean_object* v_bs_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_){
_start:
{
uint8_t v___x_4632_; 
v___x_4632_ = lean_usize_dec_lt(v_i_4628_, v_sz_4627_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
v___x_4633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4633_, 0, v_bs_4629_);
lean_ctor_set(v___x_4633_, 1, v___y_4631_);
return v___x_4633_;
}
else
{
lean_object* v_v_4634_; lean_object* v___x_4635_; 
v_v_4634_ = lean_array_uget_borrowed(v_bs_4629_, v_i_4628_);
lean_inc(v_v_4634_);
v___x_4635_ = l_Lean_Fmt_fmtQuantifierHead(v_v_4634_, v___y_4630_, v___y_4631_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v_a_4637_; lean_object* v___x_4638_; lean_object* v_bs_x27_4639_; size_t v___x_4640_; size_t v___x_4641_; lean_object* v___x_4642_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
v_a_4637_ = lean_ctor_get(v___x_4635_, 1);
lean_inc(v_a_4637_);
lean_dec_ref_known(v___x_4635_, 2);
v___x_4638_ = lean_unsigned_to_nat(0u);
v_bs_x27_4639_ = lean_array_uset(v_bs_4629_, v_i_4628_, v___x_4638_);
v___x_4640_ = ((size_t)1ULL);
v___x_4641_ = lean_usize_add(v_i_4628_, v___x_4640_);
v___x_4642_ = lean_array_uset(v_bs_x27_4639_, v_i_4628_, v_a_4636_);
v_i_4628_ = v___x_4641_;
v_bs_4629_ = v___x_4642_;
v___y_4631_ = v_a_4637_;
goto _start;
}
else
{
lean_object* v_a_4644_; lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_dec_ref(v_bs_4629_);
v_a_4644_ = lean_ctor_get(v___x_4635_, 0);
v_a_4645_ = lean_ctor_get(v___x_4635_, 1);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4635_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_inc(v_a_4644_);
lean_dec(v___x_4635_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4644_);
lean_ctor_set(v_reuseFailAlloc_4651_, 1, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0___boxed(lean_object* v_sz_4653_, lean_object* v_i_4654_, lean_object* v_bs_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
size_t v_sz_boxed_4658_; size_t v_i_boxed_4659_; lean_object* v_res_4660_; 
v_sz_boxed_4658_ = lean_unbox_usize(v_sz_4653_);
lean_dec(v_sz_4653_);
v_i_boxed_4659_ = lean_unbox_usize(v_i_4654_);
lean_dec(v_i_4654_);
v_res_4660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_boxed_4658_, v_i_boxed_4659_, v_bs_4655_, v___y_4656_, v___y_4657_);
lean_dec_ref(v___y_4656_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier(lean_object* v_deconstructQuantifier_x3f_4661_, lean_object* v_stx_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v_env_4665_; lean_object* v___x_4666_; lean_object* v_quantifiers_4667_; lean_object* v_body_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4704_; 
v_env_4665_ = lean_ctor_get(v_a_4663_, 0);
lean_inc_ref(v_env_4665_);
v___x_4666_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_quantifierChain(v_env_4665_, v_deconstructQuantifier_x3f_4661_, v_stx_4662_);
v_quantifiers_4667_ = lean_ctor_get(v___x_4666_, 0);
v_body_4668_ = lean_ctor_get(v___x_4666_, 1);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4670_ = v___x_4666_;
v_isShared_4671_ = v_isSharedCheck_4704_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_body_4668_);
lean_inc(v_quantifiers_4667_);
lean_dec(v___x_4666_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4704_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; uint8_t v___x_4674_; 
v___x_4672_ = lean_array_get_size(v_quantifiers_4667_);
v___x_4673_ = lean_unsigned_to_nat(0u);
v___x_4674_ = lean_nat_dec_eq(v___x_4672_, v___x_4673_);
if (v___x_4674_ == 0)
{
size_t v_sz_4675_; size_t v___x_4676_; lean_object* v___x_4677_; 
lean_del_object(v___x_4670_);
v_sz_4675_ = lean_array_size(v_quantifiers_4667_);
v___x_4676_ = ((size_t)0ULL);
v___x_4677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtQuantifier_spec__0(v_sz_4675_, v___x_4676_, v_quantifiers_4667_, v_a_4663_, v_a_4664_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v_a_4679_; lean_object* v___x_4680_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
v_a_4679_ = lean_ctor_get(v___x_4677_, 1);
lean_inc(v_a_4679_);
lean_dec_ref_known(v___x_4677_, 2);
v___x_4680_ = l_Lean_Fmt_fmt(v_body_4668_, v_a_4663_, v_a_4679_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4690_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
v_a_4682_ = lean_ctor_get(v___x_4680_, 1);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4684_ = v___x_4680_;
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_inc(v_a_4681_);
lean_dec(v___x_4680_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4690_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4686_; lean_object* v___x_4688_; 
v___x_4686_ = l_Lean_Fmt_Layouts_quantified(v_a_4678_, v_a_4681_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v___x_4686_);
v___x_4688_ = v___x_4684_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v_a_4682_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
else
{
lean_dec(v_a_4678_);
return v___x_4680_;
}
}
else
{
lean_object* v_a_4691_; lean_object* v_a_4692_; lean_object* v___x_4694_; uint8_t v_isShared_4695_; uint8_t v_isSharedCheck_4699_; 
lean_dec(v_body_4668_);
v_a_4691_ = lean_ctor_get(v___x_4677_, 0);
v_a_4692_ = lean_ctor_get(v___x_4677_, 1);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4694_ = v___x_4677_;
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
else
{
lean_inc(v_a_4692_);
lean_inc(v_a_4691_);
lean_dec(v___x_4677_);
v___x_4694_ = lean_box(0);
v_isShared_4695_ = v_isSharedCheck_4699_;
goto v_resetjp_4693_;
}
v_resetjp_4693_:
{
lean_object* v___x_4697_; 
if (v_isShared_4695_ == 0)
{
v___x_4697_ = v___x_4694_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4691_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v_a_4692_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
else
{
lean_object* v___x_4700_; lean_object* v___x_4702_; 
lean_dec(v_body_4668_);
lean_dec_ref(v_quantifiers_4667_);
v___x_4700_ = l_Lean_Fmt_Error_partialFormatter;
if (v_isShared_4671_ == 0)
{
lean_ctor_set_tag(v___x_4670_, 1);
lean_ctor_set(v___x_4670_, 1, v_a_4664_);
lean_ctor_set(v___x_4670_, 0, v___x_4700_);
v___x_4702_ = v___x_4670_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_a_4664_);
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
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtQuantifier___boxed(lean_object* v_deconstructQuantifier_x3f_4705_, lean_object* v_stx_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_Lean_Fmt_fmtQuantifier(v_deconstructQuantifier_x3f_4705_, v_stx_4706_, v_a_4707_, v_a_4708_);
lean_dec_ref(v_a_4707_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic(lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_){
_start:
{
uint8_t v___x_4713_; lean_object* v___x_4714_; 
v___x_4713_ = 0;
v___x_4714_ = l_Lean_Fmt_fmtRaw(v___x_4713_, v_a_4710_, v_a_4711_, v_a_4712_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_Fmt_fmtAtomic(v_a_4715_, v_a_4716_, v_a_4717_);
lean_dec_ref(v_a_4716_);
return v_res_4718_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4725_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtChoiceNode___boxed), 3, 0);
v___x_4726_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__2));
v___x_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4726_);
lean_ctor_set(v___x_4727_, 1, v___x_4725_);
return v___x_4727_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4(void){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__3);
v___x_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4728_);
return v___x_4729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(lean_object* v_kind_4730_){
_start:
{
lean_object* v___x_4731_; uint8_t v___x_4732_; 
v___x_4731_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtRaw_go___closed__1));
v___x_4732_ = lean_name_eq(v_kind_4730_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; 
v___x_4733_ = lean_box(0);
return v___x_4733_;
}
else
{
lean_object* v___x_4734_; 
v___x_4734_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___closed__4);
return v___x_4734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg___boxed(lean_object* v_kind_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4735_);
lean_dec(v_kind_4735_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(lean_object* v_x_4737_, lean_object* v_x_4738_, lean_object* v_kind_4739_){
_start:
{
lean_object* v___x_4740_; 
v___x_4740_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___redArg(v_kind_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed(lean_object* v_x_4741_, lean_object* v_x_4742_, lean_object* v_kind_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider(v_x_4741_, v_x_4742_, v_kind_4743_);
lean_dec(v_kind_4743_);
lean_dec_ref(v_x_4742_);
lean_dec_ref(v_x_4741_);
return v_res_4744_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(lean_object* v_x_4750_){
_start:
{
if (lean_obj_tag(v_x_4750_) == 1)
{
lean_object* v_pre_4751_; lean_object* v_str_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; 
v_pre_4751_ = lean_ctor_get(v_x_4750_, 0);
v_str_4752_ = lean_ctor_get(v_x_4750_, 1);
v___x_4753_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__0));
v___x_4754_ = lean_string_dec_eq(v_str_4752_, v___x_4753_);
if (v___x_4754_ == 0)
{
lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4755_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__1));
v___x_4756_ = lean_string_dec_eq(v_str_4752_, v___x_4755_);
if (v___x_4756_ == 0)
{
lean_object* v___x_4757_; uint8_t v___x_4758_; 
v___x_4757_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__2));
v___x_4758_ = lean_string_dec_eq(v_str_4752_, v___x_4757_);
if (v___x_4758_ == 0)
{
lean_object* v___x_4759_; uint8_t v___x_4760_; 
v___x_4759_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__3));
v___x_4760_ = lean_string_dec_eq(v_str_4752_, v___x_4759_);
if (v___x_4760_ == 0)
{
lean_object* v___x_4761_; uint8_t v___x_4762_; 
v___x_4761_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___closed__4));
v___x_4762_ = lean_string_dec_eq(v_str_4752_, v___x_4761_);
if (v___x_4762_ == 0)
{
return v___x_4762_;
}
else
{
if (lean_obj_tag(v_pre_4751_) == 0)
{
return v___x_4762_;
}
else
{
return v___x_4760_;
}
}
}
else
{
return v___x_4760_;
}
}
else
{
return v___x_4758_;
}
}
else
{
return v___x_4756_;
}
}
else
{
return v___x_4754_;
}
}
else
{
uint8_t v___x_4763_; 
v___x_4763_ = 0;
return v___x_4763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind___boxed(lean_object* v_x_4764_){
_start:
{
uint8_t v_res_4765_; lean_object* v_r_4766_; 
v_res_4765_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_x_4764_);
lean_dec(v_x_4764_);
v_r_4766_ = lean_box(v_res_4765_);
return v_r_4766_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2(void){
_start:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4772_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAtomic___boxed), 3, 0);
v___x_4773_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__1));
v___x_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
lean_ctor_set(v___x_4774_, 1, v___x_4772_);
return v___x_4774_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__2);
v___x_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4775_);
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(lean_object* v_kind_4777_){
_start:
{
uint8_t v___x_4778_; 
v___x_4778_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_isAntiquotKind(v_kind_4777_);
if (v___x_4778_ == 0)
{
lean_object* v___x_4779_; 
v___x_4779_ = lean_box(0);
return v___x_4779_;
}
else
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4780_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___boxed(lean_object* v_kind_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4781_);
lean_dec(v_kind_4781_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(lean_object* v_x_4783_, lean_object* v_x_4784_, lean_object* v_kind_4785_){
_start:
{
lean_object* v___x_4786_; 
v___x_4786_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg(v_kind_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed(lean_object* v_x_4787_, lean_object* v_x_4788_, lean_object* v_kind_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider(v_x_4787_, v_x_4788_, v_kind_4789_);
lean_dec(v_kind_4789_);
lean_dec_ref(v_x_4788_);
lean_dec_ref(v_x_4787_);
return v_res_4790_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4801_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPostfixOperator___boxed), 3, 0);
v___x_4802_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__3));
v___x_4803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4802_);
lean_ctor_set(v___x_4803_, 1, v___x_4801_);
return v___x_4803_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__4);
v___x_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
return v___x_4805_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8(void){
_start:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; 
v___x_4811_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrefixOperator___boxed), 3, 0);
v___x_4812_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__7));
v___x_4813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4813_, 0, v___x_4812_);
lean_ctor_set(v___x_4813_, 1, v___x_4811_);
return v___x_4813_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9(void){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__8);
v___x_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(lean_object* v_env_4816_, lean_object* v_opts_4817_, lean_object* v_kind_4818_){
_start:
{
lean_object* v___x_4819_; 
lean_inc(v_kind_4818_);
lean_inc_ref(v_env_4816_);
v___x_4819_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperationOfParserDescr_x3f(v_env_4816_, v_opts_4817_, v_kind_4818_);
if (lean_obj_tag(v___x_4819_) == 1)
{
lean_object* v_val_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4830_; 
lean_dec(v_kind_4818_);
lean_dec_ref(v_env_4816_);
v_val_4820_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4822_ = v___x_4819_;
v_isShared_4823_ = v_isSharedCheck_4830_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_val_4820_);
lean_dec(v___x_4819_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4830_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4824_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__1));
v___x_4825_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtInfixOperator___boxed), 4, 1);
lean_closure_set(v___x_4825_, 0, v_val_4820_);
v___x_4826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4824_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___x_4826_);
v___x_4828_ = v___x_4822_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
else
{
uint8_t v___x_4831_; 
lean_dec(v___x_4819_);
lean_inc(v_kind_4818_);
lean_inc_ref(v_env_4816_);
v___x_4831_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPrefixFormatter(v_env_4816_, v_opts_4817_, v_kind_4818_);
if (v___x_4831_ == 0)
{
uint8_t v___x_4832_; 
v___x_4832_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasPostfixFormatter(v_env_4816_, v_opts_4817_, v_kind_4818_);
if (v___x_4832_ == 0)
{
lean_object* v___x_4833_; 
v___x_4833_ = lean_box(0);
return v___x_4833_;
}
else
{
lean_object* v___x_4834_; 
v___x_4834_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__5);
return v___x_4834_;
}
}
else
{
lean_object* v___x_4835_; 
lean_dec(v_kind_4818_);
lean_dec_ref(v_env_4816_);
v___x_4835_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___closed__9);
return v___x_4835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed(lean_object* v_env_4836_, lean_object* v_opts_4837_, lean_object* v_kind_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider(v_env_4836_, v_opts_4837_, v_kind_4838_);
lean_dec_ref(v_opts_4837_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(lean_object* v_env_4840_, lean_object* v_opts_4841_, lean_object* v_kind_4842_){
_start:
{
uint8_t v___x_4843_; 
v___x_4843_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_hasAtomicFormatter(v_env_4840_, v_opts_4841_, v_kind_4842_);
if (v___x_4843_ == 0)
{
lean_object* v___x_4844_; 
v___x_4844_ = lean_box(0);
return v___x_4844_;
}
else
{
lean_object* v___x_4845_; 
v___x_4845_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___redArg___closed__3);
return v___x_4845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed(lean_object* v_env_4846_, lean_object* v_opts_4847_, lean_object* v_kind_4848_){
_start:
{
lean_object* v_res_4849_; 
v_res_4849_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider(v_env_4846_, v_opts_4847_, v_kind_4848_);
lean_dec_ref(v_opts_4847_);
return v_res_4849_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(lean_object* v_x_4850_, lean_object* v_x_4851_){
_start:
{
if (lean_obj_tag(v_x_4850_) == 0)
{
if (lean_obj_tag(v_x_4851_) == 0)
{
uint8_t v___x_4852_; 
v___x_4852_ = 1;
return v___x_4852_;
}
else
{
uint8_t v___x_4853_; 
v___x_4853_ = 0;
return v___x_4853_;
}
}
else
{
if (lean_obj_tag(v_x_4851_) == 0)
{
uint8_t v___x_4854_; 
v___x_4854_ = 0;
return v___x_4854_;
}
else
{
lean_object* v_val_4855_; lean_object* v_val_4856_; uint8_t v___x_4857_; 
v_val_4855_ = lean_ctor_get(v_x_4850_, 0);
v_val_4856_ = lean_ctor_get(v_x_4851_, 0);
v___x_4857_ = lean_nat_dec_eq(v_val_4855_, v_val_4856_);
return v___x_4857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0___boxed(lean_object* v_x_4858_, lean_object* v_x_4859_){
_start:
{
uint8_t v_res_4860_; lean_object* v_r_4861_; 
v_res_4860_ = l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v_x_4858_, v_x_4859_);
lean_dec(v_x_4859_);
lean_dec(v_x_4858_);
v_r_4861_ = lean_box(v_res_4860_);
return v_r_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(lean_object* v_lineInfos_4862_, lean_object* v___f_4863_, lean_object* v___f_4864_, lean_object* v_pos_4865_){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = l_Lean_Fmt_binSearchRightmost___redArg(v_lineInfos_4862_, v_pos_4865_, v___f_4863_, v___f_4864_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v___x_4867_; 
v___x_4867_ = lean_box(0);
return v___x_4867_;
}
else
{
lean_object* v_val_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4876_; 
v_val_4868_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4870_ = v___x_4866_;
v_isShared_4871_ = v_isSharedCheck_4876_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_val_4868_);
lean_dec(v___x_4866_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4876_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v_fst_4872_; lean_object* v___x_4874_; 
v_fst_4872_ = lean_ctor_get(v_val_4868_, 0);
lean_inc(v_fst_4872_);
lean_dec(v_val_4868_);
if (v_isShared_4871_ == 0)
{
lean_ctor_set(v___x_4870_, 0, v_fst_4872_);
v___x_4874_ = v___x_4870_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_fst_4872_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2___boxed(lean_object* v_lineInfos_4877_, lean_object* v___f_4878_, lean_object* v___f_4879_, lean_object* v_pos_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4877_, v___f_4878_, v___f_4879_, v_pos_4880_);
lean_dec_ref(v_lineInfos_4877_);
return v_res_4881_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(lean_object* v_lineInfos_4882_, lean_object* v_a_4883_, lean_object* v_b_4884_){
_start:
{
lean_object* v___f_4885_; lean_object* v___f_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; uint8_t v___x_4889_; 
v___f_4885_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__5));
v___f_4886_ = ((lean_object*)(l_Lean_Fmt_getLineInfo_x21___closed__4));
v___x_4887_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4882_, v___f_4885_, v___f_4886_, v_a_4883_);
v___x_4888_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___lam__2(v_lineInfos_4882_, v___f_4885_, v___f_4886_, v_b_4884_);
v___x_4889_ = l_Option_instBEq_beq___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine_spec__0(v___x_4887_, v___x_4888_);
lean_dec(v___x_4888_);
lean_dec(v___x_4887_);
return v___x_4889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine___boxed(lean_object* v_lineInfos_4890_, lean_object* v_a_4891_, lean_object* v_b_4892_){
_start:
{
uint8_t v_res_4893_; lean_object* v_r_4894_; 
v_res_4893_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4890_, v_a_4891_, v_b_4892_);
lean_dec_ref(v_lineInfos_4890_);
v_r_4894_ = lean_box(v_res_4893_);
return v_r_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(lean_object* v_val_4895_, uint8_t v_opOnRhsLine_4896_, lean_object* v_val_4897_, lean_object* v_val_4898_, lean_object* v___x_4899_, uint8_t v_opOnLhsLine_4900_, lean_object* v___x_4901_, lean_object* v_as_4902_, size_t v_sz_4903_, size_t v_i_4904_, lean_object* v_b_4905_){
_start:
{
lean_object* v_a_4907_; uint8_t v___x_4911_; 
v___x_4911_ = lean_usize_dec_lt(v_i_4904_, v_sz_4903_);
if (v___x_4911_ == 0)
{
lean_dec_ref(v_val_4898_);
lean_dec_ref(v_val_4897_);
lean_dec_ref(v_val_4895_);
return v_b_4905_;
}
else
{
lean_object* v_a_4912_; uint8_t v___y_4930_; uint8_t v___y_4931_; uint8_t v_placement_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; uint8_t v___y_4940_; 
v_a_4912_ = lean_array_uget(v_as_4902_, v_i_4904_);
v_placement_4936_ = lean_ctor_get_uint8(v_a_4912_, sizeof(void*)*3 + 1);
v___x_4937_ = lean_unsigned_to_nat(0u);
v___x_4938_ = lean_nat_dec_eq(v___x_4899_, v___x_4937_);
if (v_placement_4936_ == 0)
{
lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4941_ = lean_unsigned_to_nat(3u);
v___x_4942_ = lean_nat_dec_eq(v___x_4901_, v___x_4941_);
v___y_4940_ = v___x_4942_;
goto v___jp_4939_;
}
else
{
v___y_4940_ = v___x_4938_;
goto v___jp_4939_;
}
v___jp_4913_:
{
uint8_t v_kind_4914_; lean_object* v_originalTokenRange_4915_; lean_object* v_originalWhitespaceRange_4916_; uint8_t v_originalWhitespaceKind_4917_; lean_object* v_content_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4928_; 
v_kind_4914_ = lean_ctor_get_uint8(v_a_4912_, sizeof(void*)*3);
v_originalTokenRange_4915_ = lean_ctor_get(v_a_4912_, 0);
v_originalWhitespaceRange_4916_ = lean_ctor_get(v_a_4912_, 1);
v_originalWhitespaceKind_4917_ = lean_ctor_get_uint8(v_a_4912_, sizeof(void*)*3 + 2);
v_content_4918_ = lean_ctor_get(v_a_4912_, 2);
v_isSharedCheck_4928_ = !lean_is_exclusive(v_a_4912_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4920_ = v_a_4912_;
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_content_4918_);
lean_inc(v_originalWhitespaceRange_4916_);
lean_inc(v_originalTokenRange_4915_);
lean_dec(v_a_4912_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4928_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
uint8_t v___x_4922_; lean_object* v___x_4924_; 
v___x_4922_ = 1;
if (v_isShared_4921_ == 0)
{
v___x_4924_ = v___x_4920_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_originalTokenRange_4915_);
lean_ctor_set(v_reuseFailAlloc_4927_, 1, v_originalWhitespaceRange_4916_);
lean_ctor_set(v_reuseFailAlloc_4927_, 2, v_content_4918_);
lean_ctor_set_uint8(v_reuseFailAlloc_4927_, sizeof(void*)*3, v_kind_4914_);
lean_ctor_set_uint8(v_reuseFailAlloc_4927_, sizeof(void*)*3 + 2, v_originalWhitespaceKind_4917_);
v___x_4924_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
lean_ctor_set_uint8(v___x_4924_, sizeof(void*)*3 + 1, v___x_4922_);
lean_inc_ref(v_val_4895_);
v___x_4925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4924_);
lean_ctor_set(v___x_4925_, 1, v_val_4895_);
v___x_4926_ = lean_array_push(v_b_4905_, v___x_4925_);
v_a_4907_ = v___x_4926_;
goto v___jp_4906_;
}
}
}
v___jp_4929_:
{
if (v___y_4931_ == 0)
{
if (v___y_4930_ == 0)
{
goto v___jp_4913_;
}
else
{
if (v_opOnRhsLine_4896_ == 0)
{
goto v___jp_4913_;
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
lean_inc_ref(v_val_4897_);
v___x_4932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4932_, 0, v_a_4912_);
lean_ctor_set(v___x_4932_, 1, v_val_4897_);
v___x_4933_ = lean_array_push(v_b_4905_, v___x_4932_);
v_a_4907_ = v___x_4933_;
goto v___jp_4906_;
}
}
}
else
{
if (v_opOnRhsLine_4896_ == 0)
{
lean_object* v___x_4934_; lean_object* v___x_4935_; 
lean_inc_ref(v_val_4898_);
v___x_4934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4934_, 0, v_a_4912_);
lean_ctor_set(v___x_4934_, 1, v_val_4898_);
v___x_4935_ = lean_array_push(v_b_4905_, v___x_4934_);
v_a_4907_ = v___x_4935_;
goto v___jp_4906_;
}
else
{
lean_dec(v_a_4912_);
v_a_4907_ = v_b_4905_;
goto v___jp_4906_;
}
}
}
v___jp_4939_:
{
if (v___y_4940_ == 0)
{
v___y_4930_ = v___y_4940_;
v___y_4931_ = v___x_4938_;
goto v___jp_4929_;
}
else
{
v___y_4930_ = v___y_4940_;
v___y_4931_ = v_opOnLhsLine_4900_;
goto v___jp_4929_;
}
}
}
v___jp_4906_:
{
size_t v___x_4908_; size_t v___x_4909_; 
v___x_4908_ = ((size_t)1ULL);
v___x_4909_ = lean_usize_add(v_i_4904_, v___x_4908_);
v_i_4904_ = v___x_4909_;
v_b_4905_ = v_a_4907_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0___boxed(lean_object* v_val_4943_, lean_object* v_opOnRhsLine_4944_, lean_object* v_val_4945_, lean_object* v_val_4946_, lean_object* v___x_4947_, lean_object* v_opOnLhsLine_4948_, lean_object* v___x_4949_, lean_object* v_as_4950_, lean_object* v_sz_4951_, lean_object* v_i_4952_, lean_object* v_b_4953_){
_start:
{
uint8_t v_opOnRhsLine_boxed_4954_; uint8_t v_opOnLhsLine_boxed_4955_; size_t v_sz_boxed_4956_; size_t v_i_boxed_4957_; lean_object* v_res_4958_; 
v_opOnRhsLine_boxed_4954_ = lean_unbox(v_opOnRhsLine_4944_);
v_opOnLhsLine_boxed_4955_ = lean_unbox(v_opOnLhsLine_4948_);
v_sz_boxed_4956_ = lean_unbox_usize(v_sz_4951_);
lean_dec(v_sz_4951_);
v_i_boxed_4957_ = lean_unbox_usize(v_i_4952_);
lean_dec(v_i_4952_);
v_res_4958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_4943_, v_opOnRhsLine_boxed_4954_, v_val_4945_, v_val_4946_, v___x_4947_, v_opOnLhsLine_boxed_4955_, v___x_4949_, v_as_4950_, v_sz_boxed_4956_, v_i_boxed_4957_, v_b_4953_);
lean_dec_ref(v_as_4950_);
lean_dec(v___x_4949_);
lean_dec(v___x_4947_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector(lean_object* v_ctx_4961_, lean_object* v_stx_4962_){
_start:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; uint8_t v___x_4967_; 
v___x_4965_ = l_Lean_Syntax_getNumArgs(v_stx_4962_);
v___x_4966_ = lean_unsigned_to_nat(3u);
v___x_4967_ = lean_nat_dec_eq(v___x_4965_, v___x_4966_);
if (v___x_4967_ == 0)
{
lean_object* v___x_4968_; 
lean_dec(v___x_4965_);
lean_dec(v_stx_4962_);
lean_dec_ref(v_ctx_4961_);
v___x_4968_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4968_;
}
else
{
lean_object* v___x_4969_; lean_object* v___x_4970_; uint8_t v___x_4971_; 
v___x_4969_ = lean_unsigned_to_nat(1u);
v___x_4970_ = l_Lean_Syntax_getArg(v_stx_4962_, v___x_4969_);
v___x_4971_ = l_Lean_Syntax_isAtom(v___x_4970_);
if (v___x_4971_ == 0)
{
lean_object* v___x_4972_; 
lean_dec(v___x_4970_);
lean_dec(v___x_4965_);
lean_dec(v_stx_4962_);
lean_dec_ref(v_ctx_4961_);
v___x_4972_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4972_;
}
else
{
lean_object* v_env_4973_; lean_object* v_opts_4974_; lean_object* v_lineInfos_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v_env_4973_ = lean_ctor_get(v_ctx_4961_, 0);
v_opts_4974_ = lean_ctor_get(v_ctx_4961_, 1);
v_lineInfos_4975_ = lean_ctor_get(v_ctx_4961_, 2);
lean_inc_ref(v_lineInfos_4975_);
v___x_4976_ = lean_unsigned_to_nat(0u);
v___x_4977_ = l_Lean_Syntax_getArg(v_stx_4962_, v___x_4976_);
v___x_4978_ = lean_unsigned_to_nat(2u);
v___x_4979_ = l_Lean_Syntax_getArg(v_stx_4962_, v___x_4978_);
v___x_4980_ = l_Lean_Syntax_getKind(v_stx_4962_);
lean_inc_ref(v_env_4973_);
v___x_4981_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_getInfixOperation_x3f(v_env_4973_, v_opts_4974_, v___x_4980_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v___x_4982_; 
lean_dec(v___x_4979_);
lean_dec(v___x_4977_);
lean_dec_ref(v_lineInfos_4975_);
lean_dec(v___x_4970_);
lean_dec(v___x_4965_);
lean_dec_ref(v_ctx_4961_);
v___x_4982_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4982_;
}
else
{
lean_object* v_comments_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
lean_dec_ref_known(v___x_4981_, 1);
v_comments_4983_ = l_Lean_Fmt_CommentCollector_Context_trailingComments(v_ctx_4961_, v___x_4970_);
lean_dec_ref(v_ctx_4961_);
v___x_4984_ = lean_array_get_size(v_comments_4983_);
v___x_4985_ = lean_nat_dec_eq(v___x_4984_, v___x_4976_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v___x_4986_ = l_Lean_Syntax_getTailInfo(v___x_4977_);
lean_dec(v___x_4977_);
v___x_4987_ = l_Lean_SourceInfo_getRange_x3f(v___x_4985_, v___x_4986_);
lean_dec(v___x_4986_);
v___x_4988_ = l_Lean_Syntax_getRange_x3f(v___x_4970_, v___x_4985_);
lean_dec(v___x_4970_);
if (lean_obj_tag(v___x_4987_) == 1)
{
if (lean_obj_tag(v___x_4988_) == 1)
{
lean_object* v_val_4989_; lean_object* v_val_4990_; lean_object* v___x_4991_; 
v_val_4989_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_val_4989_);
lean_dec_ref_known(v___x_4987_, 1);
v_val_4990_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_val_4990_);
lean_dec_ref_known(v___x_4988_, 1);
v___x_4991_ = l_Lean_Syntax_getPos_x3f(v___x_4979_, v___x_4985_);
if (lean_obj_tag(v___x_4991_) == 1)
{
lean_object* v_val_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_val_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_val_4992_);
lean_dec_ref_known(v___x_4991_, 1);
v___x_4993_ = l_Lean_Syntax_getTailInfo(v___x_4979_);
lean_dec(v___x_4979_);
v___x_4994_ = l_Lean_SourceInfo_getRange_x3f(v___x_4985_, v___x_4993_);
lean_dec(v___x_4993_);
if (lean_obj_tag(v___x_4994_) == 1)
{
lean_object* v_val_4995_; lean_object* v_stop_4996_; lean_object* v_start_4997_; lean_object* v_stop_4998_; uint8_t v_opOnLhsLine_4999_; uint8_t v_opOnRhsLine_5000_; lean_object* v_r_5001_; size_t v_sz_5002_; size_t v___x_5003_; lean_object* v___x_5004_; 
v_val_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_val_4995_);
lean_dec_ref_known(v___x_4994_, 1);
v_stop_4996_ = lean_ctor_get(v_val_4989_, 1);
v_start_4997_ = lean_ctor_get(v_val_4990_, 0);
v_stop_4998_ = lean_ctor_get(v_val_4990_, 1);
lean_inc(v_start_4997_);
lean_inc(v_stop_4996_);
v_opOnLhsLine_4999_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4975_, v_stop_4996_, v_start_4997_);
lean_inc(v_stop_4998_);
v_opOnRhsLine_5000_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_sameLine(v_lineInfos_4975_, v_stop_4998_, v_val_4992_);
lean_dec_ref(v_lineInfos_4975_);
v_r_5001_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
v_sz_5002_ = lean_array_size(v_comments_4983_);
v___x_5003_ = ((size_t)0ULL);
v___x_5004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector_spec__0(v_val_4990_, v_opOnRhsLine_5000_, v_val_4995_, v_val_4989_, v___x_4984_, v_opOnLhsLine_4999_, v___x_4965_, v_comments_4983_, v_sz_5002_, v___x_5003_, v_r_5001_);
lean_dec_ref(v_comments_4983_);
lean_dec(v___x_4965_);
return v___x_5004_;
}
else
{
lean_dec(v___x_4994_);
lean_dec(v_val_4992_);
lean_dec(v_val_4990_);
lean_dec(v_val_4989_);
lean_dec_ref(v_comments_4983_);
lean_dec_ref(v_lineInfos_4975_);
lean_dec(v___x_4965_);
goto v___jp_4963_;
}
}
else
{
lean_dec(v___x_4991_);
lean_dec(v_val_4990_);
lean_dec(v_val_4989_);
lean_dec_ref(v_comments_4983_);
lean_dec(v___x_4979_);
lean_dec_ref(v_lineInfos_4975_);
lean_dec(v___x_4965_);
goto v___jp_4963_;
}
}
else
{
lean_dec_ref_known(v___x_4987_, 1);
lean_dec(v___x_4988_);
lean_dec_ref(v_comments_4983_);
lean_dec(v___x_4979_);
lean_dec_ref(v_lineInfos_4975_);
lean_dec(v___x_4965_);
goto v___jp_4963_;
}
}
else
{
lean_dec(v___x_4988_);
lean_dec(v___x_4987_);
lean_dec_ref(v_comments_4983_);
lean_dec(v___x_4979_);
lean_dec_ref(v_lineInfos_4975_);
lean_dec(v___x_4965_);
goto v___jp_4963_;
}
}
else
{
lean_object* v___x_5005_; 
lean_dec_ref(v_comments_4983_);
lean_dec(v___x_4979_);
lean_dec(v___x_4977_);
lean_dec_ref(v_lineInfos_4975_);
lean_dec(v___x_4970_);
lean_dec(v___x_4965_);
v___x_5005_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_5005_;
}
}
}
}
v___jp_4963_:
{
lean_object* v___x_4964_; 
v___x_4964_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector___closed__0));
return v___x_4964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v___x_5010_; 
lean_inc_ref(v___y_5008_);
v___x_5010_ = lean_apply_3(v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___lam__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_);
lean_dec_ref(v___y_5013_);
return v_res_5015_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___f_5018_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__1_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5019_ = l_Lean_Fmt_fmtAttribute;
v___x_5020_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5020_, 0, lean_box(0));
lean_closure_set(v___x_5020_, 1, v___x_5019_);
lean_closure_set(v___x_5020_, 2, v___f_5018_);
return v___x_5020_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___f_5021_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__0_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5022_ = l_Lean_Fmt_infixFmtAttribute;
v___x_5023_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5023_, 0, lean_box(0));
lean_closure_set(v___x_5023_, 1, v___x_5022_);
lean_closure_set(v___x_5023_, 2, v___f_5021_);
return v___x_5023_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___x_5025_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__4_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5026_ = l_Lean_Fmt_conditionalFmtAttribute;
v___x_5027_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5027_, 0, lean_box(0));
lean_closure_set(v___x_5027_, 1, v___x_5026_);
lean_closure_set(v___x_5027_, 2, v___x_5025_);
return v___x_5027_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5029_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__6_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_));
v___x_5030_ = l_Lean_Fmt_quantifierFmtAttribute;
v___x_5031_ = lean_alloc_closure((void*)(l_Lean_Fmt_keyedFmtProvider___boxed), 6, 3);
lean_closure_set(v___x_5031_, 0, lean_box(0));
lean_closure_set(v___x_5031_, 1, v___x_5030_);
lean_closure_set(v___x_5031_, 2, v___x_5029_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5033_ = lean_unsigned_to_nat(1100u);
v___x_5034_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_choiceNodeFmtProvider___boxed), 3, 0);
v___x_5035_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5033_, v___x_5034_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_dec_ref_known(v___x_5035_, 1);
v___x_5036_ = lean_unsigned_to_nat(1000u);
v___x_5037_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__2_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5038_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5036_, v___x_5037_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
lean_dec_ref_known(v___x_5038_, 1);
v___x_5039_ = lean_unsigned_to_nat(900u);
v___x_5040_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_antiquotFmtProvider___boxed), 3, 0);
v___x_5041_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5039_, v___x_5040_);
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
lean_dec_ref_known(v___x_5041_, 1);
v___x_5042_ = lean_unsigned_to_nat(800u);
v___x_5043_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__3_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5044_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5042_, v___x_5043_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_dec_ref_known(v___x_5044_, 1);
v___x_5045_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__5_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5046_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5042_, v___x_5045_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
lean_dec_ref_known(v___x_5046_, 1);
v___x_5047_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2__once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn___closed__7_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_);
v___x_5048_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5042_, v___x_5047_);
if (lean_obj_tag(v___x_5048_) == 0)
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
lean_dec_ref_known(v___x_5048_, 1);
v___x_5049_ = lean_unsigned_to_nat(600u);
v___x_5050_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedOperatorFmtProvider___boxed), 3, 0);
v___x_5051_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5049_, v___x_5050_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
lean_dec_ref_known(v___x_5051_, 1);
v___x_5052_ = lean_unsigned_to_nat(400u);
v___x_5053_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_derivedAtomicFmtProvider___boxed), 3, 0);
v___x_5054_ = l_Lean_Fmt_addBuiltinFmtProvider(v___x_5052_, v___x_5053_);
return v___x_5054_;
}
else
{
return v___x_5051_;
}
}
else
{
return v___x_5048_;
}
}
else
{
return v___x_5046_;
}
}
else
{
return v___x_5044_;
}
}
else
{
return v___x_5041_;
}
}
else
{
return v___x_5038_;
}
}
else
{
return v___x_5035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2____boxed(lean_object* v_a_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_3446410055____hygCtx___hyg_2_();
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5058_ = lean_unsigned_to_nat(500u);
v___x_5059_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_infixOperatorCommentCollector), 2, 0);
v___x_5060_ = l_Lean_Fmt_addBuiltinCommentCollector(v___x_5058_, v___x_5059_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2____boxed(lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_initFn_00___x40_Lean_Fmt_FmtM_Basic_1359926795____hygCtx___hyg_2_();
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f(lean_object* v_stx_x3f_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5063_) == 1)
{
lean_object* v_val_5066_; lean_object* v___x_5067_; 
v_val_5066_ = lean_ctor_get(v_stx_x3f_5063_, 0);
lean_inc(v_val_5066_);
lean_dec_ref_known(v_stx_x3f_5063_, 1);
v___x_5067_ = l_Lean_Fmt_fmt(v_val_5066_, v_a_5064_, v_a_5065_);
return v___x_5067_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5069_; 
lean_dec(v_stx_x3f_5063_);
v___x_5068_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5069_, 0, v___x_5068_);
lean_ctor_set(v___x_5069_, 1, v_a_5065_);
return v___x_5069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmt_x3f___boxed(lean_object* v_stx_x3f_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Lean_Fmt_fmt_x3f(v_stx_x3f_5070_, v_a_5071_, v_a_5072_);
lean_dec_ref(v_a_5071_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f(lean_object* v_f_5074_, lean_object* v_formatterName_5075_, lean_object* v_stx_x3f_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
if (lean_obj_tag(v_stx_x3f_5076_) == 1)
{
lean_object* v_val_5079_; lean_object* v___x_5080_; 
v_val_5079_ = lean_ctor_get(v_stx_x3f_5076_, 0);
lean_inc(v_val_5079_);
lean_dec_ref_known(v_stx_x3f_5076_, 1);
v___x_5080_ = l_Lean_Fmt_fmtWith(v_f_5074_, v_formatterName_5075_, v_val_5079_, v_a_5077_, v_a_5078_);
return v___x_5080_;
}
else
{
lean_object* v___x_5081_; lean_object* v___x_5082_; 
lean_dec(v_stx_x3f_5076_);
lean_dec(v_formatterName_5075_);
lean_dec_ref(v_f_5074_);
v___x_5081_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5081_);
lean_ctor_set(v___x_5082_, 1, v_a_5078_);
return v___x_5082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtWith_x3f___boxed(lean_object* v_f_5083_, lean_object* v_formatterName_5084_, lean_object* v_stx_x3f_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Lean_Fmt_fmtWith_x3f(v_f_5083_, v_formatterName_5084_, v_stx_x3f_5085_, v_a_5086_, v_a_5087_);
lean_dec_ref(v_a_5086_);
return v_res_5088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object* v_array_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_){
_start:
{
size_t v_sz_5092_; size_t v___x_5093_; lean_object* v___x_5094_; 
v_sz_5092_ = lean_array_size(v_array_5089_);
v___x_5093_ = ((size_t)0ULL);
v___x_5094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5092_, v___x_5093_, v_array_5089_, v_a_5090_, v_a_5091_);
return v___x_5094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___redArg___boxed(lean_object* v_array_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l_Lean_Fmt_fmtArray___redArg(v_array_5095_, v_a_5096_, v_a_5097_);
lean_dec_ref(v_a_5096_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray(lean_object* v_ks_5099_, lean_object* v_array_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_Lean_Fmt_fmtArray___redArg(v_array_5100_, v_a_5101_, v_a_5102_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArray___boxed(lean_object* v_ks_5104_, lean_object* v_array_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Lean_Fmt_fmtArray(v_ks_5104_, v_array_5105_, v_a_5106_, v_a_5107_);
lean_dec_ref(v_a_5106_);
lean_dec(v_ks_5104_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(lean_object* v_f_5109_, lean_object* v_formatterName_5110_, size_t v_sz_5111_, size_t v_i_5112_, lean_object* v_bs_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_){
_start:
{
uint8_t v___x_5116_; 
v___x_5116_ = lean_usize_dec_lt(v_i_5112_, v_sz_5111_);
if (v___x_5116_ == 0)
{
lean_object* v___x_5117_; 
lean_dec(v_formatterName_5110_);
lean_dec_ref(v_f_5109_);
v___x_5117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5117_, 0, v_bs_5113_);
lean_ctor_set(v___x_5117_, 1, v___y_5115_);
return v___x_5117_;
}
else
{
lean_object* v_v_5118_; lean_object* v___x_5119_; 
v_v_5118_ = lean_array_uget_borrowed(v_bs_5113_, v_i_5112_);
lean_inc(v_v_5118_);
lean_inc(v_formatterName_5110_);
lean_inc_ref(v_f_5109_);
v___x_5119_ = l_Lean_Fmt_fmtWith(v_f_5109_, v_formatterName_5110_, v_v_5118_, v___y_5114_, v___y_5115_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v_a_5120_; lean_object* v_a_5121_; lean_object* v___x_5122_; lean_object* v_bs_x27_5123_; size_t v___x_5124_; size_t v___x_5125_; lean_object* v___x_5126_; 
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_a_5120_);
v_a_5121_ = lean_ctor_get(v___x_5119_, 1);
lean_inc(v_a_5121_);
lean_dec_ref_known(v___x_5119_, 2);
v___x_5122_ = lean_unsigned_to_nat(0u);
v_bs_x27_5123_ = lean_array_uset(v_bs_5113_, v_i_5112_, v___x_5122_);
v___x_5124_ = ((size_t)1ULL);
v___x_5125_ = lean_usize_add(v_i_5112_, v___x_5124_);
v___x_5126_ = lean_array_uset(v_bs_x27_5123_, v_i_5112_, v_a_5120_);
v_i_5112_ = v___x_5125_;
v_bs_5113_ = v___x_5126_;
v___y_5115_ = v_a_5121_;
goto _start;
}
else
{
lean_object* v_a_5128_; lean_object* v_a_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5136_; 
lean_dec_ref(v_bs_5113_);
lean_dec(v_formatterName_5110_);
lean_dec_ref(v_f_5109_);
v_a_5128_ = lean_ctor_get(v___x_5119_, 0);
v_a_5129_ = lean_ctor_get(v___x_5119_, 1);
v_isSharedCheck_5136_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_5131_ = v___x_5119_;
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_a_5129_);
lean_inc(v_a_5128_);
lean_dec(v___x_5119_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5136_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5134_; 
if (v_isShared_5132_ == 0)
{
v___x_5134_ = v___x_5131_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5135_; 
v_reuseFailAlloc_5135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5128_);
lean_ctor_set(v_reuseFailAlloc_5135_, 1, v_a_5129_);
v___x_5134_ = v_reuseFailAlloc_5135_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
return v___x_5134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0___boxed(lean_object* v_f_5137_, lean_object* v_formatterName_5138_, lean_object* v_sz_5139_, lean_object* v_i_5140_, lean_object* v_bs_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_){
_start:
{
size_t v_sz_boxed_5144_; size_t v_i_boxed_5145_; lean_object* v_res_5146_; 
v_sz_boxed_5144_ = lean_unbox_usize(v_sz_5139_);
lean_dec(v_sz_5139_);
v_i_boxed_5145_ = lean_unbox_usize(v_i_5140_);
lean_dec(v_i_5140_);
v_res_5146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5137_, v_formatterName_5138_, v_sz_boxed_5144_, v_i_boxed_5145_, v_bs_5141_, v___y_5142_, v___y_5143_);
lean_dec_ref(v___y_5142_);
return v_res_5146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg(lean_object* v_f_5147_, lean_object* v_formatterName_5148_, lean_object* v_array_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_){
_start:
{
size_t v_sz_5152_; size_t v___x_5153_; lean_object* v___x_5154_; 
v_sz_5152_ = lean_array_size(v_array_5149_);
v___x_5153_ = ((size_t)0ULL);
v___x_5154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtArrayWith_spec__0(v_f_5147_, v_formatterName_5148_, v_sz_5152_, v___x_5153_, v_array_5149_, v_a_5150_, v_a_5151_);
return v___x_5154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___redArg___boxed(lean_object* v_f_5155_, lean_object* v_formatterName_5156_, lean_object* v_array_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_){
_start:
{
lean_object* v_res_5160_; 
v_res_5160_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5155_, v_formatterName_5156_, v_array_5157_, v_a_5158_, v_a_5159_);
lean_dec_ref(v_a_5158_);
return v_res_5160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith(lean_object* v_ks_5161_, lean_object* v_f_5162_, lean_object* v_formatterName_5163_, lean_object* v_array_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_){
_start:
{
lean_object* v___x_5167_; 
v___x_5167_ = l_Lean_Fmt_fmtArrayWith___redArg(v_f_5162_, v_formatterName_5163_, v_array_5164_, v_a_5165_, v_a_5166_);
return v___x_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWith___boxed(lean_object* v_ks_5168_, lean_object* v_f_5169_, lean_object* v_formatterName_5170_, lean_object* v_array_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_){
_start:
{
lean_object* v_res_5174_; 
v_res_5174_ = l_Lean_Fmt_fmtArrayWith(v_ks_5168_, v_f_5169_, v_formatterName_5170_, v_array_5171_, v_a_5172_, v_a_5173_);
lean_dec_ref(v_a_5172_);
lean_dec(v_ks_5168_);
return v_res_5174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg(lean_object* v_sepArray_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_){
_start:
{
size_t v_sz_5178_; size_t v___x_5179_; lean_object* v___x_5180_; 
v_sz_5178_ = lean_array_size(v_sepArray_5175_);
v___x_5179_ = ((size_t)0ULL);
v___x_5180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5178_, v___x_5179_, v_sepArray_5175_, v_a_5176_, v_a_5177_);
if (lean_obj_tag(v___x_5180_) == 0)
{
lean_object* v_a_5181_; lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
v_a_5181_ = lean_ctor_get(v___x_5180_, 0);
v_a_5182_ = lean_ctor_get(v___x_5180_, 1);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5180_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_inc(v_a_5181_);
lean_dec(v___x_5180_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5181_);
lean_ctor_set(v_reuseFailAlloc_5188_, 1, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
else
{
lean_object* v_a_5190_; lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
v_a_5190_ = lean_ctor_get(v___x_5180_, 0);
v_a_5191_ = lean_ctor_get(v___x_5180_, 1);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5180_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5193_ = v___x_5180_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_a_5191_);
lean_inc(v_a_5190_);
lean_dec(v___x_5180_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_a_5190_);
lean_ctor_set(v_reuseFailAlloc_5197_, 1, v_a_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___redArg___boxed(lean_object* v_sepArray_5199_, lean_object* v_a_5200_, lean_object* v_a_5201_){
_start:
{
lean_object* v_res_5202_; 
v_res_5202_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5199_, v_a_5200_, v_a_5201_);
lean_dec_ref(v_a_5200_);
return v_res_5202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray(lean_object* v_sep_5203_, lean_object* v_sepArray_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_){
_start:
{
lean_object* v___x_5207_; 
v___x_5207_ = l_Lean_Fmt_fmtSepArray___redArg(v_sepArray_5204_, v_a_5205_, v_a_5206_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArray___boxed(lean_object* v_sep_5208_, lean_object* v_sepArray_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_){
_start:
{
lean_object* v_res_5212_; 
v_res_5212_ = l_Lean_Fmt_fmtSepArray(v_sep_5208_, v_sepArray_5209_, v_a_5210_, v_a_5211_);
lean_dec_ref(v_a_5210_);
lean_dec_ref(v_sep_5208_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(lean_object* v_f_5213_, lean_object* v_formatterName_5214_, size_t v_sz_5215_, size_t v_i_5216_, lean_object* v_bs_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
uint8_t v___x_5220_; 
v___x_5220_ = lean_usize_dec_lt(v_i_5216_, v_sz_5215_);
if (v___x_5220_ == 0)
{
lean_object* v___x_5221_; 
lean_dec(v_formatterName_5214_);
lean_dec_ref(v_f_5213_);
v___x_5221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5221_, 0, v_bs_5217_);
lean_ctor_set(v___x_5221_, 1, v___y_5219_);
return v___x_5221_;
}
else
{
lean_object* v_v_5222_; lean_object* v___x_5223_; lean_object* v_bs_x27_5224_; lean_object* v___y_5226_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; uint8_t v___x_5245_; 
v_v_5222_ = lean_array_uget(v_bs_5217_, v_i_5216_);
v___x_5223_ = lean_unsigned_to_nat(0u);
v_bs_x27_5224_ = lean_array_uset(v_bs_5217_, v_i_5216_, v___x_5223_);
v___x_5242_ = lean_usize_to_nat(v_i_5216_);
v___x_5243_ = lean_unsigned_to_nat(2u);
v___x_5244_ = lean_nat_mod(v___x_5242_, v___x_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_nat_dec_eq(v___x_5244_, v___x_5223_);
lean_dec(v___x_5244_);
if (v___x_5245_ == 0)
{
lean_object* v___x_5246_; 
v___x_5246_ = l_Lean_Fmt_fmt(v_v_5222_, v___y_5218_, v___y_5219_);
v___y_5226_ = v___x_5246_;
goto v___jp_5225_;
}
else
{
lean_object* v___x_5247_; 
lean_inc(v_formatterName_5214_);
lean_inc_ref(v_f_5213_);
v___x_5247_ = l_Lean_Fmt_fmtWith(v_f_5213_, v_formatterName_5214_, v_v_5222_, v___y_5218_, v___y_5219_);
v___y_5226_ = v___x_5247_;
goto v___jp_5225_;
}
v___jp_5225_:
{
if (lean_obj_tag(v___y_5226_) == 0)
{
lean_object* v_a_5227_; lean_object* v_a_5228_; size_t v___x_5229_; size_t v___x_5230_; lean_object* v___x_5231_; 
v_a_5227_ = lean_ctor_get(v___y_5226_, 0);
lean_inc(v_a_5227_);
v_a_5228_ = lean_ctor_get(v___y_5226_, 1);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___y_5226_, 2);
v___x_5229_ = ((size_t)1ULL);
v___x_5230_ = lean_usize_add(v_i_5216_, v___x_5229_);
v___x_5231_ = lean_array_uset(v_bs_x27_5224_, v_i_5216_, v_a_5227_);
v_i_5216_ = v___x_5230_;
v_bs_5217_ = v___x_5231_;
v___y_5219_ = v_a_5228_;
goto _start;
}
else
{
lean_object* v_a_5233_; lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5241_; 
lean_dec_ref(v_bs_x27_5224_);
lean_dec(v_formatterName_5214_);
lean_dec_ref(v_f_5213_);
v_a_5233_ = lean_ctor_get(v___y_5226_, 0);
v_a_5234_ = lean_ctor_get(v___y_5226_, 1);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___y_5226_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5236_ = v___y_5226_;
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_inc(v_a_5233_);
lean_dec(v___y_5226_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5233_);
lean_ctor_set(v_reuseFailAlloc_5240_, 1, v_a_5234_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg___boxed(lean_object* v_f_5248_, lean_object* v_formatterName_5249_, lean_object* v_sz_5250_, lean_object* v_i_5251_, lean_object* v_bs_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
size_t v_sz_boxed_5255_; size_t v_i_boxed_5256_; lean_object* v_res_5257_; 
v_sz_boxed_5255_ = lean_unbox_usize(v_sz_5250_);
lean_dec(v_sz_5250_);
v_i_boxed_5256_ = lean_unbox_usize(v_i_5251_);
lean_dec(v_i_5251_);
v_res_5257_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5248_, v_formatterName_5249_, v_sz_boxed_5255_, v_i_boxed_5256_, v_bs_5252_, v___y_5253_, v___y_5254_);
lean_dec_ref(v___y_5253_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg(lean_object* v_f_5258_, lean_object* v_formatterName_5259_, lean_object* v_sepArray_5260_, lean_object* v_a_5261_, lean_object* v_a_5262_){
_start:
{
size_t v_sz_5263_; size_t v___x_5264_; lean_object* v___x_5265_; 
v_sz_5263_ = lean_array_size(v_sepArray_5260_);
v___x_5264_ = ((size_t)0ULL);
v___x_5265_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5258_, v_formatterName_5259_, v_sz_5263_, v___x_5264_, v_sepArray_5260_, v_a_5261_, v_a_5262_);
if (lean_obj_tag(v___x_5265_) == 0)
{
lean_object* v_a_5266_; lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
v_a_5266_ = lean_ctor_get(v___x_5265_, 0);
v_a_5267_ = lean_ctor_get(v___x_5265_, 1);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5265_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5265_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_inc(v_a_5266_);
lean_dec(v___x_5265_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5266_);
lean_ctor_set(v_reuseFailAlloc_5273_, 1, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
else
{
lean_object* v_a_5275_; lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5283_; 
v_a_5275_ = lean_ctor_get(v___x_5265_, 0);
v_a_5276_ = lean_ctor_get(v___x_5265_, 1);
v_isSharedCheck_5283_ = !lean_is_exclusive(v___x_5265_);
if (v_isSharedCheck_5283_ == 0)
{
v___x_5278_ = v___x_5265_;
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_inc(v_a_5275_);
lean_dec(v___x_5265_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5283_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v___x_5281_; 
if (v_isShared_5279_ == 0)
{
v___x_5281_ = v___x_5278_;
goto v_reusejp_5280_;
}
else
{
lean_object* v_reuseFailAlloc_5282_; 
v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5275_);
lean_ctor_set(v_reuseFailAlloc_5282_, 1, v_a_5276_);
v___x_5281_ = v_reuseFailAlloc_5282_;
goto v_reusejp_5280_;
}
v_reusejp_5280_:
{
return v___x_5281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___redArg___boxed(lean_object* v_f_5284_, lean_object* v_formatterName_5285_, lean_object* v_sepArray_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_){
_start:
{
lean_object* v_res_5289_; 
v_res_5289_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5284_, v_formatterName_5285_, v_sepArray_5286_, v_a_5287_, v_a_5288_);
lean_dec_ref(v_a_5287_);
return v_res_5289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith(lean_object* v_sep_5290_, lean_object* v_f_5291_, lean_object* v_formatterName_5292_, lean_object* v_sepArray_5293_, lean_object* v_a_5294_, lean_object* v_a_5295_){
_start:
{
lean_object* v___x_5296_; 
v___x_5296_ = l_Lean_Fmt_fmtSepArrayWith___redArg(v_f_5291_, v_formatterName_5292_, v_sepArray_5293_, v_a_5294_, v_a_5295_);
return v___x_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtSepArrayWith___boxed(lean_object* v_sep_5297_, lean_object* v_f_5298_, lean_object* v_formatterName_5299_, lean_object* v_sepArray_5300_, lean_object* v_a_5301_, lean_object* v_a_5302_){
_start:
{
lean_object* v_res_5303_; 
v_res_5303_ = l_Lean_Fmt_fmtSepArrayWith(v_sep_5297_, v_f_5298_, v_formatterName_5299_, v_sepArray_5300_, v_a_5301_, v_a_5302_);
lean_dec_ref(v_a_5301_);
lean_dec_ref(v_sep_5297_);
return v_res_5303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(lean_object* v_f_5304_, lean_object* v_formatterName_5305_, lean_object* v_as_5306_, size_t v_sz_5307_, size_t v_i_5308_, lean_object* v_bs_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_){
_start:
{
lean_object* v___x_5312_; 
v___x_5312_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5304_, v_formatterName_5305_, v_sz_5307_, v_i_5308_, v_bs_5309_, v___y_5310_, v___y_5311_);
return v___x_5312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___boxed(lean_object* v_f_5313_, lean_object* v_formatterName_5314_, lean_object* v_as_5315_, lean_object* v_sz_5316_, lean_object* v_i_5317_, lean_object* v_bs_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_){
_start:
{
size_t v_sz_boxed_5321_; size_t v_i_boxed_5322_; lean_object* v_res_5323_; 
v_sz_boxed_5321_ = lean_unbox_usize(v_sz_5316_);
lean_dec(v_sz_5316_);
v_i_boxed_5322_ = lean_unbox_usize(v_i_5317_);
lean_dec(v_i_5317_);
v_res_5323_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0(v_f_5313_, v_formatterName_5314_, v_as_5315_, v_sz_boxed_5321_, v_i_boxed_5322_, v_bs_5318_, v___y_5319_, v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec_ref(v_as_5315_);
return v_res_5323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object* v_sepArray_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_){
_start:
{
size_t v_sz_5327_; size_t v___x_5328_; lean_object* v___x_5329_; 
v_sz_5327_ = lean_array_size(v_sepArray_5324_);
v___x_5328_ = ((size_t)0ULL);
v___x_5329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtInfixOperator_spec__1(v_sz_5327_, v___x_5328_, v_sepArray_5324_, v_a_5325_, v_a_5326_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v_a_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5338_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
v_a_5331_ = lean_ctor_get(v___x_5329_, 1);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5338_ == 0)
{
v___x_5333_ = v___x_5329_;
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_a_5331_);
lean_inc(v_a_5330_);
lean_dec(v___x_5329_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5338_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5336_; 
if (v_isShared_5334_ == 0)
{
v___x_5336_ = v___x_5333_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5337_; 
v_reuseFailAlloc_5337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_a_5330_);
lean_ctor_set(v_reuseFailAlloc_5337_, 1, v_a_5331_);
v___x_5336_ = v_reuseFailAlloc_5337_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
return v___x_5336_;
}
}
}
else
{
lean_object* v_a_5339_; lean_object* v_a_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5347_; 
v_a_5339_ = lean_ctor_get(v___x_5329_, 0);
v_a_5340_ = lean_ctor_get(v___x_5329_, 1);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5329_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5342_ = v___x_5329_;
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_a_5340_);
lean_inc(v_a_5339_);
lean_dec(v___x_5329_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5345_; 
if (v_isShared_5343_ == 0)
{
v___x_5345_ = v___x_5342_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5339_);
lean_ctor_set(v_reuseFailAlloc_5346_, 1, v_a_5340_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___redArg___boxed(lean_object* v_sepArray_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_){
_start:
{
lean_object* v_res_5351_; 
v_res_5351_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5348_, v_a_5349_, v_a_5350_);
lean_dec_ref(v_a_5349_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray(lean_object* v_ks_5352_, lean_object* v_sep_5353_, lean_object* v_sepArray_5354_, lean_object* v_a_5355_, lean_object* v_a_5356_){
_start:
{
lean_object* v___x_5357_; 
v___x_5357_ = l_Lean_Fmt_fmtTSepArray___redArg(v_sepArray_5354_, v_a_5355_, v_a_5356_);
return v___x_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArray___boxed(lean_object* v_ks_5358_, lean_object* v_sep_5359_, lean_object* v_sepArray_5360_, lean_object* v_a_5361_, lean_object* v_a_5362_){
_start:
{
lean_object* v_res_5363_; 
v_res_5363_ = l_Lean_Fmt_fmtTSepArray(v_ks_5358_, v_sep_5359_, v_sepArray_5360_, v_a_5361_, v_a_5362_);
lean_dec_ref(v_a_5361_);
lean_dec_ref(v_sep_5359_);
lean_dec(v_ks_5358_);
return v_res_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg(lean_object* v_f_5364_, lean_object* v_formatterName_5365_, lean_object* v_sepArray_5366_, lean_object* v_a_5367_, lean_object* v_a_5368_){
_start:
{
size_t v_sz_5369_; size_t v___x_5370_; lean_object* v___x_5371_; 
v_sz_5369_ = lean_array_size(v_sepArray_5366_);
v___x_5370_ = ((size_t)0ULL);
v___x_5371_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_fmtSepArrayWith_spec__0___redArg(v_f_5364_, v_formatterName_5365_, v_sz_5369_, v___x_5370_, v_sepArray_5366_, v_a_5367_, v_a_5368_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v_a_5372_; lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
v_a_5373_ = lean_ctor_get(v___x_5371_, 1);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___x_5371_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_inc(v_a_5372_);
lean_dec(v___x_5371_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5372_);
lean_ctor_set(v_reuseFailAlloc_5379_, 1, v_a_5373_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
else
{
lean_object* v_a_5381_; lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
v_a_5381_ = lean_ctor_get(v___x_5371_, 0);
v_a_5382_ = lean_ctor_get(v___x_5371_, 1);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5371_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_inc(v_a_5381_);
lean_dec(v___x_5371_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5381_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___redArg___boxed(lean_object* v_f_5390_, lean_object* v_formatterName_5391_, lean_object* v_sepArray_5392_, lean_object* v_a_5393_, lean_object* v_a_5394_){
_start:
{
lean_object* v_res_5395_; 
v_res_5395_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5390_, v_formatterName_5391_, v_sepArray_5392_, v_a_5393_, v_a_5394_);
lean_dec_ref(v_a_5393_);
return v_res_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith(lean_object* v_ks_5396_, lean_object* v_sep_5397_, lean_object* v_f_5398_, lean_object* v_formatterName_5399_, lean_object* v_sepArray_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v___x_5403_; 
v___x_5403_ = l_Lean_Fmt_fmtTSepArrayWith___redArg(v_f_5398_, v_formatterName_5399_, v_sepArray_5400_, v_a_5401_, v_a_5402_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWith___boxed(lean_object* v_ks_5404_, lean_object* v_sep_5405_, lean_object* v_f_5406_, lean_object* v_formatterName_5407_, lean_object* v_sepArray_5408_, lean_object* v_a_5409_, lean_object* v_a_5410_){
_start:
{
lean_object* v_res_5411_; 
v_res_5411_ = l_Lean_Fmt_fmtTSepArrayWith(v_ks_5404_, v_sep_5405_, v_f_5406_, v_formatterName_5407_, v_sepArray_5408_, v_a_5409_, v_a_5410_);
lean_dec_ref(v_a_5409_);
lean_dec_ref(v_sep_5405_);
lean_dec(v_ks_5404_);
return v_res_5411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(lean_object* v___x_5412_, lean_object* v___x_5413_, lean_object* v___x_5414_, lean_object* v_a_5415_, lean_object* v_b_5416_){
_start:
{
uint8_t v___y_5418_; uint8_t v___x_5435_; uint8_t v___y_5437_; uint8_t v___x_5438_; 
v___x_5435_ = lean_string_is_valid_pos(v___x_5412_, v___x_5413_);
v___x_5438_ = lean_string_is_valid_pos(v___x_5412_, v___x_5414_);
if (v___x_5438_ == 0)
{
v___y_5437_ = v___x_5438_;
goto v___jp_5436_;
}
else
{
uint8_t v___x_5439_; 
v___x_5439_ = lean_nat_dec_le(v___x_5413_, v___x_5414_);
v___y_5437_ = v___x_5439_;
goto v___jp_5436_;
}
v___jp_5417_:
{
lean_object* v___x_5419_; uint8_t v_decide_5420_; 
v___x_5419_ = lean_nat_sub(v___x_5414_, v___x_5413_);
v_decide_5420_ = lean_nat_dec_eq(v_a_5415_, v___x_5419_);
lean_dec(v___x_5419_);
if (v_decide_5420_ == 0)
{
uint32_t v___x_5421_; lean_object* v___x_5422_; uint32_t v___x_5423_; uint8_t v___x_5424_; 
v___x_5421_ = 10;
v___x_5422_ = lean_nat_add(v___x_5413_, v_a_5415_);
v___x_5423_ = lean_string_utf8_get_fast(v___x_5412_, v___x_5422_);
v___x_5424_ = lean_uint32_dec_eq(v___x_5423_, v___x_5421_);
if (v___x_5424_ == 0)
{
lean_object* v___x_5425_; lean_object* v___x_5426_; 
lean_dec(v_a_5415_);
v___x_5425_ = lean_string_utf8_next_fast(v___x_5412_, v___x_5422_);
lean_dec(v___x_5422_);
v___x_5426_ = lean_nat_sub(v___x_5425_, v___x_5413_);
v_a_5415_ = v___x_5426_;
goto _start;
}
else
{
lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5428_ = lean_string_utf8_next_fast(v___x_5412_, v___x_5422_);
v___x_5429_ = lean_nat_sub(v___x_5428_, v___x_5422_);
lean_dec(v___x_5422_);
v___x_5430_ = lean_nat_add(v_a_5415_, v___x_5429_);
lean_dec(v___x_5429_);
lean_dec(v_a_5415_);
if (v___y_5418_ == 0)
{
v_a_5415_ = v___x_5430_;
goto _start;
}
else
{
lean_object* v___x_5432_; lean_object* v___x_5433_; 
v___x_5432_ = lean_unsigned_to_nat(1u);
v___x_5433_ = lean_nat_add(v_b_5416_, v___x_5432_);
lean_dec(v_b_5416_);
v_a_5415_ = v___x_5430_;
v_b_5416_ = v___x_5433_;
goto _start;
}
}
}
else
{
lean_dec(v_a_5415_);
return v_b_5416_;
}
}
v___jp_5436_:
{
if (v___x_5435_ == 0)
{
v___y_5418_ = v___x_5435_;
goto v___jp_5417_;
}
else
{
v___y_5418_ = v___y_5437_;
goto v___jp_5417_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___x_5440_, lean_object* v___x_5441_, lean_object* v___x_5442_, lean_object* v_a_5443_, lean_object* v_b_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5440_, v___x_5441_, v___x_5442_, v_a_5443_, v_b_5444_);
lean_dec(v___x_5442_);
lean_dec(v___x_5441_);
lean_dec_ref(v___x_5440_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5448_, lean_object* v_minNewlines_5449_, lean_object* v_leadingTk_5450_, lean_object* v_leading_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_){
_start:
{
lean_object* v___y_5455_; lean_object* v___y_5466_; lean_object* v_str_5468_; lean_object* v_startPos_5469_; lean_object* v_stopPos_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5491_; 
v_str_5468_ = lean_ctor_get(v_leading_5451_, 0);
v_startPos_5469_ = lean_ctor_get(v_leading_5451_, 1);
v_stopPos_5470_ = lean_ctor_get(v_leading_5451_, 2);
v_isSharedCheck_5491_ = !lean_is_exclusive(v_leading_5451_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5472_ = v_leading_5451_;
v_isShared_5473_ = v_isSharedCheck_5491_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_stopPos_5470_);
lean_inc(v_startPos_5469_);
lean_inc(v_str_5468_);
lean_dec(v_leading_5451_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5491_;
goto v_resetjp_5471_;
}
v___jp_5454_:
{
lean_object* v___x_5456_; lean_object* v_nls_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; 
v___x_5456_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5457_ = lean_mk_array(v___y_5455_, v___x_5456_);
v___x_5458_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5457_);
v___x_5459_ = lean_box(0);
v___x_5460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5460_, 0, v___x_5458_);
lean_ctor_set(v___x_5460_, 1, v___x_5459_);
v___x_5461_ = lean_unsigned_to_nat(1u);
v___x_5462_ = lean_mk_empty_array_with_capacity(v___x_5461_);
v___x_5463_ = lean_array_push(v___x_5462_, v___x_5460_);
v___x_5464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5463_);
lean_ctor_set(v___x_5464_, 1, v___y_5453_);
return v___x_5464_;
}
v___jp_5465_:
{
uint8_t v___x_5467_; 
v___x_5467_ = lean_nat_dec_le(v___y_5466_, v_maxNewlines_5448_);
if (v___x_5467_ == 0)
{
lean_dec(v___y_5466_);
v___y_5455_ = v_maxNewlines_5448_;
goto v___jp_5454_;
}
else
{
lean_dec(v_maxNewlines_5448_);
v___y_5455_ = v___y_5466_;
goto v___jp_5454_;
}
}
v_resetjp_5471_:
{
uint8_t v___y_5475_; uint8_t v___x_5486_; uint8_t v___y_5488_; uint8_t v___x_5489_; 
v___x_5486_ = lean_string_is_valid_pos(v_str_5468_, v_startPos_5469_);
v___x_5489_ = lean_string_is_valid_pos(v_str_5468_, v_stopPos_5470_);
if (v___x_5489_ == 0)
{
v___y_5488_ = v___x_5489_;
goto v___jp_5487_;
}
else
{
uint8_t v___x_5490_; 
v___x_5490_ = lean_nat_dec_le(v_startPos_5469_, v_stopPos_5470_);
v___y_5488_ = v___x_5490_;
goto v___jp_5487_;
}
v___jp_5474_:
{
if (v___y_5475_ == 0)
{
lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5479_; 
lean_dec(v_stopPos_5470_);
lean_dec(v_startPos_5469_);
lean_dec_ref(v_str_5468_);
lean_dec(v_minNewlines_5449_);
lean_dec(v_maxNewlines_5448_);
v___x_5476_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5477_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
if (v_isShared_5473_ == 0)
{
lean_ctor_set(v___x_5472_, 2, v___x_5477_);
lean_ctor_set(v___x_5472_, 1, v___x_5476_);
lean_ctor_set(v___x_5472_, 0, v_leadingTk_5450_);
v___x_5479_ = v___x_5472_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_leadingTk_5450_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5482_, 2, v___x_5477_);
v___x_5479_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5480_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5479_);
v___x_5481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5481_, 0, v___x_5480_);
lean_ctor_set(v___x_5481_, 1, v___y_5453_);
return v___x_5481_;
}
}
else
{
lean_object* v_searcher_5483_; lean_object* v_numNewlines_5484_; uint8_t v___x_5485_; 
lean_del_object(v___x_5472_);
lean_dec(v_leadingTk_5450_);
v_searcher_5483_ = lean_unsigned_to_nat(0u);
v_numNewlines_5484_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v_str_5468_, v_startPos_5469_, v_stopPos_5470_, v_searcher_5483_, v_searcher_5483_);
lean_dec(v_stopPos_5470_);
lean_dec(v_startPos_5469_);
lean_dec_ref(v_str_5468_);
v___x_5485_ = lean_nat_dec_le(v_numNewlines_5484_, v_minNewlines_5449_);
if (v___x_5485_ == 0)
{
lean_dec(v_minNewlines_5449_);
v___y_5466_ = v_numNewlines_5484_;
goto v___jp_5465_;
}
else
{
lean_dec(v_numNewlines_5484_);
v___y_5466_ = v_minNewlines_5449_;
goto v___jp_5465_;
}
}
}
v___jp_5487_:
{
if (v___x_5486_ == 0)
{
v___y_5475_ = v___x_5486_;
goto v___jp_5474_;
}
else
{
v___y_5475_ = v___y_5488_;
goto v___jp_5474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5492_, lean_object* v_minNewlines_5493_, lean_object* v_leadingTk_5494_, lean_object* v_leading_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_){
_start:
{
lean_object* v_res_5498_; 
v_res_5498_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0(v_maxNewlines_5492_, v_minNewlines_5493_, v_leadingTk_5494_, v_leading_5495_, v___y_5496_, v___y_5497_);
lean_dec_ref(v___y_5496_);
return v_res_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines(lean_object* v_stx_5499_, lean_object* v_minNewlines_5500_, lean_object* v_maxNewlines_5501_, lean_object* v_a_5502_, lean_object* v_a_5503_){
_start:
{
lean_object* v___f_5504_; lean_object* v___x_5505_; 
v___f_5504_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5504_, 0, v_maxNewlines_5501_);
lean_closure_set(v___f_5504_, 1, v_minNewlines_5500_);
v___x_5505_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_5499_, v___f_5504_, v_a_5502_, v_a_5503_);
return v___x_5505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlines___boxed(lean_object* v_stx_5506_, lean_object* v_minNewlines_5507_, lean_object* v_maxNewlines_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_){
_start:
{
lean_object* v_res_5511_; 
v_res_5511_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlines(v_stx_5506_, v_minNewlines_5507_, v_maxNewlines_5508_, v_a_5509_, v_a_5510_);
lean_dec_ref(v_a_5509_);
return v_res_5511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(lean_object* v___x_5512_, lean_object* v___x_5513_, lean_object* v___x_5514_, lean_object* v___x_5515_, lean_object* v_inst_5516_, lean_object* v_R_5517_, lean_object* v_a_5518_, lean_object* v_b_5519_, lean_object* v_c_5520_){
_start:
{
lean_object* v___x_5521_; 
v___x_5521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v___x_5512_, v___x_5513_, v___x_5514_, v_a_5518_, v_b_5519_);
return v___x_5521_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___boxed(lean_object* v___x_5522_, lean_object* v___x_5523_, lean_object* v___x_5524_, lean_object* v___x_5525_, lean_object* v_inst_5526_, lean_object* v_R_5527_, lean_object* v_a_5528_, lean_object* v_b_5529_, lean_object* v_c_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0(v___x_5522_, v___x_5523_, v___x_5524_, v___x_5525_, v_inst_5526_, v_R_5527_, v_a_5528_, v_b_5529_, v_c_5530_);
lean_dec_ref(v___x_5525_);
lean_dec(v___x_5524_);
lean_dec(v___x_5523_);
lean_dec_ref(v___x_5522_);
return v_res_5531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(lean_object* v_maxNewlines_5532_, lean_object* v_minNewlines_5533_, lean_object* v_trailingTk_5534_, lean_object* v_trailing_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_){
_start:
{
lean_object* v___y_5539_; lean_object* v___y_5550_; lean_object* v_str_5552_; lean_object* v_startPos_5553_; lean_object* v_stopPos_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5575_; 
v_str_5552_ = lean_ctor_get(v_trailing_5535_, 0);
v_startPos_5553_ = lean_ctor_get(v_trailing_5535_, 1);
v_stopPos_5554_ = lean_ctor_get(v_trailing_5535_, 2);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_trailing_5535_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5556_ = v_trailing_5535_;
v_isShared_5557_ = v_isSharedCheck_5575_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_stopPos_5554_);
lean_inc(v_startPos_5553_);
lean_inc(v_str_5552_);
lean_dec(v_trailing_5535_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5575_;
goto v_resetjp_5555_;
}
v___jp_5538_:
{
lean_object* v___x_5540_; lean_object* v_nls_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; 
v___x_5540_ = l_Lean_Fmt_TaggedDoc_hardNl;
v_nls_5541_ = lean_mk_array(v___y_5539_, v___x_5540_);
v___x_5542_ = l_Lean_Fmt_TaggedDoc_join(v_nls_5541_);
v___x_5543_ = lean_box(0);
v___x_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5542_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
v___x_5545_ = lean_unsigned_to_nat(1u);
v___x_5546_ = lean_mk_empty_array_with_capacity(v___x_5545_);
v___x_5547_ = lean_array_push(v___x_5546_, v___x_5544_);
v___x_5548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5548_, 0, v___x_5547_);
lean_ctor_set(v___x_5548_, 1, v___y_5537_);
return v___x_5548_;
}
v___jp_5549_:
{
uint8_t v___x_5551_; 
v___x_5551_ = lean_nat_dec_le(v___y_5550_, v_maxNewlines_5532_);
if (v___x_5551_ == 0)
{
lean_dec(v___y_5550_);
v___y_5539_ = v_maxNewlines_5532_;
goto v___jp_5538_;
}
else
{
lean_dec(v_maxNewlines_5532_);
v___y_5539_ = v___y_5550_;
goto v___jp_5538_;
}
}
v_resetjp_5555_:
{
uint8_t v___y_5559_; uint8_t v___x_5570_; uint8_t v___y_5572_; uint8_t v___x_5573_; 
v___x_5570_ = lean_string_is_valid_pos(v_str_5552_, v_startPos_5553_);
v___x_5573_ = lean_string_is_valid_pos(v_str_5552_, v_stopPos_5554_);
if (v___x_5573_ == 0)
{
v___y_5572_ = v___x_5573_;
goto v___jp_5571_;
}
else
{
uint8_t v___x_5574_; 
v___x_5574_ = lean_nat_dec_le(v_startPos_5553_, v_stopPos_5554_);
v___y_5572_ = v___x_5574_;
goto v___jp_5571_;
}
v___jp_5558_:
{
if (v___y_5559_ == 0)
{
lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5563_; 
lean_dec(v_stopPos_5554_);
lean_dec(v_startPos_5553_);
lean_dec_ref(v_str_5552_);
lean_dec(v_minNewlines_5533_);
lean_dec(v_maxNewlines_5532_);
v___x_5560_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_5561_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 2, v___x_5561_);
lean_ctor_set(v___x_5556_, 1, v___x_5560_);
lean_ctor_set(v___x_5556_, 0, v_trailingTk_5534_);
v___x_5563_ = v___x_5556_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_trailingTk_5534_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5560_);
lean_ctor_set(v_reuseFailAlloc_5566_, 2, v___x_5561_);
v___x_5563_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5564_; lean_object* v___x_5565_; 
v___x_5564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5564_, 0, v___x_5563_);
v___x_5565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
lean_ctor_set(v___x_5565_, 1, v___y_5537_);
return v___x_5565_;
}
}
else
{
lean_object* v_searcher_5567_; lean_object* v_numNewlines_5568_; uint8_t v___x_5569_; 
lean_del_object(v___x_5556_);
lean_dec(v_trailingTk_5534_);
v_searcher_5567_ = lean_unsigned_to_nat(0u);
v_numNewlines_5568_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtLeadingWithRetainedNewlines_spec__0___redArg(v_str_5552_, v_startPos_5553_, v_stopPos_5554_, v_searcher_5567_, v_searcher_5567_);
lean_dec(v_stopPos_5554_);
lean_dec(v_startPos_5553_);
lean_dec_ref(v_str_5552_);
v___x_5569_ = lean_nat_dec_le(v_numNewlines_5568_, v_minNewlines_5533_);
if (v___x_5569_ == 0)
{
lean_dec(v_minNewlines_5533_);
v___y_5550_ = v_numNewlines_5568_;
goto v___jp_5549_;
}
else
{
lean_dec(v_numNewlines_5568_);
v___y_5550_ = v_minNewlines_5533_;
goto v___jp_5549_;
}
}
}
v___jp_5571_:
{
if (v___x_5570_ == 0)
{
v___y_5559_ = v___x_5570_;
goto v___jp_5558_;
}
else
{
v___y_5559_ = v___y_5572_;
goto v___jp_5558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed(lean_object* v_maxNewlines_5576_, lean_object* v_minNewlines_5577_, lean_object* v_trailingTk_5578_, lean_object* v_trailing_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_){
_start:
{
lean_object* v_res_5582_; 
v_res_5582_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0(v_maxNewlines_5576_, v_minNewlines_5577_, v_trailingTk_5578_, v_trailing_5579_, v___y_5580_, v___y_5581_);
lean_dec_ref(v___y_5580_);
return v_res_5582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines(lean_object* v_stx_5583_, lean_object* v_minNewlines_5584_, lean_object* v_maxNewlines_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_){
_start:
{
lean_object* v___f_5588_; lean_object* v___x_5589_; 
v___f_5588_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlines___lam__0___boxed), 6, 2);
lean_closure_set(v___f_5588_, 0, v_maxNewlines_5585_);
lean_closure_set(v___f_5588_, 1, v_minNewlines_5584_);
v___x_5589_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_5583_, v___f_5588_, v_a_5586_, v_a_5587_);
return v___x_5589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlines___boxed(lean_object* v_stx_5590_, lean_object* v_minNewlines_5591_, lean_object* v_maxNewlines_5592_, lean_object* v_a_5593_, lean_object* v_a_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v_stx_5590_, v_minNewlines_5591_, v_maxNewlines_5592_, v_a_5593_, v_a_5594_);
lean_dec_ref(v_a_5593_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(lean_object* v_b_5596_, lean_object* v_a_5597_, lean_object* v_trailingDoc_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_){
_start:
{
lean_object* v___y_5602_; uint8_t v___x_5606_; 
v___x_5606_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_5597_);
if (v___x_5606_ == 0)
{
uint8_t v___x_5607_; 
v___x_5607_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_trailingDoc_5598_);
if (v___x_5607_ == 0)
{
lean_object* v_doc_5608_; lean_object* v_doc_5609_; uint8_t v___x_5610_; 
v_doc_5608_ = lean_ctor_get(v_a_5597_, 0);
lean_inc(v_doc_5608_);
lean_dec_ref(v_a_5597_);
v_doc_5609_ = lean_ctor_get(v_trailingDoc_5598_, 0);
lean_inc(v_doc_5609_);
lean_dec_ref(v_trailingDoc_5598_);
v___x_5610_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5608_);
if (v___x_5610_ == 0)
{
uint8_t v___x_5611_; 
v___x_5611_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_5609_);
if (v___x_5611_ == 0)
{
lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5612_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_5608_, v_doc_5609_);
v___x_5613_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_5612_);
v___y_5602_ = v___x_5613_;
goto v___jp_5601_;
}
else
{
lean_object* v___x_5614_; 
lean_dec(v_doc_5609_);
v___x_5614_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5608_);
v___y_5602_ = v___x_5614_;
goto v___jp_5601_;
}
}
else
{
lean_object* v___x_5615_; 
lean_dec(v_doc_5608_);
v___x_5615_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_5609_);
v___y_5602_ = v___x_5615_;
goto v___jp_5601_;
}
}
else
{
lean_dec_ref(v_trailingDoc_5598_);
v___y_5602_ = v_a_5597_;
goto v___jp_5601_;
}
}
else
{
lean_dec_ref(v_a_5597_);
v___y_5602_ = v_trailingDoc_5598_;
goto v___jp_5601_;
}
v___jp_5601_:
{
lean_object* v___x_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; 
v___x_5603_ = lean_array_push(v_b_5596_, v___y_5602_);
v___x_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
v___x_5605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5605_, 0, v___x_5604_);
lean_ctor_set(v___x_5605_, 1, v___y_5600_);
return v___x_5605_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0___boxed(lean_object* v_b_5616_, lean_object* v_a_5617_, lean_object* v_trailingDoc_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
lean_object* v_res_5621_; 
v_res_5621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5616_, v_a_5617_, v_trailingDoc_5618_, v___y_5619_, v___y_5620_);
lean_dec_ref(v___y_5619_);
return v_res_5621_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(lean_object* v_upperBound_5622_, lean_object* v_stxs_5623_, lean_object* v___x_5624_, lean_object* v_a_5625_, lean_object* v_b_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_){
_start:
{
uint8_t v___x_5629_; 
v___x_5629_ = lean_nat_dec_lt(v_a_5625_, v_upperBound_5622_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5630_; 
lean_dec(v_a_5625_);
v___x_5630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5630_, 0, v_b_5626_);
lean_ctor_set(v___x_5630_, 1, v___y_5628_);
return v___x_5630_;
}
else
{
lean_object* v___x_5631_; lean_object* v___x_5632_; 
v___x_5631_ = lean_array_fget_borrowed(v_stxs_5623_, v_a_5625_);
lean_inc(v___x_5631_);
v___x_5632_ = l_Lean_Fmt_fmt(v___x_5631_, v___y_5627_, v___y_5628_);
if (lean_obj_tag(v___x_5632_) == 0)
{
lean_object* v_a_5633_; lean_object* v_a_5634_; lean_object* v___x_5635_; lean_object* v___y_5637_; lean_object* v___x_5662_; uint8_t v___x_5663_; 
v_a_5633_ = lean_ctor_get(v___x_5632_, 0);
lean_inc(v_a_5633_);
v_a_5634_ = lean_ctor_get(v___x_5632_, 1);
lean_inc(v_a_5634_);
lean_dec_ref_known(v___x_5632_, 2);
v___x_5635_ = lean_unsigned_to_nat(1u);
v___x_5662_ = lean_nat_sub(v___x_5624_, v___x_5635_);
v___x_5663_ = lean_nat_dec_lt(v_a_5625_, v___x_5662_);
lean_dec(v___x_5662_);
if (v___x_5663_ == 0)
{
lean_object* v___x_5664_; lean_object* v___x_5665_; 
v___x_5664_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5626_, v_a_5633_, v___x_5664_, v___y_5627_, v_a_5634_);
v___y_5637_ = v___x_5665_;
goto v___jp_5636_;
}
else
{
lean_object* v___x_5666_; lean_object* v___x_5667_; 
v___x_5666_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5631_);
v___x_5667_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlines(v___x_5631_, v___x_5635_, v___x_5666_, v___y_5627_, v_a_5634_);
if (lean_obj_tag(v___x_5667_) == 0)
{
lean_object* v_a_5668_; lean_object* v_a_5669_; lean_object* v___x_5670_; 
v_a_5668_ = lean_ctor_get(v___x_5667_, 0);
lean_inc(v_a_5668_);
v_a_5669_ = lean_ctor_get(v___x_5667_, 1);
lean_inc(v_a_5669_);
lean_dec_ref_known(v___x_5667_, 2);
v___x_5670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_5626_, v_a_5633_, v_a_5668_, v___y_5627_, v_a_5669_);
v___y_5637_ = v___x_5670_;
goto v___jp_5636_;
}
else
{
lean_object* v_a_5671_; lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5679_; 
lean_dec(v_a_5633_);
lean_dec_ref(v_b_5626_);
lean_dec(v_a_5625_);
v_a_5671_ = lean_ctor_get(v___x_5667_, 0);
v_a_5672_ = lean_ctor_get(v___x_5667_, 1);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5667_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5674_ = v___x_5667_;
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_inc(v_a_5671_);
lean_dec(v___x_5667_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5677_; 
if (v_isShared_5675_ == 0)
{
v___x_5677_ = v___x_5674_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5671_);
lean_ctor_set(v_reuseFailAlloc_5678_, 1, v_a_5672_);
v___x_5677_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
return v___x_5677_;
}
}
}
}
v___jp_5636_:
{
if (lean_obj_tag(v___y_5637_) == 0)
{
lean_object* v_a_5638_; 
v_a_5638_ = lean_ctor_get(v___y_5637_, 0);
lean_inc(v_a_5638_);
if (lean_obj_tag(v_a_5638_) == 0)
{
lean_object* v_a_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5647_; 
lean_dec(v_a_5625_);
v_a_5639_ = lean_ctor_get(v___y_5637_, 1);
v_isSharedCheck_5647_ = !lean_is_exclusive(v___y_5637_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; 
v_unused_5648_ = lean_ctor_get(v___y_5637_, 0);
lean_dec(v_unused_5648_);
v___x_5641_ = v___y_5637_;
v_isShared_5642_ = v_isSharedCheck_5647_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_a_5639_);
lean_dec(v___y_5637_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5647_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v_a_5643_; lean_object* v___x_5645_; 
v_a_5643_ = lean_ctor_get(v_a_5638_, 0);
lean_inc(v_a_5643_);
lean_dec_ref_known(v_a_5638_, 1);
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 0, v_a_5643_);
v___x_5645_ = v___x_5641_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5646_; 
v_reuseFailAlloc_5646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5646_, 0, v_a_5643_);
lean_ctor_set(v_reuseFailAlloc_5646_, 1, v_a_5639_);
v___x_5645_ = v_reuseFailAlloc_5646_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
return v___x_5645_;
}
}
}
else
{
lean_object* v_a_5649_; lean_object* v_a_5650_; lean_object* v___x_5651_; 
v_a_5649_ = lean_ctor_get(v___y_5637_, 1);
lean_inc(v_a_5649_);
lean_dec_ref_known(v___y_5637_, 2);
v_a_5650_ = lean_ctor_get(v_a_5638_, 0);
lean_inc(v_a_5650_);
lean_dec_ref_known(v_a_5638_, 1);
v___x_5651_ = lean_nat_add(v_a_5625_, v___x_5635_);
lean_dec(v_a_5625_);
v_a_5625_ = v___x_5651_;
v_b_5626_ = v_a_5650_;
v___y_5628_ = v_a_5649_;
goto _start;
}
}
else
{
lean_object* v_a_5653_; lean_object* v_a_5654_; lean_object* v___x_5656_; uint8_t v_isShared_5657_; uint8_t v_isSharedCheck_5661_; 
lean_dec(v_a_5625_);
v_a_5653_ = lean_ctor_get(v___y_5637_, 0);
v_a_5654_ = lean_ctor_get(v___y_5637_, 1);
v_isSharedCheck_5661_ = !lean_is_exclusive(v___y_5637_);
if (v_isSharedCheck_5661_ == 0)
{
v___x_5656_ = v___y_5637_;
v_isShared_5657_ = v_isSharedCheck_5661_;
goto v_resetjp_5655_;
}
else
{
lean_inc(v_a_5654_);
lean_inc(v_a_5653_);
lean_dec(v___y_5637_);
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
}
else
{
lean_object* v_a_5680_; lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
lean_dec_ref(v_b_5626_);
lean_dec(v_a_5625_);
v_a_5680_ = lean_ctor_get(v___x_5632_, 0);
v_a_5681_ = lean_ctor_get(v___x_5632_, 1);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5632_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5632_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_inc(v_a_5680_);
lean_dec(v___x_5632_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5680_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___boxed(lean_object* v_upperBound_5689_, lean_object* v_stxs_5690_, lean_object* v___x_5691_, lean_object* v_a_5692_, lean_object* v_b_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5689_, v_stxs_5690_, v___x_5691_, v_a_5692_, v_b_5693_, v___y_5694_, v___y_5695_);
lean_dec_ref(v___y_5694_);
lean_dec(v___x_5691_);
lean_dec_ref(v_stxs_5690_);
lean_dec(v_upperBound_5689_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(lean_object* v_stxs_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_){
_start:
{
lean_object* v___x_5702_; lean_object* v___x_5703_; uint8_t v___x_5704_; 
v___x_5702_ = lean_array_get_size(v_stxs_5699_);
v___x_5703_ = lean_unsigned_to_nat(1u);
v___x_5704_ = lean_nat_dec_eq(v___x_5702_, v___x_5703_);
if (v___x_5704_ == 0)
{
lean_object* v___x_5705_; lean_object* v_acc_5706_; lean_object* v___x_5707_; 
v___x_5705_ = lean_unsigned_to_nat(0u);
v_acc_5706_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_5707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v___x_5702_, v_stxs_5699_, v___x_5702_, v___x_5705_, v_acc_5706_, v_a_5700_, v_a_5701_);
if (lean_obj_tag(v___x_5707_) == 0)
{
lean_object* v_a_5708_; lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5717_; 
v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
v_a_5709_ = lean_ctor_get(v___x_5707_, 1);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___x_5707_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5711_ = v___x_5707_;
v_isShared_5712_ = v_isSharedCheck_5717_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_inc(v_a_5708_);
lean_dec(v___x_5707_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5717_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5713_; lean_object* v___x_5715_; 
v___x_5713_ = l_Lean_Fmt_TaggedDoc_join(v_a_5708_);
if (v_isShared_5712_ == 0)
{
lean_ctor_set(v___x_5711_, 0, v___x_5713_);
v___x_5715_ = v___x_5711_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5713_);
lean_ctor_set(v_reuseFailAlloc_5716_, 1, v_a_5709_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
}
else
{
lean_object* v_a_5718_; lean_object* v_a_5719_; lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5726_; 
v_a_5718_ = lean_ctor_get(v___x_5707_, 0);
v_a_5719_ = lean_ctor_get(v___x_5707_, 1);
v_isSharedCheck_5726_ = !lean_is_exclusive(v___x_5707_);
if (v_isSharedCheck_5726_ == 0)
{
v___x_5721_ = v___x_5707_;
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
else
{
lean_inc(v_a_5719_);
lean_inc(v_a_5718_);
lean_dec(v___x_5707_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v___x_5724_; 
if (v_isShared_5722_ == 0)
{
v___x_5724_ = v___x_5721_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_a_5718_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v_a_5719_);
v___x_5724_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
return v___x_5724_;
}
}
}
}
else
{
lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; 
v___x_5727_ = lean_box(0);
v___x_5728_ = lean_unsigned_to_nat(0u);
v___x_5729_ = lean_array_get_borrowed(v___x_5727_, v_stxs_5699_, v___x_5728_);
lean_inc(v___x_5729_);
v___x_5730_ = l_Lean_Fmt_fmt(v___x_5729_, v_a_5700_, v_a_5701_);
return v___x_5730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___boxed(lean_object* v_stxs_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_){
_start:
{
lean_object* v_res_5734_; 
v_res_5734_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines(v_stxs_5731_, v_a_5732_, v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec_ref(v_stxs_5731_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(lean_object* v_upperBound_5735_, lean_object* v_stxs_5736_, lean_object* v___x_5737_, lean_object* v_inst_5738_, lean_object* v_R_5739_, lean_object* v_a_5740_, lean_object* v_b_5741_, lean_object* v_c_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_){
_start:
{
lean_object* v___x_5745_; 
v___x_5745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg(v_upperBound_5735_, v_stxs_5736_, v___x_5737_, v_a_5740_, v_b_5741_, v___y_5743_, v___y_5744_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___boxed(lean_object* v_upperBound_5746_, lean_object* v_stxs_5747_, lean_object* v___x_5748_, lean_object* v_inst_5749_, lean_object* v_R_5750_, lean_object* v_a_5751_, lean_object* v_b_5752_, lean_object* v_c_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
lean_object* v_res_5756_; 
v_res_5756_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0(v_upperBound_5746_, v_stxs_5747_, v___x_5748_, v_inst_5749_, v_R_5750_, v_a_5751_, v_b_5752_, v_c_5753_, v___y_5754_, v___y_5755_);
lean_dec_ref(v___y_5754_);
lean_dec(v___x_5748_);
lean_dec_ref(v_stxs_5747_);
lean_dec(v_upperBound_5746_);
return v_res_5756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(lean_object* v_comments_5757_, lean_object* v_out_5758_, lean_object* v_a_5759_){
_start:
{
lean_object* v___x_5760_; uint8_t v___x_5761_; 
v___x_5760_ = lean_array_get_size(v_comments_5757_);
v___x_5761_ = lean_nat_dec_lt(v_a_5759_, v___x_5760_);
if (v___x_5761_ == 0)
{
return v_a_5759_;
}
else
{
lean_object* v___x_5762_; lean_object* v_originalWhitespaceRange_5763_; lean_object* v_stop_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; uint8_t v___x_5767_; 
v___x_5762_ = lean_array_fget_borrowed(v_comments_5757_, v_a_5759_);
v_originalWhitespaceRange_5763_ = lean_ctor_get(v___x_5762_, 1);
v_stop_5764_ = lean_ctor_get(v_originalWhitespaceRange_5763_, 1);
v___x_5765_ = lean_unsigned_to_nat(1u);
v___x_5766_ = lean_nat_add(v_out_5758_, v___x_5765_);
v___x_5767_ = lean_nat_dec_le(v___x_5766_, v_stop_5764_);
lean_dec(v___x_5766_);
if (v___x_5767_ == 0)
{
lean_object* v___x_5768_; 
v___x_5768_ = lean_nat_add(v_a_5759_, v___x_5765_);
lean_dec(v_a_5759_);
v_a_5759_ = v___x_5768_;
goto _start;
}
else
{
return v_a_5759_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg___boxed(lean_object* v_comments_5770_, lean_object* v_out_5771_, lean_object* v_a_5772_){
_start:
{
lean_object* v_res_5773_; 
v_res_5773_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5770_, v_out_5771_, v_a_5772_);
lean_dec(v_out_5771_);
lean_dec_ref(v_comments_5770_);
return v_res_5773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_5774_, lean_object* v_x_5775_){
_start:
{
if (lean_obj_tag(v_x_5775_) == 0)
{
return v_x_5774_;
}
else
{
lean_object* v_key_5776_; lean_object* v_value_5777_; lean_object* v_tail_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5801_; 
v_key_5776_ = lean_ctor_get(v_x_5775_, 0);
v_value_5777_ = lean_ctor_get(v_x_5775_, 1);
v_tail_5778_ = lean_ctor_get(v_x_5775_, 2);
v_isSharedCheck_5801_ = !lean_is_exclusive(v_x_5775_);
if (v_isSharedCheck_5801_ == 0)
{
v___x_5780_ = v_x_5775_;
v_isShared_5781_ = v_isSharedCheck_5801_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_tail_5778_);
lean_inc(v_value_5777_);
lean_inc(v_key_5776_);
lean_dec(v_x_5775_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5801_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5782_; uint64_t v___x_5783_; uint64_t v___x_5784_; uint64_t v___x_5785_; uint64_t v_fold_5786_; uint64_t v___x_5787_; uint64_t v___x_5788_; uint64_t v___x_5789_; size_t v___x_5790_; size_t v___x_5791_; size_t v___x_5792_; size_t v___x_5793_; size_t v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5797_; 
v___x_5782_ = lean_array_get_size(v_x_5774_);
v___x_5783_ = lean_uint64_of_nat(v_key_5776_);
v___x_5784_ = 32ULL;
v___x_5785_ = lean_uint64_shift_right(v___x_5783_, v___x_5784_);
v_fold_5786_ = lean_uint64_xor(v___x_5783_, v___x_5785_);
v___x_5787_ = 16ULL;
v___x_5788_ = lean_uint64_shift_right(v_fold_5786_, v___x_5787_);
v___x_5789_ = lean_uint64_xor(v_fold_5786_, v___x_5788_);
v___x_5790_ = lean_uint64_to_usize(v___x_5789_);
v___x_5791_ = lean_usize_of_nat(v___x_5782_);
v___x_5792_ = ((size_t)1ULL);
v___x_5793_ = lean_usize_sub(v___x_5791_, v___x_5792_);
v___x_5794_ = lean_usize_land(v___x_5790_, v___x_5793_);
v___x_5795_ = lean_array_uget_borrowed(v_x_5774_, v___x_5794_);
lean_inc(v___x_5795_);
if (v_isShared_5781_ == 0)
{
lean_ctor_set(v___x_5780_, 2, v___x_5795_);
v___x_5797_ = v___x_5780_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5800_; 
v_reuseFailAlloc_5800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5800_, 0, v_key_5776_);
lean_ctor_set(v_reuseFailAlloc_5800_, 1, v_value_5777_);
lean_ctor_set(v_reuseFailAlloc_5800_, 2, v___x_5795_);
v___x_5797_ = v_reuseFailAlloc_5800_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
lean_object* v___x_5798_; 
v___x_5798_ = lean_array_uset(v_x_5774_, v___x_5794_, v___x_5797_);
v_x_5774_ = v___x_5798_;
v_x_5775_ = v_tail_5778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(lean_object* v_i_5802_, lean_object* v_source_5803_, lean_object* v_target_5804_){
_start:
{
lean_object* v___x_5805_; uint8_t v___x_5806_; 
v___x_5805_ = lean_array_get_size(v_source_5803_);
v___x_5806_ = lean_nat_dec_lt(v_i_5802_, v___x_5805_);
if (v___x_5806_ == 0)
{
lean_dec_ref(v_source_5803_);
lean_dec(v_i_5802_);
return v_target_5804_;
}
else
{
lean_object* v_es_5807_; lean_object* v___x_5808_; lean_object* v_source_5809_; lean_object* v_target_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v_es_5807_ = lean_array_fget(v_source_5803_, v_i_5802_);
v___x_5808_ = lean_box(0);
v_source_5809_ = lean_array_fset(v_source_5803_, v_i_5802_, v___x_5808_);
v_target_5810_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_target_5804_, v_es_5807_);
v___x_5811_ = lean_unsigned_to_nat(1u);
v___x_5812_ = lean_nat_add(v_i_5802_, v___x_5811_);
lean_dec(v_i_5802_);
v_i_5802_ = v___x_5812_;
v_source_5803_ = v_source_5809_;
v_target_5804_ = v_target_5810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(lean_object* v_data_5814_){
_start:
{
lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v_nbuckets_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5815_ = lean_array_get_size(v_data_5814_);
v___x_5816_ = lean_unsigned_to_nat(2u);
v_nbuckets_5817_ = lean_nat_mul(v___x_5815_, v___x_5816_);
v___x_5818_ = lean_unsigned_to_nat(0u);
v___x_5819_ = lean_box(0);
v___x_5820_ = lean_mk_array(v_nbuckets_5817_, v___x_5819_);
v___x_5821_ = lean_array_propagate_mark(v_data_5814_, v___x_5820_);
v___x_5822_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v___x_5818_, v_data_5814_, v___x_5821_);
return v___x_5822_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(lean_object* v_a_5823_, lean_object* v_x_5824_){
_start:
{
if (lean_obj_tag(v_x_5824_) == 0)
{
uint8_t v___x_5825_; 
v___x_5825_ = 0;
return v___x_5825_;
}
else
{
lean_object* v_key_5826_; lean_object* v_tail_5827_; uint8_t v___x_5828_; 
v_key_5826_ = lean_ctor_get(v_x_5824_, 0);
v_tail_5827_ = lean_ctor_get(v_x_5824_, 2);
v___x_5828_ = lean_nat_dec_eq(v_key_5826_, v_a_5823_);
if (v___x_5828_ == 0)
{
v_x_5824_ = v_tail_5827_;
goto _start;
}
else
{
return v___x_5828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg___boxed(lean_object* v_a_5830_, lean_object* v_x_5831_){
_start:
{
uint8_t v_res_5832_; lean_object* v_r_5833_; 
v_res_5832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5830_, v_x_5831_);
lean_dec(v_x_5831_);
lean_dec(v_a_5830_);
v_r_5833_ = lean_box(v_res_5832_);
return v_r_5833_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(lean_object* v_x_5836_){
_start:
{
if (lean_obj_tag(v_x_5836_) == 0)
{
lean_object* v___x_5837_; 
v___x_5837_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0___closed__0));
return v___x_5837_;
}
else
{
lean_object* v_val_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5847_; 
v_val_5838_ = lean_ctor_get(v_x_5836_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v_x_5836_);
if (v_isSharedCheck_5847_ == 0)
{
v___x_5840_ = v_x_5836_;
v_isShared_5841_ = v_isSharedCheck_5847_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_val_5838_);
lean_dec(v_x_5836_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5847_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5845_; 
v___x_5842_ = lean_unsigned_to_nat(1u);
v___x_5843_ = lean_nat_add(v_val_5838_, v___x_5842_);
lean_dec(v_val_5838_);
if (v_isShared_5841_ == 0)
{
lean_ctor_set(v___x_5840_, 0, v___x_5843_);
v___x_5845_ = v___x_5840_;
goto v_reusejp_5844_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5843_);
v___x_5845_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5844_;
}
v_reusejp_5844_:
{
return v___x_5845_;
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5848_ = lean_box(0);
v___x_5849_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5848_);
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(lean_object* v_a_5850_, lean_object* v_x_5851_){
_start:
{
if (lean_obj_tag(v_x_5851_) == 0)
{
lean_object* v___x_5852_; lean_object* v_val_5853_; lean_object* v___x_5854_; 
v___x_5852_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0, &l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___closed__0);
v_val_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_val_5853_);
v___x_5854_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5854_, 0, v_a_5850_);
lean_ctor_set(v___x_5854_, 1, v_val_5853_);
lean_ctor_set(v___x_5854_, 2, v_x_5851_);
return v___x_5854_;
}
else
{
lean_object* v_key_5855_; lean_object* v_value_5856_; lean_object* v_tail_5857_; lean_object* v___x_5859_; uint8_t v_isShared_5860_; uint8_t v_isSharedCheck_5872_; 
v_key_5855_ = lean_ctor_get(v_x_5851_, 0);
v_value_5856_ = lean_ctor_get(v_x_5851_, 1);
v_tail_5857_ = lean_ctor_get(v_x_5851_, 2);
v_isSharedCheck_5872_ = !lean_is_exclusive(v_x_5851_);
if (v_isSharedCheck_5872_ == 0)
{
v___x_5859_ = v_x_5851_;
v_isShared_5860_ = v_isSharedCheck_5872_;
goto v_resetjp_5858_;
}
else
{
lean_inc(v_tail_5857_);
lean_inc(v_value_5856_);
lean_inc(v_key_5855_);
lean_dec(v_x_5851_);
v___x_5859_ = lean_box(0);
v_isShared_5860_ = v_isSharedCheck_5872_;
goto v_resetjp_5858_;
}
v_resetjp_5858_:
{
uint8_t v___x_5861_; 
v___x_5861_ = lean_nat_dec_eq(v_key_5855_, v_a_5850_);
if (v___x_5861_ == 0)
{
lean_object* v_tail_5862_; lean_object* v___x_5864_; 
v_tail_5862_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5850_, v_tail_5857_);
if (v_isShared_5860_ == 0)
{
lean_ctor_set(v___x_5859_, 2, v_tail_5862_);
v___x_5864_ = v___x_5859_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_key_5855_);
lean_ctor_set(v_reuseFailAlloc_5865_, 1, v_value_5856_);
lean_ctor_set(v_reuseFailAlloc_5865_, 2, v_tail_5862_);
v___x_5864_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
return v___x_5864_;
}
}
else
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v_val_5868_; lean_object* v___x_5870_; 
lean_dec(v_key_5855_);
v___x_5866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5866_, 0, v_value_5856_);
v___x_5867_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3___lam__0(v___x_5866_);
v_val_5868_ = lean_ctor_get(v___x_5867_, 0);
lean_inc(v_val_5868_);
lean_dec(v___x_5867_);
if (v_isShared_5860_ == 0)
{
lean_ctor_set(v___x_5859_, 1, v_val_5868_);
lean_ctor_set(v___x_5859_, 0, v_a_5850_);
v___x_5870_ = v___x_5859_;
goto v_reusejp_5869_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v_a_5850_);
lean_ctor_set(v_reuseFailAlloc_5871_, 1, v_val_5868_);
lean_ctor_set(v_reuseFailAlloc_5871_, 2, v_tail_5857_);
v___x_5870_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5869_;
}
v_reusejp_5869_:
{
return v___x_5870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(lean_object* v_m_5873_, lean_object* v_a_5874_){
_start:
{
lean_object* v_size_5875_; lean_object* v_buckets_5876_; lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5924_; 
v_size_5875_ = lean_ctor_get(v_m_5873_, 0);
v_buckets_5876_ = lean_ctor_get(v_m_5873_, 1);
v_isSharedCheck_5924_ = !lean_is_exclusive(v_m_5873_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5878_ = v_m_5873_;
v_isShared_5879_ = v_isSharedCheck_5924_;
goto v_resetjp_5877_;
}
else
{
lean_inc(v_buckets_5876_);
lean_inc(v_size_5875_);
lean_dec(v_m_5873_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5924_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v___x_5880_; uint64_t v___x_5881_; uint64_t v___x_5882_; uint64_t v___x_5883_; uint64_t v_fold_5884_; uint64_t v___x_5885_; uint64_t v___x_5886_; uint64_t v___x_5887_; size_t v___x_5888_; size_t v___x_5889_; size_t v___x_5890_; size_t v___x_5891_; size_t v___x_5892_; lean_object* v_bkt_5893_; uint8_t v___x_5894_; 
v___x_5880_ = lean_array_get_size(v_buckets_5876_);
v___x_5881_ = lean_uint64_of_nat(v_a_5874_);
v___x_5882_ = 32ULL;
v___x_5883_ = lean_uint64_shift_right(v___x_5881_, v___x_5882_);
v_fold_5884_ = lean_uint64_xor(v___x_5881_, v___x_5883_);
v___x_5885_ = 16ULL;
v___x_5886_ = lean_uint64_shift_right(v_fold_5884_, v___x_5885_);
v___x_5887_ = lean_uint64_xor(v_fold_5884_, v___x_5886_);
v___x_5888_ = lean_uint64_to_usize(v___x_5887_);
v___x_5889_ = lean_usize_of_nat(v___x_5880_);
v___x_5890_ = ((size_t)1ULL);
v___x_5891_ = lean_usize_sub(v___x_5889_, v___x_5890_);
v___x_5892_ = lean_usize_land(v___x_5888_, v___x_5891_);
v_bkt_5893_ = lean_array_uget_borrowed(v_buckets_5876_, v___x_5892_);
v___x_5894_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5874_, v_bkt_5893_);
if (v___x_5894_ == 0)
{
lean_object* v___x_5895_; lean_object* v_size_x27_5896_; lean_object* v___x_5897_; lean_object* v_buckets_x27_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; uint8_t v___x_5904_; 
v___x_5895_ = lean_unsigned_to_nat(1u);
v_size_x27_5896_ = lean_nat_add(v_size_5875_, v___x_5895_);
lean_dec(v_size_5875_);
lean_inc(v_bkt_5893_);
v___x_5897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5897_, 0, v_a_5874_);
lean_ctor_set(v___x_5897_, 1, v___x_5895_);
lean_ctor_set(v___x_5897_, 2, v_bkt_5893_);
v_buckets_x27_5898_ = lean_array_uset(v_buckets_5876_, v___x_5892_, v___x_5897_);
v___x_5899_ = lean_unsigned_to_nat(4u);
v___x_5900_ = lean_nat_mul(v_size_x27_5896_, v___x_5899_);
v___x_5901_ = lean_unsigned_to_nat(3u);
v___x_5902_ = lean_nat_div(v___x_5900_, v___x_5901_);
lean_dec(v___x_5900_);
v___x_5903_ = lean_array_get_size(v_buckets_x27_5898_);
v___x_5904_ = lean_nat_dec_le(v___x_5902_, v___x_5903_);
lean_dec(v___x_5902_);
if (v___x_5904_ == 0)
{
lean_object* v_val_5905_; lean_object* v___x_5907_; 
v_val_5905_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_buckets_x27_5898_);
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 1, v_val_5905_);
lean_ctor_set(v___x_5878_, 0, v_size_x27_5896_);
v___x_5907_ = v___x_5878_;
goto v_reusejp_5906_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_size_x27_5896_);
lean_ctor_set(v_reuseFailAlloc_5908_, 1, v_val_5905_);
v___x_5907_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5906_;
}
v_reusejp_5906_:
{
return v___x_5907_;
}
}
else
{
lean_object* v___x_5910_; 
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 1, v_buckets_x27_5898_);
lean_ctor_set(v___x_5878_, 0, v_size_x27_5896_);
v___x_5910_ = v___x_5878_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_size_x27_5896_);
lean_ctor_set(v_reuseFailAlloc_5911_, 1, v_buckets_x27_5898_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
else
{
lean_object* v___x_5912_; lean_object* v_buckets_x27_5913_; lean_object* v_bkt_x27_5914_; lean_object* v___y_5916_; uint8_t v___x_5921_; 
lean_inc(v_bkt_5893_);
v___x_5912_ = lean_box(0);
v_buckets_x27_5913_ = lean_array_uset(v_buckets_5876_, v___x_5892_, v___x_5912_);
lean_inc(v_a_5874_);
v_bkt_x27_5914_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__3(v_a_5874_, v_bkt_5893_);
v___x_5921_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_5874_, v_bkt_x27_5914_);
lean_dec(v_a_5874_);
if (v___x_5921_ == 0)
{
lean_object* v___x_5922_; lean_object* v___x_5923_; 
v___x_5922_ = lean_unsigned_to_nat(1u);
v___x_5923_ = lean_nat_sub(v_size_5875_, v___x_5922_);
lean_dec(v_size_5875_);
v___y_5916_ = v___x_5923_;
goto v___jp_5915_;
}
else
{
v___y_5916_ = v_size_5875_;
goto v___jp_5915_;
}
v___jp_5915_:
{
lean_object* v___x_5917_; lean_object* v___x_5919_; 
v___x_5917_ = lean_array_uset(v_buckets_x27_5913_, v___x_5892_, v_bkt_x27_5914_);
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 1, v___x_5917_);
lean_ctor_set(v___x_5878_, 0, v___y_5916_);
v___x_5919_ = v___x_5878_;
goto v_reusejp_5918_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v___y_5916_);
lean_ctor_set(v_reuseFailAlloc_5920_, 1, v___x_5917_);
v___x_5919_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5918_;
}
v_reusejp_5918_:
{
return v___x_5919_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(lean_object* v_fst_5925_, lean_object* v___x_5926_, lean_object* v_____r_5927_){
_start:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; 
lean_inc(v___x_5926_);
v___x_5928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1(v_fst_5925_, v___x_5926_);
v___x_5929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5928_);
lean_ctor_set(v___x_5929_, 1, v___x_5926_);
v___x_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5929_);
return v___x_5930_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(lean_object* v_comments_5931_, lean_object* v_whitespace_5932_, lean_object* v_a_5933_, lean_object* v_b_5934_){
_start:
{
lean_object* v_str_5935_; lean_object* v_startInclusive_5936_; lean_object* v_endExclusive_5937_; lean_object* v___x_5938_; uint8_t v_decide_5939_; 
v_str_5935_ = lean_ctor_get(v_whitespace_5932_, 0);
v_startInclusive_5936_ = lean_ctor_get(v_whitespace_5932_, 1);
v_endExclusive_5937_ = lean_ctor_get(v_whitespace_5932_, 2);
v___x_5938_ = lean_nat_sub(v_endExclusive_5937_, v_startInclusive_5936_);
v_decide_5939_ = lean_nat_dec_eq(v_a_5933_, v___x_5938_);
lean_dec(v___x_5938_);
if (v_decide_5939_ == 0)
{
uint32_t v___x_5940_; lean_object* v___x_5941_; uint32_t v___x_5942_; uint8_t v___x_5943_; 
v___x_5940_ = 10;
v___x_5941_ = lean_nat_add(v_startInclusive_5936_, v_a_5933_);
v___x_5942_ = lean_string_utf8_get_fast(v_str_5935_, v___x_5941_);
v___x_5943_ = lean_uint32_dec_eq(v___x_5942_, v___x_5940_);
if (v___x_5943_ == 0)
{
lean_object* v___x_5944_; lean_object* v___x_5945_; 
lean_dec(v_a_5933_);
v___x_5944_ = lean_string_utf8_next_fast(v_str_5935_, v___x_5941_);
lean_dec(v___x_5941_);
v___x_5945_ = lean_nat_sub(v___x_5944_, v_startInclusive_5936_);
v_a_5933_ = v___x_5945_;
goto _start;
}
else
{
lean_object* v_fst_5947_; lean_object* v_snd_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5974_; 
v_fst_5947_ = lean_ctor_get(v_b_5934_, 0);
v_snd_5948_ = lean_ctor_get(v_b_5934_, 1);
v_isSharedCheck_5974_ = !lean_is_exclusive(v_b_5934_);
if (v_isSharedCheck_5974_ == 0)
{
v___x_5950_ = v_b_5934_;
v_isShared_5951_ = v_isSharedCheck_5974_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_snd_5948_);
lean_inc(v_fst_5947_);
lean_dec(v_b_5934_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5974_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v_val_5956_; lean_object* v___x_5960_; lean_object* v___x_5961_; uint8_t v___x_5962_; 
v___x_5952_ = lean_string_utf8_next_fast(v_str_5935_, v___x_5941_);
v___x_5953_ = lean_nat_sub(v___x_5952_, v___x_5941_);
v___x_5954_ = lean_nat_add(v_a_5933_, v___x_5953_);
lean_dec(v___x_5953_);
lean_dec(v_a_5933_);
v___x_5960_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5931_, v___x_5941_, v_snd_5948_);
v___x_5961_ = lean_array_get_size(v_comments_5931_);
v___x_5962_ = lean_nat_dec_lt(v___x_5960_, v___x_5961_);
if (v___x_5962_ == 0)
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
lean_del_object(v___x_5950_);
lean_dec(v___x_5941_);
v___x_5963_ = lean_box(0);
v___x_5964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5947_, v___x_5960_, v___x_5963_);
v_val_5956_ = v___x_5964_;
goto v___jp_5955_;
}
else
{
lean_object* v___x_5965_; lean_object* v_originalWhitespaceRange_5966_; uint8_t v___x_5967_; 
v___x_5965_ = lean_array_fget_borrowed(v_comments_5931_, v___x_5960_);
v_originalWhitespaceRange_5966_ = lean_ctor_get(v___x_5965_, 1);
v___x_5967_ = l_Lean_Syntax_Range_contains(v_originalWhitespaceRange_5966_, v___x_5941_, v_decide_5939_);
lean_dec(v___x_5941_);
if (v___x_5967_ == 0)
{
lean_object* v___x_5968_; lean_object* v___x_5969_; 
lean_del_object(v___x_5950_);
v___x_5968_ = lean_box(0);
v___x_5969_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___lam__0(v_fst_5947_, v___x_5960_, v___x_5968_);
v_val_5956_ = v___x_5969_;
goto v___jp_5955_;
}
else
{
lean_object* v___x_5971_; 
if (v_isShared_5951_ == 0)
{
lean_ctor_set(v___x_5950_, 1, v___x_5960_);
v___x_5971_ = v___x_5950_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_fst_5947_);
lean_ctor_set(v_reuseFailAlloc_5973_, 1, v___x_5960_);
v___x_5971_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
v_a_5933_ = v___x_5954_;
v_b_5934_ = v___x_5971_;
goto _start;
}
}
}
v___jp_5955_:
{
if (lean_obj_tag(v_val_5956_) == 0)
{
lean_object* v_a_5957_; 
lean_dec(v___x_5954_);
v_a_5957_ = lean_ctor_get(v_val_5956_, 0);
lean_inc(v_a_5957_);
lean_dec_ref_known(v_val_5956_, 1);
return v_a_5957_;
}
else
{
lean_object* v_a_5958_; 
v_a_5958_ = lean_ctor_get(v_val_5956_, 0);
lean_inc(v_a_5958_);
lean_dec_ref_known(v_val_5956_, 1);
v_a_5933_ = v___x_5954_;
v_b_5934_ = v_a_5958_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_5933_);
return v_b_5934_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg___boxed(lean_object* v_comments_5975_, lean_object* v_whitespace_5976_, lean_object* v_a_5977_, lean_object* v_b_5978_){
_start:
{
lean_object* v_res_5979_; 
v_res_5979_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5975_, v_whitespace_5976_, v_a_5977_, v_b_5978_);
lean_dec_ref(v_whitespace_5976_);
lean_dec_ref(v_comments_5975_);
return v_res_5979_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0(void){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; 
v___x_5980_ = lean_box(0);
v___x_5981_ = lean_unsigned_to_nat(16u);
v___x_5982_ = lean_mk_array(v___x_5981_, v___x_5980_);
return v___x_5982_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1(void){
_start:
{
lean_object* v___x_5983_; lean_object* v_newlinePositions_5984_; lean_object* v_newlinesBeforeComment_5985_; 
v___x_5983_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__0);
v_newlinePositions_5984_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_newlinesBeforeComment_5985_, 0, v_newlinePositions_5984_);
lean_ctor_set(v_newlinesBeforeComment_5985_, 1, v___x_5983_);
return v_newlinesBeforeComment_5985_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2(void){
_start:
{
lean_object* v_newlinePositions_5986_; lean_object* v_newlinesBeforeComment_5987_; lean_object* v___x_5988_; 
v_newlinePositions_5986_ = lean_unsigned_to_nat(0u);
v_newlinesBeforeComment_5987_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__1);
v___x_5988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5988_, 0, v_newlinesBeforeComment_5987_);
lean_ctor_set(v___x_5988_, 1, v_newlinePositions_5986_);
return v___x_5988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(lean_object* v_comments_5989_, lean_object* v_whitespace_5990_){
_start:
{
lean_object* v_newlinePositions_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v_fst_5994_; 
v_newlinePositions_5991_ = lean_unsigned_to_nat(0u);
v___x_5992_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2, &l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2_once, _init_l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___closed__2);
v___x_5993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_5989_, v_whitespace_5990_, v_newlinePositions_5991_, v___x_5992_);
v_fst_5994_ = lean_ctor_get(v___x_5993_, 0);
lean_inc(v_fst_5994_);
lean_dec_ref(v___x_5993_);
return v_fst_5994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments___boxed(lean_object* v_comments_5995_, lean_object* v_whitespace_5996_){
_start:
{
lean_object* v_res_5997_; 
v_res_5997_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v_comments_5995_, v_whitespace_5996_);
lean_dec_ref(v_whitespace_5996_);
lean_dec_ref(v_comments_5995_);
return v_res_5997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(lean_object* v_comments_5998_, lean_object* v_out_5999_, lean_object* v_inst_6000_, lean_object* v_a_6001_){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___redArg(v_comments_5998_, v_out_5999_, v_a_6001_);
return v___x_6002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0___boxed(lean_object* v_comments_6003_, lean_object* v_out_6004_, lean_object* v_inst_6005_, lean_object* v_a_6006_){
_start:
{
lean_object* v_res_6007_; 
v_res_6007_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__0(v_comments_6003_, v_out_6004_, v_inst_6005_, v_a_6006_);
lean_dec(v_out_6004_);
lean_dec_ref(v_comments_6003_);
return v_res_6007_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(lean_object* v_comments_6008_, lean_object* v_whitespace_6009_, lean_object* v_inst_6010_, lean_object* v_R_6011_, lean_object* v_a_6012_, lean_object* v_b_6013_, lean_object* v_c_6014_){
_start:
{
lean_object* v___x_6015_; 
v___x_6015_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___redArg(v_comments_6008_, v_whitespace_6009_, v_a_6012_, v_b_6013_);
return v___x_6015_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2___boxed(lean_object* v_comments_6016_, lean_object* v_whitespace_6017_, lean_object* v_inst_6018_, lean_object* v_R_6019_, lean_object* v_a_6020_, lean_object* v_b_6021_, lean_object* v_c_6022_){
_start:
{
lean_object* v_res_6023_; 
v_res_6023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__2(v_comments_6016_, v_whitespace_6017_, v_inst_6018_, v_R_6019_, v_a_6020_, v_b_6021_, v_c_6022_);
lean_dec_ref(v_whitespace_6017_);
lean_dec_ref(v_comments_6016_);
return v_res_6023_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(lean_object* v_00_u03b2_6024_, lean_object* v_a_6025_, lean_object* v_x_6026_){
_start:
{
uint8_t v___x_6027_; 
v___x_6027_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___redArg(v_a_6025_, v_x_6026_);
return v___x_6027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6028_, lean_object* v_a_6029_, lean_object* v_x_6030_){
_start:
{
uint8_t v_res_6031_; lean_object* v_r_6032_; 
v_res_6031_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__1(v_00_u03b2_6028_, v_a_6029_, v_x_6030_);
lean_dec(v_x_6030_);
lean_dec(v_a_6029_);
v_r_6032_ = lean_box(v_res_6031_);
return v_r_6032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2(lean_object* v_00_u03b2_6033_, lean_object* v_data_6034_){
_start:
{
lean_object* v___x_6035_; 
v___x_6035_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2___redArg(v_data_6034_);
return v___x_6035_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_6036_, lean_object* v_i_6037_, lean_object* v_source_6038_, lean_object* v_target_6039_){
_start:
{
lean_object* v___x_6040_; 
v___x_6040_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3___redArg(v_i_6037_, v_source_6038_, v_target_6039_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_6041_, lean_object* v_x_6042_, lean_object* v_x_6043_){
_start:
{
lean_object* v___x_6044_; 
v___x_6044_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments_spec__1_spec__2_spec__3_spec__5___redArg(v_x_6042_, v_x_6043_);
return v___x_6044_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg(){
_start:
{
lean_object* v___x_6048_; 
v___x_6048_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___closed__0));
return v___x_6048_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg___boxed(lean_object* v___dummy_6049_){
_start:
{
lean_object* v_res_6050_; 
v_res_6050_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v_res_6050_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_6051_; 
v___x_6051_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___redArg();
return v___x_6051_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(lean_object* v_s_6052_){
_start:
{
lean_object* v___x_6053_; 
v___x_6053_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
return v___x_6053_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___boxed(lean_object* v_s_6054_){
_start:
{
lean_object* v_res_6055_; 
v_res_6055_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0(v_s_6054_);
lean_dec_ref(v_s_6054_);
return v_res_6055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(size_t v_sz_6056_, size_t v_i_6057_, lean_object* v_bs_6058_){
_start:
{
uint8_t v___x_6059_; 
v___x_6059_ = lean_usize_dec_lt(v_i_6057_, v_sz_6056_);
if (v___x_6059_ == 0)
{
return v_bs_6058_;
}
else
{
lean_object* v_v_6060_; lean_object* v_rendered_6061_; lean_object* v___x_6062_; lean_object* v_bs_x27_6063_; size_t v___x_6064_; size_t v___x_6065_; lean_object* v___x_6066_; 
v_v_6060_ = lean_array_uget_borrowed(v_bs_6058_, v_i_6057_);
v_rendered_6061_ = lean_ctor_get(v_v_6060_, 0);
lean_inc_ref(v_rendered_6061_);
v___x_6062_ = lean_unsigned_to_nat(0u);
v_bs_x27_6063_ = lean_array_uset(v_bs_6058_, v_i_6057_, v___x_6062_);
v___x_6064_ = ((size_t)1ULL);
v___x_6065_ = lean_usize_add(v_i_6057_, v___x_6064_);
v___x_6066_ = lean_array_uset(v_bs_x27_6063_, v_i_6057_, v_rendered_6061_);
v_i_6057_ = v___x_6065_;
v_bs_6058_ = v___x_6066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2___boxed(lean_object* v_sz_6068_, lean_object* v_i_6069_, lean_object* v_bs_6070_){
_start:
{
size_t v_sz_boxed_6071_; size_t v_i_boxed_6072_; lean_object* v_res_6073_; 
v_sz_boxed_6071_ = lean_unbox_usize(v_sz_6068_);
lean_dec(v_sz_6068_);
v_i_boxed_6072_ = lean_unbox_usize(v_i_6069_);
lean_dec(v_i_6069_);
v_res_6073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_boxed_6071_, v_i_boxed_6072_, v_bs_6070_);
return v_res_6073_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6074_ = lean_box(0);
v___x_6075_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6075_);
lean_ctor_set(v___x_6076_, 1, v___x_6074_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(lean_object* v_upperBound_6077_, lean_object* v_next_6078_, lean_object* v_upperBound_6079_, lean_object* v_a_6080_, lean_object* v_b_6081_){
_start:
{
uint8_t v___x_6082_; 
v___x_6082_ = lean_nat_dec_lt(v_a_6080_, v_upperBound_6077_);
if (v___x_6082_ == 0)
{
lean_dec(v_a_6080_);
return v_b_6081_;
}
else
{
lean_object* v_fst_6083_; lean_object* v___x_6085_; uint8_t v_isShared_6086_; uint8_t v_isSharedCheck_6097_; 
v_fst_6083_ = lean_ctor_get(v_b_6081_, 0);
v_isSharedCheck_6097_ = !lean_is_exclusive(v_b_6081_);
if (v_isSharedCheck_6097_ == 0)
{
lean_object* v_unused_6098_; 
v_unused_6098_ = lean_ctor_get(v_b_6081_, 1);
lean_dec(v_unused_6098_);
v___x_6085_ = v_b_6081_;
v_isShared_6086_ = v_isSharedCheck_6097_;
goto v_resetjp_6084_;
}
else
{
lean_inc(v_fst_6083_);
lean_dec(v_b_6081_);
v___x_6085_ = lean_box(0);
v_isShared_6086_ = v_isSharedCheck_6097_;
goto v_resetjp_6084_;
}
v_resetjp_6084_:
{
uint8_t v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6092_; 
v___x_6087_ = lean_nat_dec_lt(v_next_6078_, v_upperBound_6079_);
v___x_6088_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6089_ = lean_array_push(v_fst_6083_, v___x_6088_);
v___x_6090_ = lean_box(v___x_6087_);
if (v_isShared_6086_ == 0)
{
lean_ctor_set(v___x_6085_, 1, v___x_6090_);
lean_ctor_set(v___x_6085_, 0, v___x_6089_);
v___x_6092_ = v___x_6085_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6096_; 
v_reuseFailAlloc_6096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6096_, 0, v___x_6089_);
lean_ctor_set(v_reuseFailAlloc_6096_, 1, v___x_6090_);
v___x_6092_ = v_reuseFailAlloc_6096_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
lean_object* v___x_6093_; lean_object* v___x_6094_; 
v___x_6093_ = lean_unsigned_to_nat(1u);
v___x_6094_ = lean_nat_add(v_a_6080_, v___x_6093_);
lean_dec(v_a_6080_);
v_a_6080_ = v___x_6094_;
v_b_6081_ = v___x_6092_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___boxed(lean_object* v_upperBound_6099_, lean_object* v_next_6100_, lean_object* v_upperBound_6101_, lean_object* v_a_6102_, lean_object* v_b_6103_){
_start:
{
lean_object* v_res_6104_; 
v_res_6104_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6099_, v_next_6100_, v_upperBound_6101_, v_a_6102_, v_b_6103_);
lean_dec(v_upperBound_6101_);
lean_dec(v_next_6100_);
lean_dec(v_upperBound_6099_);
return v_res_6104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(lean_object* v___x_6105_, lean_object* v_fst_6106_, lean_object* v_____r_6107_, uint8_t v_insertedAnyNewlines_6108_, lean_object* v_d_6109_){
_start:
{
lean_object* v_originalWhitespaceRange_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; 
v_originalWhitespaceRange_6110_ = lean_ctor_get(v___x_6105_, 1);
lean_inc_ref(v_originalWhitespaceRange_6110_);
v___x_6111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6111_, 0, v_originalWhitespaceRange_6110_);
v___x_6112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6112_, 0, v_d_6109_);
lean_ctor_set(v___x_6112_, 1, v___x_6111_);
v___x_6113_ = lean_array_push(v_fst_6106_, v___x_6112_);
v___x_6114_ = lean_box(v_insertedAnyNewlines_6108_);
v___x_6115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6113_);
lean_ctor_set(v___x_6115_, 1, v___x_6114_);
v___x_6116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
return v___x_6116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed(lean_object* v___x_6117_, lean_object* v_fst_6118_, lean_object* v_____r_6119_, lean_object* v_insertedAnyNewlines_6120_, lean_object* v_d_6121_){
_start:
{
uint8_t v_insertedAnyNewlines_boxed_6122_; lean_object* v_res_6123_; 
v_insertedAnyNewlines_boxed_6122_ = lean_unbox(v_insertedAnyNewlines_6120_);
v_res_6123_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v___x_6117_, v_fst_6118_, v_____r_6119_, v_insertedAnyNewlines_boxed_6122_, v_d_6121_);
lean_dec_ref(v___x_6117_);
return v_res_6123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(lean_object* v_a_6124_, lean_object* v___x_6125_, lean_object* v___x_6126_, lean_object* v_a_6127_, lean_object* v_b_6128_){
_start:
{
lean_object* v_it_6130_; lean_object* v_startInclusive_6131_; lean_object* v_endExclusive_6132_; 
if (lean_obj_tag(v_a_6127_) == 0)
{
lean_object* v_currPos_6138_; lean_object* v_searcher_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6162_; 
v_currPos_6138_ = lean_ctor_get(v_a_6127_, 0);
v_searcher_6139_ = lean_ctor_get(v_a_6127_, 1);
v_isSharedCheck_6162_ = !lean_is_exclusive(v_a_6127_);
if (v_isSharedCheck_6162_ == 0)
{
v___x_6141_ = v_a_6127_;
v_isShared_6142_ = v_isSharedCheck_6162_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_searcher_6139_);
lean_inc(v_currPos_6138_);
lean_dec(v_a_6127_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6162_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
uint8_t v_decide_6143_; 
v_decide_6143_ = lean_nat_dec_eq(v_searcher_6139_, v___x_6126_);
if (v_decide_6143_ == 0)
{
uint32_t v___x_6144_; uint32_t v___x_6145_; uint8_t v___x_6146_; 
v___x_6144_ = 10;
v___x_6145_ = lean_string_utf8_get_fast(v_a_6124_, v_searcher_6139_);
v___x_6146_ = lean_uint32_dec_eq(v___x_6145_, v___x_6144_);
if (v___x_6146_ == 0)
{
lean_object* v___x_6147_; lean_object* v___x_6149_; 
v___x_6147_ = lean_string_utf8_next_fast(v_a_6124_, v_searcher_6139_);
lean_dec(v_searcher_6139_);
if (v_isShared_6142_ == 0)
{
lean_ctor_set(v___x_6141_, 1, v___x_6147_);
v___x_6149_ = v___x_6141_;
goto v_reusejp_6148_;
}
else
{
lean_object* v_reuseFailAlloc_6151_; 
v_reuseFailAlloc_6151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6151_, 0, v_currPos_6138_);
lean_ctor_set(v_reuseFailAlloc_6151_, 1, v___x_6147_);
v___x_6149_ = v_reuseFailAlloc_6151_;
goto v_reusejp_6148_;
}
v_reusejp_6148_:
{
v_a_6127_ = v___x_6149_;
goto _start;
}
}
else
{
lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v_slice_6155_; lean_object* v_nextIt_6157_; 
v___x_6152_ = lean_string_utf8_next_fast(v_a_6124_, v_searcher_6139_);
v___x_6153_ = lean_nat_sub(v___x_6152_, v_searcher_6139_);
v___x_6154_ = lean_nat_add(v_searcher_6139_, v___x_6153_);
lean_dec(v___x_6153_);
v_slice_6155_ = l_String_Slice_subslice_x21(v___x_6125_, v_currPos_6138_, v_searcher_6139_);
lean_inc(v___x_6154_);
if (v_isShared_6142_ == 0)
{
lean_ctor_set(v___x_6141_, 1, v___x_6154_);
lean_ctor_set(v___x_6141_, 0, v___x_6154_);
v_nextIt_6157_ = v___x_6141_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6160_; 
v_reuseFailAlloc_6160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6160_, 0, v___x_6154_);
lean_ctor_set(v_reuseFailAlloc_6160_, 1, v___x_6154_);
v_nextIt_6157_ = v_reuseFailAlloc_6160_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
lean_object* v_startInclusive_6158_; lean_object* v_endExclusive_6159_; 
v_startInclusive_6158_ = lean_ctor_get(v_slice_6155_, 0);
lean_inc(v_startInclusive_6158_);
v_endExclusive_6159_ = lean_ctor_get(v_slice_6155_, 1);
lean_inc(v_endExclusive_6159_);
lean_dec_ref(v_slice_6155_);
v_it_6130_ = v_nextIt_6157_;
v_startInclusive_6131_ = v_startInclusive_6158_;
v_endExclusive_6132_ = v_endExclusive_6159_;
goto v___jp_6129_;
}
}
}
else
{
lean_object* v___x_6161_; 
lean_del_object(v___x_6141_);
lean_dec(v_searcher_6139_);
v___x_6161_ = lean_box(1);
lean_inc(v___x_6126_);
v_it_6130_ = v___x_6161_;
v_startInclusive_6131_ = v_currPos_6138_;
v_endExclusive_6132_ = v___x_6126_;
goto v___jp_6129_;
}
}
}
else
{
lean_dec(v___x_6126_);
lean_dec_ref(v_a_6124_);
return v_b_6128_;
}
v___jp_6129_:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; 
lean_inc_ref(v_a_6124_);
v___x_6133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6133_, 0, v_a_6124_);
lean_ctor_set(v___x_6133_, 1, v_startInclusive_6131_);
lean_ctor_set(v___x_6133_, 2, v_endExclusive_6132_);
v___x_6134_ = l_String_Slice_toString(v___x_6133_);
lean_dec_ref_known(v___x_6133_, 3);
v___x_6135_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_6134_);
v___x_6136_ = lean_array_push(v_b_6128_, v___x_6135_);
v_a_6127_ = v_it_6130_;
v_b_6128_ = v___x_6136_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg___boxed(lean_object* v_a_6163_, lean_object* v___x_6164_, lean_object* v___x_6165_, lean_object* v_a_6166_, lean_object* v_b_6167_){
_start:
{
lean_object* v_res_6168_; 
v_res_6168_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6163_, v___x_6164_, v___x_6165_, v_a_6166_, v_b_6167_);
lean_dec_ref(v___x_6164_);
return v_res_6168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(size_t v_sz_6169_, size_t v_i_6170_, lean_object* v_bs_6171_){
_start:
{
uint8_t v___x_6172_; 
v___x_6172_ = lean_usize_dec_lt(v_i_6170_, v_sz_6169_);
if (v___x_6172_ == 0)
{
return v_bs_6171_;
}
else
{
lean_object* v_v_6173_; lean_object* v___x_6174_; lean_object* v_bs_x27_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; size_t v___x_6184_; size_t v___x_6185_; lean_object* v___x_6186_; 
v_v_6173_ = lean_array_uget(v_bs_6171_, v_i_6170_);
v___x_6174_ = lean_unsigned_to_nat(0u);
v_bs_x27_6175_ = lean_array_uset(v_bs_6171_, v_i_6170_, v___x_6174_);
v___x_6176_ = lean_string_utf8_byte_size(v_v_6173_);
lean_inc(v_v_6173_);
v___x_6177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6177_, 0, v_v_6173_);
lean_ctor_set(v___x_6177_, 1, v___x_6174_);
lean_ctor_set(v___x_6177_, 2, v___x_6176_);
v___x_6178_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__0___closed__0);
v___x_6179_ = ((lean_object*)(l_Lean_Fmt_fmtRawAsInSource___closed__2));
v___x_6180_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_v_6173_, v___x_6177_, v___x_6176_, v___x_6178_, v___x_6179_);
lean_dec_ref_known(v___x_6177_, 3);
v___x_6181_ = lean_obj_once(&l_Lean_Fmt_fmtRawAsInSource___closed__3, &l_Lean_Fmt_fmtRawAsInSource___closed__3_once, _init_l_Lean_Fmt_fmtRawAsInSource___closed__3);
v___x_6182_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_6181_, v___x_6180_);
v___x_6183_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6182_);
v___x_6184_ = ((size_t)1ULL);
v___x_6185_ = lean_usize_add(v_i_6170_, v___x_6184_);
v___x_6186_ = lean_array_uset(v_bs_x27_6175_, v_i_6170_, v___x_6183_);
v_i_6170_ = v___x_6185_;
v_bs_6171_ = v___x_6186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg___boxed(lean_object* v_sz_6188_, lean_object* v_i_6189_, lean_object* v_bs_6190_){
_start:
{
size_t v_sz_boxed_6191_; size_t v_i_boxed_6192_; lean_object* v_res_6193_; 
v_sz_boxed_6191_ = lean_unbox_usize(v_sz_6188_);
lean_dec(v_sz_6188_);
v_i_boxed_6192_ = lean_unbox_usize(v_i_6189_);
lean_dec(v_i_6189_);
v_res_6193_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_boxed_6191_, v_i_boxed_6192_, v_bs_6190_);
return v_res_6193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(lean_object* v_a_6194_, lean_object* v_x_6195_){
_start:
{
if (lean_obj_tag(v_x_6195_) == 0)
{
lean_object* v___x_6196_; 
v___x_6196_ = lean_box(0);
return v___x_6196_;
}
else
{
lean_object* v_key_6197_; lean_object* v_value_6198_; lean_object* v_tail_6199_; uint8_t v___x_6200_; 
v_key_6197_ = lean_ctor_get(v_x_6195_, 0);
v_value_6198_ = lean_ctor_get(v_x_6195_, 1);
v_tail_6199_ = lean_ctor_get(v_x_6195_, 2);
v___x_6200_ = lean_nat_dec_eq(v_key_6197_, v_a_6194_);
if (v___x_6200_ == 0)
{
v_x_6195_ = v_tail_6199_;
goto _start;
}
else
{
lean_object* v___x_6202_; 
lean_inc(v_value_6198_);
v___x_6202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6202_, 0, v_value_6198_);
return v___x_6202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg___boxed(lean_object* v_a_6203_, lean_object* v_x_6204_){
_start:
{
lean_object* v_res_6205_; 
v_res_6205_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6203_, v_x_6204_);
lean_dec(v_x_6204_);
lean_dec(v_a_6203_);
return v_res_6205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(lean_object* v_m_6206_, lean_object* v_a_6207_){
_start:
{
lean_object* v_buckets_6208_; lean_object* v___x_6209_; uint64_t v___x_6210_; uint64_t v___x_6211_; uint64_t v___x_6212_; uint64_t v_fold_6213_; uint64_t v___x_6214_; uint64_t v___x_6215_; uint64_t v___x_6216_; size_t v___x_6217_; size_t v___x_6218_; size_t v___x_6219_; size_t v___x_6220_; size_t v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; 
v_buckets_6208_ = lean_ctor_get(v_m_6206_, 1);
v___x_6209_ = lean_array_get_size(v_buckets_6208_);
v___x_6210_ = lean_uint64_of_nat(v_a_6207_);
v___x_6211_ = 32ULL;
v___x_6212_ = lean_uint64_shift_right(v___x_6210_, v___x_6211_);
v_fold_6213_ = lean_uint64_xor(v___x_6210_, v___x_6212_);
v___x_6214_ = 16ULL;
v___x_6215_ = lean_uint64_shift_right(v_fold_6213_, v___x_6214_);
v___x_6216_ = lean_uint64_xor(v_fold_6213_, v___x_6215_);
v___x_6217_ = lean_uint64_to_usize(v___x_6216_);
v___x_6218_ = lean_usize_of_nat(v___x_6209_);
v___x_6219_ = ((size_t)1ULL);
v___x_6220_ = lean_usize_sub(v___x_6218_, v___x_6219_);
v___x_6221_ = lean_usize_land(v___x_6217_, v___x_6220_);
v___x_6222_ = lean_array_uget_borrowed(v_buckets_6208_, v___x_6221_);
v___x_6223_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6207_, v___x_6222_);
return v___x_6223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg___boxed(lean_object* v_m_6224_, lean_object* v_a_6225_){
_start:
{
lean_object* v_res_6226_; 
v_res_6226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6224_, v_a_6225_);
lean_dec(v_a_6225_);
lean_dec_ref(v_m_6224_);
return v_res_6226_;
}
}
static uint8_t _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_6227_; uint8_t v___x_6228_; 
v___x_6227_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6228_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6227_);
return v___x_6228_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(lean_object* v_upperBound_6229_, lean_object* v_comments_6230_, lean_object* v_numNewlinesBeforeComments_6231_, lean_object* v_a_6232_, lean_object* v_b_6233_){
_start:
{
lean_object* v___y_6235_; uint8_t v___x_6241_; lean_object* v___y_6243_; lean_object* v___y_6244_; 
v___x_6241_ = lean_nat_dec_lt(v_a_6232_, v_upperBound_6229_);
if (v___x_6241_ == 0)
{
lean_dec(v_a_6232_);
return v_b_6233_;
}
else
{
lean_object* v_fst_6248_; lean_object* v_snd_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6314_; 
v_fst_6248_ = lean_ctor_get(v_b_6233_, 0);
v_snd_6249_ = lean_ctor_get(v_b_6233_, 1);
v_isSharedCheck_6314_ = !lean_is_exclusive(v_b_6233_);
if (v_isSharedCheck_6314_ == 0)
{
v___x_6251_ = v_b_6233_;
v_isShared_6252_ = v_isSharedCheck_6314_;
goto v_resetjp_6250_;
}
else
{
lean_inc(v_snd_6249_);
lean_inc(v_fst_6248_);
lean_dec(v_b_6233_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6314_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v___x_6253_; lean_object* v___y_6255_; lean_object* v___y_6288_; lean_object* v___y_6289_; lean_object* v___y_6292_; uint8_t v___y_6295_; lean_object* v___y_6296_; uint8_t v___y_6300_; lean_object* v___y_6301_; uint8_t v___y_6305_; uint8_t v_insertedAnyNewlines_6308_; uint8_t v___x_6309_; 
v___x_6253_ = lean_unsigned_to_nat(0u);
v_insertedAnyNewlines_6308_ = 0;
v___x_6309_ = lean_nat_dec_eq(v_a_6232_, v___x_6253_);
if (v___x_6309_ == 0)
{
lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; uint8_t v_kind_6313_; 
v___x_6310_ = lean_unsigned_to_nat(1u);
v___x_6311_ = lean_nat_sub(v_a_6232_, v___x_6310_);
v___x_6312_ = lean_array_fget_borrowed(v_comments_6230_, v___x_6311_);
lean_dec(v___x_6311_);
v_kind_6313_ = lean_ctor_get_uint8(v___x_6312_, sizeof(void*)*3);
if (v_kind_6313_ == 1)
{
v___y_6305_ = v___x_6241_;
goto v___jp_6304_;
}
else
{
v___y_6305_ = v_insertedAnyNewlines_6308_;
goto v___jp_6304_;
}
}
else
{
v___y_6305_ = v_insertedAnyNewlines_6308_;
goto v___jp_6304_;
}
v___jp_6254_:
{
lean_object* v___x_6257_; 
if (v_isShared_6252_ == 0)
{
v___x_6257_ = v___x_6251_;
goto v_reusejp_6256_;
}
else
{
lean_object* v_reuseFailAlloc_6286_; 
v_reuseFailAlloc_6286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6286_, 0, v_fst_6248_);
lean_ctor_set(v_reuseFailAlloc_6286_, 1, v_snd_6249_);
v___x_6257_ = v_reuseFailAlloc_6286_;
goto v_reusejp_6256_;
}
v_reusejp_6256_:
{
lean_object* v___x_6258_; lean_object* v_fst_6259_; lean_object* v_snd_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; size_t v_sz_6263_; size_t v___x_6264_; lean_object* v___x_6265_; size_t v_sz_6266_; uint8_t v_kind_6267_; lean_object* v___x_6268_; lean_object* v___f_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; 
v___x_6258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v___y_6255_, v_a_6232_, v_upperBound_6229_, v___x_6253_, v___x_6257_);
lean_dec(v___y_6255_);
v_fst_6259_ = lean_ctor_get(v___x_6258_, 0);
lean_inc_n(v_fst_6259_, 2);
v_snd_6260_ = lean_ctor_get(v___x_6258_, 1);
lean_inc(v_snd_6260_);
lean_dec_ref(v___x_6258_);
v___x_6261_ = lean_array_fget_borrowed(v_comments_6230_, v_a_6232_);
lean_inc_n(v___x_6261_, 2);
v___x_6262_ = l_Lean_Fmt_Comment_render(v___x_6261_);
v_sz_6263_ = lean_array_size(v___x_6262_);
v___x_6264_ = ((size_t)0ULL);
v___x_6265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__2(v_sz_6263_, v___x_6264_, v___x_6262_);
v_sz_6266_ = lean_array_size(v___x_6265_);
v_kind_6267_ = lean_ctor_get_uint8(v___x_6261_, sizeof(void*)*3);
v___x_6268_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6266_, v___x_6264_, v___x_6265_);
v___f_6269_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_6269_, 0, v___x_6261_);
lean_closure_set(v___f_6269_, 1, v_fst_6259_);
v___x_6270_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_6268_);
v___x_6271_ = l_Lean_Fmt_TaggedDoc_free(v___x_6270_);
if (v_kind_6267_ == 0)
{
lean_object* v___x_6272_; uint8_t v___x_6273_; 
lean_dec(v_snd_6260_);
lean_dec(v_fst_6259_);
v___x_6272_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_6273_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_6271_);
if (v___x_6273_ == 0)
{
uint8_t v___x_6274_; 
v___x_6274_ = lean_uint8_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___closed__0);
if (v___x_6274_ == 0)
{
lean_object* v_doc_6275_; lean_object* v_doc_6276_; uint8_t v___x_6277_; 
v_doc_6275_ = lean_ctor_get(v___x_6271_, 0);
lean_inc(v_doc_6275_);
lean_dec_ref(v___x_6271_);
v_doc_6276_ = lean_ctor_get(v___x_6272_, 0);
v___x_6277_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6275_);
if (v___x_6277_ == 0)
{
uint8_t v___x_6278_; 
v___x_6278_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_6276_);
if (v___x_6278_ == 0)
{
lean_object* v___x_6279_; lean_object* v___x_6280_; 
lean_inc(v_doc_6276_);
v___x_6279_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_6275_, v_doc_6276_);
v___x_6280_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_6279_);
v___y_6243_ = v___f_6269_;
v___y_6244_ = v___x_6280_;
goto v___jp_6242_;
}
else
{
lean_object* v___x_6281_; 
v___x_6281_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6275_);
v___y_6243_ = v___f_6269_;
v___y_6244_ = v___x_6281_;
goto v___jp_6242_;
}
}
else
{
lean_object* v___x_6282_; 
lean_dec(v_doc_6275_);
lean_inc(v_doc_6276_);
v___x_6282_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_6276_);
v___y_6243_ = v___f_6269_;
v___y_6244_ = v___x_6282_;
goto v___jp_6242_;
}
}
else
{
v___y_6243_ = v___f_6269_;
v___y_6244_ = v___x_6271_;
goto v___jp_6242_;
}
}
else
{
lean_dec_ref(v___x_6271_);
v___y_6243_ = v___f_6269_;
v___y_6244_ = v___x_6272_;
goto v___jp_6242_;
}
}
else
{
lean_object* v___x_6283_; uint8_t v___x_6284_; lean_object* v___x_6285_; 
lean_dec_ref(v___f_6269_);
v___x_6283_ = lean_box(0);
v___x_6284_ = lean_unbox(v_snd_6260_);
lean_dec(v_snd_6260_);
v___x_6285_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___lam__0(v___x_6261_, v_fst_6259_, v___x_6283_, v___x_6284_, v___x_6271_);
v___y_6235_ = v___x_6285_;
goto v___jp_6234_;
}
}
}
v___jp_6287_:
{
uint8_t v___x_6290_; 
v___x_6290_ = lean_nat_dec_le(v___y_6288_, v___y_6289_);
if (v___x_6290_ == 0)
{
lean_dec(v___y_6288_);
v___y_6255_ = v___y_6289_;
goto v___jp_6254_;
}
else
{
lean_dec(v___y_6289_);
v___y_6255_ = v___y_6288_;
goto v___jp_6254_;
}
}
v___jp_6291_:
{
lean_object* v___x_6293_; 
v___x_6293_ = lean_unsigned_to_nat(2u);
v___y_6288_ = v___y_6292_;
v___y_6289_ = v___x_6293_;
goto v___jp_6287_;
}
v___jp_6294_:
{
uint8_t v___x_6297_; 
v___x_6297_ = lean_nat_dec_eq(v_a_6232_, v___x_6253_);
if (v___x_6297_ == 0)
{
if (v___y_6295_ == 0)
{
lean_object* v___x_6298_; 
v___x_6298_ = lean_unsigned_to_nat(1u);
v___y_6288_ = v___y_6296_;
v___y_6289_ = v___x_6298_;
goto v___jp_6287_;
}
else
{
v___y_6292_ = v___y_6296_;
goto v___jp_6291_;
}
}
else
{
v___y_6292_ = v___y_6296_;
goto v___jp_6291_;
}
}
v___jp_6299_:
{
if (v___y_6300_ == 0)
{
v___y_6295_ = v___y_6300_;
v___y_6296_ = v___y_6301_;
goto v___jp_6294_;
}
else
{
lean_object* v___x_6302_; uint8_t v___x_6303_; 
v___x_6302_ = lean_unsigned_to_nat(1u);
v___x_6303_ = lean_nat_dec_le(v___y_6301_, v___x_6302_);
if (v___x_6303_ == 0)
{
v___y_6295_ = v___y_6300_;
v___y_6296_ = v___y_6301_;
goto v___jp_6294_;
}
else
{
lean_dec(v___y_6301_);
v___y_6295_ = v___y_6300_;
v___y_6296_ = v___x_6302_;
goto v___jp_6294_;
}
}
}
v___jp_6304_:
{
lean_object* v___x_6306_; 
v___x_6306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_numNewlinesBeforeComments_6231_, v_a_6232_);
if (lean_obj_tag(v___x_6306_) == 0)
{
v___y_6300_ = v___y_6305_;
v___y_6301_ = v___x_6253_;
goto v___jp_6299_;
}
else
{
lean_object* v_val_6307_; 
v_val_6307_ = lean_ctor_get(v___x_6306_, 0);
lean_inc(v_val_6307_);
lean_dec_ref_known(v___x_6306_, 1);
v___y_6300_ = v___y_6305_;
v___y_6301_ = v_val_6307_;
goto v___jp_6299_;
}
}
}
}
v___jp_6234_:
{
if (lean_obj_tag(v___y_6235_) == 0)
{
lean_object* v_a_6236_; 
lean_dec(v_a_6232_);
v_a_6236_ = lean_ctor_get(v___y_6235_, 0);
lean_inc(v_a_6236_);
lean_dec_ref_known(v___y_6235_, 1);
return v_a_6236_;
}
else
{
lean_object* v_a_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; 
v_a_6237_ = lean_ctor_get(v___y_6235_, 0);
lean_inc(v_a_6237_);
lean_dec_ref_known(v___y_6235_, 1);
v___x_6238_ = lean_unsigned_to_nat(1u);
v___x_6239_ = lean_nat_add(v_a_6232_, v___x_6238_);
lean_dec(v_a_6232_);
v_a_6232_ = v___x_6239_;
v_b_6233_ = v_a_6237_;
goto _start;
}
}
v___jp_6242_:
{
lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; 
v___x_6245_ = lean_box(0);
v___x_6246_ = lean_box(v___x_6241_);
v___x_6247_ = lean_apply_3(v___y_6243_, v___x_6245_, v___x_6246_, v___y_6244_);
v___y_6235_ = v___x_6247_;
goto v___jp_6234_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg___boxed(lean_object* v_upperBound_6315_, lean_object* v_comments_6316_, lean_object* v_numNewlinesBeforeComments_6317_, lean_object* v_a_6318_, lean_object* v_b_6319_){
_start:
{
lean_object* v_res_6320_; 
v_res_6320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6315_, v_comments_6316_, v_numNewlinesBeforeComments_6317_, v_a_6318_, v_b_6319_);
lean_dec_ref(v_numNewlinesBeforeComments_6317_);
lean_dec_ref(v_comments_6316_);
lean_dec(v_upperBound_6315_);
return v_res_6320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(lean_object* v_upperBound_6321_, lean_object* v_a_6322_, lean_object* v_b_6323_){
_start:
{
uint8_t v___x_6324_; 
v___x_6324_ = lean_nat_dec_lt(v_a_6322_, v_upperBound_6321_);
if (v___x_6324_ == 0)
{
lean_dec(v_a_6322_);
return v_b_6323_;
}
else
{
lean_object* v_fst_6325_; lean_object* v___x_6327_; uint8_t v_isShared_6328_; uint8_t v_isSharedCheck_6338_; 
v_fst_6325_ = lean_ctor_get(v_b_6323_, 0);
v_isSharedCheck_6338_ = !lean_is_exclusive(v_b_6323_);
if (v_isSharedCheck_6338_ == 0)
{
lean_object* v_unused_6339_; 
v_unused_6339_ = lean_ctor_get(v_b_6323_, 1);
lean_dec(v_unused_6339_);
v___x_6327_ = v_b_6323_;
v_isShared_6328_ = v_isSharedCheck_6338_;
goto v_resetjp_6326_;
}
else
{
lean_inc(v_fst_6325_);
lean_dec(v_b_6323_);
v___x_6327_ = lean_box(0);
v_isShared_6328_ = v_isSharedCheck_6338_;
goto v_resetjp_6326_;
}
v_resetjp_6326_:
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6333_; 
v___x_6329_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6330_ = lean_array_push(v_fst_6325_, v___x_6329_);
v___x_6331_ = lean_box(v___x_6324_);
if (v_isShared_6328_ == 0)
{
lean_ctor_set(v___x_6327_, 1, v___x_6331_);
lean_ctor_set(v___x_6327_, 0, v___x_6330_);
v___x_6333_ = v___x_6327_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6337_; 
v_reuseFailAlloc_6337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6337_, 0, v___x_6330_);
lean_ctor_set(v_reuseFailAlloc_6337_, 1, v___x_6331_);
v___x_6333_ = v_reuseFailAlloc_6337_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6334_ = lean_unsigned_to_nat(1u);
v___x_6335_ = lean_nat_add(v_a_6322_, v___x_6334_);
lean_dec(v_a_6322_);
v_a_6322_ = v___x_6335_;
v_b_6323_ = v___x_6333_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg___boxed(lean_object* v_upperBound_6340_, lean_object* v_a_6341_, lean_object* v_b_6342_){
_start:
{
lean_object* v_res_6343_; 
v_res_6343_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6340_, v_a_6341_, v_b_6342_);
lean_dec(v_upperBound_6340_);
return v_res_6343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(lean_object* v_as_6344_, size_t v_i_6345_, size_t v_stop_6346_, lean_object* v_b_6347_){
_start:
{
lean_object* v___y_6349_; uint8_t v___x_6353_; 
v___x_6353_ = lean_usize_dec_eq(v_i_6345_, v_stop_6346_);
if (v___x_6353_ == 0)
{
lean_object* v___x_6354_; uint8_t v_placement_6355_; 
v___x_6354_ = lean_array_uget_borrowed(v_as_6344_, v_i_6345_);
v_placement_6355_ = lean_ctor_get_uint8(v___x_6354_, sizeof(void*)*3 + 1);
if (v_placement_6355_ == 0)
{
v___y_6349_ = v_b_6347_;
goto v___jp_6348_;
}
else
{
lean_object* v___x_6356_; 
lean_inc(v___x_6354_);
v___x_6356_ = lean_array_push(v_b_6347_, v___x_6354_);
v___y_6349_ = v___x_6356_;
goto v___jp_6348_;
}
}
else
{
return v_b_6347_;
}
v___jp_6348_:
{
size_t v___x_6350_; size_t v___x_6351_; 
v___x_6350_ = ((size_t)1ULL);
v___x_6351_ = lean_usize_add(v_i_6345_, v___x_6350_);
v_i_6345_ = v___x_6351_;
v_b_6347_ = v___y_6349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8___boxed(lean_object* v_as_6357_, lean_object* v_i_6358_, lean_object* v_stop_6359_, lean_object* v_b_6360_){
_start:
{
size_t v_i_boxed_6361_; size_t v_stop_boxed_6362_; lean_object* v_res_6363_; 
v_i_boxed_6361_ = lean_unbox_usize(v_i_6358_);
lean_dec(v_i_6358_);
v_stop_boxed_6362_ = lean_unbox_usize(v_stop_6359_);
lean_dec(v_stop_6359_);
v_res_6363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_as_6357_, v_i_boxed_6361_, v_stop_boxed_6362_, v_b_6360_);
lean_dec_ref(v_as_6357_);
return v_res_6363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(lean_object* v_comments_6370_, lean_object* v_whitespace_6371_, uint8_t v_isLeading_6372_){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___y_6376_; lean_object* v___y_6377_; lean_object* v___y_6378_; lean_object* v___y_6391_; lean_object* v___y_6392_; lean_object* v___y_6393_; lean_object* v___y_6394_; lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v___y_6399_; lean_object* v___x_6401_; lean_object* v___y_6403_; lean_object* v___y_6404_; uint8_t v___y_6405_; lean_object* v___y_6406_; lean_object* v___y_6412_; lean_object* v___y_6413_; uint8_t v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6419_; lean_object* v___y_6420_; lean_object* v___y_6421_; uint8_t v___y_6422_; lean_object* v___y_6426_; lean_object* v___x_6439_; uint8_t v___x_6440_; 
v___x_6373_ = l_Lean_Fmt_instInhabitedComment_default;
v___x_6374_ = lean_unsigned_to_nat(0u);
v___x_6401_ = lean_array_get_size(v_comments_6370_);
v___x_6439_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6440_ = lean_nat_dec_lt(v___x_6374_, v___x_6401_);
if (v___x_6440_ == 0)
{
v___y_6426_ = v___x_6439_;
goto v___jp_6425_;
}
else
{
uint8_t v___x_6441_; 
v___x_6441_ = lean_nat_dec_le(v___x_6401_, v___x_6401_);
if (v___x_6441_ == 0)
{
if (v___x_6440_ == 0)
{
v___y_6426_ = v___x_6439_;
goto v___jp_6425_;
}
else
{
size_t v___x_6442_; size_t v___x_6443_; lean_object* v___x_6444_; 
v___x_6442_ = ((size_t)0ULL);
v___x_6443_ = lean_usize_of_nat(v___x_6401_);
v___x_6444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_comments_6370_, v___x_6442_, v___x_6443_, v___x_6439_);
v___y_6426_ = v___x_6444_;
goto v___jp_6425_;
}
}
else
{
size_t v___x_6445_; size_t v___x_6446_; lean_object* v___x_6447_; 
v___x_6445_ = ((size_t)0ULL);
v___x_6446_ = lean_usize_of_nat(v___x_6401_);
v___x_6447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v_comments_6370_, v___x_6445_, v___x_6446_, v___x_6439_);
v___y_6426_ = v___x_6447_;
goto v___jp_6425_;
}
}
v___jp_6375_:
{
lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v_fst_6381_; lean_object* v_snd_6382_; lean_object* v___x_6384_; uint8_t v_isShared_6385_; uint8_t v_isSharedCheck_6389_; 
v___x_6379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6379_, 0, v___y_6377_);
lean_ctor_set(v___x_6379_, 1, v___y_6376_);
v___x_6380_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v___y_6378_, v___x_6374_, v___x_6379_);
lean_dec(v___y_6378_);
v_fst_6381_ = lean_ctor_get(v___x_6380_, 0);
v_snd_6382_ = lean_ctor_get(v___x_6380_, 1);
v_isSharedCheck_6389_ = !lean_is_exclusive(v___x_6380_);
if (v_isSharedCheck_6389_ == 0)
{
v___x_6384_ = v___x_6380_;
v_isShared_6385_ = v_isSharedCheck_6389_;
goto v_resetjp_6383_;
}
else
{
lean_inc(v_snd_6382_);
lean_inc(v_fst_6381_);
lean_dec(v___x_6380_);
v___x_6384_ = lean_box(0);
v_isShared_6385_ = v_isSharedCheck_6389_;
goto v_resetjp_6383_;
}
v_resetjp_6383_:
{
lean_object* v___x_6387_; 
if (v_isShared_6385_ == 0)
{
v___x_6387_ = v___x_6384_;
goto v_reusejp_6386_;
}
else
{
lean_object* v_reuseFailAlloc_6388_; 
v_reuseFailAlloc_6388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_fst_6381_);
lean_ctor_set(v_reuseFailAlloc_6388_, 1, v_snd_6382_);
v___x_6387_ = v_reuseFailAlloc_6388_;
goto v_reusejp_6386_;
}
v_reusejp_6386_:
{
return v___x_6387_;
}
}
}
v___jp_6390_:
{
uint8_t v___x_6395_; 
v___x_6395_ = lean_nat_dec_le(v___y_6393_, v___y_6394_);
if (v___x_6395_ == 0)
{
lean_dec(v___y_6393_);
v___y_6376_ = v___y_6391_;
v___y_6377_ = v___y_6392_;
v___y_6378_ = v___y_6394_;
goto v___jp_6375_;
}
else
{
lean_dec(v___y_6394_);
v___y_6376_ = v___y_6391_;
v___y_6377_ = v___y_6392_;
v___y_6378_ = v___y_6393_;
goto v___jp_6375_;
}
}
v___jp_6396_:
{
lean_object* v___x_6400_; 
v___x_6400_ = lean_unsigned_to_nat(2u);
v___y_6391_ = v___y_6397_;
v___y_6392_ = v___y_6398_;
v___y_6393_ = v___y_6399_;
v___y_6394_ = v___x_6400_;
goto v___jp_6390_;
}
v___jp_6402_:
{
if (v_isLeading_6372_ == 0)
{
uint8_t v___x_6407_; 
v___x_6407_ = lean_nat_dec_eq(v___x_6401_, v___x_6374_);
if (v___x_6407_ == 0)
{
if (v___y_6405_ == 0)
{
lean_object* v___x_6408_; 
v___x_6408_ = lean_unsigned_to_nat(1u);
v___y_6391_ = v___y_6403_;
v___y_6392_ = v___y_6404_;
v___y_6393_ = v___y_6406_;
v___y_6394_ = v___x_6408_;
goto v___jp_6390_;
}
else
{
v___y_6397_ = v___y_6403_;
v___y_6398_ = v___y_6404_;
v___y_6399_ = v___y_6406_;
goto v___jp_6396_;
}
}
else
{
v___y_6397_ = v___y_6403_;
v___y_6398_ = v___y_6404_;
v___y_6399_ = v___y_6406_;
goto v___jp_6396_;
}
}
else
{
uint8_t v___x_6409_; 
v___x_6409_ = lean_nat_dec_lt(v___x_6374_, v___x_6401_);
if (v___x_6409_ == 0)
{
v___y_6391_ = v___y_6403_;
v___y_6392_ = v___y_6404_;
v___y_6393_ = v___y_6406_;
v___y_6394_ = v___x_6374_;
goto v___jp_6390_;
}
else
{
lean_object* v___x_6410_; 
v___x_6410_ = lean_unsigned_to_nat(2u);
v___y_6391_ = v___y_6403_;
v___y_6392_ = v___y_6404_;
v___y_6393_ = v___y_6406_;
v___y_6394_ = v___x_6410_;
goto v___jp_6390_;
}
}
}
v___jp_6411_:
{
if (v___y_6414_ == 0)
{
v___y_6403_ = v___y_6412_;
v___y_6404_ = v___y_6413_;
v___y_6405_ = v___y_6414_;
v___y_6406_ = v___y_6415_;
goto v___jp_6402_;
}
else
{
lean_object* v___x_6416_; uint8_t v___x_6417_; 
v___x_6416_ = lean_unsigned_to_nat(1u);
v___x_6417_ = lean_nat_dec_le(v___y_6415_, v___x_6416_);
if (v___x_6417_ == 0)
{
v___y_6403_ = v___y_6412_;
v___y_6404_ = v___y_6413_;
v___y_6405_ = v___y_6414_;
v___y_6406_ = v___y_6415_;
goto v___jp_6402_;
}
else
{
lean_dec(v___y_6415_);
v___y_6403_ = v___y_6412_;
v___y_6404_ = v___y_6413_;
v___y_6405_ = v___y_6414_;
v___y_6406_ = v___x_6416_;
goto v___jp_6402_;
}
}
}
v___jp_6418_:
{
lean_object* v___x_6423_; 
v___x_6423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v___y_6419_, v___x_6401_);
lean_dec_ref(v___y_6419_);
if (lean_obj_tag(v___x_6423_) == 0)
{
v___y_6412_ = v___y_6420_;
v___y_6413_ = v___y_6421_;
v___y_6414_ = v___y_6422_;
v___y_6415_ = v___x_6374_;
goto v___jp_6411_;
}
else
{
lean_object* v_val_6424_; 
v_val_6424_ = lean_ctor_get(v___x_6423_, 0);
lean_inc(v_val_6424_);
lean_dec_ref_known(v___x_6423_, 1);
v___y_6412_ = v___y_6420_;
v___y_6413_ = v___y_6421_;
v___y_6414_ = v___y_6422_;
v___y_6415_ = v_val_6424_;
goto v___jp_6411_;
}
}
v___jp_6425_:
{
lean_object* v_numNewlinesBeforeComments_6427_; uint8_t v_insertedAnyNewlines_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v_fst_6431_; lean_object* v_snd_6432_; uint8_t v___x_6433_; 
v_numNewlinesBeforeComments_6427_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_countNewlinesBeforeComments(v___y_6426_, v_whitespace_6371_);
lean_dec_ref(v___y_6426_);
v_insertedAnyNewlines_6428_ = 0;
v___x_6429_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__0));
v___x_6430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v___x_6401_, v_comments_6370_, v_numNewlinesBeforeComments_6427_, v___x_6374_, v___x_6429_);
v_fst_6431_ = lean_ctor_get(v___x_6430_, 0);
lean_inc(v_fst_6431_);
v_snd_6432_ = lean_ctor_get(v___x_6430_, 1);
lean_inc(v_snd_6432_);
lean_dec_ref(v___x_6430_);
v___x_6433_ = lean_nat_dec_eq(v___x_6401_, v___x_6374_);
if (v___x_6433_ == 0)
{
lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; uint8_t v_kind_6437_; 
v___x_6434_ = lean_unsigned_to_nat(1u);
v___x_6435_ = lean_nat_sub(v___x_6401_, v___x_6434_);
v___x_6436_ = lean_array_get_borrowed(v___x_6373_, v_comments_6370_, v___x_6435_);
lean_dec(v___x_6435_);
v_kind_6437_ = lean_ctor_get_uint8(v___x_6436_, sizeof(void*)*3);
if (v_kind_6437_ == 1)
{
uint8_t v___x_6438_; 
v___x_6438_ = 1;
v___y_6419_ = v_numNewlinesBeforeComments_6427_;
v___y_6420_ = v_snd_6432_;
v___y_6421_ = v_fst_6431_;
v___y_6422_ = v___x_6438_;
goto v___jp_6418_;
}
else
{
v___y_6419_ = v_numNewlinesBeforeComments_6427_;
v___y_6420_ = v_snd_6432_;
v___y_6421_ = v_fst_6431_;
v___y_6422_ = v_insertedAnyNewlines_6428_;
goto v___jp_6418_;
}
}
else
{
v___y_6419_ = v_numNewlinesBeforeComments_6427_;
v___y_6420_ = v_snd_6432_;
v___y_6421_ = v_fst_6431_;
v___y_6422_ = v_insertedAnyNewlines_6428_;
goto v___jp_6418_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___boxed(lean_object* v_comments_6448_, lean_object* v_whitespace_6449_, lean_object* v_isLeading_6450_){
_start:
{
uint8_t v_isLeading_boxed_6451_; lean_object* v_res_6452_; 
v_isLeading_boxed_6451_ = lean_unbox(v_isLeading_6450_);
v_res_6452_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v_comments_6448_, v_whitespace_6449_, v_isLeading_boxed_6451_);
lean_dec_ref(v_whitespace_6449_);
lean_dec_ref(v_comments_6448_);
return v_res_6452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(lean_object* v_a_6453_, lean_object* v___x_6454_, lean_object* v___x_6455_, lean_object* v_inst_6456_, lean_object* v_R_6457_, lean_object* v_a_6458_, lean_object* v_b_6459_){
_start:
{
lean_object* v___x_6460_; 
v___x_6460_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___redArg(v_a_6453_, v___x_6454_, v___x_6455_, v_a_6458_, v_b_6459_);
return v___x_6460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1___boxed(lean_object* v_a_6461_, lean_object* v___x_6462_, lean_object* v___x_6463_, lean_object* v_inst_6464_, lean_object* v_R_6465_, lean_object* v_a_6466_, lean_object* v_b_6467_){
_start:
{
lean_object* v_res_6468_; 
v_res_6468_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__1(v_a_6461_, v___x_6462_, v___x_6463_, v_inst_6464_, v_R_6465_, v_a_6466_, v_b_6467_);
lean_dec_ref(v___x_6462_);
return v_res_6468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(lean_object* v_as_6469_, size_t v_sz_6470_, size_t v_i_6471_, lean_object* v_bs_6472_){
_start:
{
lean_object* v___x_6473_; 
v___x_6473_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___redArg(v_sz_6470_, v_i_6471_, v_bs_6472_);
return v___x_6473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3___boxed(lean_object* v_as_6474_, lean_object* v_sz_6475_, lean_object* v_i_6476_, lean_object* v_bs_6477_){
_start:
{
size_t v_sz_boxed_6478_; size_t v_i_boxed_6479_; lean_object* v_res_6480_; 
v_sz_boxed_6478_ = lean_unbox_usize(v_sz_6475_);
lean_dec(v_sz_6475_);
v_i_boxed_6479_ = lean_unbox_usize(v_i_6476_);
lean_dec(v_i_6476_);
v_res_6480_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__3(v_as_6474_, v_sz_boxed_6478_, v_i_boxed_6479_, v_bs_6477_);
lean_dec_ref(v_as_6474_);
return v_res_6480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(lean_object* v_upperBound_6481_, lean_object* v_next_6482_, lean_object* v_upperBound_6483_, lean_object* v_inst_6484_, lean_object* v_R_6485_, lean_object* v_a_6486_, lean_object* v_b_6487_, lean_object* v_c_6488_){
_start:
{
lean_object* v___x_6489_; 
v___x_6489_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg(v_upperBound_6481_, v_next_6482_, v_upperBound_6483_, v_a_6486_, v_b_6487_);
return v___x_6489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___boxed(lean_object* v_upperBound_6490_, lean_object* v_next_6491_, lean_object* v_upperBound_6492_, lean_object* v_inst_6493_, lean_object* v_R_6494_, lean_object* v_a_6495_, lean_object* v_b_6496_, lean_object* v_c_6497_){
_start:
{
lean_object* v_res_6498_; 
v_res_6498_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4(v_upperBound_6490_, v_next_6491_, v_upperBound_6492_, v_inst_6493_, v_R_6494_, v_a_6495_, v_b_6496_, v_c_6497_);
lean_dec(v_upperBound_6492_);
lean_dec(v_next_6491_);
lean_dec(v_upperBound_6490_);
return v_res_6498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(lean_object* v_00_u03b2_6499_, lean_object* v_m_6500_, lean_object* v_a_6501_){
_start:
{
lean_object* v___x_6502_; 
v___x_6502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___redArg(v_m_6500_, v_a_6501_);
return v___x_6502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5___boxed(lean_object* v_00_u03b2_6503_, lean_object* v_m_6504_, lean_object* v_a_6505_){
_start:
{
lean_object* v_res_6506_; 
v_res_6506_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5(v_00_u03b2_6503_, v_m_6504_, v_a_6505_);
lean_dec(v_a_6505_);
lean_dec_ref(v_m_6504_);
return v_res_6506_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(lean_object* v_upperBound_6507_, lean_object* v_inst_6508_, lean_object* v_R_6509_, lean_object* v_a_6510_, lean_object* v_b_6511_, lean_object* v_c_6512_){
_start:
{
lean_object* v___x_6513_; 
v___x_6513_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___redArg(v_upperBound_6507_, v_a_6510_, v_b_6511_);
return v___x_6513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6___boxed(lean_object* v_upperBound_6514_, lean_object* v_inst_6515_, lean_object* v_R_6516_, lean_object* v_a_6517_, lean_object* v_b_6518_, lean_object* v_c_6519_){
_start:
{
lean_object* v_res_6520_; 
v_res_6520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__6(v_upperBound_6514_, v_inst_6515_, v_R_6516_, v_a_6517_, v_b_6518_, v_c_6519_);
lean_dec(v_upperBound_6514_);
return v_res_6520_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(lean_object* v_upperBound_6521_, lean_object* v_comments_6522_, lean_object* v_numNewlinesBeforeComments_6523_, lean_object* v_inst_6524_, lean_object* v_R_6525_, lean_object* v_a_6526_, lean_object* v_b_6527_, lean_object* v_c_6528_){
_start:
{
lean_object* v___x_6529_; 
v___x_6529_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___redArg(v_upperBound_6521_, v_comments_6522_, v_numNewlinesBeforeComments_6523_, v_a_6526_, v_b_6527_);
return v___x_6529_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7___boxed(lean_object* v_upperBound_6530_, lean_object* v_comments_6531_, lean_object* v_numNewlinesBeforeComments_6532_, lean_object* v_inst_6533_, lean_object* v_R_6534_, lean_object* v_a_6535_, lean_object* v_b_6536_, lean_object* v_c_6537_){
_start:
{
lean_object* v_res_6538_; 
v_res_6538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__7(v_upperBound_6530_, v_comments_6531_, v_numNewlinesBeforeComments_6532_, v_inst_6533_, v_R_6534_, v_a_6535_, v_b_6536_, v_c_6537_);
lean_dec_ref(v_numNewlinesBeforeComments_6532_);
lean_dec_ref(v_comments_6531_);
lean_dec(v_upperBound_6530_);
return v_res_6538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(lean_object* v_00_u03b2_6539_, lean_object* v_a_6540_, lean_object* v_x_6541_){
_start:
{
lean_object* v___x_6542_; 
v___x_6542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___redArg(v_a_6540_, v_x_6541_);
return v___x_6542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5___boxed(lean_object* v_00_u03b2_6543_, lean_object* v_a_6544_, lean_object* v_x_6545_){
_start:
{
lean_object* v_res_6546_; 
v_res_6546_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__5_spec__5(v_00_u03b2_6543_, v_a_6544_, v_x_6545_);
lean_dec(v_x_6545_);
lean_dec(v_a_6544_);
return v_res_6546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(lean_object* v_leadingTk_6549_, lean_object* v_leading_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_){
_start:
{
uint8_t v___x_6553_; lean_object* v___x_6554_; 
v___x_6553_ = 0;
v___x_6554_ = l_Lean_Syntax_getRange_x3f(v_leadingTk_6549_, v___x_6553_);
if (lean_obj_tag(v___x_6554_) == 1)
{
lean_object* v_val_6555_; lean_object* v___x_6557_; uint8_t v_isShared_6558_; uint8_t v_isSharedCheck_6598_; 
v_val_6555_ = lean_ctor_get(v___x_6554_, 0);
v_isSharedCheck_6598_ = !lean_is_exclusive(v___x_6554_);
if (v_isSharedCheck_6598_ == 0)
{
v___x_6557_ = v___x_6554_;
v_isShared_6558_ = v_isSharedCheck_6598_;
goto v_resetjp_6556_;
}
else
{
lean_inc(v_val_6555_);
lean_dec(v___x_6554_);
v___x_6557_ = lean_box(0);
v_isShared_6558_ = v_isSharedCheck_6598_;
goto v_resetjp_6556_;
}
v_resetjp_6556_:
{
lean_object* v_str_6559_; lean_object* v_startPos_6560_; lean_object* v_stopPos_6561_; lean_object* v___x_6563_; uint8_t v_isShared_6564_; uint8_t v_isSharedCheck_6597_; 
v_str_6559_ = lean_ctor_get(v_leading_6550_, 0);
v_startPos_6560_ = lean_ctor_get(v_leading_6550_, 1);
v_stopPos_6561_ = lean_ctor_get(v_leading_6550_, 2);
v_isSharedCheck_6597_ = !lean_is_exclusive(v_leading_6550_);
if (v_isSharedCheck_6597_ == 0)
{
v___x_6563_ = v_leading_6550_;
v_isShared_6564_ = v_isSharedCheck_6597_;
goto v_resetjp_6562_;
}
else
{
lean_inc(v_stopPos_6561_);
lean_inc(v_startPos_6560_);
lean_inc(v_str_6559_);
lean_dec(v_leading_6550_);
v___x_6563_ = lean_box(0);
v_isShared_6564_ = v_isSharedCheck_6597_;
goto v_resetjp_6562_;
}
v_resetjp_6562_:
{
uint8_t v___y_6566_; uint8_t v___x_6592_; uint8_t v___y_6594_; uint8_t v___x_6595_; 
v___x_6592_ = lean_string_is_valid_pos(v_str_6559_, v_startPos_6560_);
v___x_6595_ = lean_string_is_valid_pos(v_str_6559_, v_stopPos_6561_);
if (v___x_6595_ == 0)
{
v___y_6594_ = v___x_6595_;
goto v___jp_6593_;
}
else
{
uint8_t v___x_6596_; 
v___x_6596_ = lean_nat_dec_le(v_startPos_6560_, v_stopPos_6561_);
v___y_6594_ = v___x_6596_;
goto v___jp_6593_;
}
v___jp_6565_:
{
if (v___y_6566_ == 0)
{
lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6570_; 
lean_dec(v_stopPos_6561_);
lean_dec(v_startPos_6560_);
lean_dec_ref(v_str_6559_);
lean_dec(v_val_6555_);
v___x_6567_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6568_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
if (v_isShared_6564_ == 0)
{
lean_ctor_set(v___x_6563_, 2, v___x_6568_);
lean_ctor_set(v___x_6563_, 1, v___x_6567_);
lean_ctor_set(v___x_6563_, 0, v_leadingTk_6549_);
v___x_6570_ = v___x_6563_;
goto v_reusejp_6569_;
}
else
{
lean_object* v_reuseFailAlloc_6575_; 
v_reuseFailAlloc_6575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_leadingTk_6549_);
lean_ctor_set(v_reuseFailAlloc_6575_, 1, v___x_6567_);
lean_ctor_set(v_reuseFailAlloc_6575_, 2, v___x_6568_);
v___x_6570_ = v_reuseFailAlloc_6575_;
goto v_reusejp_6569_;
}
v_reusejp_6569_:
{
lean_object* v___x_6572_; 
if (v_isShared_6558_ == 0)
{
lean_ctor_set_tag(v___x_6557_, 2);
lean_ctor_set(v___x_6557_, 0, v___x_6570_);
v___x_6572_ = v___x_6557_;
goto v_reusejp_6571_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v___x_6570_);
v___x_6572_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6571_;
}
v_reusejp_6571_:
{
lean_object* v___x_6573_; 
v___x_6573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6573_, 0, v___x_6572_);
lean_ctor_set(v___x_6573_, 1, v___y_6552_);
return v___x_6573_;
}
}
}
else
{
lean_object* v_lineInfos_6576_; lean_object* v___x_6578_; 
lean_del_object(v___x_6557_);
lean_dec(v_leadingTk_6549_);
v_lineInfos_6576_ = lean_ctor_get(v___y_6551_, 4);
if (v_isShared_6564_ == 0)
{
v___x_6578_ = v___x_6563_;
goto v_reusejp_6577_;
}
else
{
lean_object* v_reuseFailAlloc_6591_; 
v_reuseFailAlloc_6591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6591_, 0, v_str_6559_);
lean_ctor_set(v_reuseFailAlloc_6591_, 1, v_startPos_6560_);
lean_ctor_set(v_reuseFailAlloc_6591_, 2, v_stopPos_6561_);
v___x_6578_ = v_reuseFailAlloc_6591_;
goto v_reusejp_6577_;
}
v_reusejp_6577_:
{
uint8_t v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v_fst_6582_; lean_object* v___x_6584_; uint8_t v_isShared_6585_; uint8_t v_isSharedCheck_6589_; 
v___x_6579_ = 0;
lean_inc_ref(v___x_6578_);
v___x_6580_ = l_Lean_Fmt_parseComments(v_lineInfos_6576_, v_val_6555_, v___x_6579_, v___x_6578_);
v___x_6581_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___x_6580_, v___x_6578_, v___y_6566_);
lean_dec_ref(v___x_6578_);
lean_dec_ref(v___x_6580_);
v_fst_6582_ = lean_ctor_get(v___x_6581_, 0);
v_isSharedCheck_6589_ = !lean_is_exclusive(v___x_6581_);
if (v_isSharedCheck_6589_ == 0)
{
lean_object* v_unused_6590_; 
v_unused_6590_ = lean_ctor_get(v___x_6581_, 1);
lean_dec(v_unused_6590_);
v___x_6584_ = v___x_6581_;
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
else
{
lean_inc(v_fst_6582_);
lean_dec(v___x_6581_);
v___x_6584_ = lean_box(0);
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
v_resetjp_6583_:
{
lean_object* v___x_6587_; 
if (v_isShared_6585_ == 0)
{
lean_ctor_set(v___x_6584_, 1, v___y_6552_);
v___x_6587_ = v___x_6584_;
goto v_reusejp_6586_;
}
else
{
lean_object* v_reuseFailAlloc_6588_; 
v_reuseFailAlloc_6588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6588_, 0, v_fst_6582_);
lean_ctor_set(v_reuseFailAlloc_6588_, 1, v___y_6552_);
v___x_6587_ = v_reuseFailAlloc_6588_;
goto v_reusejp_6586_;
}
v_reusejp_6586_:
{
return v___x_6587_;
}
}
}
}
}
v___jp_6593_:
{
if (v___x_6592_ == 0)
{
v___y_6566_ = v___x_6592_;
goto v___jp_6565_;
}
else
{
v___y_6566_ = v___y_6594_;
goto v___jp_6565_;
}
}
}
}
}
else
{
lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; 
lean_dec(v___x_6554_);
lean_dec_ref(v_leading_6550_);
v___x_6599_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6600_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6601_, 0, v_leadingTk_6549_);
lean_ctor_set(v___x_6601_, 1, v___x_6599_);
lean_ctor_set(v___x_6601_, 2, v___x_6600_);
v___x_6602_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6602_, 0, v___x_6601_);
v___x_6603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6603_, 0, v___x_6602_);
lean_ctor_set(v___x_6603_, 1, v___y_6552_);
return v___x_6603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_leadingTk_6604_, lean_object* v_leading_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_){
_start:
{
lean_object* v_res_6608_; 
v_res_6608_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0(v_leadingTk_6604_, v_leading_6605_, v___y_6606_, v___y_6607_);
lean_dec_ref(v___y_6606_);
return v_res_6608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(lean_object* v_stx_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_){
_start:
{
lean_object* v___f_6613_; lean_object* v___x_6614_; 
v___f_6613_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___closed__0));
v___x_6614_ = l_Lean_Fmt_fmtLeadingWhitespace(v_stx_6610_, v___f_6613_, v_a_6611_, v_a_6612_);
return v___x_6614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_){
_start:
{
lean_object* v_res_6618_; 
v_res_6618_ = l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments(v_stx_6615_, v_a_6616_, v_a_6617_);
lean_dec_ref(v_a_6616_);
return v_res_6618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(uint8_t v_atleastOneNewline_6619_, lean_object* v_trailingTk_6620_, lean_object* v_trailing_6621_, lean_object* v___y_6622_, lean_object* v___y_6623_){
_start:
{
uint8_t v___x_6624_; lean_object* v___y_6626_; lean_object* v___y_6627_; lean_object* v___x_6660_; 
v___x_6624_ = 0;
v___x_6660_ = l_Lean_Syntax_getRange_x3f(v_trailingTk_6620_, v___x_6624_);
if (lean_obj_tag(v___x_6660_) == 1)
{
lean_object* v_val_6661_; lean_object* v___x_6663_; uint8_t v_isShared_6664_; uint8_t v_isSharedCheck_6705_; 
v_val_6661_ = lean_ctor_get(v___x_6660_, 0);
v_isSharedCheck_6705_ = !lean_is_exclusive(v___x_6660_);
if (v_isSharedCheck_6705_ == 0)
{
v___x_6663_ = v___x_6660_;
v_isShared_6664_ = v_isSharedCheck_6705_;
goto v_resetjp_6662_;
}
else
{
lean_inc(v_val_6661_);
lean_dec(v___x_6660_);
v___x_6663_ = lean_box(0);
v_isShared_6664_ = v_isSharedCheck_6705_;
goto v_resetjp_6662_;
}
v_resetjp_6662_:
{
lean_object* v_str_6665_; lean_object* v_startPos_6666_; lean_object* v_stopPos_6667_; lean_object* v___x_6669_; uint8_t v_isShared_6670_; uint8_t v_isSharedCheck_6704_; 
v_str_6665_ = lean_ctor_get(v_trailing_6621_, 0);
v_startPos_6666_ = lean_ctor_get(v_trailing_6621_, 1);
v_stopPos_6667_ = lean_ctor_get(v_trailing_6621_, 2);
v_isSharedCheck_6704_ = !lean_is_exclusive(v_trailing_6621_);
if (v_isSharedCheck_6704_ == 0)
{
v___x_6669_ = v_trailing_6621_;
v_isShared_6670_ = v_isSharedCheck_6704_;
goto v_resetjp_6668_;
}
else
{
lean_inc(v_stopPos_6667_);
lean_inc(v_startPos_6666_);
lean_inc(v_str_6665_);
lean_dec(v_trailing_6621_);
v___x_6669_ = lean_box(0);
v_isShared_6670_ = v_isSharedCheck_6704_;
goto v_resetjp_6668_;
}
v_resetjp_6668_:
{
uint8_t v___y_6672_; uint8_t v___x_6699_; uint8_t v___y_6701_; uint8_t v___x_6702_; 
v___x_6699_ = lean_string_is_valid_pos(v_str_6665_, v_startPos_6666_);
v___x_6702_ = lean_string_is_valid_pos(v_str_6665_, v_stopPos_6667_);
if (v___x_6702_ == 0)
{
v___y_6701_ = v___x_6702_;
goto v___jp_6700_;
}
else
{
uint8_t v___x_6703_; 
v___x_6703_ = lean_nat_dec_le(v_startPos_6666_, v_stopPos_6667_);
v___y_6701_ = v___x_6703_;
goto v___jp_6700_;
}
v___jp_6671_:
{
if (v___y_6672_ == 0)
{
lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6676_; 
lean_dec(v_stopPos_6667_);
lean_dec(v_startPos_6666_);
lean_dec_ref(v_str_6665_);
lean_dec(v_val_6661_);
v___x_6673_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__0));
v___x_6674_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlines___lam__0___closed__1));
if (v_isShared_6670_ == 0)
{
lean_ctor_set(v___x_6669_, 2, v___x_6674_);
lean_ctor_set(v___x_6669_, 1, v___x_6673_);
lean_ctor_set(v___x_6669_, 0, v_trailingTk_6620_);
v___x_6676_ = v___x_6669_;
goto v_reusejp_6675_;
}
else
{
lean_object* v_reuseFailAlloc_6681_; 
v_reuseFailAlloc_6681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6681_, 0, v_trailingTk_6620_);
lean_ctor_set(v_reuseFailAlloc_6681_, 1, v___x_6673_);
lean_ctor_set(v_reuseFailAlloc_6681_, 2, v___x_6674_);
v___x_6676_ = v_reuseFailAlloc_6681_;
goto v_reusejp_6675_;
}
v_reusejp_6675_:
{
lean_object* v___x_6678_; 
if (v_isShared_6664_ == 0)
{
lean_ctor_set_tag(v___x_6663_, 2);
lean_ctor_set(v___x_6663_, 0, v___x_6676_);
v___x_6678_ = v___x_6663_;
goto v_reusejp_6677_;
}
else
{
lean_object* v_reuseFailAlloc_6680_; 
v_reuseFailAlloc_6680_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6680_, 0, v___x_6676_);
v___x_6678_ = v_reuseFailAlloc_6680_;
goto v_reusejp_6677_;
}
v_reusejp_6677_:
{
lean_object* v___x_6679_; 
v___x_6679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6679_, 0, v___x_6678_);
lean_ctor_set(v___x_6679_, 1, v___y_6623_);
return v___x_6679_;
}
}
}
else
{
lean_object* v_lineInfos_6682_; lean_object* v___x_6684_; 
lean_del_object(v___x_6663_);
lean_dec(v_trailingTk_6620_);
v_lineInfos_6682_ = lean_ctor_get(v___y_6622_, 4);
if (v_isShared_6670_ == 0)
{
v___x_6684_ = v___x_6669_;
goto v_reusejp_6683_;
}
else
{
lean_object* v_reuseFailAlloc_6698_; 
v_reuseFailAlloc_6698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6698_, 0, v_str_6665_);
lean_ctor_set(v_reuseFailAlloc_6698_, 1, v_startPos_6666_);
lean_ctor_set(v_reuseFailAlloc_6698_, 2, v_stopPos_6667_);
v___x_6684_ = v_reuseFailAlloc_6698_;
goto v_reusejp_6683_;
}
v_reusejp_6683_:
{
uint8_t v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; uint8_t v___x_6690_; 
v___x_6685_ = 1;
lean_inc_ref(v___x_6684_);
v___x_6686_ = l_Lean_Fmt_parseComments(v_lineInfos_6682_, v_val_6661_, v___x_6685_, v___x_6684_);
v___x_6687_ = lean_unsigned_to_nat(0u);
v___x_6688_ = lean_array_get_size(v___x_6686_);
v___x_6689_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines___closed__1));
v___x_6690_ = lean_nat_dec_lt(v___x_6687_, v___x_6688_);
if (v___x_6690_ == 0)
{
lean_dec_ref(v___x_6686_);
v___y_6626_ = v___x_6684_;
v___y_6627_ = v___x_6689_;
goto v___jp_6625_;
}
else
{
uint8_t v___x_6691_; 
v___x_6691_ = lean_nat_dec_le(v___x_6688_, v___x_6688_);
if (v___x_6691_ == 0)
{
if (v___x_6690_ == 0)
{
lean_dec_ref(v___x_6686_);
v___y_6626_ = v___x_6684_;
v___y_6627_ = v___x_6689_;
goto v___jp_6625_;
}
else
{
size_t v___x_6692_; size_t v___x_6693_; lean_object* v___x_6694_; 
v___x_6692_ = ((size_t)0ULL);
v___x_6693_ = lean_usize_of_nat(v___x_6688_);
v___x_6694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v___x_6686_, v___x_6692_, v___x_6693_, v___x_6689_);
lean_dec_ref(v___x_6686_);
v___y_6626_ = v___x_6684_;
v___y_6627_ = v___x_6694_;
goto v___jp_6625_;
}
}
else
{
size_t v___x_6695_; size_t v___x_6696_; lean_object* v___x_6697_; 
v___x_6695_ = ((size_t)0ULL);
v___x_6696_ = lean_usize_of_nat(v___x_6688_);
v___x_6697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__8(v___x_6686_, v___x_6695_, v___x_6696_, v___x_6689_);
lean_dec_ref(v___x_6686_);
v___y_6626_ = v___x_6684_;
v___y_6627_ = v___x_6697_;
goto v___jp_6625_;
}
}
}
}
}
v___jp_6700_:
{
if (v___x_6699_ == 0)
{
v___y_6672_ = v___x_6699_;
goto v___jp_6671_;
}
else
{
v___y_6672_ = v___y_6701_;
goto v___jp_6671_;
}
}
}
}
}
else
{
lean_object* v___x_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; 
lean_dec(v___x_6660_);
lean_dec_ref(v_trailing_6621_);
v___x_6706_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__0));
v___x_6707_ = ((lean_object*)(l_Lean_Fmt_fmtLeadingWithRetainedNewlinesAndComments___lam__0___closed__1));
v___x_6708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6708_, 0, v_trailingTk_6620_);
lean_ctor_set(v___x_6708_, 1, v___x_6706_);
lean_ctor_set(v___x_6708_, 2, v___x_6707_);
v___x_6709_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_6709_, 0, v___x_6708_);
v___x_6710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6710_, 0, v___x_6709_);
lean_ctor_set(v___x_6710_, 1, v___y_6623_);
return v___x_6710_;
}
v___jp_6625_:
{
lean_object* v___x_6628_; lean_object* v_snd_6629_; uint8_t v___x_6630_; 
v___x_6628_ = l___private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines(v___y_6627_, v___y_6626_, v___x_6624_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v___y_6627_);
v_snd_6629_ = lean_ctor_get(v___x_6628_, 1);
lean_inc(v_snd_6629_);
v___x_6630_ = lean_unbox(v_snd_6629_);
lean_dec(v_snd_6629_);
if (v___x_6630_ == 0)
{
if (v_atleastOneNewline_6619_ == 0)
{
lean_object* v_fst_6631_; lean_object* v___x_6633_; uint8_t v_isShared_6634_; uint8_t v_isSharedCheck_6638_; 
v_fst_6631_ = lean_ctor_get(v___x_6628_, 0);
v_isSharedCheck_6638_ = !lean_is_exclusive(v___x_6628_);
if (v_isSharedCheck_6638_ == 0)
{
lean_object* v_unused_6639_; 
v_unused_6639_ = lean_ctor_get(v___x_6628_, 1);
lean_dec(v_unused_6639_);
v___x_6633_ = v___x_6628_;
v_isShared_6634_ = v_isSharedCheck_6638_;
goto v_resetjp_6632_;
}
else
{
lean_inc(v_fst_6631_);
lean_dec(v___x_6628_);
v___x_6633_ = lean_box(0);
v_isShared_6634_ = v_isSharedCheck_6638_;
goto v_resetjp_6632_;
}
v_resetjp_6632_:
{
lean_object* v___x_6636_; 
if (v_isShared_6634_ == 0)
{
lean_ctor_set(v___x_6633_, 1, v___y_6623_);
v___x_6636_ = v___x_6633_;
goto v_reusejp_6635_;
}
else
{
lean_object* v_reuseFailAlloc_6637_; 
v_reuseFailAlloc_6637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6637_, 0, v_fst_6631_);
lean_ctor_set(v_reuseFailAlloc_6637_, 1, v___y_6623_);
v___x_6636_ = v_reuseFailAlloc_6637_;
goto v_reusejp_6635_;
}
v_reusejp_6635_:
{
return v___x_6636_;
}
}
}
else
{
lean_object* v_fst_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6649_; 
v_fst_6640_ = lean_ctor_get(v___x_6628_, 0);
v_isSharedCheck_6649_ = !lean_is_exclusive(v___x_6628_);
if (v_isSharedCheck_6649_ == 0)
{
lean_object* v_unused_6650_; 
v_unused_6650_ = lean_ctor_get(v___x_6628_, 1);
lean_dec(v_unused_6650_);
v___x_6642_ = v___x_6628_;
v_isShared_6643_ = v_isSharedCheck_6649_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_fst_6640_);
lean_dec(v___x_6628_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6649_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6647_; 
v___x_6644_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Basic_0__Lean_Fmt_fmtCommentsWithRetainedNewlines_spec__4___redArg___closed__0);
v___x_6645_ = lean_array_push(v_fst_6640_, v___x_6644_);
if (v_isShared_6643_ == 0)
{
lean_ctor_set(v___x_6642_, 1, v___y_6623_);
lean_ctor_set(v___x_6642_, 0, v___x_6645_);
v___x_6647_ = v___x_6642_;
goto v_reusejp_6646_;
}
else
{
lean_object* v_reuseFailAlloc_6648_; 
v_reuseFailAlloc_6648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6648_, 0, v___x_6645_);
lean_ctor_set(v_reuseFailAlloc_6648_, 1, v___y_6623_);
v___x_6647_ = v_reuseFailAlloc_6648_;
goto v_reusejp_6646_;
}
v_reusejp_6646_:
{
return v___x_6647_;
}
}
}
}
else
{
lean_object* v_fst_6651_; lean_object* v___x_6653_; uint8_t v_isShared_6654_; uint8_t v_isSharedCheck_6658_; 
v_fst_6651_ = lean_ctor_get(v___x_6628_, 0);
v_isSharedCheck_6658_ = !lean_is_exclusive(v___x_6628_);
if (v_isSharedCheck_6658_ == 0)
{
lean_object* v_unused_6659_; 
v_unused_6659_ = lean_ctor_get(v___x_6628_, 1);
lean_dec(v_unused_6659_);
v___x_6653_ = v___x_6628_;
v_isShared_6654_ = v_isSharedCheck_6658_;
goto v_resetjp_6652_;
}
else
{
lean_inc(v_fst_6651_);
lean_dec(v___x_6628_);
v___x_6653_ = lean_box(0);
v_isShared_6654_ = v_isSharedCheck_6658_;
goto v_resetjp_6652_;
}
v_resetjp_6652_:
{
lean_object* v___x_6656_; 
if (v_isShared_6654_ == 0)
{
lean_ctor_set(v___x_6653_, 1, v___y_6623_);
v___x_6656_ = v___x_6653_;
goto v_reusejp_6655_;
}
else
{
lean_object* v_reuseFailAlloc_6657_; 
v_reuseFailAlloc_6657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6657_, 0, v_fst_6651_);
lean_ctor_set(v_reuseFailAlloc_6657_, 1, v___y_6623_);
v___x_6656_ = v_reuseFailAlloc_6657_;
goto v_reusejp_6655_;
}
v_reusejp_6655_:
{
return v___x_6656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed(lean_object* v_atleastOneNewline_6711_, lean_object* v_trailingTk_6712_, lean_object* v_trailing_6713_, lean_object* v___y_6714_, lean_object* v___y_6715_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6716_; lean_object* v_res_6717_; 
v_atleastOneNewline_boxed_6716_ = lean_unbox(v_atleastOneNewline_6711_);
v_res_6717_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0(v_atleastOneNewline_boxed_6716_, v_trailingTk_6712_, v_trailing_6713_, v___y_6714_, v___y_6715_);
lean_dec_ref(v___y_6714_);
return v_res_6717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(lean_object* v_stx_6718_, uint8_t v_atleastOneNewline_6719_, lean_object* v_a_6720_, lean_object* v_a_6721_){
_start:
{
lean_object* v___x_6722_; lean_object* v___f_6723_; lean_object* v___x_6724_; 
v___x_6722_ = lean_box(v_atleastOneNewline_6719_);
v___f_6723_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___lam__0___boxed), 5, 1);
lean_closure_set(v___f_6723_, 0, v___x_6722_);
v___x_6724_ = l_Lean_Fmt_fmtTrailingWhitespace(v_stx_6718_, v___f_6723_, v_a_6720_, v_a_6721_);
return v___x_6724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments___boxed(lean_object* v_stx_6725_, lean_object* v_atleastOneNewline_6726_, lean_object* v_a_6727_, lean_object* v_a_6728_){
_start:
{
uint8_t v_atleastOneNewline_boxed_6729_; lean_object* v_res_6730_; 
v_atleastOneNewline_boxed_6729_ = lean_unbox(v_atleastOneNewline_6726_);
v_res_6730_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v_stx_6725_, v_atleastOneNewline_boxed_6729_, v_a_6727_, v_a_6728_);
lean_dec_ref(v_a_6727_);
return v_res_6730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(lean_object* v_upperBound_6731_, lean_object* v_stxs_6732_, lean_object* v_f_6733_, lean_object* v___x_6734_, lean_object* v_a_6735_, lean_object* v_b_6736_, lean_object* v___y_6737_, lean_object* v___y_6738_){
_start:
{
uint8_t v___x_6739_; 
v___x_6739_ = lean_nat_dec_lt(v_a_6735_, v_upperBound_6731_);
if (v___x_6739_ == 0)
{
lean_object* v___x_6740_; 
lean_dec(v_a_6735_);
lean_dec_ref(v_f_6733_);
v___x_6740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6740_, 0, v_b_6736_);
lean_ctor_set(v___x_6740_, 1, v___y_6738_);
return v___x_6740_;
}
else
{
lean_object* v___x_6741_; lean_object* v___x_6742_; 
v___x_6741_ = lean_array_fget_borrowed(v_stxs_6732_, v_a_6735_);
lean_inc_ref(v_f_6733_);
lean_inc_ref(v___y_6737_);
lean_inc(v___x_6741_);
v___x_6742_ = lean_apply_3(v_f_6733_, v___x_6741_, v___y_6737_, v___y_6738_);
if (lean_obj_tag(v___x_6742_) == 0)
{
lean_object* v_a_6743_; lean_object* v_a_6744_; lean_object* v___x_6745_; lean_object* v___y_6747_; lean_object* v___x_6772_; uint8_t v___x_6773_; 
v_a_6743_ = lean_ctor_get(v___x_6742_, 0);
lean_inc(v_a_6743_);
v_a_6744_ = lean_ctor_get(v___x_6742_, 1);
lean_inc(v_a_6744_);
lean_dec_ref_known(v___x_6742_, 2);
v___x_6745_ = lean_unsigned_to_nat(1u);
v___x_6772_ = lean_nat_sub(v___x_6734_, v___x_6745_);
v___x_6773_ = lean_nat_dec_lt(v_a_6735_, v___x_6772_);
lean_dec(v___x_6772_);
if (v___x_6773_ == 0)
{
lean_object* v___x_6774_; lean_object* v___x_6775_; 
v___x_6774_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_6775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6736_, v_a_6743_, v___x_6774_, v___y_6737_, v_a_6744_);
v___y_6747_ = v___x_6775_;
goto v___jp_6746_;
}
else
{
lean_object* v___x_6776_; 
lean_inc(v___x_6741_);
v___x_6776_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___x_6741_, v___x_6773_, v___y_6737_, v_a_6744_);
if (lean_obj_tag(v___x_6776_) == 0)
{
lean_object* v_a_6777_; lean_object* v_a_6778_; lean_object* v___x_6779_; 
v_a_6777_ = lean_ctor_get(v___x_6776_, 0);
lean_inc(v_a_6777_);
v_a_6778_ = lean_ctor_get(v___x_6776_, 1);
lean_inc(v_a_6778_);
lean_dec_ref_known(v___x_6776_, 2);
v___x_6779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines_spec__0___redArg___lam__0(v_b_6736_, v_a_6743_, v_a_6777_, v___y_6737_, v_a_6778_);
v___y_6747_ = v___x_6779_;
goto v___jp_6746_;
}
else
{
lean_object* v_a_6780_; lean_object* v_a_6781_; lean_object* v___x_6783_; uint8_t v_isShared_6784_; uint8_t v_isSharedCheck_6788_; 
lean_dec(v_a_6743_);
lean_dec_ref(v_b_6736_);
lean_dec(v_a_6735_);
lean_dec_ref(v_f_6733_);
v_a_6780_ = lean_ctor_get(v___x_6776_, 0);
v_a_6781_ = lean_ctor_get(v___x_6776_, 1);
v_isSharedCheck_6788_ = !lean_is_exclusive(v___x_6776_);
if (v_isSharedCheck_6788_ == 0)
{
v___x_6783_ = v___x_6776_;
v_isShared_6784_ = v_isSharedCheck_6788_;
goto v_resetjp_6782_;
}
else
{
lean_inc(v_a_6781_);
lean_inc(v_a_6780_);
lean_dec(v___x_6776_);
v___x_6783_ = lean_box(0);
v_isShared_6784_ = v_isSharedCheck_6788_;
goto v_resetjp_6782_;
}
v_resetjp_6782_:
{
lean_object* v___x_6786_; 
if (v_isShared_6784_ == 0)
{
v___x_6786_ = v___x_6783_;
goto v_reusejp_6785_;
}
else
{
lean_object* v_reuseFailAlloc_6787_; 
v_reuseFailAlloc_6787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6787_, 0, v_a_6780_);
lean_ctor_set(v_reuseFailAlloc_6787_, 1, v_a_6781_);
v___x_6786_ = v_reuseFailAlloc_6787_;
goto v_reusejp_6785_;
}
v_reusejp_6785_:
{
return v___x_6786_;
}
}
}
}
v___jp_6746_:
{
if (lean_obj_tag(v___y_6747_) == 0)
{
lean_object* v_a_6748_; 
v_a_6748_ = lean_ctor_get(v___y_6747_, 0);
lean_inc(v_a_6748_);
if (lean_obj_tag(v_a_6748_) == 0)
{
lean_object* v_a_6749_; lean_object* v___x_6751_; uint8_t v_isShared_6752_; uint8_t v_isSharedCheck_6757_; 
lean_dec(v_a_6735_);
lean_dec_ref(v_f_6733_);
v_a_6749_ = lean_ctor_get(v___y_6747_, 1);
v_isSharedCheck_6757_ = !lean_is_exclusive(v___y_6747_);
if (v_isSharedCheck_6757_ == 0)
{
lean_object* v_unused_6758_; 
v_unused_6758_ = lean_ctor_get(v___y_6747_, 0);
lean_dec(v_unused_6758_);
v___x_6751_ = v___y_6747_;
v_isShared_6752_ = v_isSharedCheck_6757_;
goto v_resetjp_6750_;
}
else
{
lean_inc(v_a_6749_);
lean_dec(v___y_6747_);
v___x_6751_ = lean_box(0);
v_isShared_6752_ = v_isSharedCheck_6757_;
goto v_resetjp_6750_;
}
v_resetjp_6750_:
{
lean_object* v_a_6753_; lean_object* v___x_6755_; 
v_a_6753_ = lean_ctor_get(v_a_6748_, 0);
lean_inc(v_a_6753_);
lean_dec_ref_known(v_a_6748_, 1);
if (v_isShared_6752_ == 0)
{
lean_ctor_set(v___x_6751_, 0, v_a_6753_);
v___x_6755_ = v___x_6751_;
goto v_reusejp_6754_;
}
else
{
lean_object* v_reuseFailAlloc_6756_; 
v_reuseFailAlloc_6756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6756_, 0, v_a_6753_);
lean_ctor_set(v_reuseFailAlloc_6756_, 1, v_a_6749_);
v___x_6755_ = v_reuseFailAlloc_6756_;
goto v_reusejp_6754_;
}
v_reusejp_6754_:
{
return v___x_6755_;
}
}
}
else
{
lean_object* v_a_6759_; lean_object* v_a_6760_; lean_object* v___x_6761_; 
v_a_6759_ = lean_ctor_get(v___y_6747_, 1);
lean_inc(v_a_6759_);
lean_dec_ref_known(v___y_6747_, 2);
v_a_6760_ = lean_ctor_get(v_a_6748_, 0);
lean_inc(v_a_6760_);
lean_dec_ref_known(v_a_6748_, 1);
v___x_6761_ = lean_nat_add(v_a_6735_, v___x_6745_);
lean_dec(v_a_6735_);
v_a_6735_ = v___x_6761_;
v_b_6736_ = v_a_6760_;
v___y_6738_ = v_a_6759_;
goto _start;
}
}
else
{
lean_object* v_a_6763_; lean_object* v_a_6764_; lean_object* v___x_6766_; uint8_t v_isShared_6767_; uint8_t v_isSharedCheck_6771_; 
lean_dec(v_a_6735_);
lean_dec_ref(v_f_6733_);
v_a_6763_ = lean_ctor_get(v___y_6747_, 0);
v_a_6764_ = lean_ctor_get(v___y_6747_, 1);
v_isSharedCheck_6771_ = !lean_is_exclusive(v___y_6747_);
if (v_isSharedCheck_6771_ == 0)
{
v___x_6766_ = v___y_6747_;
v_isShared_6767_ = v_isSharedCheck_6771_;
goto v_resetjp_6765_;
}
else
{
lean_inc(v_a_6764_);
lean_inc(v_a_6763_);
lean_dec(v___y_6747_);
v___x_6766_ = lean_box(0);
v_isShared_6767_ = v_isSharedCheck_6771_;
goto v_resetjp_6765_;
}
v_resetjp_6765_:
{
lean_object* v___x_6769_; 
if (v_isShared_6767_ == 0)
{
v___x_6769_ = v___x_6766_;
goto v_reusejp_6768_;
}
else
{
lean_object* v_reuseFailAlloc_6770_; 
v_reuseFailAlloc_6770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6770_, 0, v_a_6763_);
lean_ctor_set(v_reuseFailAlloc_6770_, 1, v_a_6764_);
v___x_6769_ = v_reuseFailAlloc_6770_;
goto v_reusejp_6768_;
}
v_reusejp_6768_:
{
return v___x_6769_;
}
}
}
}
}
else
{
lean_object* v_a_6789_; lean_object* v_a_6790_; lean_object* v___x_6792_; uint8_t v_isShared_6793_; uint8_t v_isSharedCheck_6797_; 
lean_dec_ref(v_b_6736_);
lean_dec(v_a_6735_);
lean_dec_ref(v_f_6733_);
v_a_6789_ = lean_ctor_get(v___x_6742_, 0);
v_a_6790_ = lean_ctor_get(v___x_6742_, 1);
v_isSharedCheck_6797_ = !lean_is_exclusive(v___x_6742_);
if (v_isSharedCheck_6797_ == 0)
{
v___x_6792_ = v___x_6742_;
v_isShared_6793_ = v_isSharedCheck_6797_;
goto v_resetjp_6791_;
}
else
{
lean_inc(v_a_6790_);
lean_inc(v_a_6789_);
lean_dec(v___x_6742_);
v___x_6792_ = lean_box(0);
v_isShared_6793_ = v_isSharedCheck_6797_;
goto v_resetjp_6791_;
}
v_resetjp_6791_:
{
lean_object* v___x_6795_; 
if (v_isShared_6793_ == 0)
{
v___x_6795_ = v___x_6792_;
goto v_reusejp_6794_;
}
else
{
lean_object* v_reuseFailAlloc_6796_; 
v_reuseFailAlloc_6796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6796_, 0, v_a_6789_);
lean_ctor_set(v_reuseFailAlloc_6796_, 1, v_a_6790_);
v___x_6795_ = v_reuseFailAlloc_6796_;
goto v_reusejp_6794_;
}
v_reusejp_6794_:
{
return v___x_6795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg___boxed(lean_object* v_upperBound_6798_, lean_object* v_stxs_6799_, lean_object* v_f_6800_, lean_object* v___x_6801_, lean_object* v_a_6802_, lean_object* v_b_6803_, lean_object* v___y_6804_, lean_object* v___y_6805_){
_start:
{
lean_object* v_res_6806_; 
v_res_6806_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6798_, v_stxs_6799_, v_f_6800_, v___x_6801_, v_a_6802_, v_b_6803_, v___y_6804_, v___y_6805_);
lean_dec_ref(v___y_6804_);
lean_dec(v___x_6801_);
lean_dec_ref(v_stxs_6799_);
lean_dec(v_upperBound_6798_);
return v_res_6806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(lean_object* v_f_6807_, lean_object* v_stxs_6808_, lean_object* v_a_6809_, lean_object* v_a_6810_){
_start:
{
lean_object* v___x_6811_; lean_object* v___x_6812_; uint8_t v___x_6813_; 
v___x_6811_ = lean_array_get_size(v_stxs_6808_);
v___x_6812_ = lean_unsigned_to_nat(1u);
v___x_6813_ = lean_nat_dec_eq(v___x_6811_, v___x_6812_);
if (v___x_6813_ == 0)
{
lean_object* v___x_6814_; lean_object* v_acc_6815_; lean_object* v___x_6816_; 
v___x_6814_ = lean_unsigned_to_nat(0u);
v_acc_6815_ = ((lean_object*)(l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlines___closed__0));
v___x_6816_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v___x_6811_, v_stxs_6808_, v_f_6807_, v___x_6811_, v___x_6814_, v_acc_6815_, v_a_6809_, v_a_6810_);
if (lean_obj_tag(v___x_6816_) == 0)
{
lean_object* v_a_6817_; lean_object* v_a_6818_; lean_object* v___x_6820_; uint8_t v_isShared_6821_; uint8_t v_isSharedCheck_6826_; 
v_a_6817_ = lean_ctor_get(v___x_6816_, 0);
v_a_6818_ = lean_ctor_get(v___x_6816_, 1);
v_isSharedCheck_6826_ = !lean_is_exclusive(v___x_6816_);
if (v_isSharedCheck_6826_ == 0)
{
v___x_6820_ = v___x_6816_;
v_isShared_6821_ = v_isSharedCheck_6826_;
goto v_resetjp_6819_;
}
else
{
lean_inc(v_a_6818_);
lean_inc(v_a_6817_);
lean_dec(v___x_6816_);
v___x_6820_ = lean_box(0);
v_isShared_6821_ = v_isSharedCheck_6826_;
goto v_resetjp_6819_;
}
v_resetjp_6819_:
{
lean_object* v___x_6822_; lean_object* v___x_6824_; 
v___x_6822_ = l_Lean_Fmt_TaggedDoc_join(v_a_6817_);
if (v_isShared_6821_ == 0)
{
lean_ctor_set(v___x_6820_, 0, v___x_6822_);
v___x_6824_ = v___x_6820_;
goto v_reusejp_6823_;
}
else
{
lean_object* v_reuseFailAlloc_6825_; 
v_reuseFailAlloc_6825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6825_, 0, v___x_6822_);
lean_ctor_set(v_reuseFailAlloc_6825_, 1, v_a_6818_);
v___x_6824_ = v_reuseFailAlloc_6825_;
goto v_reusejp_6823_;
}
v_reusejp_6823_:
{
return v___x_6824_;
}
}
}
else
{
lean_object* v_a_6827_; lean_object* v_a_6828_; lean_object* v___x_6830_; uint8_t v_isShared_6831_; uint8_t v_isSharedCheck_6835_; 
v_a_6827_ = lean_ctor_get(v___x_6816_, 0);
v_a_6828_ = lean_ctor_get(v___x_6816_, 1);
v_isSharedCheck_6835_ = !lean_is_exclusive(v___x_6816_);
if (v_isSharedCheck_6835_ == 0)
{
v___x_6830_ = v___x_6816_;
v_isShared_6831_ = v_isSharedCheck_6835_;
goto v_resetjp_6829_;
}
else
{
lean_inc(v_a_6828_);
lean_inc(v_a_6827_);
lean_dec(v___x_6816_);
v___x_6830_ = lean_box(0);
v_isShared_6831_ = v_isSharedCheck_6835_;
goto v_resetjp_6829_;
}
v_resetjp_6829_:
{
lean_object* v___x_6833_; 
if (v_isShared_6831_ == 0)
{
v___x_6833_ = v___x_6830_;
goto v_reusejp_6832_;
}
else
{
lean_object* v_reuseFailAlloc_6834_; 
v_reuseFailAlloc_6834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6834_, 0, v_a_6827_);
lean_ctor_set(v_reuseFailAlloc_6834_, 1, v_a_6828_);
v___x_6833_ = v_reuseFailAlloc_6834_;
goto v_reusejp_6832_;
}
v_reusejp_6832_:
{
return v___x_6833_;
}
}
}
}
else
{
lean_object* v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; 
v___x_6836_ = lean_box(0);
v___x_6837_ = lean_unsigned_to_nat(0u);
v___x_6838_ = lean_array_get_borrowed(v___x_6836_, v_stxs_6808_, v___x_6837_);
lean_inc_ref(v_a_6809_);
lean_inc(v___x_6838_);
v___x_6839_ = lean_apply_3(v_f_6807_, v___x_6838_, v_a_6809_, v_a_6810_);
return v___x_6839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith___boxed(lean_object* v_f_6840_, lean_object* v_stxs_6841_, lean_object* v_a_6842_, lean_object* v_a_6843_){
_start:
{
lean_object* v_res_6844_; 
v_res_6844_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v_f_6840_, v_stxs_6841_, v_a_6842_, v_a_6843_);
lean_dec_ref(v_a_6842_);
lean_dec_ref(v_stxs_6841_);
return v_res_6844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(lean_object* v_upperBound_6845_, lean_object* v_stxs_6846_, lean_object* v_f_6847_, lean_object* v___x_6848_, lean_object* v_inst_6849_, lean_object* v_R_6850_, lean_object* v_a_6851_, lean_object* v_b_6852_, lean_object* v_c_6853_, lean_object* v___y_6854_, lean_object* v___y_6855_){
_start:
{
lean_object* v___x_6856_; 
v___x_6856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___redArg(v_upperBound_6845_, v_stxs_6846_, v_f_6847_, v___x_6848_, v_a_6851_, v_b_6852_, v___y_6854_, v___y_6855_);
return v___x_6856_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0___boxed(lean_object* v_upperBound_6857_, lean_object* v_stxs_6858_, lean_object* v_f_6859_, lean_object* v___x_6860_, lean_object* v_inst_6861_, lean_object* v_R_6862_, lean_object* v_a_6863_, lean_object* v_b_6864_, lean_object* v_c_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_){
_start:
{
lean_object* v_res_6868_; 
v_res_6868_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith_spec__0(v_upperBound_6857_, v_stxs_6858_, v_f_6859_, v___x_6860_, v_inst_6861_, v_R_6862_, v_a_6863_, v_b_6864_, v_c_6865_, v___y_6866_, v___y_6867_);
lean_dec_ref(v___y_6866_);
lean_dec(v___x_6860_);
lean_dec_ref(v_stxs_6858_);
lean_dec(v_upperBound_6857_);
return v_res_6868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_stxs_6869_, lean_object* v_a_6870_, lean_object* v_a_6871_){
_start:
{
lean_object* v___x_6872_; lean_object* v___x_6873_; 
v___x_6872_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmt___boxed), 3, 0);
v___x_6873_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndCommentsWith(v___x_6872_, v_stxs_6869_, v_a_6870_, v_a_6871_);
return v___x_6873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_stxs_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_){
_start:
{
lean_object* v_res_6877_; 
v_res_6877_ = l_Lean_Fmt_fmtArrayWithRetainedIntermediateNewlinesAndComments(v_stxs_6874_, v_a_6875_, v_a_6876_);
lean_dec_ref(v_a_6875_);
lean_dec_ref(v_stxs_6874_);
return v_res_6877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___redArg(lean_object* v_x_6878_){
_start:
{
if (lean_obj_tag(v_x_6878_) == 0)
{
lean_object* v___x_6879_; 
v___x_6879_ = lean_unsigned_to_nat(0u);
return v___x_6879_;
}
else
{
lean_object* v___x_6880_; 
v___x_6880_ = lean_unsigned_to_nat(1u);
return v___x_6880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___redArg___boxed(lean_object* v_x_6881_){
_start:
{
lean_object* v_res_6882_; 
v_res_6882_ = l_Lean_Fmt_TrailingGroup_ctorIdx___redArg(v_x_6881_);
lean_dec_ref(v_x_6881_);
return v_res_6882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx(lean_object* v_sep_6883_, lean_object* v_x_6884_){
_start:
{
lean_object* v___x_6885_; 
v___x_6885_ = l_Lean_Fmt_TrailingGroup_ctorIdx___redArg(v_x_6884_);
return v___x_6885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorIdx___boxed(lean_object* v_sep_6886_, lean_object* v_x_6887_){
_start:
{
lean_object* v_res_6888_; 
v_res_6888_ = l_Lean_Fmt_TrailingGroup_ctorIdx(v_sep_6886_, v_x_6887_);
lean_dec_ref(v_x_6887_);
lean_dec_ref(v_sep_6886_);
return v_res_6888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___redArg(lean_object* v_t_6889_, lean_object* v_k_6890_){
_start:
{
lean_object* v_g_6891_; lean_object* v___x_6892_; 
v_g_6891_ = lean_ctor_get(v_t_6889_, 0);
lean_inc_ref(v_g_6891_);
lean_dec_ref(v_t_6889_);
v___x_6892_ = lean_apply_1(v_k_6890_, v_g_6891_);
return v___x_6892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim(lean_object* v_sep_6893_, lean_object* v_motive_6894_, lean_object* v_ctorIdx_6895_, lean_object* v_t_6896_, lean_object* v_h_6897_, lean_object* v_k_6898_){
_start:
{
lean_object* v___x_6899_; 
v___x_6899_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6896_, v_k_6898_);
return v___x_6899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_ctorElim___boxed(lean_object* v_sep_6900_, lean_object* v_motive_6901_, lean_object* v_ctorIdx_6902_, lean_object* v_t_6903_, lean_object* v_h_6904_, lean_object* v_k_6905_){
_start:
{
lean_object* v_res_6906_; 
v_res_6906_ = l_Lean_Fmt_TrailingGroup_ctorElim(v_sep_6900_, v_motive_6901_, v_ctorIdx_6902_, v_t_6903_, v_h_6904_, v_k_6905_);
lean_dec(v_ctorIdx_6902_);
lean_dec_ref(v_sep_6900_);
return v_res_6906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___redArg(lean_object* v_t_6907_, lean_object* v_group_6908_){
_start:
{
lean_object* v___x_6909_; 
v___x_6909_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6907_, v_group_6908_);
return v___x_6909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim(lean_object* v_sep_6910_, lean_object* v_motive_6911_, lean_object* v_t_6912_, lean_object* v_h_6913_, lean_object* v_group_6914_){
_start:
{
lean_object* v___x_6915_; 
v___x_6915_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6912_, v_group_6914_);
return v___x_6915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_group_elim___boxed(lean_object* v_sep_6916_, lean_object* v_motive_6917_, lean_object* v_t_6918_, lean_object* v_h_6919_, lean_object* v_group_6920_){
_start:
{
lean_object* v_res_6921_; 
v_res_6921_ = l_Lean_Fmt_TrailingGroup_group_elim(v_sep_6916_, v_motive_6917_, v_t_6918_, v_h_6919_, v_group_6920_);
lean_dec_ref(v_sep_6916_);
return v_res_6921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___redArg(lean_object* v_t_6922_, lean_object* v_trailing_6923_){
_start:
{
lean_object* v___x_6924_; 
v___x_6924_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6922_, v_trailing_6923_);
return v___x_6924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim(lean_object* v_sep_6925_, lean_object* v_motive_6926_, lean_object* v_t_6927_, lean_object* v_h_6928_, lean_object* v_trailing_6929_){
_start:
{
lean_object* v___x_6930_; 
v___x_6930_ = l_Lean_Fmt_TrailingGroup_ctorElim___redArg(v_t_6927_, v_trailing_6929_);
return v___x_6930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TrailingGroup_trailing_elim___boxed(lean_object* v_sep_6931_, lean_object* v_motive_6932_, lean_object* v_t_6933_, lean_object* v_h_6934_, lean_object* v_trailing_6935_){
_start:
{
lean_object* v_res_6936_; 
v_res_6936_ = l_Lean_Fmt_TrailingGroup_trailing_elim(v_sep_6931_, v_motive_6932_, v_t_6933_, v_h_6934_, v_trailing_6935_);
lean_dec_ref(v_sep_6931_);
return v_res_6936_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_6937_; lean_object* v___x_6938_; 
v___x_6937_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_6938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6938_, 0, v___x_6937_);
return v___x_6938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg(){
_start:
{
lean_object* v___x_6940_; 
v___x_6940_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___closed__0);
return v___x_6940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg___boxed(lean_object* v___dummy_6941_){
_start:
{
lean_object* v_res_6942_; 
v_res_6942_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v_res_6942_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0(void){
_start:
{
lean_object* v___x_6943_; 
v___x_6943_ = l_Lean_Fmt_instInhabitedTrailingGroup_default___redArg();
return v___x_6943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default(lean_object* v_sep_6944_){
_start:
{
lean_object* v___x_6945_; 
v___x_6945_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup_default___boxed(lean_object* v_sep_6946_){
_start:
{
lean_object* v_res_6947_; 
v_res_6947_ = l_Lean_Fmt_instInhabitedTrailingGroup_default(v_sep_6946_);
lean_dec_ref(v_sep_6946_);
return v_res_6947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg(){
_start:
{
lean_object* v___x_6949_; 
v___x_6949_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___redArg___boxed(lean_object* v___dummy_6950_){
_start:
{
lean_object* v_res_6951_; 
v_res_6951_ = l_Lean_Fmt_instInhabitedTrailingGroup___redArg();
return v_res_6951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup(lean_object* v_a_6952_){
_start:
{
lean_object* v___x_6953_; 
v___x_6953_ = lean_obj_once(&l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0, &l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0_once, _init_l_Lean_Fmt_instInhabitedTrailingGroup_default___closed__0);
return v___x_6953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTrailingGroup___boxed(lean_object* v_a_6954_){
_start:
{
lean_object* v_res_6955_; 
v_res_6955_ = l_Lean_Fmt_instInhabitedTrailingGroup(v_a_6954_);
lean_dec_ref(v_a_6954_);
return v_res_6955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(lean_object* v_upperBound_6956_, lean_object* v_elemsAndSeps_6957_, lean_object* v_pendingGroup_6958_, lean_object* v___x_6959_, lean_object* v_a_6960_, lean_object* v_b_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_){
_start:
{
lean_object* v_a_6965_; lean_object* v_a_6966_; uint8_t v___x_6970_; 
v___x_6970_ = lean_nat_dec_lt(v_a_6960_, v_upperBound_6956_);
if (v___x_6970_ == 0)
{
lean_object* v___x_6971_; 
lean_dec(v_a_6960_);
lean_dec_ref(v_pendingGroup_6958_);
v___x_6971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6971_, 0, v_b_6961_);
lean_ctor_set(v___x_6971_, 1, v___y_6963_);
return v___x_6971_;
}
else
{
lean_object* v___x_6972_; lean_object* v___x_6973_; 
v___x_6972_ = lean_array_fget_borrowed(v_elemsAndSeps_6957_, v_a_6960_);
lean_inc(v___x_6972_);
v___x_6973_ = l_Lean_Fmt_fmt(v___x_6972_, v___y_6962_, v___y_6963_);
if (lean_obj_tag(v___x_6973_) == 0)
{
lean_object* v_a_6974_; lean_object* v_a_6975_; lean_object* v_fst_6976_; lean_object* v_snd_6977_; lean_object* v___x_6979_; uint8_t v_isShared_6980_; uint8_t v_isSharedCheck_7024_; 
v_a_6974_ = lean_ctor_get(v___x_6973_, 0);
lean_inc(v_a_6974_);
v_a_6975_ = lean_ctor_get(v___x_6973_, 1);
lean_inc(v_a_6975_);
lean_dec_ref_known(v___x_6973_, 2);
v_fst_6976_ = lean_ctor_get(v_b_6961_, 0);
v_snd_6977_ = lean_ctor_get(v_b_6961_, 1);
v_isSharedCheck_7024_ = !lean_is_exclusive(v_b_6961_);
if (v_isSharedCheck_7024_ == 0)
{
v___x_6979_ = v_b_6961_;
v_isShared_6980_ = v_isSharedCheck_7024_;
goto v_resetjp_6978_;
}
else
{
lean_inc(v_snd_6977_);
lean_inc(v_fst_6976_);
lean_dec(v_b_6961_);
v___x_6979_ = lean_box(0);
v_isShared_6980_ = v_isSharedCheck_7024_;
goto v_resetjp_6978_;
}
v_resetjp_6978_:
{
lean_object* v___x_6981_; lean_object* v___x_6982_; lean_object* v___x_6983_; lean_object* v___y_6985_; uint8_t v___y_7013_; lean_object* v___x_7020_; lean_object* v___x_7021_; uint8_t v___x_7022_; 
v___x_6981_ = lean_unsigned_to_nat(0u);
v___x_6982_ = lean_box(0);
v___x_6983_ = lean_array_push(v_snd_6977_, v_a_6974_);
v___x_7020_ = lean_unsigned_to_nat(2u);
v___x_7021_ = lean_nat_mod(v_a_6960_, v___x_7020_);
v___x_7022_ = lean_nat_dec_eq(v___x_7021_, v___x_6981_);
lean_dec(v___x_7021_);
if (v___x_7022_ == 0)
{
v___y_7013_ = v___x_6970_;
goto v___jp_7012_;
}
else
{
uint8_t v___x_7023_; 
v___x_7023_ = 0;
v___y_7013_ = v___x_7023_;
goto v___jp_7012_;
}
v___jp_6984_:
{
uint8_t v___x_6986_; lean_object* v___x_6987_; 
v___x_6986_ = 0;
v___x_6987_ = l_Lean_Fmt_fmtTrailingWithRetainedNewlinesAndComments(v___y_6985_, v___x_6986_, v___y_6962_, v_a_6975_);
if (lean_obj_tag(v___x_6987_) == 0)
{
lean_object* v_a_6988_; lean_object* v_a_6989_; uint8_t v___x_6990_; 
v_a_6988_ = lean_ctor_get(v___x_6987_, 0);
lean_inc(v_a_6988_);
v_a_6989_ = lean_ctor_get(v___x_6987_, 1);
lean_inc(v_a_6989_);
lean_dec_ref_known(v___x_6987_, 2);
v___x_6990_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_6988_);
if (v___x_6990_ == 0)
{
lean_object* v___x_6991_; lean_object* v___x_6992_; lean_object* v___x_6993_; lean_object* v___x_6994_; lean_object* v___x_6996_; 
v___x_6991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6991_, 0, v___x_6983_);
v___x_6992_ = lean_array_push(v_fst_6976_, v___x_6991_);
v___x_6993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6993_, 0, v_a_6988_);
v___x_6994_ = lean_array_push(v___x_6992_, v___x_6993_);
lean_inc_ref(v_pendingGroup_6958_);
if (v_isShared_6980_ == 0)
{
lean_ctor_set(v___x_6979_, 1, v_pendingGroup_6958_);
lean_ctor_set(v___x_6979_, 0, v___x_6994_);
v___x_6996_ = v___x_6979_;
goto v_reusejp_6995_;
}
else
{
lean_object* v_reuseFailAlloc_6997_; 
v_reuseFailAlloc_6997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6997_, 0, v___x_6994_);
lean_ctor_set(v_reuseFailAlloc_6997_, 1, v_pendingGroup_6958_);
v___x_6996_ = v_reuseFailAlloc_6997_;
goto v_reusejp_6995_;
}
v_reusejp_6995_:
{
v_a_6965_ = v___x_6996_;
v_a_6966_ = v_a_6989_;
goto v___jp_6964_;
}
}
else
{
lean_object* v___x_6999_; 
lean_dec(v_a_6988_);
if (v_isShared_6980_ == 0)
{
lean_ctor_set(v___x_6979_, 1, v___x_6983_);
v___x_6999_ = v___x_6979_;
goto v_reusejp_6998_;
}
else
{
lean_object* v_reuseFailAlloc_7000_; 
v_reuseFailAlloc_7000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7000_, 0, v_fst_6976_);
lean_ctor_set(v_reuseFailAlloc_7000_, 1, v___x_6983_);
v___x_6999_ = v_reuseFailAlloc_7000_;
goto v_reusejp_6998_;
}
v_reusejp_6998_:
{
v_a_6965_ = v___x_6999_;
v_a_6966_ = v_a_6989_;
goto v___jp_6964_;
}
}
}
else
{
lean_object* v_a_7001_; lean_object* v_a_7002_; lean_object* v___x_7004_; uint8_t v_isShared_7005_; uint8_t v_isSharedCheck_7009_; 
lean_dec_ref(v___x_6983_);
lean_del_object(v___x_6979_);
lean_dec(v_fst_6976_);
lean_dec(v_a_6960_);
lean_dec_ref(v_pendingGroup_6958_);
v_a_7001_ = lean_ctor_get(v___x_6987_, 0);
v_a_7002_ = lean_ctor_get(v___x_6987_, 1);
v_isSharedCheck_7009_ = !lean_is_exclusive(v___x_6987_);
if (v_isSharedCheck_7009_ == 0)
{
v___x_7004_ = v___x_6987_;
v_isShared_7005_ = v_isSharedCheck_7009_;
goto v_resetjp_7003_;
}
else
{
lean_inc(v_a_7002_);
lean_inc(v_a_7001_);
lean_dec(v___x_6987_);
v___x_7004_ = lean_box(0);
v_isShared_7005_ = v_isSharedCheck_7009_;
goto v_resetjp_7003_;
}
v_resetjp_7003_:
{
lean_object* v___x_7007_; 
if (v_isShared_7005_ == 0)
{
v___x_7007_ = v___x_7004_;
goto v_reusejp_7006_;
}
else
{
lean_object* v_reuseFailAlloc_7008_; 
v_reuseFailAlloc_7008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7008_, 0, v_a_7001_);
lean_ctor_set(v_reuseFailAlloc_7008_, 1, v_a_7002_);
v___x_7007_ = v_reuseFailAlloc_7008_;
goto v_reusejp_7006_;
}
v_reusejp_7006_:
{
return v___x_7007_;
}
}
}
}
v___jp_7010_:
{
lean_object* v___x_7011_; 
v___x_7011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7011_, 0, v_fst_6976_);
lean_ctor_set(v___x_7011_, 1, v___x_6983_);
v_a_6965_ = v___x_7011_;
v_a_6966_ = v_a_6975_;
goto v___jp_6964_;
}
v___jp_7012_:
{
lean_object* v___x_7014_; lean_object* v___x_7015_; uint8_t v___x_7016_; 
v___x_7014_ = lean_unsigned_to_nat(1u);
v___x_7015_ = lean_nat_sub(v___x_6959_, v___x_7014_);
v___x_7016_ = lean_nat_dec_lt(v_a_6960_, v___x_7015_);
lean_dec(v___x_7015_);
if (v___x_7016_ == 0)
{
lean_del_object(v___x_6979_);
goto v___jp_7010_;
}
else
{
if (v___y_7013_ == 0)
{
lean_del_object(v___x_6979_);
goto v___jp_7010_;
}
else
{
uint8_t v___x_7017_; 
lean_inc(v___x_6972_);
v___x_7017_ = l_Lean_Syntax_matchesNull(v___x_6972_, v___x_6981_);
if (v___x_7017_ == 0)
{
lean_inc(v___x_6972_);
v___y_6985_ = v___x_6972_;
goto v___jp_6984_;
}
else
{
lean_object* v___x_7018_; lean_object* v___x_7019_; 
v___x_7018_ = lean_nat_sub(v_a_6960_, v___x_7014_);
v___x_7019_ = lean_array_get_borrowed(v___x_6982_, v_elemsAndSeps_6957_, v___x_7018_);
lean_dec(v___x_7018_);
lean_inc(v___x_7019_);
v___y_6985_ = v___x_7019_;
goto v___jp_6984_;
}
}
}
}
}
}
else
{
lean_object* v_a_7025_; lean_object* v_a_7026_; lean_object* v___x_7028_; uint8_t v_isShared_7029_; uint8_t v_isSharedCheck_7033_; 
lean_dec_ref(v_b_6961_);
lean_dec(v_a_6960_);
lean_dec_ref(v_pendingGroup_6958_);
v_a_7025_ = lean_ctor_get(v___x_6973_, 0);
v_a_7026_ = lean_ctor_get(v___x_6973_, 1);
v_isSharedCheck_7033_ = !lean_is_exclusive(v___x_6973_);
if (v_isSharedCheck_7033_ == 0)
{
v___x_7028_ = v___x_6973_;
v_isShared_7029_ = v_isSharedCheck_7033_;
goto v_resetjp_7027_;
}
else
{
lean_inc(v_a_7026_);
lean_inc(v_a_7025_);
lean_dec(v___x_6973_);
v___x_7028_ = lean_box(0);
v_isShared_7029_ = v_isSharedCheck_7033_;
goto v_resetjp_7027_;
}
v_resetjp_7027_:
{
lean_object* v___x_7031_; 
if (v_isShared_7029_ == 0)
{
v___x_7031_ = v___x_7028_;
goto v_reusejp_7030_;
}
else
{
lean_object* v_reuseFailAlloc_7032_; 
v_reuseFailAlloc_7032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7032_, 0, v_a_7025_);
lean_ctor_set(v_reuseFailAlloc_7032_, 1, v_a_7026_);
v___x_7031_ = v_reuseFailAlloc_7032_;
goto v_reusejp_7030_;
}
v_reusejp_7030_:
{
return v___x_7031_;
}
}
}
}
v___jp_6964_:
{
lean_object* v___x_6967_; lean_object* v___x_6968_; 
v___x_6967_ = lean_unsigned_to_nat(1u);
v___x_6968_ = lean_nat_add(v_a_6960_, v___x_6967_);
lean_dec(v_a_6960_);
v_a_6960_ = v___x_6968_;
v_b_6961_ = v_a_6965_;
v___y_6963_ = v_a_6966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg___boxed(lean_object* v_upperBound_7034_, lean_object* v_elemsAndSeps_7035_, lean_object* v_pendingGroup_7036_, lean_object* v___x_7037_, lean_object* v_a_7038_, lean_object* v_b_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_){
_start:
{
lean_object* v_res_7042_; 
v_res_7042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7034_, v_elemsAndSeps_7035_, v_pendingGroup_7036_, v___x_7037_, v_a_7038_, v_b_7039_, v___y_7040_, v___y_7041_);
lean_dec_ref(v___y_7040_);
lean_dec(v___x_7037_);
lean_dec_ref(v_elemsAndSeps_7035_);
lean_dec(v_upperBound_7034_);
return v_res_7042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(lean_object* v_sep_7047_, lean_object* v_stxs_7048_, lean_object* v_a_7049_, lean_object* v_a_7050_){
_start:
{
lean_object* v___x_7051_; lean_object* v___x_7052_; lean_object* v_acc_7053_; lean_object* v___x_7054_; lean_object* v___x_7055_; 
v___x_7051_ = lean_unsigned_to_nat(0u);
v___x_7052_ = lean_array_get_size(v_stxs_7048_);
v_acc_7053_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__0));
v___x_7054_ = ((lean_object*)(l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___closed__1));
v___x_7055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v___x_7052_, v_stxs_7048_, v_acc_7053_, v___x_7052_, v___x_7051_, v___x_7054_, v_a_7049_, v_a_7050_);
if (lean_obj_tag(v___x_7055_) == 0)
{
lean_object* v_a_7056_; lean_object* v_a_7057_; lean_object* v___x_7059_; uint8_t v_isShared_7060_; uint8_t v_isSharedCheck_7073_; 
v_a_7056_ = lean_ctor_get(v___x_7055_, 0);
v_a_7057_ = lean_ctor_get(v___x_7055_, 1);
v_isSharedCheck_7073_ = !lean_is_exclusive(v___x_7055_);
if (v_isSharedCheck_7073_ == 0)
{
v___x_7059_ = v___x_7055_;
v_isShared_7060_ = v_isSharedCheck_7073_;
goto v_resetjp_7058_;
}
else
{
lean_inc(v_a_7057_);
lean_inc(v_a_7056_);
lean_dec(v___x_7055_);
v___x_7059_ = lean_box(0);
v_isShared_7060_ = v_isSharedCheck_7073_;
goto v_resetjp_7058_;
}
v_resetjp_7058_:
{
lean_object* v_fst_7061_; lean_object* v_snd_7062_; lean_object* v___x_7063_; uint8_t v___x_7064_; 
v_fst_7061_ = lean_ctor_get(v_a_7056_, 0);
lean_inc(v_fst_7061_);
v_snd_7062_ = lean_ctor_get(v_a_7056_, 1);
lean_inc(v_snd_7062_);
lean_dec(v_a_7056_);
v___x_7063_ = lean_array_get_size(v_snd_7062_);
v___x_7064_ = lean_nat_dec_eq(v___x_7063_, v___x_7051_);
if (v___x_7064_ == 0)
{
lean_object* v___x_7065_; lean_object* v___x_7066_; lean_object* v___x_7068_; 
v___x_7065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7065_, 0, v_snd_7062_);
v___x_7066_ = lean_array_push(v_fst_7061_, v___x_7065_);
if (v_isShared_7060_ == 0)
{
lean_ctor_set(v___x_7059_, 0, v___x_7066_);
v___x_7068_ = v___x_7059_;
goto v_reusejp_7067_;
}
else
{
lean_object* v_reuseFailAlloc_7069_; 
v_reuseFailAlloc_7069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___x_7066_);
lean_ctor_set(v_reuseFailAlloc_7069_, 1, v_a_7057_);
v___x_7068_ = v_reuseFailAlloc_7069_;
goto v_reusejp_7067_;
}
v_reusejp_7067_:
{
return v___x_7068_;
}
}
else
{
lean_object* v___x_7071_; 
lean_dec(v_snd_7062_);
if (v_isShared_7060_ == 0)
{
lean_ctor_set(v___x_7059_, 0, v_fst_7061_);
v___x_7071_ = v___x_7059_;
goto v_reusejp_7070_;
}
else
{
lean_object* v_reuseFailAlloc_7072_; 
v_reuseFailAlloc_7072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7072_, 0, v_fst_7061_);
lean_ctor_set(v_reuseFailAlloc_7072_, 1, v_a_7057_);
v___x_7071_ = v_reuseFailAlloc_7072_;
goto v_reusejp_7070_;
}
v_reusejp_7070_:
{
return v___x_7071_;
}
}
}
}
else
{
lean_object* v_a_7074_; lean_object* v_a_7075_; lean_object* v___x_7077_; uint8_t v_isShared_7078_; uint8_t v_isSharedCheck_7082_; 
v_a_7074_ = lean_ctor_get(v___x_7055_, 0);
v_a_7075_ = lean_ctor_get(v___x_7055_, 1);
v_isSharedCheck_7082_ = !lean_is_exclusive(v___x_7055_);
if (v_isSharedCheck_7082_ == 0)
{
v___x_7077_ = v___x_7055_;
v_isShared_7078_ = v_isSharedCheck_7082_;
goto v_resetjp_7076_;
}
else
{
lean_inc(v_a_7075_);
lean_inc(v_a_7074_);
lean_dec(v___x_7055_);
v___x_7077_ = lean_box(0);
v_isShared_7078_ = v_isSharedCheck_7082_;
goto v_resetjp_7076_;
}
v_resetjp_7076_:
{
lean_object* v___x_7080_; 
if (v_isShared_7078_ == 0)
{
v___x_7080_ = v___x_7077_;
goto v_reusejp_7079_;
}
else
{
lean_object* v_reuseFailAlloc_7081_; 
v_reuseFailAlloc_7081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7081_, 0, v_a_7074_);
lean_ctor_set(v_reuseFailAlloc_7081_, 1, v_a_7075_);
v___x_7080_ = v_reuseFailAlloc_7081_;
goto v_reusejp_7079_;
}
v_reusejp_7079_:
{
return v___x_7080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg___boxed(lean_object* v_sep_7083_, lean_object* v_stxs_7084_, lean_object* v_a_7085_, lean_object* v_a_7086_){
_start:
{
lean_object* v_res_7087_; 
v_res_7087_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7083_, v_stxs_7084_, v_a_7085_, v_a_7086_);
lean_dec_ref(v_a_7085_);
lean_dec_ref(v_stxs_7084_);
lean_dec_ref(v_sep_7083_);
return v_res_7087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups(lean_object* v_ks_7088_, lean_object* v_sep_7089_, lean_object* v_stxs_7090_, lean_object* v_a_7091_, lean_object* v_a_7092_){
_start:
{
lean_object* v___x_7093_; 
v___x_7093_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7089_, v_stxs_7090_, v_a_7091_, v_a_7092_);
return v___x_7093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayTrailingGroups___boxed(lean_object* v_ks_7094_, lean_object* v_sep_7095_, lean_object* v_stxs_7096_, lean_object* v_a_7097_, lean_object* v_a_7098_){
_start:
{
lean_object* v_res_7099_; 
v_res_7099_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups(v_ks_7094_, v_sep_7095_, v_stxs_7096_, v_a_7097_, v_a_7098_);
lean_dec_ref(v_a_7097_);
lean_dec_ref(v_stxs_7096_);
lean_dec_ref(v_sep_7095_);
lean_dec(v_ks_7094_);
return v_res_7099_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(lean_object* v_upperBound_7100_, lean_object* v_elemsAndSeps_7101_, lean_object* v_sep_7102_, lean_object* v_pendingGroup_7103_, lean_object* v___x_7104_, lean_object* v_inst_7105_, lean_object* v_R_7106_, lean_object* v_a_7107_, lean_object* v_b_7108_, lean_object* v_c_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_){
_start:
{
lean_object* v___x_7112_; 
v___x_7112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___redArg(v_upperBound_7100_, v_elemsAndSeps_7101_, v_pendingGroup_7103_, v___x_7104_, v_a_7107_, v_b_7108_, v___y_7110_, v___y_7111_);
return v___x_7112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0___boxed(lean_object* v_upperBound_7113_, lean_object* v_elemsAndSeps_7114_, lean_object* v_sep_7115_, lean_object* v_pendingGroup_7116_, lean_object* v___x_7117_, lean_object* v_inst_7118_, lean_object* v_R_7119_, lean_object* v_a_7120_, lean_object* v_b_7121_, lean_object* v_c_7122_, lean_object* v___y_7123_, lean_object* v___y_7124_){
_start:
{
lean_object* v_res_7125_; 
v_res_7125_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_fmtTSepArrayTrailingGroups_spec__0(v_upperBound_7113_, v_elemsAndSeps_7114_, v_sep_7115_, v_pendingGroup_7116_, v___x_7117_, v_inst_7118_, v_R_7119_, v_a_7120_, v_b_7121_, v_c_7122_, v___y_7123_, v___y_7124_);
lean_dec_ref(v___y_7123_);
lean_dec(v___x_7117_);
lean_dec_ref(v_sep_7115_);
lean_dec_ref(v_elemsAndSeps_7114_);
lean_dec(v_upperBound_7113_);
return v_res_7125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(lean_object* v_sep_7129_, size_t v_sz_7130_, size_t v_i_7131_, lean_object* v_bs_7132_){
_start:
{
uint8_t v___x_7133_; 
v___x_7133_ = lean_usize_dec_lt(v_i_7131_, v_sz_7130_);
if (v___x_7133_ == 0)
{
lean_dec_ref(v_sep_7129_);
return v_bs_7132_;
}
else
{
lean_object* v_v_7134_; lean_object* v___x_7135_; lean_object* v_bs_x27_7136_; lean_object* v___y_7138_; 
v_v_7134_ = lean_array_uget(v_bs_7132_, v_i_7131_);
v___x_7135_ = lean_unsigned_to_nat(0u);
v_bs_x27_7136_ = lean_array_uset(v_bs_7132_, v_i_7131_, v___x_7135_);
if (lean_obj_tag(v_v_7134_) == 0)
{
lean_object* v_g_7143_; lean_object* v___x_7144_; lean_object* v___x_7145_; 
v_g_7143_ = lean_ctor_get(v_v_7134_, 0);
lean_inc_ref(v_g_7143_);
lean_dec_ref_known(v_v_7134_, 1);
v___x_7144_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___closed__0));
lean_inc_ref(v_sep_7129_);
v___x_7145_ = l_Lean_Fmt_Layouts_sepArray(v_sep_7129_, v_g_7143_, v___x_7144_);
lean_dec_ref(v_g_7143_);
v___y_7138_ = v___x_7145_;
goto v___jp_7137_;
}
else
{
lean_object* v_t_7146_; 
v_t_7146_ = lean_ctor_get(v_v_7134_, 0);
lean_inc_ref(v_t_7146_);
lean_dec_ref_known(v_v_7134_, 1);
v___y_7138_ = v_t_7146_;
goto v___jp_7137_;
}
v___jp_7137_:
{
size_t v___x_7139_; size_t v___x_7140_; lean_object* v___x_7141_; 
v___x_7139_ = ((size_t)1ULL);
v___x_7140_ = lean_usize_add(v_i_7131_, v___x_7139_);
v___x_7141_ = lean_array_uset(v_bs_x27_7136_, v_i_7131_, v___y_7138_);
v_i_7131_ = v___x_7140_;
v_bs_7132_ = v___x_7141_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0___boxed(lean_object* v_sep_7147_, lean_object* v_sz_7148_, lean_object* v_i_7149_, lean_object* v_bs_7150_){
_start:
{
size_t v_sz_boxed_7151_; size_t v_i_boxed_7152_; lean_object* v_res_7153_; 
v_sz_boxed_7151_ = lean_unbox_usize(v_sz_7148_);
lean_dec(v_sz_7148_);
v_i_boxed_7152_ = lean_unbox_usize(v_i_7149_);
lean_dec(v_i_7149_);
v_res_7153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7147_, v_sz_boxed_7151_, v_i_boxed_7152_, v_bs_7150_);
return v_res_7153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(lean_object* v_sep_7154_, lean_object* v_stxs_7155_, lean_object* v_a_7156_, lean_object* v_a_7157_){
_start:
{
lean_object* v___x_7158_; 
v___x_7158_ = l_Lean_Fmt_fmtTSepArrayTrailingGroups___redArg(v_sep_7154_, v_stxs_7155_, v_a_7156_, v_a_7157_);
if (lean_obj_tag(v___x_7158_) == 0)
{
lean_object* v_a_7159_; lean_object* v_a_7160_; lean_object* v___x_7162_; uint8_t v_isShared_7163_; uint8_t v_isSharedCheck_7171_; 
v_a_7159_ = lean_ctor_get(v___x_7158_, 0);
v_a_7160_ = lean_ctor_get(v___x_7158_, 1);
v_isSharedCheck_7171_ = !lean_is_exclusive(v___x_7158_);
if (v_isSharedCheck_7171_ == 0)
{
v___x_7162_ = v___x_7158_;
v_isShared_7163_ = v_isSharedCheck_7171_;
goto v_resetjp_7161_;
}
else
{
lean_inc(v_a_7160_);
lean_inc(v_a_7159_);
lean_dec(v___x_7158_);
v___x_7162_ = lean_box(0);
v_isShared_7163_ = v_isSharedCheck_7171_;
goto v_resetjp_7161_;
}
v_resetjp_7161_:
{
size_t v_sz_7164_; size_t v___x_7165_; lean_object* v___x_7166_; lean_object* v___x_7167_; lean_object* v___x_7169_; 
v_sz_7164_ = lean_array_size(v_a_7159_);
v___x_7165_ = ((size_t)0ULL);
v___x_7166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments_spec__0(v_sep_7154_, v_sz_7164_, v___x_7165_, v_a_7159_);
v___x_7167_ = l_Lean_Fmt_TaggedDoc_join(v___x_7166_);
if (v_isShared_7163_ == 0)
{
lean_ctor_set(v___x_7162_, 0, v___x_7167_);
v___x_7169_ = v___x_7162_;
goto v_reusejp_7168_;
}
else
{
lean_object* v_reuseFailAlloc_7170_; 
v_reuseFailAlloc_7170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7170_, 0, v___x_7167_);
lean_ctor_set(v_reuseFailAlloc_7170_, 1, v_a_7160_);
v___x_7169_ = v_reuseFailAlloc_7170_;
goto v_reusejp_7168_;
}
v_reusejp_7168_:
{
return v___x_7169_;
}
}
}
else
{
lean_object* v_a_7172_; lean_object* v_a_7173_; lean_object* v___x_7175_; uint8_t v_isShared_7176_; uint8_t v_isSharedCheck_7180_; 
lean_dec_ref(v_sep_7154_);
v_a_7172_ = lean_ctor_get(v___x_7158_, 0);
v_a_7173_ = lean_ctor_get(v___x_7158_, 1);
v_isSharedCheck_7180_ = !lean_is_exclusive(v___x_7158_);
if (v_isSharedCheck_7180_ == 0)
{
v___x_7175_ = v___x_7158_;
v_isShared_7176_ = v_isSharedCheck_7180_;
goto v_resetjp_7174_;
}
else
{
lean_inc(v_a_7173_);
lean_inc(v_a_7172_);
lean_dec(v___x_7158_);
v___x_7175_ = lean_box(0);
v_isShared_7176_ = v_isSharedCheck_7180_;
goto v_resetjp_7174_;
}
v_resetjp_7174_:
{
lean_object* v___x_7178_; 
if (v_isShared_7176_ == 0)
{
v___x_7178_ = v___x_7175_;
goto v_reusejp_7177_;
}
else
{
lean_object* v_reuseFailAlloc_7179_; 
v_reuseFailAlloc_7179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_7179_, 0, v_a_7172_);
lean_ctor_set(v_reuseFailAlloc_7179_, 1, v_a_7173_);
v___x_7178_ = v_reuseFailAlloc_7179_;
goto v_reusejp_7177_;
}
v_reusejp_7177_:
{
return v___x_7178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg___boxed(lean_object* v_sep_7181_, lean_object* v_stxs_7182_, lean_object* v_a_7183_, lean_object* v_a_7184_){
_start:
{
lean_object* v_res_7185_; 
v_res_7185_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7181_, v_stxs_7182_, v_a_7183_, v_a_7184_);
lean_dec_ref(v_a_7183_);
lean_dec_ref(v_stxs_7182_);
return v_res_7185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(lean_object* v_ks_7186_, lean_object* v_sep_7187_, lean_object* v_stxs_7188_, lean_object* v_a_7189_, lean_object* v_a_7190_){
_start:
{
lean_object* v___x_7191_; 
v___x_7191_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___redArg(v_sep_7187_, v_stxs_7188_, v_a_7189_, v_a_7190_);
return v___x_7191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments___boxed(lean_object* v_ks_7192_, lean_object* v_sep_7193_, lean_object* v_stxs_7194_, lean_object* v_a_7195_, lean_object* v_a_7196_){
_start:
{
lean_object* v_res_7197_; 
v_res_7197_ = l_Lean_Fmt_fmtTSepArrayWithRetainedIntermediateNewlinesAndComments(v_ks_7192_, v_sep_7193_, v_stxs_7194_, v_a_7195_, v_a_7196_);
lean_dec_ref(v_a_7195_);
lean_dec_ref(v_stxs_7194_);
lean_dec(v_ks_7192_);
return v_res_7197_;
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
