// Lean compiler output
// Module: Lean.Data.Markdown.Parser.Block
// Imports: public import Init.While import Init.Data.String.Iterate import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Init.Data.Array.QSort.Basic import Init.Data.String.Compare public import Lean.Data.Markdown.Block public import Lean.Data.Markdown.InlineCursor public import Lean.Data.Markdown.Parser.RefDef import Lean.Data.Markdown.Parser.Cursor import Lean.Data.Markdown.Parser.BlockZipper import Lean.Data.Markdown.Parser.Html
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Markdown_LinkLabel_ofString(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Markdown_instHashableLinkLabel_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Markdown_instBEqLinkLabel_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_empty___redArg();
lean_object* l_Lean_Markdown_BlockZipper_closeContainer(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_trimTrailing(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_addBlock(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_parseLineEnding_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Markdown_normalizeLabel(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_openLeaf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_extendParagraph___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_FenceChar_ofChar_x3f(uint32_t);
uint32_t l_Lean_Markdown_FenceChar_toChar(uint8_t);
uint8_t l_Lean_Markdown_instBEqFenceChar_beq(uint8_t, uint8_t);
lean_object* l_Lean_Markdown_BlockZipper_closeLeaf(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_recordBlankLine(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_Children_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_recordContentLine___redArg(lean_object*);
lean_object* l_Lean_Markdown_Cursor_verbatimLine(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_HtmlBlockKind_endConditionMet(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_openBlockquote(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Markdown_BlockZipper_openItem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Markdown_Cursor_isBlank(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineSource_ofLines(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineSource_startPos___redArg(lean_object*);
lean_object* l_Lean_Markdown_InlineSource_stopPos___redArg(lean_object*);
lean_object* l_Lean_Markdown_InlineSource_cursor___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_parseCompleteTagLine_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_isBlockTagName(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_startsWithAscii(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Markdown_isRawTextTagName(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(uint8_t);
lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine(uint8_t);
lean_object* l_Lean_Markdown_BlockZipper_extendHtml___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_extendFencedCode___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_closeFencedCode(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_extractRefDefs(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_BlockZipper_finalize(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_isBreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_isBreak_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_isBreak_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_failsAt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_failsAt_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_failsAt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_notCandidate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_notCandidate_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_notCandidate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___redArg(lean_object*, uint32_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0(lean_object*, uint32_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceClose_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceClose_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__1 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__2 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/>"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__3 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__4 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__6 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__7 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "[CDATA["};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__8 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__8_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__9 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__10 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_listMarkerInterruptsParagraph(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_listMarkerInterruptsParagraph___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isInterrupt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isInterrupt___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_takeState___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_takeState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_takeState___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLine___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLineWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLineWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLineWith___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_finishLineWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_finishLineWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_finishLineWith___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_runContainerM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_runContainerM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_runContainerM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__0_value;
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__1 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__1_value;
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__2 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__2_value;
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__3 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__3_value;
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__4 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__4_value;
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__5 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__5_value;
static const lean_closure_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__6 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__6_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__0_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__1_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__7 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__7_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__7_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__2_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__3_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__4_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__5_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__8 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__8_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__8_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__6_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__9 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryLazyContinuation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryLazyContinuation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeFencedCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeFencedCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeHtmlBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeHtmlBlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentedCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentedCode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishThematicBreak(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishThematicBreak___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryAtxHeading(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryAtxHeading___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryHtmlBlockOpener(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryHtmlBlockOpener___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryIndentedCodeOpener(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryIndentedCodeOpener___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_emitParagraph(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_emitParagraph___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openLeafBlock(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openLeafBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__1 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Markdown_buildRefTable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_buildRefTable___closed__0;
static lean_once_cell_t l_Lean_Markdown_buildRefTable___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_buildRefTable___closed__1;
LEAN_EXPORT lean_object* l_Lean_Markdown_buildRefTable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_buildRefTable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseBlocks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseBlocks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___redArg(lean_object* v_s_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_fst_3_; lean_object* v_snd_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_68_; 
v_fst_3_ = lean_ctor_get(v_a_2_, 0);
v_snd_4_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_68_ == 0)
{
v___x_6_ = v_a_2_;
v_isShared_7_ = v_isSharedCheck_68_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_snd_4_);
lean_inc(v_fst_3_);
lean_dec(v_a_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_68_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v_pos_8_; lean_object* v_stop_9_; lean_object* v_col_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_pos_8_ = lean_ctor_get(v_fst_3_, 0);
v_stop_9_ = lean_ctor_get(v_fst_3_, 1);
v_col_10_ = lean_ctor_get(v_fst_3_, 2);
v___x_11_ = lean_unsigned_to_nat(1u);
v___x_12_ = lean_nat_add(v_pos_8_, v___x_11_);
v___x_13_ = lean_nat_dec_le(v___x_12_, v_stop_9_);
lean_dec(v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_15_; 
if (v_isShared_7_ == 0)
{
v___x_15_ = v___x_6_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_fst_3_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_snd_4_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v_str_17_; lean_object* v_startInclusive_18_; lean_object* v___x_19_; uint32_t v___x_20_; uint32_t v___x_21_; uint8_t v___x_22_; 
v_str_17_ = lean_ctor_get(v_s_1_, 0);
v_startInclusive_18_ = lean_ctor_get(v_s_1_, 1);
v___x_19_ = lean_nat_add(v_startInclusive_18_, v_pos_8_);
v___x_20_ = lean_string_utf8_get_fast(v_str_17_, v___x_19_);
v___x_21_ = 32;
v___x_22_ = lean_uint32_dec_eq(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
uint32_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = 9;
v___x_24_ = lean_uint32_dec_eq(v___x_20_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_26_; 
lean_dec(v___x_19_);
if (v_isShared_7_ == 0)
{
v___x_26_ = v___x_6_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_fst_3_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_snd_4_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
else
{
lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_45_; 
lean_inc(v_col_10_);
lean_inc(v_stop_9_);
v_isSharedCheck_45_ = !lean_is_exclusive(v_fst_3_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; lean_object* v_unused_47_; lean_object* v_unused_48_; 
v_unused_46_ = lean_ctor_get(v_fst_3_, 2);
lean_dec(v_unused_46_);
v_unused_47_ = lean_ctor_get(v_fst_3_, 1);
lean_dec(v_unused_47_);
v_unused_48_ = lean_ctor_get(v_fst_3_, 0);
lean_dec(v_unused_48_);
v___x_29_ = v_fst_3_;
v_isShared_30_ = v_isSharedCheck_45_;
goto v_resetjp_28_;
}
else
{
lean_dec(v_fst_3_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_45_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_31_ = lean_unsigned_to_nat(4u);
v___x_32_ = lean_nat_mod(v_col_10_, v___x_31_);
v___x_33_ = lean_nat_sub(v___x_31_, v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = lean_nat_add(v_snd_4_, v___x_33_);
lean_dec(v_snd_4_);
v___x_35_ = lean_string_utf8_next_fast(v_str_17_, v___x_19_);
lean_dec(v___x_19_);
v___x_36_ = lean_nat_sub(v___x_35_, v_startInclusive_18_);
v___x_37_ = lean_nat_add(v_col_10_, v___x_33_);
lean_dec(v___x_33_);
lean_dec(v_col_10_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 2, v___x_37_);
lean_ctor_set(v___x_29_, 0, v___x_36_);
v___x_39_ = v___x_29_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_stop_9_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v___x_37_);
v___x_39_ = v_reuseFailAlloc_44_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_41_; 
lean_ctor_set_uint8(v___x_39_, sizeof(void*)*3, v___x_22_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_34_);
lean_ctor_set(v___x_6_, 0, v___x_39_);
v___x_41_ = v___x_6_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_39_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_34_);
v___x_41_ = v_reuseFailAlloc_43_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
v_a_2_ = v___x_41_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_64_; 
lean_inc(v_col_10_);
lean_inc(v_stop_9_);
v_isSharedCheck_64_ = !lean_is_exclusive(v_fst_3_);
if (v_isSharedCheck_64_ == 0)
{
lean_object* v_unused_65_; lean_object* v_unused_66_; lean_object* v_unused_67_; 
v_unused_65_ = lean_ctor_get(v_fst_3_, 2);
lean_dec(v_unused_65_);
v_unused_66_ = lean_ctor_get(v_fst_3_, 1);
lean_dec(v_unused_66_);
v_unused_67_ = lean_ctor_get(v_fst_3_, 0);
lean_dec(v_unused_67_);
v___x_50_ = v_fst_3_;
v_isShared_51_ = v_isSharedCheck_64_;
goto v_resetjp_49_;
}
else
{
lean_dec(v_fst_3_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_64_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_58_; 
v___x_52_ = lean_nat_add(v_snd_4_, v___x_11_);
lean_dec(v_snd_4_);
v___x_53_ = lean_string_utf8_next_fast(v_str_17_, v___x_19_);
lean_dec(v___x_19_);
v___x_54_ = lean_nat_sub(v___x_53_, v_startInclusive_18_);
v___x_55_ = lean_nat_add(v_col_10_, v___x_11_);
lean_dec(v_col_10_);
v___x_56_ = 0;
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 2, v___x_55_);
lean_ctor_set(v___x_50_, 0, v___x_54_);
v___x_58_ = v___x_50_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_stop_9_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v___x_55_);
v___x_58_ = v_reuseFailAlloc_63_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_60_; 
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*3, v___x_56_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 1, v___x_52_);
lean_ctor_set(v___x_6_, 0, v___x_58_);
v___x_60_ = v___x_6_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___x_52_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
v_a_2_ = v___x_60_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___redArg___boxed(lean_object* v_s_69_, lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___redArg(v_s_69_, v_a_70_);
lean_dec_ref(v_s_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols(lean_object* v_s_72_, lean_object* v_c_73_){
_start:
{
lean_object* v_cols_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_fst_77_; lean_object* v_snd_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_cols_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_c_73_);
lean_ctor_set(v___x_75_, 1, v_cols_74_);
v___x_76_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___redArg(v_s_72_, v___x_75_);
v_fst_77_ = lean_ctor_get(v___x_76_, 0);
v_snd_78_ = lean_ctor_get(v___x_76_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_snd_78_);
lean_inc(v_fst_77_);
lean_dec(v___x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_fst_77_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_snd_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols___boxed(lean_object* v_s_86_, lean_object* v_c_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols(v_s_86_, v_c_87_);
lean_dec_ref(v_s_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0(lean_object* v_s_89_, lean_object* v_inst_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___redArg(v_s_89_, v_a_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0___boxed(lean_object* v_s_93_, lean_object* v_inst_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols_spec__0(v_s_93_, v_inst_94_, v_a_95_);
lean_dec_ref(v_s_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(lean_object* v_s_97_, lean_object* v_c_98_){
_start:
{
lean_object* v___x_99_; lean_object* v_fst_100_; lean_object* v_snd_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
v___x_99_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols(v_s_97_, v_c_98_);
v_fst_100_ = lean_ctor_get(v___x_99_, 0);
v_snd_101_ = lean_ctor_get(v___x_99_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_99_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_snd_101_);
lean_inc(v_fst_100_);
lean_dec(v___x_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_fst_100_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_snd_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent___boxed(lean_object* v_s_109_, lean_object* v_c_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_109_, v_c_110_);
lean_dec_ref(v_s_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___redArg(lean_object* v_maxCols_112_, lean_object* v_s_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_194_; 
v_fst_115_ = lean_ctor_get(v_a_114_, 0);
v_snd_116_ = lean_ctor_get(v_a_114_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_194_ == 0)
{
v___x_118_ = v_a_114_;
v_isShared_119_ = v_isSharedCheck_194_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
lean_dec(v_a_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_194_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_pos_120_; lean_object* v_stop_121_; lean_object* v_col_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v_pos_120_ = lean_ctor_get(v_fst_115_, 0);
v_stop_121_ = lean_ctor_get(v_fst_115_, 1);
v_col_122_ = lean_ctor_get(v_fst_115_, 2);
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_add(v_pos_120_, v___x_123_);
v___x_125_ = lean_nat_dec_le(v___x_124_, v_stop_121_);
lean_dec(v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v_maxCols_112_);
if (v_isShared_119_ == 0)
{
v___x_127_ = v___x_118_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_snd_116_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_le(v_maxCols_112_, v_snd_116_);
if (v___x_129_ == 0)
{
lean_object* v_str_130_; lean_object* v_startInclusive_131_; lean_object* v___x_132_; uint32_t v___x_133_; uint32_t v___x_134_; uint8_t v___x_135_; 
v_str_130_ = lean_ctor_get(v_s_113_, 0);
v_startInclusive_131_ = lean_ctor_get(v_s_113_, 1);
v___x_132_ = lean_nat_add(v_startInclusive_131_, v_pos_120_);
v___x_133_ = lean_string_utf8_get_fast(v_str_130_, v___x_132_);
v___x_134_ = 32;
v___x_135_ = lean_uint32_dec_eq(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_136_ = 9;
v___x_137_ = lean_uint32_dec_eq(v___x_133_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_139_; 
lean_dec(v___x_132_);
lean_dec(v_maxCols_112_);
if (v_isShared_119_ == 0)
{
v___x_139_ = v___x_118_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_snd_116_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
else
{
lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_169_; 
lean_inc(v_col_122_);
lean_inc(v_stop_121_);
lean_inc(v_pos_120_);
v_isSharedCheck_169_ = !lean_is_exclusive(v_fst_115_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; lean_object* v_unused_171_; lean_object* v_unused_172_; 
v_unused_170_ = lean_ctor_get(v_fst_115_, 2);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_fst_115_, 1);
lean_dec(v_unused_171_);
v_unused_172_ = lean_ctor_get(v_fst_115_, 0);
lean_dec(v_unused_172_);
v___x_142_ = v_fst_115_;
v_isShared_143_ = v_isSharedCheck_169_;
goto v_resetjp_141_;
}
else
{
lean_dec(v_fst_115_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_169_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_144_ = lean_unsigned_to_nat(4u);
v___x_145_ = lean_nat_mod(v_col_122_, v___x_144_);
v___x_146_ = lean_nat_sub(v___x_144_, v___x_145_);
lean_dec(v___x_145_);
v___x_147_ = lean_nat_add(v_snd_116_, v___x_146_);
v___x_148_ = lean_nat_add(v_maxCols_112_, v___x_123_);
v___x_149_ = lean_nat_dec_le(v___x_148_, v___x_147_);
lean_dec(v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
lean_dec(v_pos_120_);
lean_dec(v_snd_116_);
v___x_150_ = lean_string_utf8_next_fast(v_str_130_, v___x_132_);
lean_dec(v___x_132_);
v___x_151_ = lean_nat_sub(v___x_150_, v_startInclusive_131_);
v___x_152_ = lean_nat_add(v_col_122_, v___x_146_);
lean_dec(v___x_146_);
lean_dec(v_col_122_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 2, v___x_152_);
lean_ctor_set(v___x_142_, 0, v___x_151_);
v___x_154_ = v___x_142_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_stop_121_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v___x_152_);
v___x_154_ = v_reuseFailAlloc_159_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_object* v___x_156_; 
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*3, v___x_149_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_147_);
lean_ctor_set(v___x_118_, 0, v___x_154_);
v___x_156_ = v___x_118_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_147_);
v___x_156_ = v_reuseFailAlloc_158_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
v_a_114_ = v___x_156_;
goto _start;
}
}
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_163_; 
lean_dec(v___x_147_);
lean_dec(v___x_146_);
lean_dec(v___x_132_);
v___x_160_ = lean_nat_sub(v_maxCols_112_, v_snd_116_);
lean_dec(v_snd_116_);
v___x_161_ = lean_nat_add(v_col_122_, v___x_160_);
lean_dec(v___x_160_);
lean_dec(v_col_122_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 2, v___x_161_);
v___x_163_ = v___x_142_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_pos_120_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_stop_121_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v___x_161_);
v___x_163_ = v_reuseFailAlloc_168_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
lean_ctor_set_uint8(v___x_163_, sizeof(void*)*3, v___x_149_);
lean_inc(v_maxCols_112_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v_maxCols_112_);
lean_ctor_set(v___x_118_, 0, v___x_163_);
v___x_165_ = v___x_118_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_maxCols_112_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v_a_114_ = v___x_165_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_187_; 
lean_inc(v_col_122_);
lean_inc(v_stop_121_);
v_isSharedCheck_187_ = !lean_is_exclusive(v_fst_115_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; lean_object* v_unused_189_; lean_object* v_unused_190_; 
v_unused_188_ = lean_ctor_get(v_fst_115_, 2);
lean_dec(v_unused_188_);
v_unused_189_ = lean_ctor_get(v_fst_115_, 1);
lean_dec(v_unused_189_);
v_unused_190_ = lean_ctor_get(v_fst_115_, 0);
lean_dec(v_unused_190_);
v___x_174_ = v_fst_115_;
v_isShared_175_ = v_isSharedCheck_187_;
goto v_resetjp_173_;
}
else
{
lean_dec(v_fst_115_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_187_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_176_ = lean_nat_add(v_snd_116_, v___x_123_);
lean_dec(v_snd_116_);
v___x_177_ = lean_string_utf8_next_fast(v_str_130_, v___x_132_);
lean_dec(v___x_132_);
v___x_178_ = lean_nat_sub(v___x_177_, v_startInclusive_131_);
v___x_179_ = lean_nat_add(v_col_122_, v___x_123_);
lean_dec(v_col_122_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 2, v___x_179_);
lean_ctor_set(v___x_174_, 0, v___x_178_);
v___x_181_ = v___x_174_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v_stop_121_);
lean_ctor_set(v_reuseFailAlloc_186_, 2, v___x_179_);
v___x_181_ = v_reuseFailAlloc_186_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
lean_object* v___x_183_; 
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*3, v___x_129_);
if (v_isShared_119_ == 0)
{
lean_ctor_set(v___x_118_, 1, v___x_176_);
lean_ctor_set(v___x_118_, 0, v___x_181_);
v___x_183_ = v___x_118_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_176_);
v___x_183_ = v_reuseFailAlloc_185_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v_a_114_ = v___x_183_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_192_; 
lean_dec(v_maxCols_112_);
if (v_isShared_119_ == 0)
{
v___x_192_ = v___x_118_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_fst_115_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_snd_116_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___redArg___boxed(lean_object* v_maxCols_195_, lean_object* v_s_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___redArg(v_maxCols_195_, v_s_196_, v_a_197_);
lean_dec_ref(v_s_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(lean_object* v_s_199_, lean_object* v_c_200_, lean_object* v_maxCols_201_){
_start:
{
lean_object* v_cols_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_cols_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_c_200_);
lean_ctor_set(v___x_203_, 1, v_cols_202_);
v___x_204_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___redArg(v_maxCols_201_, v_s_199_, v___x_203_);
v_fst_205_ = lean_ctor_get(v___x_204_, 0);
v_snd_206_ = lean_ctor_get(v___x_204_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_204_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_snd_206_);
lean_inc(v_fst_205_);
lean_dec(v___x_204_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_fst_205_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_snd_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped___boxed(lean_object* v_s_214_, lean_object* v_c_215_, lean_object* v_maxCols_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(v_s_214_, v_c_215_, v_maxCols_216_);
lean_dec_ref(v_s_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0(lean_object* v_maxCols_218_, lean_object* v_s_219_, lean_object* v_inst_220_, lean_object* v_a_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___redArg(v_maxCols_218_, v_s_219_, v_a_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0___boxed(lean_object* v_maxCols_223_, lean_object* v_s_224_, lean_object* v_inst_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped_spec__0(v_maxCols_223_, v_s_224_, v_inst_225_, v_a_226_);
lean_dec_ref(v_s_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(lean_object* v_s_228_, lean_object* v_c_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_fst_232_; lean_object* v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(4u);
v___x_231_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(v_s_228_, v_c_229_, v___x_230_);
v_fst_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_fst_232_);
lean_dec_ref(v___x_231_);
v___x_233_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_228_, v_fst_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine___boxed(lean_object* v_s_234_, lean_object* v_c_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_234_, v_c_235_);
lean_dec_ref(v_s_234_);
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___lam__0(uint32_t v_c_237_){
_start:
{
uint32_t v___x_238_; uint8_t v___x_239_; 
v___x_238_ = 32;
v___x_239_ = lean_uint32_dec_eq(v_c_237_, v___x_238_);
if (v___x_239_ == 0)
{
uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_240_ = 9;
v___x_241_ = lean_uint32_dec_eq(v_c_237_, v___x_240_);
return v___x_241_;
}
else
{
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___lam__0___boxed(lean_object* v_c_242_){
_start:
{
uint32_t v_c_boxed_243_; uint8_t v_res_244_; lean_object* v_r_245_; 
v_c_boxed_243_ = lean_unbox_uint32(v_c_242_);
lean_dec(v_c_242_);
v_res_244_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___lam__0(v_c_boxed_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(lean_object* v_s_247_, lean_object* v_text_248_){
_start:
{
lean_object* v___f_249_; lean_object* v___x_250_; 
v___f_249_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___closed__0));
v___x_250_ = l_Lean_Markdown_trimTrailing(v_s_247_, v_text_248_, v___f_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs___boxed(lean_object* v_s_251_, lean_object* v_text_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(v_s_251_, v_text_252_);
lean_dec_ref(v_s_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___redArg(lean_object* v_upperBound_254_, lean_object* v_line_255_, lean_object* v_s_256_, lean_object* v_a_257_, lean_object* v_b_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = lean_nat_dec_lt(v_a_257_, v_upperBound_254_);
if (v___x_259_ == 0)
{
lean_dec(v_a_257_);
return v_b_258_;
}
else
{
lean_object* v_endExclusive_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_endExclusive_260_ = lean_ctor_get(v_line_255_, 1);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_b_258_, v___x_261_);
v___x_263_ = lean_nat_dec_le(v___x_262_, v_endExclusive_260_);
lean_dec(v___x_262_);
if (v___x_263_ == 0)
{
lean_dec(v_a_257_);
return v_b_258_;
}
else
{
lean_object* v_str_264_; lean_object* v_startInclusive_265_; lean_object* v___x_266_; uint32_t v___x_267_; uint32_t v___x_268_; uint8_t v___x_269_; 
v_str_264_ = lean_ctor_get(v_s_256_, 0);
v_startInclusive_265_ = lean_ctor_get(v_s_256_, 1);
v___x_266_ = lean_nat_add(v_startInclusive_265_, v_b_258_);
v___x_267_ = lean_string_utf8_get_fast(v_str_264_, v___x_266_);
v___x_268_ = 32;
v___x_269_ = lean_uint32_dec_eq(v___x_267_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec(v___x_266_);
lean_dec(v_a_257_);
return v_b_258_;
}
else
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v_b_258_);
v___x_270_ = lean_string_utf8_next_fast(v_str_264_, v___x_266_);
lean_dec(v___x_266_);
v___x_271_ = lean_nat_sub(v___x_270_, v_startInclusive_265_);
v___x_272_ = lean_nat_add(v_a_257_, v___x_261_);
lean_dec(v_a_257_);
v_a_257_ = v___x_272_;
v_b_258_ = v___x_271_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___redArg___boxed(lean_object* v_upperBound_274_, lean_object* v_line_275_, lean_object* v_s_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___redArg(v_upperBound_274_, v_line_275_, v_s_276_, v_a_277_, v_b_278_);
lean_dec_ref(v_s_276_);
lean_dec_ref(v_line_275_);
lean_dec(v_upperBound_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent(lean_object* v_s_280_, lean_object* v_line_281_, lean_object* v_indent_282_){
_start:
{
lean_object* v_startInclusive_283_; lean_object* v_endExclusive_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v_startInclusive_283_ = lean_ctor_get(v_line_281_, 0);
lean_inc(v_startInclusive_283_);
v_endExclusive_284_ = lean_ctor_get(v_line_281_, 1);
lean_inc(v_endExclusive_284_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___redArg(v_indent_282_, v_line_281_, v_s_280_, v___x_285_, v_startInclusive_283_);
lean_dec_ref(v_line_281_);
v___x_287_ = l_Lean_Markdown_subsliceClamped___redArg(v___x_286_, v_endExclusive_284_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent___boxed(lean_object* v_s_288_, lean_object* v_line_289_, lean_object* v_indent_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent(v_s_288_, v_line_289_, v_indent_290_);
lean_dec(v_indent_290_);
lean_dec_ref(v_s_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0(lean_object* v_upperBound_292_, lean_object* v_line_293_, lean_object* v_s_294_, lean_object* v_inst_295_, lean_object* v_R_296_, lean_object* v_a_297_, lean_object* v_b_298_, lean_object* v_c_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___redArg(v_upperBound_292_, v_line_293_, v_s_294_, v_a_297_, v_b_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0___boxed(lean_object* v_upperBound_301_, lean_object* v_line_302_, lean_object* v_s_303_, lean_object* v_inst_304_, lean_object* v_R_305_, lean_object* v_a_306_, lean_object* v_b_307_, lean_object* v_c_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent_spec__0(v_upperBound_301_, v_line_302_, v_s_303_, v_inst_304_, v_R_305_, v_a_306_, v_b_307_, v_c_308_);
lean_dec_ref(v_s_303_);
lean_dec_ref(v_line_302_);
lean_dec(v_upperBound_301_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines_go(lean_object* v_s_310_, lean_object* v_text_311_, lean_object* v_p_312_, lean_object* v_lineStart_313_, lean_object* v_lines_314_){
_start:
{
lean_object* v___y_316_; lean_object* v_endExclusive_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_endExclusive_320_ = lean_ctor_get(v_text_311_, 1);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_p_312_, v___x_321_);
v___x_323_ = lean_nat_dec_le(v___x_322_, v_endExclusive_320_);
lean_dec(v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_nat_add(v_lineStart_313_, v___x_321_);
v___x_325_ = lean_nat_dec_le(v___x_324_, v_p_312_);
lean_dec(v___x_324_);
if (v___x_325_ == 0)
{
lean_dec(v_lineStart_313_);
lean_dec(v_p_312_);
return v_lines_314_;
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = l_Lean_Markdown_subsliceClamped___redArg(v_lineStart_313_, v_p_312_);
v___x_327_ = lean_array_push(v_lines_314_, v___x_326_);
return v___x_327_;
}
}
else
{
lean_object* v_str_328_; lean_object* v_startInclusive_329_; lean_object* v___x_336_; uint32_t v_c_337_; uint32_t v___x_338_; uint8_t v___x_339_; 
v_str_328_ = lean_ctor_get(v_s_310_, 0);
v_startInclusive_329_ = lean_ctor_get(v_s_310_, 1);
v___x_336_ = lean_nat_add(v_startInclusive_329_, v_p_312_);
v_c_337_ = lean_string_utf8_get_fast(v_str_328_, v___x_336_);
v___x_338_ = 10;
v___x_339_ = lean_uint32_dec_eq(v_c_337_, v___x_338_);
if (v___x_339_ == 0)
{
uint32_t v___x_340_; uint8_t v___x_341_; 
v___x_340_ = 13;
v___x_341_ = lean_uint32_dec_eq(v_c_337_, v___x_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec(v_p_312_);
v___x_342_ = lean_string_utf8_next_fast(v_str_328_, v___x_336_);
lean_dec(v___x_336_);
v___x_343_ = lean_nat_sub(v___x_342_, v_startInclusive_329_);
v_p_312_ = v___x_343_;
goto _start;
}
else
{
lean_dec(v___x_336_);
goto v___jp_330_;
}
}
else
{
lean_dec(v___x_336_);
goto v___jp_330_;
}
v___jp_330_:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Markdown_parseLineEnding_x3f(v_s_310_, v_text_311_, v_p_312_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_nat_add(v_startInclusive_329_, v_p_312_);
v___x_333_ = lean_string_utf8_next_fast(v_str_328_, v___x_332_);
lean_dec(v___x_332_);
v___x_334_ = lean_nat_sub(v___x_333_, v_startInclusive_329_);
v___y_316_ = v___x_334_;
goto v___jp_315_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_331_, 1);
v___y_316_ = v_val_335_;
goto v___jp_315_;
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_Lean_Markdown_subsliceClamped___redArg(v_lineStart_313_, v_p_312_);
v___x_318_ = lean_array_push(v_lines_314_, v___x_317_);
lean_inc(v___y_316_);
v_p_312_ = v___y_316_;
v_lineStart_313_ = v___y_316_;
v_lines_314_ = v___x_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines_go___boxed(lean_object* v_s_345_, lean_object* v_text_346_, lean_object* v_p_347_, lean_object* v_lineStart_348_, lean_object* v_lines_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines_go(v_s_345_, v_text_346_, v_p_347_, v_lineStart_348_, v_lines_349_);
lean_dec_ref(v_text_346_);
lean_dec_ref(v_s_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines(lean_object* v_s_353_, lean_object* v_text_354_){
_start:
{
lean_object* v_startInclusive_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_startInclusive_355_ = lean_ctor_get(v_text_354_, 0);
lean_inc_n(v_startInclusive_355_, 2);
v___x_356_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines___closed__0));
v___x_357_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines_go(v_s_353_, v_text_354_, v_startInclusive_355_, v_startInclusive_355_, v___x_356_);
lean_dec_ref(v_text_354_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines___boxed(lean_object* v_s_358_, lean_object* v_text_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines(v_s_358_, v_text_359_);
lean_dec_ref(v_s_358_);
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
if (lean_obj_tag(v_x_361_) == 0)
{
if (lean_obj_tag(v_x_362_) == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 1;
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 0;
return v___x_364_;
}
}
else
{
if (lean_obj_tag(v_x_362_) == 0)
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
else
{
lean_object* v_val_366_; lean_object* v_val_367_; uint32_t v___x_368_; uint32_t v___x_369_; uint8_t v___x_370_; 
v_val_366_ = lean_ctor_get(v_x_361_, 0);
v_val_367_ = lean_ctor_get(v_x_362_, 0);
v___x_368_ = lean_unbox_uint32(v_val_366_);
v___x_369_ = lean_unbox_uint32(v_val_367_);
v___x_370_ = lean_uint32_dec_eq(v___x_368_, v___x_369_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0___boxed(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v_x_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec(v_x_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_375_; lean_object* v___x_376_; 
v___x_375_ = 35;
v___x_376_ = lean_box_uint32(v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0___boxed__const__1;
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg(lean_object* v_s_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v_fst_386_; lean_object* v_snd_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_431_; 
v_fst_386_ = lean_ctor_get(v_a_380_, 0);
v_snd_387_ = lean_ctor_get(v_a_380_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_431_ == 0)
{
v___x_389_ = v_a_380_;
v_isShared_390_ = v_isSharedCheck_431_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_snd_387_);
lean_inc(v_fst_386_);
lean_dec(v_a_380_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_431_;
goto v_resetjp_388_;
}
v___jp_381_:
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___y_383_);
lean_ctor_set(v___x_384_, 1, v___y_382_);
v_a_380_ = v___x_384_;
goto _start;
}
v_resetjp_388_:
{
lean_object* v_pos_396_; lean_object* v_stop_397_; lean_object* v_col_398_; lean_object* v___y_400_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_pos_396_ = lean_ctor_get(v_fst_386_, 0);
v_stop_397_ = lean_ctor_get(v_fst_386_, 1);
v_col_398_ = lean_ctor_get(v_fst_386_, 2);
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_pos_396_, v___x_426_);
v___x_428_ = lean_nat_dec_le(v___x_427_, v_stop_397_);
lean_dec(v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
v___y_400_ = v___x_429_;
goto v___jp_399_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = l_String_Slice_Pos_get_x3f(v_s_379_, v_pos_396_);
v___y_400_ = v___x_430_;
goto v___jp_399_;
}
v___jp_391_:
{
lean_object* v___x_393_; 
if (v_isShared_390_ == 0)
{
v___x_393_ = v___x_389_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_fst_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_snd_387_);
v___x_393_ = v_reuseFailAlloc_395_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
v___jp_399_:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0);
v___x_402_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___y_400_, v___x_401_);
lean_dec(v___y_400_);
if (v___x_402_ == 0)
{
goto v___jp_391_;
}
else
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(7u);
v___x_404_ = lean_nat_dec_lt(v_snd_387_, v___x_403_);
if (v___x_404_ == 0)
{
goto v___jp_391_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
lean_del_object(v___x_389_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_add(v_snd_387_, v___x_405_);
lean_dec(v_snd_387_);
v___x_407_ = lean_nat_add(v_pos_396_, v___x_405_);
v___x_408_ = lean_nat_dec_le(v___x_407_, v_stop_397_);
lean_dec(v___x_407_);
if (v___x_408_ == 0)
{
v___y_382_ = v___x_406_;
v___y_383_ = v_fst_386_;
goto v___jp_381_;
}
else
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_422_; 
lean_inc(v_col_398_);
lean_inc(v_stop_397_);
lean_inc(v_pos_396_);
v_isSharedCheck_422_ = !lean_is_exclusive(v_fst_386_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; lean_object* v_unused_424_; lean_object* v_unused_425_; 
v_unused_423_ = lean_ctor_get(v_fst_386_, 2);
lean_dec(v_unused_423_);
v_unused_424_ = lean_ctor_get(v_fst_386_, 1);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_fst_386_, 0);
lean_dec(v_unused_425_);
v___x_410_ = v_fst_386_;
v_isShared_411_ = v_isSharedCheck_422_;
goto v_resetjp_409_;
}
else
{
lean_dec(v_fst_386_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_422_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_str_412_; lean_object* v_startInclusive_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_420_; 
v_str_412_ = lean_ctor_get(v_s_379_, 0);
v_startInclusive_413_ = lean_ctor_get(v_s_379_, 1);
v___x_414_ = lean_nat_add(v_startInclusive_413_, v_pos_396_);
lean_dec(v_pos_396_);
v___x_415_ = lean_string_utf8_next_fast(v_str_412_, v___x_414_);
lean_dec(v___x_414_);
v___x_416_ = lean_nat_sub(v___x_415_, v_startInclusive_413_);
v___x_417_ = lean_nat_add(v_col_398_, v___x_405_);
lean_dec(v_col_398_);
v___x_418_ = 0;
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 2, v___x_417_);
lean_ctor_set(v___x_410_, 0, v___x_416_);
v___x_420_ = v___x_410_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_stop_397_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_417_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3, v___x_418_);
v___y_382_ = v___x_406_;
v___y_383_ = v___x_420_;
goto v___jp_381_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___boxed(lean_object* v_s_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg(v_s_432_, v_a_433_);
lean_dec_ref(v_s_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___redArg(lean_object* v___x_435_, lean_object* v_s_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v___x_435_, v___x_438_);
v___x_440_ = lean_nat_dec_le(v___x_439_, v_a_437_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_a_437_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; 
v___x_442_ = l_String_Slice_Pos_prev_x3f(v_s_436_, v_a_437_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_a_437_);
return v___x_443_;
}
else
{
lean_object* v_val_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_455_; 
v_val_444_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_455_ == 0)
{
v___x_446_ = v___x_442_;
v_isShared_447_ = v_isSharedCheck_455_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_val_444_);
lean_dec(v___x_442_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_455_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = l_String_Slice_Pos_get_x3f(v_s_436_, v_val_444_);
v___x_449_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0);
v___x_450_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
if (v___x_450_ == 0)
{
lean_object* v___x_452_; 
lean_dec(v_val_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_a_437_);
v___x_452_ = v___x_446_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_437_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
lean_del_object(v___x_446_);
lean_dec(v_a_437_);
v_a_437_ = v_val_444_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___redArg___boxed(lean_object* v___x_456_, lean_object* v_s_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___redArg(v___x_456_, v_s_457_, v_a_458_);
lean_dec_ref(v_s_457_);
lean_dec(v___x_456_);
return v_res_459_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_460_; lean_object* v___x_461_; 
v___x_460_ = 32;
v___x_461_ = lean_box_uint32(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0___boxed__const__1;
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_464_; lean_object* v___x_465_; 
v___x_464_ = 9;
v___x_465_ = lean_box_uint32(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1___boxed__const__1;
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f(lean_object* v_s_468_, lean_object* v_line_469_){
_start:
{
lean_object* v_after_470_; lean_object* v_indent_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_561_; 
v_after_470_ = lean_ctor_get(v_line_469_, 0);
v_indent_471_ = lean_ctor_get(v_line_469_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_line_469_);
if (v_isSharedCheck_561_ == 0)
{
v___x_473_ = v_line_469_;
v_isShared_474_ = v_isSharedCheck_561_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_indent_471_);
lean_inc(v_after_470_);
lean_dec(v_line_469_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_561_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_unsigned_to_nat(3u);
v___x_476_ = lean_nat_dec_le(v_indent_471_, v___x_475_);
lean_dec(v_indent_471_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_del_object(v___x_473_);
lean_dec_ref(v_after_470_);
v___x_477_ = lean_box(0);
return v___x_477_;
}
else
{
lean_object* v_pos_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v_pos_478_ = lean_ctor_get(v_after_470_, 0);
lean_inc(v_pos_478_);
v___x_479_ = lean_unsigned_to_nat(0u);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v___x_479_);
v___x_481_ = v___x_473_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_after_470_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_560_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; 
v___x_482_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg(v_s_468_, v___x_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v___x_483_; 
lean_dec(v_pos_478_);
v___x_483_ = lean_box(0);
return v___x_483_;
}
else
{
lean_object* v_val_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_559_; 
v_val_484_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_559_ == 0)
{
v___x_486_ = v___x_482_;
v_isShared_487_ = v_isSharedCheck_559_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_val_484_);
lean_dec(v___x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_559_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v_fst_488_; lean_object* v_snd_489_; lean_object* v___y_491_; lean_object* v_content_492_; lean_object* v_closeHashes_x3f_493_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; uint8_t v___x_507_; 
v_fst_488_ = lean_ctor_get(v_val_484_, 0);
lean_inc(v_fst_488_);
v_snd_489_ = lean_ctor_get(v_val_484_, 1);
lean_inc(v_snd_489_);
lean_dec(v_val_484_);
v___x_507_ = lean_nat_dec_lt(v___x_479_, v_snd_489_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v_snd_489_);
lean_dec(v_fst_488_);
lean_del_object(v___x_486_);
lean_dec(v_pos_478_);
v___x_508_ = lean_box(0);
return v___x_508_;
}
else
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(6u);
v___x_510_ = lean_nat_dec_le(v_snd_489_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec(v_snd_489_);
lean_dec(v_fst_488_);
lean_del_object(v___x_486_);
lean_dec(v_pos_478_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
else
{
lean_object* v_pos_512_; lean_object* v_stop_513_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_pos_512_ = lean_ctor_get(v_fst_488_, 0);
lean_inc(v_pos_512_);
v_stop_513_ = lean_ctor_get(v_fst_488_, 1);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_add(v_pos_512_, v___x_547_);
v___x_549_ = lean_nat_dec_le(v___x_548_, v_stop_513_);
lean_dec(v___x_548_);
if (v___x_549_ == 0)
{
goto v___jp_514_;
}
else
{
lean_object* v___x_550_; 
v___x_550_ = l_String_Slice_Pos_get_x3f(v_s_468_, v_pos_512_);
if (lean_obj_tag(v___x_550_) == 1)
{
lean_object* v_val_551_; uint32_t v___x_552_; uint32_t v___x_553_; uint8_t v___x_554_; 
v_val_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = 32;
v___x_553_ = lean_unbox_uint32(v_val_551_);
v___x_554_ = lean_uint32_dec_eq(v___x_553_, v___x_552_);
if (v___x_554_ == 0)
{
uint32_t v___x_555_; uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = 9;
v___x_556_ = lean_unbox_uint32(v_val_551_);
lean_dec(v_val_551_);
v___x_557_ = lean_uint32_dec_eq(v___x_556_, v___x_555_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v_pos_512_);
lean_dec(v_snd_489_);
lean_dec(v_fst_488_);
lean_del_object(v___x_486_);
lean_dec(v_pos_478_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
else
{
goto v___jp_514_;
}
}
else
{
lean_dec(v_val_551_);
goto v___jp_514_;
}
}
else
{
lean_dec(v___x_550_);
goto v___jp_514_;
}
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v_fst_516_; lean_object* v_pos_517_; lean_object* v_stop_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_endExclusive_521_; lean_object* v___x_522_; 
v___x_515_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols(v_s_468_, v_fst_488_);
v_fst_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_fst_516_);
lean_dec_ref(v___x_515_);
v_pos_517_ = lean_ctor_get(v_fst_516_, 0);
lean_inc_n(v_pos_517_, 2);
v_stop_518_ = lean_ctor_get(v_fst_516_, 1);
lean_inc(v_stop_518_);
lean_dec(v_fst_516_);
v___x_519_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_517_, v_stop_518_);
v___x_520_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(v_s_468_, v___x_519_);
v_endExclusive_521_ = lean_ctor_get(v___x_520_, 1);
lean_inc(v_endExclusive_521_);
v___x_522_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___redArg(v_pos_517_, v_s_468_, v_endExclusive_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; 
lean_dec_ref(v___x_520_);
lean_dec(v_pos_517_);
lean_dec(v_pos_512_);
lean_dec(v_snd_489_);
lean_del_object(v___x_486_);
lean_dec(v_pos_478_);
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_546_; 
v_val_524_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_546_ == 0)
{
v___x_526_ = v___x_522_;
v_isShared_527_ = v_isSharedCheck_546_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_dec(v___x_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_546_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_528_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_478_, v_pos_512_);
v___x_529_ = lean_box(0);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_val_524_, v___x_530_);
v___x_532_ = lean_nat_dec_le(v___x_531_, v_endExclusive_521_);
lean_dec(v___x_531_);
if (v___x_532_ == 0)
{
lean_del_object(v___x_526_);
lean_dec(v_val_524_);
lean_dec(v_pos_517_);
v___y_491_ = v___x_528_;
v_content_492_ = v___x_520_;
v_closeHashes_x3f_493_ = v___x_529_;
goto v___jp_490_;
}
else
{
uint8_t v_decide_533_; 
v_decide_533_ = lean_nat_dec_eq(v_val_524_, v_pos_517_);
if (v_decide_533_ == 0)
{
lean_object* v___x_534_; 
lean_del_object(v___x_526_);
v___x_534_ = l_String_Slice_Pos_prev_x3f(v_s_468_, v_val_524_);
if (lean_obj_tag(v___x_534_) == 1)
{
lean_object* v_val_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v___x_534_, 1);
v___x_536_ = l_String_Slice_Pos_get_x3f(v_s_468_, v_val_535_);
lean_dec(v_val_535_);
v___x_537_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0);
v___x_538_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1);
v___x_540_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___x_536_, v___x_539_);
lean_dec(v___x_536_);
if (v___x_540_ == 0)
{
lean_dec(v_val_524_);
lean_dec(v_pos_517_);
v___y_491_ = v___x_528_;
v_content_492_ = v___x_520_;
v_closeHashes_x3f_493_ = v___x_529_;
goto v___jp_490_;
}
else
{
lean_inc(v_endExclusive_521_);
lean_dec_ref(v___x_520_);
v___y_499_ = v_pos_517_;
v___y_500_ = v_val_524_;
v___y_501_ = v_endExclusive_521_;
v___y_502_ = v___x_528_;
goto v___jp_498_;
}
}
else
{
lean_inc(v_endExclusive_521_);
lean_dec(v___x_536_);
lean_dec_ref(v___x_520_);
v___y_499_ = v_pos_517_;
v___y_500_ = v_val_524_;
v___y_501_ = v_endExclusive_521_;
v___y_502_ = v___x_528_;
goto v___jp_498_;
}
}
else
{
lean_dec(v___x_534_);
lean_dec(v_val_524_);
lean_dec(v_pos_517_);
v___y_491_ = v___x_528_;
v_content_492_ = v___x_520_;
v_closeHashes_x3f_493_ = v___x_529_;
goto v___jp_490_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_543_; 
lean_inc(v_endExclusive_521_);
lean_dec_ref(v___x_520_);
lean_inc(v_val_524_);
v___x_541_ = l_Lean_Markdown_subsliceClamped___redArg(v_val_524_, v_endExclusive_521_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_541_);
v___x_543_ = v___x_526_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_517_, v_val_524_);
v___y_491_ = v___x_528_;
v_content_492_ = v___x_544_;
v_closeHashes_x3f_493_ = v___x_543_;
goto v___jp_490_;
}
}
}
}
}
}
}
}
v___jp_490_:
{
lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_494_, 0, v_snd_489_);
lean_ctor_set(v___x_494_, 1, v___y_491_);
lean_ctor_set(v___x_494_, 2, v_content_492_);
lean_ctor_set(v___x_494_, 3, v_closeHashes_x3f_493_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_494_);
v___x_496_ = v___x_486_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
v___jp_498_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc(v___y_500_);
v___x_503_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_500_, v___y_501_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
v___x_505_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_499_, v___y_500_);
v___x_506_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(v_s_468_, v___x_505_);
v___y_491_ = v___y_502_;
v_content_492_ = v___x_506_;
v_closeHashes_x3f_493_ = v___x_504_;
goto v___jp_490_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___boxed(lean_object* v_s_562_, lean_object* v_line_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f(v_s_562_, v_line_563_);
lean_dec_ref(v_s_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1(lean_object* v_s_565_, lean_object* v_inst_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg(v_s_565_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___boxed(lean_object* v_s_569_, lean_object* v_inst_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1(v_s_569_, v_inst_570_, v_a_571_);
lean_dec_ref(v_s_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2(lean_object* v___x_573_, lean_object* v_s_574_, lean_object* v_inst_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___redArg(v___x_573_, v_s_574_, v_a_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2___boxed(lean_object* v___x_578_, lean_object* v_s_579_, lean_object* v_inst_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__2(v___x_578_, v_s_579_, v_inst_580_, v_a_581_);
lean_dec_ref(v_s_579_);
lean_dec(v___x_578_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl___redArg(lean_object* v_x_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_tag_nat(v_x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl___redArg___boxed(lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl___redArg(v_x_585_);
lean_dec(v_x_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl(lean_object* v_s_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_tag_nat(v_x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl___boxed(lean_object* v_s_590_, lean_object* v_x_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorIdx___impl(v_s_590_, v_x_591_);
lean_dec(v_x_591_);
lean_dec_ref(v_s_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(lean_object* v_t_593_, lean_object* v_k_594_){
_start:
{
if (lean_obj_tag(v_t_593_) == 1)
{
lean_object* v_pos_595_; lean_object* v___x_596_; 
v_pos_595_ = lean_ctor_get(v_t_593_, 0);
lean_inc(v_pos_595_);
lean_dec_ref_known(v_t_593_, 1);
v___x_596_ = lean_apply_1(v_k_594_, v_pos_595_);
return v___x_596_;
}
else
{
lean_dec(v_t_593_);
return v_k_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim(lean_object* v_s_597_, lean_object* v_motive_598_, lean_object* v_ctorIdx_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_k_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(v_t_600_, v_k_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___boxed(lean_object* v_s_604_, lean_object* v_motive_605_, lean_object* v_ctorIdx_606_, lean_object* v_t_607_, lean_object* v_h_608_, lean_object* v_k_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim(v_s_604_, v_motive_605_, v_ctorIdx_606_, v_t_607_, v_h_608_, v_k_609_);
lean_dec(v_ctorIdx_606_);
lean_dec_ref(v_s_604_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_isBreak_elim___redArg(lean_object* v_t_611_, lean_object* v_isBreak_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(v_t_611_, v_isBreak_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_isBreak_elim(lean_object* v_s_614_, lean_object* v_motive_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_isBreak_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(v_t_616_, v_isBreak_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_isBreak_elim___boxed(lean_object* v_s_620_, lean_object* v_motive_621_, lean_object* v_t_622_, lean_object* v_h_623_, lean_object* v_isBreak_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_isBreak_elim(v_s_620_, v_motive_621_, v_t_622_, v_h_623_, v_isBreak_624_);
lean_dec_ref(v_s_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_failsAt_elim___redArg(lean_object* v_t_626_, lean_object* v_failsAt_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(v_t_626_, v_failsAt_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_failsAt_elim(lean_object* v_s_629_, lean_object* v_motive_630_, lean_object* v_t_631_, lean_object* v_h_632_, lean_object* v_failsAt_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(v_t_631_, v_failsAt_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_failsAt_elim___boxed(lean_object* v_s_635_, lean_object* v_motive_636_, lean_object* v_t_637_, lean_object* v_h_638_, lean_object* v_failsAt_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_failsAt_elim(v_s_635_, v_motive_636_, v_t_637_, v_h_638_, v_failsAt_639_);
lean_dec_ref(v_s_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_notCandidate_elim___redArg(lean_object* v_t_641_, lean_object* v_notCandidate_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(v_t_641_, v_notCandidate_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_notCandidate_elim(lean_object* v_s_644_, lean_object* v_motive_645_, lean_object* v_t_646_, lean_object* v_h_647_, lean_object* v_notCandidate_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_ctorElim___redArg(v_t_646_, v_notCandidate_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_notCandidate_elim___boxed(lean_object* v_s_650_, lean_object* v_motive_651_, lean_object* v_t_652_, lean_object* v_h_653_, lean_object* v_notCandidate_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ThematicBreakCheck_notCandidate_elim(v_s_650_, v_motive_651_, v_t_652_, v_h_653_, v_notCandidate_654_);
lean_dec_ref(v_s_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___redArg(lean_object* v_s_656_, uint32_t v_val_657_, uint8_t v___y_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_snd_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_735_; 
v_snd_660_ = lean_ctor_get(v_a_659_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v_a_659_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v_a_659_, 0);
lean_dec(v_unused_736_);
v___x_662_ = v_a_659_;
v_isShared_663_ = v_isSharedCheck_735_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snd_660_);
lean_dec(v_a_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_735_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v_fst_664_; lean_object* v_snd_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_734_; 
v_fst_664_ = lean_ctor_get(v_snd_660_, 0);
v_snd_665_ = lean_ctor_get(v_snd_660_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_snd_660_);
if (v_isSharedCheck_734_ == 0)
{
v___x_667_ = v_snd_660_;
v_isShared_668_ = v_isSharedCheck_734_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_snd_665_);
lean_inc(v_fst_664_);
lean_dec(v_snd_660_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_734_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_pos_669_; lean_object* v_stop_670_; lean_object* v_col_671_; lean_object* v___x_672_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_pos_669_ = lean_ctor_get(v_fst_664_, 0);
v_stop_670_ = lean_ctor_get(v_fst_664_, 1);
v_col_671_ = lean_ctor_get(v_fst_664_, 2);
v___x_672_ = lean_box(0);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_pos_669_, v___x_680_);
v___x_682_ = lean_nat_dec_le(v___x_681_, v_stop_670_);
lean_dec(v___x_681_);
if (v___x_682_ == 0)
{
goto v___jp_673_;
}
else
{
lean_object* v___x_683_; 
v___x_683_ = l_String_Slice_Pos_get_x3f(v_s_656_, v_pos_669_);
if (lean_obj_tag(v___x_683_) == 1)
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_733_; 
lean_del_object(v___x_667_);
lean_del_object(v___x_662_);
v_val_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_733_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_733_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_733_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
uint32_t v___x_688_; uint8_t v___x_689_; 
v___x_688_ = lean_unbox_uint32(v_val_684_);
v___x_689_ = lean_uint32_dec_eq(v___x_688_, v_val_657_);
if (v___x_689_ == 0)
{
uint32_t v___x_701_; uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_701_ = 32;
v___x_702_ = lean_unbox_uint32(v_val_684_);
v___x_703_ = lean_uint32_dec_eq(v___x_702_, v___x_701_);
if (v___x_703_ == 0)
{
uint32_t v___x_704_; uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_704_ = 9;
v___x_705_ = lean_unbox_uint32(v_val_684_);
lean_dec(v_val_684_);
v___x_706_ = lean_uint32_dec_eq(v___x_705_, v___x_704_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_inc(v_pos_669_);
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v_pos_669_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_707_);
v___x_709_ = v___x_686_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_712_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_fst_664_);
lean_ctor_set(v___x_710_, 1, v_snd_665_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
return v___x_711_;
}
}
else
{
lean_inc(v_col_671_);
lean_inc(v_stop_670_);
lean_inc(v_pos_669_);
lean_del_object(v___x_686_);
lean_dec(v_fst_664_);
goto v___jp_690_;
}
}
else
{
lean_inc(v_col_671_);
lean_inc(v_stop_670_);
lean_inc(v_pos_669_);
lean_del_object(v___x_686_);
lean_dec(v_val_684_);
lean_dec(v_fst_664_);
goto v___jp_690_;
}
}
else
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_729_; 
lean_inc(v_col_671_);
lean_inc(v_stop_670_);
lean_inc(v_pos_669_);
lean_del_object(v___x_686_);
lean_dec(v_val_684_);
v_isSharedCheck_729_ = !lean_is_exclusive(v_fst_664_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; lean_object* v_unused_731_; lean_object* v_unused_732_; 
v_unused_730_ = lean_ctor_get(v_fst_664_, 2);
lean_dec(v_unused_730_);
v_unused_731_ = lean_ctor_get(v_fst_664_, 1);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_fst_664_, 0);
lean_dec(v_unused_732_);
v___x_714_ = v_fst_664_;
v_isShared_715_ = v_isSharedCheck_729_;
goto v_resetjp_713_;
}
else
{
lean_dec(v_fst_664_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_729_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_str_716_; lean_object* v_startInclusive_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v_str_716_ = lean_ctor_get(v_s_656_, 0);
v_startInclusive_717_ = lean_ctor_get(v_s_656_, 1);
v___x_718_ = lean_nat_add(v_snd_665_, v___x_680_);
lean_dec(v_snd_665_);
v___x_719_ = lean_nat_add(v_startInclusive_717_, v_pos_669_);
lean_dec(v_pos_669_);
v___x_720_ = lean_string_utf8_next_fast(v_str_716_, v___x_719_);
lean_dec(v___x_719_);
v___x_721_ = lean_nat_sub(v___x_720_, v_startInclusive_717_);
v___x_722_ = lean_nat_add(v_col_671_, v___x_680_);
lean_dec(v_col_671_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 2, v___x_722_);
lean_ctor_set(v___x_714_, 0, v___x_721_);
v___x_724_ = v___x_714_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_stop_670_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v___x_722_);
v___x_724_ = v_reuseFailAlloc_728_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_ctor_set_uint8(v___x_724_, sizeof(void*)*3, v___y_658_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_718_);
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_672_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v_a_659_ = v___x_726_;
goto _start;
}
}
}
v___jp_690_:
{
lean_object* v_str_691_; lean_object* v_startInclusive_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_str_691_ = lean_ctor_get(v_s_656_, 0);
v_startInclusive_692_ = lean_ctor_get(v_s_656_, 1);
v___x_693_ = lean_nat_add(v_startInclusive_692_, v_pos_669_);
lean_dec(v_pos_669_);
v___x_694_ = lean_string_utf8_next_fast(v_str_691_, v___x_693_);
lean_dec(v___x_693_);
v___x_695_ = lean_nat_sub(v___x_694_, v_startInclusive_692_);
v___x_696_ = lean_nat_add(v_col_671_, v___x_680_);
lean_dec(v_col_671_);
v___x_697_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v_stop_670_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*3, v___x_689_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_snd_665_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_672_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v_a_659_ = v___x_699_;
goto _start;
}
}
}
else
{
lean_dec(v___x_683_);
goto v___jp_673_;
}
}
v___jp_673_:
{
lean_object* v___x_675_; 
if (v_isShared_668_ == 0)
{
v___x_675_ = v___x_667_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_fst_664_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_snd_665_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 1, v___x_675_);
lean_ctor_set(v___x_662_, 0, v___x_672_);
v___x_677_ = v___x_662_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___redArg___boxed(lean_object* v_s_737_, lean_object* v_val_738_, lean_object* v___y_739_, lean_object* v_a_740_){
_start:
{
uint32_t v_val_2362__boxed_741_; uint8_t v___y_2363__boxed_742_; lean_object* v_res_743_; 
v_val_2362__boxed_741_ = lean_unbox_uint32(v_val_738_);
lean_dec(v_val_738_);
v___y_2363__boxed_742_ = lean_unbox(v___y_739_);
v_res_743_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___redArg(v_s_737_, v_val_2362__boxed_741_, v___y_2363__boxed_742_, v_a_740_);
lean_dec_ref(v_s_737_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak(lean_object* v_s_744_, lean_object* v_line_745_){
_start:
{
lean_object* v_after_746_; lean_object* v_indent_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_799_; 
v_after_746_ = lean_ctor_get(v_line_745_, 0);
v_indent_747_ = lean_ctor_get(v_line_745_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_line_745_);
if (v_isSharedCheck_799_ == 0)
{
v___x_749_ = v_line_745_;
v_isShared_750_ = v_isSharedCheck_799_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_indent_747_);
lean_inc(v_after_746_);
lean_dec(v_line_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_799_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_unsigned_to_nat(4u);
v___x_752_ = lean_nat_dec_le(v___x_751_, v_indent_747_);
lean_dec(v_indent_747_);
if (v___x_752_ == 0)
{
lean_object* v_pos_753_; lean_object* v_stop_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_pos_753_ = lean_ctor_get(v_after_746_, 0);
v_stop_754_ = lean_ctor_get(v_after_746_, 1);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_pos_753_, v___x_755_);
v___x_757_ = lean_nat_dec_le(v___x_756_, v_stop_754_);
lean_dec(v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_del_object(v___x_749_);
lean_dec_ref(v_after_746_);
v___x_758_ = lean_box(2);
return v___x_758_;
}
else
{
lean_object* v___x_759_; 
v___x_759_ = l_String_Slice_Pos_get_x3f(v_s_744_, v_pos_753_);
if (lean_obj_tag(v___x_759_) == 1)
{
lean_object* v_val_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_796_; 
v_val_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_796_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_796_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_val_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_796_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; uint8_t v___y_766_; uint32_t v___x_786_; uint32_t v___x_787_; uint8_t v___x_788_; 
v___x_764_ = lean_unsigned_to_nat(3u);
v___x_786_ = 42;
v___x_787_ = lean_unbox_uint32(v_val_760_);
v___x_788_ = lean_uint32_dec_eq(v___x_787_, v___x_786_);
if (v___x_788_ == 0)
{
uint32_t v___x_789_; uint32_t v___x_790_; uint8_t v___x_791_; 
v___x_789_ = 45;
v___x_790_ = lean_unbox_uint32(v_val_760_);
v___x_791_ = lean_uint32_dec_eq(v___x_790_, v___x_789_);
if (v___x_791_ == 0)
{
uint32_t v___x_792_; uint32_t v___x_793_; uint8_t v___x_794_; 
v___x_792_ = 95;
v___x_793_ = lean_unbox_uint32(v_val_760_);
v___x_794_ = lean_uint32_dec_eq(v___x_793_, v___x_792_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_del_object(v___x_762_);
lean_dec(v_val_760_);
lean_del_object(v___x_749_);
lean_dec_ref(v_after_746_);
v___x_795_ = lean_box(2);
return v___x_795_;
}
else
{
v___y_766_ = v___x_752_;
goto v___jp_765_;
}
}
else
{
v___y_766_ = v___x_752_;
goto v___jp_765_;
}
}
else
{
v___y_766_ = v___x_752_;
goto v___jp_765_;
}
v___jp_765_:
{
lean_object* v_markerCount_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v_markerCount_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 1, v_markerCount_767_);
v___x_770_ = v___x_749_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_after_746_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_markerCount_767_);
v___x_770_ = v_reuseFailAlloc_785_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; uint32_t v___x_772_; lean_object* v___x_773_; lean_object* v_fst_774_; 
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_768_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_unbox_uint32(v_val_760_);
lean_dec(v_val_760_);
v___x_773_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___redArg(v_s_744_, v___x_772_, v___y_766_, v___x_771_);
v_fst_774_ = lean_ctor_get(v___x_773_, 0);
if (lean_obj_tag(v_fst_774_) == 0)
{
lean_object* v_snd_775_; lean_object* v_fst_776_; lean_object* v_snd_777_; uint8_t v___x_778_; 
v_snd_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_snd_775_);
lean_dec_ref(v___x_773_);
v_fst_776_ = lean_ctor_get(v_snd_775_, 0);
lean_inc(v_fst_776_);
v_snd_777_ = lean_ctor_get(v_snd_775_, 1);
lean_inc(v_snd_777_);
lean_dec(v_snd_775_);
v___x_778_ = lean_nat_dec_le(v___x_764_, v_snd_777_);
lean_dec(v_snd_777_);
if (v___x_778_ == 0)
{
lean_object* v_pos_779_; lean_object* v___x_781_; 
v_pos_779_ = lean_ctor_get(v_fst_776_, 0);
lean_inc(v_pos_779_);
lean_dec(v_fst_776_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_pos_779_);
v___x_781_ = v___x_762_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_pos_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v___x_783_; 
lean_dec(v_fst_776_);
lean_del_object(v___x_762_);
v___x_783_ = lean_box(0);
return v___x_783_;
}
}
else
{
lean_object* v_val_784_; 
lean_inc_ref(v_fst_774_);
lean_dec_ref(v___x_773_);
lean_del_object(v___x_762_);
v_val_784_ = lean_ctor_get(v_fst_774_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v_fst_774_, 1);
return v_val_784_;
}
}
}
}
}
else
{
lean_object* v___x_797_; 
lean_dec(v___x_759_);
lean_del_object(v___x_749_);
lean_dec_ref(v_after_746_);
v___x_797_ = lean_box(2);
return v___x_797_;
}
}
}
else
{
lean_object* v___x_798_; 
lean_del_object(v___x_749_);
lean_dec_ref(v_after_746_);
v___x_798_ = lean_box(2);
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak___boxed(lean_object* v_s_800_, lean_object* v_line_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak(v_s_800_, v_line_801_);
lean_dec_ref(v_s_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0(lean_object* v_s_803_, uint32_t v_val_804_, uint8_t v___y_805_, lean_object* v_inst_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___redArg(v_s_803_, v_val_804_, v___y_805_, v_a_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0___boxed(lean_object* v_s_809_, lean_object* v_val_810_, lean_object* v___y_811_, lean_object* v_inst_812_, lean_object* v_a_813_){
_start:
{
uint32_t v_val_2594__boxed_814_; uint8_t v___y_2595__boxed_815_; lean_object* v_res_816_; 
v_val_2594__boxed_814_ = lean_unbox_uint32(v_val_810_);
lean_dec(v_val_810_);
v___y_2595__boxed_815_ = lean_unbox(v___y_811_);
v_res_816_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak_spec__0(v_s_809_, v_val_2594__boxed_814_, v___y_2595__boxed_815_, v_inst_812_, v_a_813_);
lean_dec_ref(v_s_809_);
return v_res_816_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak(lean_object* v_s_817_, lean_object* v_line_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak(v_s_817_, v_line_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
uint8_t v___x_820_; 
v___x_820_ = 1;
return v___x_820_;
}
else
{
uint8_t v___x_821_; 
lean_dec(v___x_819_);
v___x_821_ = 0;
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak___boxed(lean_object* v_s_822_, lean_object* v_line_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak(v_s_822_, v_line_823_);
lean_dec_ref(v_s_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg(lean_object* v_s_826_, uint32_t v_val_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_fst_829_; lean_object* v_snd_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_870_; 
v_fst_829_ = lean_ctor_get(v_a_828_, 0);
v_snd_830_ = lean_ctor_get(v_a_828_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_870_ == 0)
{
v___x_832_ = v_a_828_;
v_isShared_833_ = v_isSharedCheck_870_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snd_830_);
lean_inc(v_fst_829_);
lean_dec(v_a_828_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_870_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_pos_834_; lean_object* v_stop_835_; lean_object* v_col_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_pos_834_ = lean_ctor_get(v_fst_829_, 0);
v_stop_835_ = lean_ctor_get(v_fst_829_, 1);
v_col_836_ = lean_ctor_get(v_fst_829_, 2);
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_add(v_pos_834_, v___x_837_);
v___x_839_ = lean_nat_dec_le(v___x_838_, v_stop_835_);
lean_dec(v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_841_; 
if (v_isShared_833_ == 0)
{
v___x_841_ = v___x_832_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_fst_829_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_snd_830_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v_str_843_; lean_object* v_startInclusive_844_; lean_object* v___x_845_; uint32_t v___x_846_; uint8_t v___x_847_; 
v_str_843_ = lean_ctor_get(v_s_826_, 0);
v_startInclusive_844_ = lean_ctor_get(v_s_826_, 1);
v___x_845_ = lean_nat_add(v_startInclusive_844_, v_pos_834_);
v___x_846_ = lean_string_utf8_get_fast(v_str_843_, v___x_845_);
v___x_847_ = lean_uint32_dec_eq(v___x_846_, v_val_827_);
if (v___x_847_ == 0)
{
lean_object* v___x_849_; 
lean_dec(v___x_845_);
if (v_isShared_833_ == 0)
{
v___x_849_ = v___x_832_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_829_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_snd_830_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
else
{
lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_866_; 
lean_inc(v_col_836_);
lean_inc(v_stop_835_);
v_isSharedCheck_866_ = !lean_is_exclusive(v_fst_829_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_867_ = lean_ctor_get(v_fst_829_, 2);
lean_dec(v_unused_867_);
v_unused_868_ = lean_ctor_get(v_fst_829_, 1);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_fst_829_, 0);
lean_dec(v_unused_869_);
v___x_852_ = v_fst_829_;
v_isShared_853_ = v_isSharedCheck_866_;
goto v_resetjp_851_;
}
else
{
lean_dec(v_fst_829_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_866_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_854_ = 0;
v___x_855_ = lean_nat_add(v_snd_830_, v___x_837_);
lean_dec(v_snd_830_);
v___x_856_ = lean_string_utf8_next_fast(v_str_843_, v___x_845_);
lean_dec(v___x_845_);
v___x_857_ = lean_nat_sub(v___x_856_, v_startInclusive_844_);
v___x_858_ = lean_nat_add(v_col_836_, v___x_837_);
lean_dec(v_col_836_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 2, v___x_858_);
lean_ctor_set(v___x_852_, 0, v___x_857_);
v___x_860_ = v___x_852_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_stop_835_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v___x_858_);
v___x_860_ = v_reuseFailAlloc_865_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
lean_ctor_set_uint8(v___x_860_, sizeof(void*)*3, v___x_854_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v___x_855_);
lean_ctor_set(v___x_832_, 0, v___x_860_);
v___x_862_ = v___x_832_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_855_);
v___x_862_ = v_reuseFailAlloc_864_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v_a_828_ = v___x_862_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg___boxed(lean_object* v_s_871_, lean_object* v_val_872_, lean_object* v_a_873_){
_start:
{
uint32_t v_val_2842__boxed_874_; lean_object* v_res_875_; 
v_val_2842__boxed_874_ = lean_unbox_uint32(v_val_872_);
lean_dec(v_val_872_);
v_res_875_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg(v_s_871_, v_val_2842__boxed_874_, v_a_873_);
lean_dec_ref(v_s_871_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg(lean_object* v_s_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_912_; 
v_fst_878_ = lean_ctor_get(v_a_877_, 0);
v_snd_879_ = lean_ctor_get(v_a_877_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_912_ == 0)
{
v___x_881_ = v_a_877_;
v_isShared_882_ = v_isSharedCheck_912_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_snd_879_);
lean_inc(v_fst_878_);
lean_dec(v_a_877_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_912_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_pos_883_; lean_object* v_stop_884_; lean_object* v_col_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_pos_883_ = lean_ctor_get(v_fst_878_, 0);
v_stop_884_ = lean_ctor_get(v_fst_878_, 1);
v_col_885_ = lean_ctor_get(v_fst_878_, 2);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_nat_add(v_pos_883_, v___x_886_);
v___x_888_ = lean_nat_dec_le(v___x_887_, v_stop_884_);
lean_dec(v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_890_; 
if (v_isShared_882_ == 0)
{
v___x_890_ = v___x_881_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_878_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_snd_879_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
lean_object* v_str_892_; lean_object* v_startInclusive_893_; lean_object* v___x_894_; uint32_t v___x_906_; uint32_t v___x_907_; uint8_t v___x_908_; 
v_str_892_ = lean_ctor_get(v_s_876_, 0);
v_startInclusive_893_ = lean_ctor_get(v_s_876_, 1);
v___x_894_ = lean_nat_add(v_startInclusive_893_, v_pos_883_);
v___x_906_ = lean_string_utf8_get_fast(v_str_892_, v___x_894_);
v___x_907_ = 32;
v___x_908_ = lean_uint32_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
uint32_t v___x_909_; uint8_t v___x_910_; 
v___x_909_ = 9;
v___x_910_ = lean_uint32_dec_eq(v___x_906_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
lean_dec(v___x_894_);
lean_del_object(v___x_881_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v_fst_878_);
lean_ctor_set(v___x_911_, 1, v_snd_879_);
return v___x_911_;
}
else
{
lean_inc(v_col_885_);
lean_inc(v_stop_884_);
lean_dec(v_fst_878_);
goto v___jp_895_;
}
}
else
{
lean_inc(v_col_885_);
lean_inc(v_stop_884_);
lean_dec(v_fst_878_);
goto v___jp_895_;
}
v___jp_895_:
{
uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_896_ = 0;
v___x_897_ = lean_nat_add(v_snd_879_, v___x_886_);
lean_dec(v_snd_879_);
v___x_898_ = lean_string_utf8_next_fast(v_str_892_, v___x_894_);
lean_dec(v___x_894_);
v___x_899_ = lean_nat_sub(v___x_898_, v_startInclusive_893_);
v___x_900_ = lean_nat_add(v_col_885_, v___x_886_);
lean_dec(v_col_885_);
v___x_901_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v_stop_884_);
lean_ctor_set(v___x_901_, 2, v___x_900_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*3, v___x_896_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v___x_897_);
lean_ctor_set(v___x_881_, 0, v___x_901_);
v___x_903_ = v___x_881_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_897_);
v___x_903_ = v_reuseFailAlloc_905_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
v_a_877_ = v___x_903_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg___boxed(lean_object* v_s_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg(v_s_913_, v_a_914_);
lean_dec_ref(v_s_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f(lean_object* v_s_916_, lean_object* v_line_917_){
_start:
{
lean_object* v_after_918_; lean_object* v_indent_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_972_; 
v_after_918_ = lean_ctor_get(v_line_917_, 0);
v_indent_919_ = lean_ctor_get(v_line_917_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_line_917_);
if (v_isSharedCheck_972_ == 0)
{
v___x_921_ = v_line_917_;
v_isShared_922_ = v_isSharedCheck_972_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_indent_919_);
lean_inc(v_after_918_);
lean_dec(v_line_917_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_972_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_unsigned_to_nat(3u);
v___x_924_ = lean_nat_dec_le(v_indent_919_, v___x_923_);
lean_dec(v_indent_919_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
lean_del_object(v___x_921_);
lean_dec_ref(v_after_918_);
v___x_925_ = lean_box(0);
return v___x_925_;
}
else
{
lean_object* v_pos_926_; lean_object* v_stop_927_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_pos_926_ = lean_ctor_get(v_after_918_, 0);
lean_inc(v_pos_926_);
v_stop_927_ = lean_ctor_get(v_after_918_, 1);
v___x_937_ = lean_unsigned_to_nat(1u);
v___x_938_ = lean_nat_add(v_pos_926_, v___x_937_);
v___x_939_ = lean_nat_dec_le(v___x_938_, v_stop_927_);
lean_dec(v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; 
lean_dec(v_pos_926_);
lean_del_object(v___x_921_);
lean_dec_ref(v_after_918_);
v___x_940_ = lean_box(0);
return v___x_940_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = l_String_Slice_Pos_get_x3f(v_s_916_, v_pos_926_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v___x_942_; 
lean_dec(v_pos_926_);
lean_del_object(v___x_921_);
lean_dec_ref(v_after_918_);
v___x_942_ = lean_box(0);
return v___x_942_;
}
else
{
lean_object* v_val_943_; uint32_t v___x_944_; uint32_t v___x_945_; uint8_t v___x_946_; 
v_val_943_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_val_943_);
lean_dec_ref_known(v___x_941_, 1);
v___x_944_ = 61;
v___x_945_ = lean_unbox_uint32(v_val_943_);
v___x_946_ = lean_uint32_dec_eq(v___x_945_, v___x_944_);
if (v___x_946_ == 0)
{
uint32_t v___x_968_; uint32_t v___x_969_; uint8_t v___x_970_; 
v___x_968_ = 45;
v___x_969_ = lean_unbox_uint32(v_val_943_);
v___x_970_ = lean_uint32_dec_eq(v___x_969_, v___x_968_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v_val_943_);
lean_dec(v_pos_926_);
lean_del_object(v___x_921_);
lean_dec_ref(v_after_918_);
v___x_971_ = lean_box(0);
return v___x_971_;
}
else
{
goto v___jp_947_;
}
}
else
{
goto v___jp_947_;
}
v___jp_947_:
{
lean_object* v_count_948_; lean_object* v___x_949_; uint32_t v___x_950_; lean_object* v___x_951_; lean_object* v_fst_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_966_; 
v_count_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v_after_918_);
lean_ctor_set(v___x_949_, 1, v_count_948_);
v___x_950_ = lean_unbox_uint32(v_val_943_);
lean_dec(v_val_943_);
v___x_951_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg(v_s_916_, v___x_950_, v___x_949_);
v_fst_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_951_, 1);
lean_dec(v_unused_967_);
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_fst_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
lean_inc(v_fst_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_count_948_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_fst_952_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_count_948_);
v___x_957_ = v_reuseFailAlloc_965_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v_fst_959_; lean_object* v_pos_960_; lean_object* v_stop_961_; uint8_t v___x_962_; 
v___x_958_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg(v_s_916_, v___x_957_);
v_fst_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_fst_959_);
lean_dec_ref(v___x_958_);
v_pos_960_ = lean_ctor_get(v_fst_959_, 0);
lean_inc(v_pos_960_);
v_stop_961_ = lean_ctor_get(v_fst_959_, 1);
lean_inc(v_stop_961_);
lean_dec(v_fst_959_);
v___x_962_ = lean_nat_dec_le(v_stop_961_, v_pos_960_);
lean_dec(v_pos_960_);
lean_dec(v_stop_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v_fst_952_);
lean_dec(v_pos_926_);
lean_del_object(v___x_921_);
v___x_963_ = lean_box(0);
return v___x_963_;
}
else
{
if (v___x_946_ == 0)
{
lean_object* v___x_964_; 
v___x_964_ = lean_unsigned_to_nat(2u);
v___y_929_ = v_fst_952_;
v___y_930_ = v___x_964_;
goto v___jp_928_;
}
else
{
v___y_929_ = v_fst_952_;
v___y_930_ = v___x_937_;
goto v___jp_928_;
}
}
}
}
}
}
}
v___jp_928_:
{
lean_object* v_pos_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v_pos_931_ = lean_ctor_get(v___y_929_, 0);
lean_inc(v_pos_931_);
lean_dec(v___y_929_);
v___x_932_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_926_, v_pos_931_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_932_);
lean_ctor_set(v___x_921_, 0, v___y_930_);
v___x_934_ = v___x_921_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___y_930_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_932_);
v___x_934_ = v_reuseFailAlloc_936_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f___boxed(lean_object* v_s_973_, lean_object* v_line_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f(v_s_973_, v_line_974_);
lean_dec_ref(v_s_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0(lean_object* v_s_976_, uint32_t v_val_977_, lean_object* v_inst_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg(v_s_976_, v_val_977_, v_a_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___boxed(lean_object* v_s_981_, lean_object* v_val_982_, lean_object* v_inst_983_, lean_object* v_a_984_){
_start:
{
uint32_t v_val_3065__boxed_985_; lean_object* v_res_986_; 
v_val_3065__boxed_985_ = lean_unbox_uint32(v_val_982_);
lean_dec(v_val_982_);
v_res_986_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0(v_s_981_, v_val_3065__boxed_985_, v_inst_983_, v_a_984_);
lean_dec_ref(v_s_981_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1(lean_object* v_s_987_, lean_object* v_inst_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg(v_s_987_, v_a_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___boxed(lean_object* v_s_991_, lean_object* v_inst_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1(v_s_991_, v_inst_992_, v_a_993_);
lean_dec_ref(v_s_991_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___redArg(lean_object* v_s_995_, uint8_t v_val_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1040_; 
v_fst_998_ = lean_ctor_get(v_a_997_, 0);
v_snd_999_ = lean_ctor_get(v_a_997_, 1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_997_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1001_ = v_a_997_;
v_isShared_1002_ = v_isSharedCheck_1040_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snd_999_);
lean_inc(v_fst_998_);
lean_dec(v_a_997_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1040_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_pos_1003_; lean_object* v_stop_1004_; lean_object* v_col_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_pos_1003_ = lean_ctor_get(v_fst_998_, 0);
v_stop_1004_ = lean_ctor_get(v_fst_998_, 1);
v_col_1005_ = lean_ctor_get(v_fst_998_, 2);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = lean_nat_add(v_pos_1003_, v___x_1006_);
v___x_1008_ = lean_nat_dec_le(v___x_1007_, v_stop_1004_);
lean_dec(v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1010_; 
if (v_isShared_1002_ == 0)
{
v___x_1010_ = v___x_1001_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_fst_998_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_snd_999_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v_str_1012_; lean_object* v_startInclusive_1013_; lean_object* v___x_1014_; uint32_t v___x_1015_; uint32_t v___x_1016_; uint8_t v___x_1017_; 
v_str_1012_ = lean_ctor_get(v_s_995_, 0);
v_startInclusive_1013_ = lean_ctor_get(v_s_995_, 1);
v___x_1014_ = lean_nat_add(v_startInclusive_1013_, v_pos_1003_);
v___x_1015_ = lean_string_utf8_get_fast(v_str_1012_, v___x_1014_);
v___x_1016_ = l_Lean_Markdown_FenceChar_toChar(v_val_996_);
v___x_1017_ = lean_uint32_dec_eq(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1019_; 
lean_dec(v___x_1014_);
if (v_isShared_1002_ == 0)
{
v___x_1019_ = v___x_1001_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_fst_998_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_snd_999_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
else
{
lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1036_; 
lean_inc(v_col_1005_);
lean_inc(v_stop_1004_);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_fst_998_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; lean_object* v_unused_1038_; lean_object* v_unused_1039_; 
v_unused_1037_ = lean_ctor_get(v_fst_998_, 2);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_fst_998_, 1);
lean_dec(v_unused_1038_);
v_unused_1039_ = lean_ctor_get(v_fst_998_, 0);
lean_dec(v_unused_1039_);
v___x_1022_ = v_fst_998_;
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v_fst_998_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1024_ = 0;
v___x_1025_ = lean_nat_add(v_snd_999_, v___x_1006_);
lean_dec(v_snd_999_);
v___x_1026_ = lean_string_utf8_next_fast(v_str_1012_, v___x_1014_);
lean_dec(v___x_1014_);
v___x_1027_ = lean_nat_sub(v___x_1026_, v_startInclusive_1013_);
v___x_1028_ = lean_nat_add(v_col_1005_, v___x_1006_);
lean_dec(v_col_1005_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 2, v___x_1028_);
lean_ctor_set(v___x_1022_, 0, v___x_1027_);
v___x_1030_ = v___x_1022_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_stop_1004_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*3, v___x_1024_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___x_1025_);
lean_ctor_set(v___x_1001_, 0, v___x_1030_);
v___x_1032_ = v___x_1001_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1025_);
v___x_1032_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v_a_997_ = v___x_1032_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___redArg___boxed(lean_object* v_s_1041_, lean_object* v_val_1042_, lean_object* v_a_1043_){
_start:
{
uint8_t v_val_5022__boxed_1044_; lean_object* v_res_1045_; 
v_val_5022__boxed_1044_ = lean_unbox(v_val_1042_);
v_res_1045_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___redArg(v_s_1041_, v_val_5022__boxed_1044_, v_a_1043_);
lean_dec_ref(v_s_1041_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___redArg(lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_a_1049_, lean_object* v_b_1050_){
_start:
{
lean_object* v___x_1051_; uint8_t v_decide_1052_; 
v___x_1051_ = lean_nat_sub(v___x_1046_, v___x_1047_);
v_decide_1052_ = lean_nat_dec_eq(v_a_1049_, v___x_1051_);
lean_dec(v___x_1051_);
if (v_decide_1052_ == 0)
{
lean_object* v___x_1053_; uint32_t v___x_1054_; uint32_t v___x_1055_; uint8_t v___x_1056_; 
v___x_1053_ = lean_nat_add(v___x_1047_, v_a_1049_);
lean_dec(v_a_1049_);
v___x_1054_ = lean_string_utf8_get_fast(v___x_1048_, v___x_1053_);
v___x_1055_ = 96;
v___x_1056_ = lean_uint32_dec_eq(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_string_utf8_next_fast(v___x_1048_, v___x_1053_);
lean_dec(v___x_1053_);
v___x_1059_ = lean_nat_sub(v___x_1058_, v___x_1047_);
v_a_1049_ = v___x_1059_;
v_b_1050_ = v___x_1057_;
goto _start;
}
else
{
lean_object* v___x_1061_; 
lean_dec(v___x_1053_);
v___x_1061_ = lean_box(0);
return v___x_1061_;
}
}
else
{
lean_object* v___x_1062_; 
lean_dec(v_a_1049_);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_b_1050_);
return v___x_1062_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___redArg___boxed(lean_object* v___x_1063_, lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v_a_1066_, lean_object* v_b_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___redArg(v___x_1063_, v___x_1064_, v___x_1065_, v_a_1066_, v_b_1067_);
lean_dec_ref(v___x_1065_);
lean_dec(v___x_1064_);
lean_dec(v___x_1063_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f(lean_object* v_s_1069_, lean_object* v_line_1070_){
_start:
{
lean_object* v_after_1071_; lean_object* v_indent_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1171_; 
v_after_1071_ = lean_ctor_get(v_line_1070_, 0);
v_indent_1072_ = lean_ctor_get(v_line_1070_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_line_1070_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1074_ = v_line_1070_;
v_isShared_1075_ = v_isSharedCheck_1171_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_indent_1072_);
lean_inc(v_after_1071_);
lean_dec(v_line_1070_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1171_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(3u);
v___x_1077_ = lean_nat_dec_le(v_indent_1072_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; 
lean_del_object(v___x_1074_);
lean_dec(v_indent_1072_);
lean_dec_ref(v_after_1071_);
v___x_1078_ = lean_box(0);
return v___x_1078_;
}
else
{
lean_object* v_pos_1079_; lean_object* v_stop_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_pos_1079_ = lean_ctor_get(v_after_1071_, 0);
lean_inc(v_pos_1079_);
v_stop_1080_ = lean_ctor_get(v_after_1071_, 1);
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_nat_add(v_pos_1079_, v___x_1081_);
v___x_1083_ = lean_nat_dec_le(v___x_1082_, v_stop_1080_);
lean_dec(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; 
lean_dec(v_pos_1079_);
lean_del_object(v___x_1074_);
lean_dec(v_indent_1072_);
lean_dec_ref(v_after_1071_);
v___x_1084_ = lean_box(0);
return v___x_1084_;
}
else
{
lean_object* v___x_1085_; 
v___x_1085_ = l_String_Slice_Pos_get_x3f(v_s_1069_, v_pos_1079_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1086_; 
lean_dec(v_pos_1079_);
lean_del_object(v___x_1074_);
lean_dec(v_indent_1072_);
lean_dec_ref(v_after_1071_);
v___x_1086_ = lean_box(0);
return v___x_1086_;
}
else
{
lean_object* v_val_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1170_; 
v_val_1087_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1170_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_val_1087_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1170_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint32_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_unbox_uint32(v_val_1087_);
lean_dec(v_val_1087_);
v___x_1092_ = l_Lean_Markdown_FenceChar_ofChar_x3f(v___x_1091_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1093_; 
lean_del_object(v___x_1089_);
lean_dec(v_pos_1079_);
lean_del_object(v___x_1074_);
lean_dec(v_indent_1072_);
lean_dec_ref(v_after_1071_);
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
else
{
lean_object* v_val_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1169_; 
v_val_1094_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1096_ = v___x_1092_;
v_isShared_1097_ = v_isSharedCheck_1169_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_val_1094_);
lean_dec(v___x_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1169_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_count_1098_; lean_object* v___x_1100_; 
v_count_1098_ = lean_unsigned_to_nat(0u);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v_count_1098_);
v___x_1100_ = v___x_1074_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_after_1071_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_count_1098_);
v___x_1100_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1167_; 
v___x_1101_ = lean_unbox(v_val_1094_);
v___x_1102_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___redArg(v_s_1069_, v___x_1101_, v___x_1100_);
v_fst_1103_ = lean_ctor_get(v___x_1102_, 0);
v_snd_1104_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1106_ = v___x_1102_;
v_isShared_1107_ = v_isSharedCheck_1167_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_inc(v_fst_1103_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1167_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_nat_dec_le(v___x_1076_, v_snd_1104_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
lean_del_object(v___x_1106_);
lean_dec(v_snd_1104_);
lean_dec(v_fst_1103_);
lean_del_object(v___x_1096_);
lean_dec(v_val_1094_);
lean_del_object(v___x_1089_);
lean_dec(v_pos_1079_);
lean_dec(v_indent_1072_);
v___x_1109_ = lean_box(0);
return v___x_1109_;
}
else
{
lean_object* v_pos_1110_; lean_object* v___x_1112_; 
v_pos_1110_ = lean_ctor_get(v_fst_1103_, 0);
lean_inc(v_pos_1110_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v_count_1098_);
v___x_1112_ = v___x_1106_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_fst_1103_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_count_1098_);
v___x_1112_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; lean_object* v_fst_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1164_; 
v___x_1113_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__1___redArg(v_s_1069_, v___x_1112_);
v_fst_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1164_ == 0)
{
lean_object* v_unused_1165_; 
v_unused_1165_ = lean_ctor_get(v___x_1113_, 1);
lean_dec(v_unused_1165_);
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1164_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_fst_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1164_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_pos_1118_; lean_object* v_stop_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1162_; 
v_pos_1118_ = lean_ctor_get(v_fst_1114_, 0);
v_stop_1119_ = lean_ctor_get(v_fst_1114_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_fst_1114_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_fst_1114_, 2);
lean_dec(v_unused_1163_);
v___x_1121_ = v_fst_1114_;
v_isShared_1122_ = v_isSharedCheck_1162_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_stop_1119_);
lean_inc(v_pos_1118_);
lean_dec(v_fst_1114_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1162_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___y_1125_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1150_; uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1123_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1079_, v_pos_1110_);
v___x_1136_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1118_, v_stop_1119_);
v___x_1137_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(v_s_1069_, v___x_1136_);
v___x_1150_ = 0;
v___x_1151_ = lean_unbox(v_val_1094_);
v___x_1152_ = l_Lean_Markdown_instBEqFenceChar_beq(v___x_1151_, v___x_1150_);
if (v___x_1152_ == 0)
{
goto v___jp_1138_;
}
else
{
lean_object* v_startInclusive_1153_; lean_object* v_endExclusive_1154_; lean_object* v_str_1155_; lean_object* v_startInclusive_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_startInclusive_1153_ = lean_ctor_get(v___x_1137_, 0);
v_endExclusive_1154_ = lean_ctor_get(v___x_1137_, 1);
v_str_1155_ = lean_ctor_get(v_s_1069_, 0);
v_startInclusive_1156_ = lean_ctor_get(v_s_1069_, 1);
v___x_1157_ = lean_nat_add(v_startInclusive_1156_, v_startInclusive_1153_);
v___x_1158_ = lean_nat_add(v_startInclusive_1156_, v_endExclusive_1154_);
v___x_1159_ = lean_box(0);
v___x_1160_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___redArg(v___x_1158_, v___x_1157_, v_str_1155_, v_count_1098_, v___x_1159_);
lean_dec(v___x_1157_);
lean_dec(v___x_1158_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v___x_1161_; 
lean_dec_ref(v___x_1137_);
lean_dec_ref(v___x_1123_);
lean_del_object(v___x_1121_);
lean_del_object(v___x_1116_);
lean_dec(v_snd_1104_);
lean_del_object(v___x_1096_);
lean_dec(v_val_1094_);
lean_del_object(v___x_1089_);
lean_dec(v_indent_1072_);
v___x_1161_ = lean_box(0);
return v___x_1161_;
}
else
{
lean_dec_ref_known(v___x_1160_, 1);
goto v___jp_1138_;
}
}
v___jp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 2, v___y_1125_);
lean_ctor_set(v___x_1121_, 1, v_indent_1072_);
lean_ctor_set(v___x_1121_, 0, v_snd_1104_);
v___x_1127_ = v___x_1121_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_snd_1104_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_indent_1072_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v___y_1125_);
v___x_1127_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
uint8_t v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_unbox(v_val_1094_);
lean_dec(v_val_1094_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*3, v___x_1128_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 1, v___x_1123_);
lean_ctor_set(v___x_1116_, 0, v___x_1127_);
v___x_1130_ = v___x_1116_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___x_1123_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1130_);
v___x_1132_ = v___x_1096_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
v___jp_1138_:
{
lean_object* v_startInclusive_1139_; lean_object* v_endExclusive_1140_; lean_object* v_startInclusive_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_startInclusive_1139_ = lean_ctor_get(v___x_1137_, 0);
v_endExclusive_1140_ = lean_ctor_get(v___x_1137_, 1);
v_startInclusive_1141_ = lean_ctor_get(v_s_1069_, 1);
v___x_1142_ = lean_nat_add(v_startInclusive_1141_, v_startInclusive_1139_);
v___x_1143_ = lean_nat_add(v_startInclusive_1141_, v_endExclusive_1140_);
v___x_1144_ = lean_nat_sub(v___x_1143_, v___x_1142_);
lean_dec(v___x_1142_);
lean_dec(v___x_1143_);
v___x_1145_ = lean_nat_dec_eq(v___x_1144_, v_count_1098_);
lean_dec(v___x_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1147_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1137_);
v___x_1147_ = v___x_1089_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1137_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
v___y_1125_ = v___x_1147_;
goto v___jp_1124_;
}
}
else
{
lean_object* v___x_1149_; 
lean_dec_ref(v___x_1137_);
lean_del_object(v___x_1089_);
v___x_1149_ = lean_box(0);
v___y_1125_ = v___x_1149_;
goto v___jp_1124_;
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f___boxed(lean_object* v_s_1172_, lean_object* v_line_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f(v_s_1172_, v_line_1173_);
lean_dec_ref(v_s_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0(lean_object* v_s_1175_, uint8_t v_val_1176_, lean_object* v_inst_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___redArg(v_s_1175_, v_val_1176_, v_a_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0___boxed(lean_object* v_s_1180_, lean_object* v_val_1181_, lean_object* v_inst_1182_, lean_object* v_a_1183_){
_start:
{
uint8_t v_val_5301__boxed_1184_; lean_object* v_res_1185_; 
v_val_5301__boxed_1184_ = lean_unbox(v_val_1181_);
v_res_1185_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__0(v_s_1180_, v_val_5301__boxed_1184_, v_inst_1182_, v_a_1183_);
lean_dec_ref(v_s_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1(lean_object* v___x_1186_, lean_object* v___x_1187_, lean_object* v___x_1188_, lean_object* v___x_1189_, lean_object* v_inst_1190_, lean_object* v_R_1191_, lean_object* v_a_1192_, lean_object* v_b_1193_, lean_object* v_c_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___redArg(v___x_1186_, v___x_1187_, v___x_1189_, v_a_1192_, v_b_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1___boxed(lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v_inst_1200_, lean_object* v_R_1201_, lean_object* v_a_1202_, lean_object* v_b_1203_, lean_object* v_c_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f_spec__1(v___x_1196_, v___x_1197_, v___x_1198_, v___x_1199_, v_inst_1200_, v_R_1201_, v_a_1202_, v_b_1203_, v_c_1204_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1198_);
lean_dec(v___x_1197_);
lean_dec(v___x_1196_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceClose_x3f(lean_object* v_s_1206_, lean_object* v_line_1207_, lean_object* v_info_1208_){
_start:
{
lean_object* v_after_1209_; lean_object* v_indent_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1247_; 
v_after_1209_ = lean_ctor_get(v_line_1207_, 0);
v_indent_1210_ = lean_ctor_get(v_line_1207_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_line_1207_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1212_ = v_line_1207_;
v_isShared_1213_ = v_isSharedCheck_1247_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_indent_1210_);
lean_inc(v_after_1209_);
lean_dec(v_line_1207_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1247_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(3u);
v___x_1215_ = lean_nat_dec_le(v_indent_1210_, v___x_1214_);
lean_dec(v_indent_1210_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; 
lean_del_object(v___x_1212_);
lean_dec_ref(v_after_1209_);
v___x_1216_ = lean_box(0);
return v___x_1216_;
}
else
{
lean_object* v_pos_1217_; lean_object* v_stop_1218_; lean_object* v___y_1220_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_pos_1217_ = lean_ctor_get(v_after_1209_, 0);
lean_inc(v_pos_1217_);
v_stop_1218_ = lean_ctor_get(v_after_1209_, 1);
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_add(v_pos_1217_, v___x_1242_);
v___x_1244_ = lean_nat_dec_le(v___x_1243_, v_stop_1218_);
lean_dec(v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_box(0);
v___y_1220_ = v___x_1245_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1246_; 
v___x_1246_ = l_String_Slice_Pos_get_x3f(v_s_1206_, v_pos_1217_);
v___y_1220_ = v___x_1246_;
goto v___jp_1219_;
}
v___jp_1219_:
{
uint8_t v_fenceChar_1221_; lean_object* v_fenceLen_1222_; uint32_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_fenceChar_1221_ = lean_ctor_get_uint8(v_info_1208_, sizeof(void*)*3);
v_fenceLen_1222_ = lean_ctor_get(v_info_1208_, 0);
v___x_1223_ = l_Lean_Markdown_FenceChar_toChar(v_fenceChar_1221_);
v___x_1224_ = lean_box_uint32(v___x_1223_);
v___x_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
v___x_1226_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___y_1220_, v___x_1225_);
lean_dec_ref_known(v___x_1225_, 1);
lean_dec(v___y_1220_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; 
lean_dec(v_pos_1217_);
lean_del_object(v___x_1212_);
lean_dec_ref(v_after_1209_);
v___x_1227_ = lean_box(0);
return v___x_1227_;
}
else
{
lean_object* v_count_1228_; lean_object* v___x_1230_; 
v_count_1228_ = lean_unsigned_to_nat(0u);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v_count_1228_);
v___x_1230_ = v___x_1212_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_after_1209_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_count_1228_);
v___x_1230_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v_fst_1232_; lean_object* v_snd_1233_; uint8_t v___x_1234_; 
v___x_1231_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f_spec__0___redArg(v_s_1206_, v___x_1223_, v___x_1230_);
v_fst_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_fst_1232_);
v_snd_1233_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_snd_1233_);
lean_dec_ref(v___x_1231_);
v___x_1234_ = lean_nat_dec_le(v_fenceLen_1222_, v_snd_1233_);
lean_dec(v_snd_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_fst_1232_);
lean_dec(v_pos_1217_);
v___x_1235_ = lean_box(0);
return v___x_1235_;
}
else
{
uint8_t v___x_1236_; 
lean_inc(v_fst_1232_);
v___x_1236_ = l_Lean_Markdown_Cursor_isBlank(v_s_1206_, v_fst_1232_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_dec(v_fst_1232_);
lean_dec(v_pos_1217_);
v___x_1237_ = lean_box(0);
return v___x_1237_;
}
else
{
lean_object* v_pos_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_pos_1238_ = lean_ctor_get(v_fst_1232_, 0);
lean_inc(v_pos_1238_);
lean_dec(v_fst_1232_);
v___x_1239_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1217_, v_pos_1238_);
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceClose_x3f___boxed(lean_object* v_s_1248_, lean_object* v_line_1249_, lean_object* v_info_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceClose_x3f(v_s_1248_, v_line_1249_, v_info_1250_);
lean_dec_ref(v_info_1250_);
lean_dec_ref(v_s_1248_);
return v_res_1251_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = 62;
v___x_1253_ = lean_box_uint32(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0___boxed__const__1;
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f(lean_object* v_s_1256_, lean_object* v_line_1257_){
_start:
{
lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v_after_1263_; lean_object* v_indent_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1364_; 
v_after_1263_ = lean_ctor_get(v_line_1257_, 0);
v_indent_1264_ = lean_ctor_get(v_line_1257_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_line_1257_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1266_ = v_line_1257_;
v_isShared_1267_ = v_isSharedCheck_1364_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_indent_1264_);
lean_inc(v_after_1263_);
lean_dec(v_line_1257_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1364_;
goto v_resetjp_1265_;
}
v___jp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1260_);
lean_ctor_set(v___x_1261_, 1, v___y_1259_);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = lean_unsigned_to_nat(3u);
v___x_1269_ = lean_nat_dec_le(v_indent_1264_, v___x_1268_);
lean_dec(v_indent_1264_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_del_object(v___x_1266_);
lean_dec_ref(v_after_1263_);
v___x_1270_ = lean_box(0);
return v___x_1270_;
}
else
{
lean_object* v_pos_1271_; lean_object* v_stop_1272_; lean_object* v_col_1273_; lean_object* v___y_1275_; lean_object* v_pos_1276_; lean_object* v_stop_1277_; lean_object* v_col_1278_; lean_object* v___y_1335_; lean_object* v___x_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_pos_1271_ = lean_ctor_get(v_after_1263_, 0);
lean_inc(v_pos_1271_);
v_stop_1272_ = lean_ctor_get(v_after_1263_, 1);
lean_inc(v_stop_1272_);
v_col_1273_ = lean_ctor_get(v_after_1263_, 2);
lean_inc(v_col_1273_);
v___x_1359_ = lean_unsigned_to_nat(1u);
v___x_1360_ = lean_nat_add(v_pos_1271_, v___x_1359_);
v___x_1361_ = lean_nat_dec_le(v___x_1360_, v_stop_1272_);
lean_dec(v___x_1360_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_box(0);
v___y_1335_ = v___x_1362_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1363_; 
v___x_1363_ = l_String_Slice_Pos_get_x3f(v_s_1256_, v_pos_1271_);
v___y_1335_ = v___x_1363_;
goto v___jp_1334_;
}
v___jp_1274_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
lean_inc(v_pos_1276_);
v___x_1279_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1271_, v_pos_1276_);
v___x_1280_ = lean_unsigned_to_nat(1u);
v___x_1281_ = lean_nat_add(v_pos_1276_, v___x_1280_);
v___x_1282_ = lean_nat_dec_le(v___x_1281_, v_stop_1277_);
lean_dec(v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec(v_col_1278_);
lean_dec(v_stop_1277_);
lean_dec(v_pos_1276_);
lean_del_object(v___x_1266_);
v___y_1259_ = v___y_1275_;
v___y_1260_ = v___x_1279_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1283_; 
v___x_1283_ = l_String_Slice_Pos_get_x3f(v_s_1256_, v_pos_1276_);
if (lean_obj_tag(v___x_1283_) == 1)
{
lean_object* v_val_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1333_; 
v_val_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1333_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_val_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1333_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint32_t v___x_1288_; uint32_t v___x_1289_; uint8_t v___x_1290_; 
v___x_1288_ = 32;
v___x_1289_ = lean_unbox_uint32(v_val_1284_);
v___x_1290_ = lean_uint32_dec_eq(v___x_1289_, v___x_1288_);
if (v___x_1290_ == 0)
{
uint32_t v___x_1291_; uint32_t v___x_1292_; uint8_t v___x_1293_; 
v___x_1291_ = 9;
v___x_1292_ = lean_unbox_uint32(v_val_1284_);
lean_dec(v_val_1284_);
v___x_1293_ = lean_uint32_dec_eq(v___x_1292_, v___x_1291_);
if (v___x_1293_ == 0)
{
lean_del_object(v___x_1286_);
lean_dec(v_col_1278_);
lean_dec(v_stop_1277_);
lean_dec(v_pos_1276_);
lean_del_object(v___x_1266_);
v___y_1259_ = v___y_1275_;
v___y_1260_ = v___x_1279_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
lean_dec_ref(v___y_1275_);
v___x_1294_ = lean_unsigned_to_nat(4u);
v___x_1295_ = lean_nat_mod(v_col_1278_, v___x_1294_);
v___x_1296_ = lean_nat_sub(v___x_1294_, v___x_1295_);
lean_dec(v___x_1295_);
v___x_1297_ = lean_nat_dec_eq(v___x_1296_, v___x_1280_);
lean_dec(v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1298_ = lean_nat_add(v_col_1278_, v___x_1280_);
lean_dec(v_col_1278_);
v___x_1299_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1299_, 0, v_pos_1276_);
lean_ctor_set(v___x_1299_, 1, v_stop_1277_);
lean_ctor_set(v___x_1299_, 2, v___x_1298_);
lean_ctor_set_uint8(v___x_1299_, sizeof(void*)*3, v___x_1293_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1299_);
lean_ctor_set(v___x_1266_, 0, v___x_1279_);
v___x_1301_ = v___x_1266_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1301_);
v___x_1303_ = v___x_1286_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_str_1306_; lean_object* v_startInclusive_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v_str_1306_ = lean_ctor_get(v_s_1256_, 0);
v_startInclusive_1307_ = lean_ctor_get(v_s_1256_, 1);
v___x_1308_ = lean_nat_add(v_startInclusive_1307_, v_pos_1276_);
lean_dec(v_pos_1276_);
v___x_1309_ = lean_string_utf8_next_fast(v_str_1306_, v___x_1308_);
lean_dec(v___x_1308_);
v___x_1310_ = lean_nat_sub(v___x_1309_, v_startInclusive_1307_);
v___x_1311_ = lean_nat_add(v_col_1278_, v___x_1280_);
lean_dec(v_col_1278_);
v___x_1312_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v_stop_1277_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*3, v___x_1290_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1312_);
lean_ctor_set(v___x_1266_, 0, v___x_1279_);
v___x_1314_ = v___x_1266_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1314_);
v___x_1316_ = v___x_1286_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
else
{
lean_object* v_str_1319_; lean_object* v_startInclusive_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_dec(v_val_1284_);
lean_dec_ref(v___y_1275_);
v_str_1319_ = lean_ctor_get(v_s_1256_, 0);
v_startInclusive_1320_ = lean_ctor_get(v_s_1256_, 1);
v___x_1321_ = lean_nat_add(v_startInclusive_1320_, v_pos_1276_);
lean_dec(v_pos_1276_);
v___x_1322_ = lean_string_utf8_next_fast(v_str_1319_, v___x_1321_);
lean_dec(v___x_1321_);
v___x_1323_ = lean_nat_sub(v___x_1322_, v_startInclusive_1320_);
v___x_1324_ = lean_nat_add(v_col_1278_, v___x_1280_);
lean_dec(v_col_1278_);
v___x_1325_ = 0;
v___x_1326_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1326_, 0, v___x_1323_);
lean_ctor_set(v___x_1326_, 1, v_stop_1277_);
lean_ctor_set(v___x_1326_, 2, v___x_1324_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*3, v___x_1325_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1326_);
lean_ctor_set(v___x_1266_, 0, v___x_1279_);
v___x_1328_ = v___x_1266_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1328_);
v___x_1330_ = v___x_1286_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
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
else
{
lean_dec(v___x_1283_);
lean_dec(v_col_1278_);
lean_dec(v_stop_1277_);
lean_dec(v_pos_1276_);
lean_del_object(v___x_1266_);
v___y_1259_ = v___y_1275_;
v___y_1260_ = v___x_1279_;
goto v___jp_1258_;
}
}
}
v___jp_1334_:
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0);
v___x_1337_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___y_1335_, v___x_1336_);
lean_dec(v___y_1335_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_dec(v_col_1273_);
lean_dec(v_stop_1272_);
lean_dec(v_pos_1271_);
lean_del_object(v___x_1266_);
lean_dec_ref(v_after_1263_);
v___x_1338_ = lean_box(0);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = lean_unsigned_to_nat(1u);
v___x_1340_ = lean_nat_add(v_pos_1271_, v___x_1339_);
v___x_1341_ = lean_nat_dec_le(v___x_1340_, v_stop_1272_);
lean_dec(v___x_1340_);
if (v___x_1341_ == 0)
{
lean_inc(v_pos_1271_);
v___y_1275_ = v_after_1263_;
v_pos_1276_ = v_pos_1271_;
v_stop_1277_ = v_stop_1272_;
v_col_1278_ = v_col_1273_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1355_; 
v_isSharedCheck_1355_ = !lean_is_exclusive(v_after_1263_);
if (v_isSharedCheck_1355_ == 0)
{
lean_object* v_unused_1356_; lean_object* v_unused_1357_; lean_object* v_unused_1358_; 
v_unused_1356_ = lean_ctor_get(v_after_1263_, 2);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_after_1263_, 1);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_after_1263_, 0);
lean_dec(v_unused_1358_);
v___x_1343_ = v_after_1263_;
v_isShared_1344_ = v_isSharedCheck_1355_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v_after_1263_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1355_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_str_1345_; lean_object* v_startInclusive_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1353_; 
v_str_1345_ = lean_ctor_get(v_s_1256_, 0);
v_startInclusive_1346_ = lean_ctor_get(v_s_1256_, 1);
v___x_1347_ = lean_nat_add(v_startInclusive_1346_, v_pos_1271_);
v___x_1348_ = lean_string_utf8_next_fast(v_str_1345_, v___x_1347_);
lean_dec(v___x_1347_);
v___x_1349_ = lean_nat_sub(v___x_1348_, v_startInclusive_1346_);
v___x_1350_ = lean_nat_add(v_col_1273_, v___x_1339_);
lean_dec(v_col_1273_);
v___x_1351_ = 0;
lean_inc(v___x_1350_);
lean_inc(v_stop_1272_);
lean_inc(v___x_1349_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 2, v___x_1350_);
lean_ctor_set(v___x_1343_, 0, v___x_1349_);
v___x_1353_ = v___x_1343_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v_stop_1272_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v___x_1350_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3, v___x_1351_);
v___y_1275_ = v___x_1353_;
v_pos_1276_ = v___x_1349_;
v_stop_1277_ = v_stop_1272_;
v_col_1278_ = v___x_1350_;
goto v___jp_1274_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___boxed(lean_object* v_s_1365_, lean_object* v_line_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f(v_s_1365_, v_line_1366_);
lean_dec_ref(v_s_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___lam__0(lean_object* v_s_1368_, lean_object* v_afterMarker_1369_){
_start:
{
lean_object* v___y_1371_; lean_object* v_pos_1386_; lean_object* v_stop_1387_; lean_object* v_col_1388_; uint8_t v_partialTab_1389_; uint8_t v___x_1390_; 
v_pos_1386_ = lean_ctor_get(v_afterMarker_1369_, 0);
v_stop_1387_ = lean_ctor_get(v_afterMarker_1369_, 1);
v_col_1388_ = lean_ctor_get(v_afterMarker_1369_, 2);
v_partialTab_1389_ = lean_ctor_get_uint8(v_afterMarker_1369_, sizeof(void*)*3);
v___x_1390_ = lean_nat_dec_le(v_stop_1387_, v_pos_1386_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_nat_add(v_pos_1386_, v___x_1391_);
v___x_1393_ = lean_nat_dec_le(v___x_1392_, v_stop_1387_);
lean_dec(v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; 
lean_dec_ref(v_afterMarker_1369_);
v___x_1394_ = lean_box(0);
return v___x_1394_;
}
else
{
lean_object* v___x_1395_; 
v___x_1395_ = l_String_Slice_Pos_get_x3f(v_s_1368_, v_pos_1386_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v_afterMarker_1369_);
v___x_1396_ = lean_box(0);
return v___x_1396_;
}
else
{
lean_object* v_val_1397_; uint32_t v___x_1398_; uint32_t v___x_1399_; uint8_t v___x_1400_; 
v_val_1397_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_val_1397_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1398_ = 32;
v___x_1399_ = lean_unbox_uint32(v_val_1397_);
v___x_1400_ = lean_uint32_dec_eq(v___x_1399_, v___x_1398_);
if (v___x_1400_ == 0)
{
uint32_t v___x_1401_; uint32_t v___x_1402_; uint8_t v___x_1403_; 
v___x_1401_ = 9;
v___x_1402_ = lean_unbox_uint32(v_val_1397_);
lean_dec(v_val_1397_);
v___x_1403_ = lean_uint32_dec_eq(v___x_1402_, v___x_1401_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_dec_ref(v_afterMarker_1369_);
v___x_1404_ = lean_box(0);
return v___x_1404_;
}
else
{
goto v___jp_1377_;
}
}
else
{
lean_dec(v_val_1397_);
goto v___jp_1377_;
}
}
}
}
else
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1414_; 
lean_inc(v_col_1388_);
lean_inc(v_stop_1387_);
lean_inc(v_pos_1386_);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_afterMarker_1369_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; lean_object* v_unused_1416_; lean_object* v_unused_1417_; 
v_unused_1415_ = lean_ctor_get(v_afterMarker_1369_, 2);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_afterMarker_1369_, 1);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_afterMarker_1369_, 0);
lean_dec(v_unused_1417_);
v___x_1406_ = v_afterMarker_1369_;
v_isShared_1407_ = v_isSharedCheck_1414_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_afterMarker_1369_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1414_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_add(v_col_1388_, v___x_1408_);
lean_dec(v_col_1388_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 2, v___x_1409_);
v___x_1411_ = v___x_1406_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_pos_1386_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_stop_1387_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v___x_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1413_, sizeof(void*)*3, v_partialTab_1389_);
v___x_1411_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
}
}
}
v___jp_1370_:
{
lean_object* v___x_1372_; lean_object* v_fst_1373_; lean_object* v___x_1374_; 
v___x_1372_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(v_s_1368_, v_afterMarker_1369_, v___y_1371_);
v_fst_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_fst_1373_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_fst_1373_);
return v___x_1374_;
}
v___jp_1375_:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_unsigned_to_nat(1u);
v___y_1371_ = v___x_1376_;
goto v___jp_1370_;
}
v___jp_1377_:
{
lean_object* v___x_1378_; lean_object* v_fst_1379_; lean_object* v_snd_1380_; lean_object* v_pos_1381_; lean_object* v_stop_1382_; uint8_t v___x_1383_; 
lean_inc_ref(v_afterMarker_1369_);
v___x_1378_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols(v_s_1368_, v_afterMarker_1369_);
v_fst_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_fst_1379_);
v_snd_1380_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_snd_1380_);
lean_dec_ref(v___x_1378_);
v_pos_1381_ = lean_ctor_get(v_fst_1379_, 0);
lean_inc(v_pos_1381_);
v_stop_1382_ = lean_ctor_get(v_fst_1379_, 1);
lean_inc(v_stop_1382_);
lean_dec(v_fst_1379_);
v___x_1383_ = lean_nat_dec_le(v_stop_1382_, v_pos_1381_);
lean_dec(v_pos_1381_);
lean_dec(v_stop_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_unsigned_to_nat(5u);
v___x_1385_ = lean_nat_dec_le(v___x_1384_, v_snd_1380_);
if (v___x_1385_ == 0)
{
v___y_1371_ = v_snd_1380_;
goto v___jp_1370_;
}
else
{
lean_dec(v_snd_1380_);
goto v___jp_1375_;
}
}
else
{
lean_dec(v_snd_1380_);
goto v___jp_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___lam__0___boxed(lean_object* v_s_1418_, lean_object* v_afterMarker_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___lam__0(v_s_1418_, v_afterMarker_1419_);
lean_dec_ref(v_s_1418_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___redArg(lean_object* v_s_1421_, uint32_t v___x_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_snd_1424_; lean_object* v_fst_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1494_; 
v_snd_1424_ = lean_ctor_get(v_a_1423_, 1);
v_fst_1425_ = lean_ctor_get(v_a_1423_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v_a_1423_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1427_ = v_a_1423_;
v_isShared_1428_ = v_isSharedCheck_1494_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snd_1424_);
lean_inc(v_fst_1425_);
lean_dec(v_a_1423_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1494_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1493_; 
v_fst_1429_ = lean_ctor_get(v_snd_1424_, 0);
v_snd_1430_ = lean_ctor_get(v_snd_1424_, 1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_snd_1424_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1432_ = v_snd_1424_;
v_isShared_1433_ = v_isSharedCheck_1493_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_inc(v_fst_1429_);
lean_dec(v_snd_1424_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1493_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_unsigned_to_nat(10u);
v___x_1447_ = lean_nat_dec_lt(v_fst_1429_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_del_object(v___x_1432_);
lean_del_object(v___x_1427_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_fst_1429_);
lean_ctor_set(v___x_1448_, 1, v_snd_1430_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_fst_1425_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
else
{
lean_object* v_pos_1451_; lean_object* v_stop_1452_; lean_object* v_col_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_pos_1451_ = lean_ctor_get(v_fst_1425_, 0);
v_stop_1452_ = lean_ctor_get(v_fst_1425_, 1);
v_col_1453_ = lean_ctor_get(v_fst_1425_, 2);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_pos_1451_, v___x_1454_);
v___x_1456_ = lean_nat_dec_le(v___x_1455_, v_stop_1452_);
lean_dec(v___x_1455_);
if (v___x_1456_ == 0)
{
lean_del_object(v___x_1432_);
lean_del_object(v___x_1427_);
goto v___jp_1442_;
}
else
{
lean_object* v___x_1457_; 
v___x_1457_ = l_String_Slice_Pos_get_x3f(v_s_1421_, v_pos_1451_);
if (lean_obj_tag(v___x_1457_) == 1)
{
lean_object* v_val_1458_; uint32_t v___x_1459_; uint32_t v___x_1460_; uint8_t v___x_1461_; 
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = 48;
v___x_1460_ = lean_unbox_uint32(v_val_1458_);
v___x_1461_ = lean_uint32_dec_le(v___x_1459_, v___x_1460_);
if (v___x_1461_ == 0)
{
lean_dec(v_val_1458_);
goto v___jp_1434_;
}
else
{
uint32_t v___x_1462_; uint32_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = 57;
v___x_1463_ = lean_unbox_uint32(v_val_1458_);
v___x_1464_ = lean_uint32_dec_le(v___x_1463_, v___x_1462_);
if (v___x_1464_ == 0)
{
lean_dec(v_val_1458_);
goto v___jp_1434_;
}
else
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1489_; 
lean_inc(v_col_1453_);
lean_inc(v_stop_1452_);
lean_inc(v_pos_1451_);
lean_del_object(v___x_1432_);
lean_del_object(v___x_1427_);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_fst_1425_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; lean_object* v_unused_1491_; lean_object* v_unused_1492_; 
v_unused_1490_ = lean_ctor_get(v_fst_1425_, 2);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v_fst_1425_, 1);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_fst_1425_, 0);
lean_dec(v_unused_1492_);
v___x_1466_ = v_fst_1425_;
v_isShared_1467_ = v_isSharedCheck_1489_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_fst_1425_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1489_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_str_1468_; lean_object* v_startInclusive_1469_; uint32_t v___x_1470_; uint8_t v___x_1471_; lean_object* v___x_1472_; uint32_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v_str_1468_ = lean_ctor_get(v_s_1421_, 0);
v_startInclusive_1469_ = lean_ctor_get(v_s_1421_, 1);
v___x_1470_ = 43;
v___x_1471_ = lean_uint32_dec_eq(v___x_1422_, v___x_1470_);
v___x_1472_ = lean_nat_mul(v_snd_1430_, v___x_1446_);
lean_dec(v_snd_1430_);
v___x_1473_ = lean_unbox_uint32(v_val_1458_);
lean_dec(v_val_1458_);
v___x_1474_ = lean_uint32_to_nat(v___x_1473_);
v___x_1475_ = lean_unsigned_to_nat(48u);
v___x_1476_ = lean_nat_sub(v___x_1474_, v___x_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_nat_add(v___x_1472_, v___x_1476_);
lean_dec(v___x_1476_);
lean_dec(v___x_1472_);
v___x_1478_ = lean_nat_add(v_fst_1429_, v___x_1454_);
lean_dec(v_fst_1429_);
v___x_1479_ = lean_nat_add(v_startInclusive_1469_, v_pos_1451_);
lean_dec(v_pos_1451_);
v___x_1480_ = lean_string_utf8_next_fast(v_str_1468_, v___x_1479_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_nat_sub(v___x_1480_, v_startInclusive_1469_);
v___x_1482_ = lean_nat_add(v_col_1453_, v___x_1454_);
lean_dec(v_col_1453_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 2, v___x_1482_);
lean_ctor_set(v___x_1466_, 0, v___x_1481_);
v___x_1484_ = v___x_1466_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_stop_1452_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3, v___x_1471_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1478_);
lean_ctor_set(v___x_1485_, 1, v___x_1477_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v_a_1423_ = v___x_1486_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v___x_1457_);
lean_del_object(v___x_1432_);
lean_del_object(v___x_1427_);
goto v___jp_1442_;
}
}
}
v___jp_1434_:
{
lean_object* v___x_1436_; 
if (v_isShared_1433_ == 0)
{
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_fst_1429_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_snd_1430_);
v___x_1436_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1438_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1436_);
v___x_1438_ = v___x_1427_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_fst_1425_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
}
v___jp_1442_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_fst_1429_);
lean_ctor_set(v___x_1443_, 1, v_snd_1430_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_fst_1425_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___redArg___boxed(lean_object* v_s_1495_, lean_object* v___x_1496_, lean_object* v_a_1497_){
_start:
{
uint32_t v___x_7473__boxed_1498_; lean_object* v_res_1499_; 
v___x_7473__boxed_1498_ = lean_unbox_uint32(v___x_1496_);
lean_dec(v___x_1496_);
v_res_1499_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___redArg(v_s_1495_, v___x_7473__boxed_1498_, v_a_1497_);
lean_dec_ref(v_s_1495_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f(lean_object* v_s_1502_, lean_object* v_line_1503_){
_start:
{
lean_object* v_after_1504_; lean_object* v_indent_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1643_; 
v_after_1504_ = lean_ctor_get(v_line_1503_, 0);
v_indent_1505_ = lean_ctor_get(v_line_1503_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_line_1503_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1507_ = v_line_1503_;
v_isShared_1508_ = v_isSharedCheck_1643_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_indent_1505_);
lean_inc(v_after_1504_);
lean_dec(v_line_1503_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1643_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; uint8_t v___x_1510_; 
v___x_1509_ = lean_unsigned_to_nat(3u);
v___x_1510_ = lean_nat_dec_le(v_indent_1505_, v___x_1509_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
lean_del_object(v___x_1507_);
lean_dec(v_indent_1505_);
lean_dec_ref(v_after_1504_);
v___x_1511_ = lean_box(0);
return v___x_1511_;
}
else
{
lean_object* v_pos_1512_; lean_object* v_stop_1513_; lean_object* v_col_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v_pos_1512_ = lean_ctor_get(v_after_1504_, 0);
lean_inc(v_pos_1512_);
v_stop_1513_ = lean_ctor_get(v_after_1504_, 1);
v_col_1514_ = lean_ctor_get(v_after_1504_, 2);
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = lean_nat_add(v_pos_1512_, v___x_1515_);
v___x_1517_ = lean_nat_dec_le(v___x_1516_, v_stop_1513_);
lean_dec(v___x_1516_);
if (v___x_1517_ == 0)
{
lean_object* v___x_1518_; 
lean_dec(v_pos_1512_);
lean_del_object(v___x_1507_);
lean_dec(v_indent_1505_);
lean_dec_ref(v_after_1504_);
v___x_1518_ = lean_box(0);
return v___x_1518_;
}
else
{
lean_object* v___x_1519_; 
v___x_1519_ = l_String_Slice_Pos_get_x3f(v_s_1502_, v_pos_1512_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1520_; 
lean_dec(v_pos_1512_);
lean_del_object(v___x_1507_);
lean_dec(v_indent_1505_);
lean_dec_ref(v_after_1504_);
v___x_1520_ = lean_box(0);
return v___x_1520_;
}
else
{
lean_object* v_val_1521_; lean_object* v___x_1522_; lean_object* v___y_1524_; lean_object* v___y_1525_; uint8_t v___y_1526_; uint32_t v___x_1542_; uint32_t v___x_1543_; uint8_t v___x_1544_; 
v_val_1521_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_val_1521_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1522_ = lean_nat_sub(v_col_1514_, v_indent_1505_);
lean_dec(v_indent_1505_);
v___x_1542_ = 42;
v___x_1543_ = lean_unbox_uint32(v_val_1521_);
v___x_1544_ = lean_uint32_dec_eq(v___x_1543_, v___x_1542_);
if (v___x_1544_ == 0)
{
uint32_t v___x_1560_; uint32_t v___x_1561_; uint8_t v___x_1562_; 
v___x_1560_ = 45;
v___x_1561_ = lean_unbox_uint32(v_val_1521_);
v___x_1562_ = lean_uint32_dec_eq(v___x_1561_, v___x_1560_);
if (v___x_1562_ == 0)
{
uint32_t v___x_1563_; uint32_t v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = 43;
v___x_1564_ = lean_unbox_uint32(v_val_1521_);
v___x_1565_ = lean_uint32_dec_eq(v___x_1564_, v___x_1563_);
if (v___x_1565_ == 0)
{
uint32_t v___x_1566_; uint32_t v___x_1567_; uint8_t v___x_1568_; 
v___x_1566_ = 48;
v___x_1567_ = lean_unbox_uint32(v_val_1521_);
v___x_1568_ = lean_uint32_dec_le(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec(v___x_1522_);
lean_dec(v_val_1521_);
lean_dec(v_pos_1512_);
lean_del_object(v___x_1507_);
lean_dec_ref(v_after_1504_);
v___x_1569_ = lean_box(0);
return v___x_1569_;
}
else
{
uint32_t v___x_1570_; uint32_t v___x_1571_; uint8_t v___x_1572_; 
v___x_1570_ = 57;
v___x_1571_ = lean_unbox_uint32(v_val_1521_);
v___x_1572_ = lean_uint32_dec_le(v___x_1571_, v___x_1570_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; 
lean_dec(v___x_1522_);
lean_dec(v_val_1521_);
lean_dec(v_pos_1512_);
lean_del_object(v___x_1507_);
lean_dec_ref(v_after_1504_);
v___x_1573_ = lean_box(0);
return v___x_1573_;
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___closed__0));
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1575_);
v___x_1577_ = v___x_1507_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_after_1504_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
uint32_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_unbox_uint32(v_val_1521_);
lean_dec(v_val_1521_);
v___x_1579_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___redArg(v_s_1502_, v___x_1578_, v___x_1577_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1580_; 
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
else
{
lean_object* v_val_1581_; lean_object* v_snd_1582_; lean_object* v_fst_1583_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___y_1587_; lean_object* v___y_1588_; uint8_t v___y_1589_; uint8_t v___x_1605_; 
v_val_1581_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v___x_1579_, 1);
v_snd_1582_ = lean_ctor_get(v_val_1581_, 1);
lean_inc(v_snd_1582_);
v_fst_1583_ = lean_ctor_get(v_val_1581_, 0);
lean_inc(v_fst_1583_);
lean_dec(v_val_1581_);
v_fst_1584_ = lean_ctor_get(v_snd_1582_, 0);
lean_inc(v_fst_1584_);
v_snd_1585_ = lean_ctor_get(v_snd_1582_, 1);
lean_inc(v_snd_1585_);
lean_dec(v_snd_1582_);
v___x_1605_ = lean_nat_dec_eq(v_fst_1584_, v___x_1574_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(9u);
v___x_1607_ = lean_nat_dec_le(v_fst_1584_, v___x_1606_);
lean_dec(v_fst_1584_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec(v_snd_1585_);
lean_dec(v_fst_1583_);
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1608_ = lean_box(0);
return v___x_1608_;
}
else
{
lean_object* v_pos_1609_; lean_object* v_stop_1610_; lean_object* v_col_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1640_; 
v_pos_1609_ = lean_ctor_get(v_fst_1583_, 0);
v_stop_1610_ = lean_ctor_get(v_fst_1583_, 1);
v_col_1611_ = lean_ctor_get(v_fst_1583_, 2);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_fst_1583_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1613_ = v_fst_1583_;
v_isShared_1614_ = v_isSharedCheck_1640_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_col_1611_);
lean_inc(v_stop_1610_);
lean_inc(v_pos_1609_);
lean_dec(v_fst_1583_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1640_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = lean_nat_add(v_pos_1609_, v___x_1515_);
v___x_1616_ = lean_nat_dec_le(v___x_1615_, v_stop_1610_);
lean_dec(v___x_1615_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; 
lean_del_object(v___x_1613_);
lean_dec(v_col_1611_);
lean_dec(v_stop_1610_);
lean_dec(v_pos_1609_);
lean_dec(v_snd_1585_);
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1617_ = lean_box(0);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = l_String_Slice_Pos_get_x3f(v_s_1502_, v_pos_1609_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v___x_1619_; 
lean_del_object(v___x_1613_);
lean_dec(v_col_1611_);
lean_dec(v_stop_1610_);
lean_dec(v_pos_1609_);
lean_dec(v_snd_1585_);
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1619_ = lean_box(0);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; uint32_t v___x_1621_; uint32_t v___x_1622_; uint8_t v___x_1623_; 
v_val_1620_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1620_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1621_ = 46;
v___x_1622_ = lean_unbox_uint32(v_val_1620_);
v___x_1623_ = lean_uint32_dec_eq(v___x_1622_, v___x_1621_);
if (v___x_1623_ == 0)
{
uint32_t v___x_1636_; uint32_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = 41;
v___x_1637_ = lean_unbox_uint32(v_val_1620_);
lean_dec(v_val_1620_);
v___x_1638_ = lean_uint32_dec_eq(v___x_1637_, v___x_1636_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_del_object(v___x_1613_);
lean_dec(v_col_1611_);
lean_dec(v_stop_1610_);
lean_dec(v_pos_1609_);
lean_dec(v_snd_1585_);
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1639_ = lean_box(0);
return v___x_1639_;
}
else
{
goto v___jp_1624_;
}
}
else
{
lean_dec(v_val_1620_);
goto v___jp_1624_;
}
v___jp_1624_:
{
lean_object* v_str_1625_; lean_object* v_startInclusive_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
v_str_1625_ = lean_ctor_get(v_s_1502_, 0);
v_startInclusive_1626_ = lean_ctor_get(v_s_1502_, 1);
v___x_1627_ = lean_nat_add(v_startInclusive_1626_, v_pos_1609_);
lean_dec(v_pos_1609_);
v___x_1628_ = lean_string_utf8_next_fast(v_str_1625_, v___x_1627_);
lean_dec(v___x_1627_);
v___x_1629_ = lean_nat_sub(v___x_1628_, v_startInclusive_1626_);
v___x_1630_ = lean_nat_add(v_col_1611_, v___x_1515_);
lean_dec(v_col_1611_);
lean_inc(v___x_1629_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 2, v___x_1630_);
lean_ctor_set(v___x_1613_, 0, v___x_1629_);
v___x_1632_ = v___x_1613_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_stop_1610_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v___x_1630_);
v___x_1632_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_ctor_set_uint8(v___x_1632_, sizeof(void*)*3, v___x_1565_);
if (v___x_1623_ == 0)
{
uint8_t v___x_1633_; 
v___x_1633_ = 1;
v___y_1587_ = v___x_1629_;
v___y_1588_ = v___x_1632_;
v___y_1589_ = v___x_1633_;
goto v___jp_1586_;
}
else
{
uint8_t v___x_1634_; 
v___x_1634_ = 0;
v___y_1587_ = v___x_1629_;
v___y_1588_ = v___x_1632_;
v___y_1589_ = v___x_1634_;
goto v___jp_1586_;
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
lean_object* v___x_1641_; 
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_dec(v_fst_1583_);
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1641_ = lean_box(0);
return v___x_1641_;
}
v___jp_1586_:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___lam__0(v_s_1502_, v___y_1588_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v___x_1591_; 
lean_dec(v___y_1587_);
lean_dec(v_snd_1585_);
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1591_ = lean_box(0);
return v___x_1591_;
}
else
{
lean_object* v_val_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1604_; 
v_val_1592_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1594_ = v___x_1590_;
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_val_1592_);
lean_dec(v___x_1590_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_col_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v_col_1596_ = lean_ctor_get(v_val_1592_, 2);
v___x_1597_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1512_, v___y_1587_);
v___x_1598_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_1598_, 0, v_snd_1585_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*1, v___y_1589_);
v___x_1599_ = lean_nat_sub(v_col_1596_, v___x_1522_);
lean_dec(v___x_1522_);
v___x_1600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1597_);
lean_ctor_set(v___x_1600_, 1, v_val_1592_);
lean_ctor_set(v___x_1600_, 2, v___x_1598_);
lean_ctor_set(v___x_1600_, 3, v___x_1599_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1600_);
v___x_1602_ = v___x_1594_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
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
lean_inc(v_col_1514_);
lean_inc(v_stop_1513_);
lean_del_object(v___x_1507_);
lean_dec_ref(v_after_1504_);
goto v___jp_1545_;
}
}
else
{
lean_inc(v_col_1514_);
lean_inc(v_stop_1513_);
lean_del_object(v___x_1507_);
lean_dec_ref(v_after_1504_);
goto v___jp_1545_;
}
}
else
{
lean_inc(v_col_1514_);
lean_inc(v_stop_1513_);
lean_del_object(v___x_1507_);
lean_dec_ref(v_after_1504_);
goto v___jp_1545_;
}
v___jp_1523_:
{
lean_object* v___x_1527_; 
v___x_1527_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___lam__0(v_s_1502_, v___y_1525_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1528_; 
lean_dec(v___y_1524_);
lean_dec(v___x_1522_);
lean_dec(v_pos_1512_);
v___x_1528_ = lean_box(0);
return v___x_1528_;
}
else
{
lean_object* v_val_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1541_; 
v_val_1529_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1531_ = v___x_1527_;
v_isShared_1532_ = v_isSharedCheck_1541_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_val_1529_);
lean_dec(v___x_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1541_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_col_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v_col_1533_ = lean_ctor_get(v_val_1529_, 2);
v___x_1534_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1512_, v___y_1524_);
v___x_1535_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1535_, 0, v___y_1526_);
v___x_1536_ = lean_nat_sub(v_col_1533_, v___x_1522_);
lean_dec(v___x_1522_);
v___x_1537_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1534_);
lean_ctor_set(v___x_1537_, 1, v_val_1529_);
lean_ctor_set(v___x_1537_, 2, v___x_1535_);
lean_ctor_set(v___x_1537_, 3, v___x_1536_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1537_);
v___x_1539_ = v___x_1531_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
v___jp_1545_:
{
lean_object* v_str_1546_; lean_object* v_startInclusive_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; 
v_str_1546_ = lean_ctor_get(v_s_1502_, 0);
v_startInclusive_1547_ = lean_ctor_get(v_s_1502_, 1);
v___x_1548_ = lean_nat_add(v_startInclusive_1547_, v_pos_1512_);
v___x_1549_ = lean_string_utf8_next_fast(v_str_1546_, v___x_1548_);
lean_dec(v___x_1548_);
v___x_1550_ = lean_nat_sub(v___x_1549_, v_startInclusive_1547_);
v___x_1551_ = lean_nat_add(v_col_1514_, v___x_1515_);
lean_dec(v_col_1514_);
v___x_1552_ = 0;
lean_inc(v___x_1550_);
v___x_1553_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1553_, 0, v___x_1550_);
lean_ctor_set(v___x_1553_, 1, v_stop_1513_);
lean_ctor_set(v___x_1553_, 2, v___x_1551_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*3, v___x_1552_);
if (v___x_1544_ == 0)
{
uint32_t v___x_1554_; uint32_t v___x_1555_; uint8_t v___x_1556_; 
v___x_1554_ = 45;
v___x_1555_ = lean_unbox_uint32(v_val_1521_);
lean_dec(v_val_1521_);
v___x_1556_ = lean_uint32_dec_eq(v___x_1555_, v___x_1554_);
if (v___x_1556_ == 0)
{
uint8_t v___x_1557_; 
v___x_1557_ = 2;
v___y_1524_ = v___x_1550_;
v___y_1525_ = v___x_1553_;
v___y_1526_ = v___x_1557_;
goto v___jp_1523_;
}
else
{
uint8_t v___x_1558_; 
v___x_1558_ = 1;
v___y_1524_ = v___x_1550_;
v___y_1525_ = v___x_1553_;
v___y_1526_ = v___x_1558_;
goto v___jp_1523_;
}
}
else
{
uint8_t v___x_1559_; 
lean_dec(v_val_1521_);
v___x_1559_ = 0;
v___y_1524_ = v___x_1550_;
v___y_1525_ = v___x_1553_;
v___y_1526_ = v___x_1559_;
goto v___jp_1523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f___boxed(lean_object* v_s_1644_, lean_object* v_line_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f(v_s_1644_, v_line_1645_);
lean_dec_ref(v_s_1644_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0(lean_object* v_s_1647_, uint32_t v___x_1648_, lean_object* v_inst_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___redArg(v_s_1647_, v___x_1648_, v_a_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0___boxed(lean_object* v_s_1652_, lean_object* v___x_1653_, lean_object* v_inst_1654_, lean_object* v_a_1655_){
_start:
{
uint32_t v___x_7856__boxed_1656_; lean_object* v_res_1657_; 
v___x_7856__boxed_1656_ = lean_unbox_uint32(v___x_1653_);
lean_dec(v___x_1653_);
v_res_1657_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f_spec__0(v_s_1652_, v___x_7856__boxed_1656_, v_inst_1654_, v_a_1655_);
lean_dec_ref(v_s_1652_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___redArg(lean_object* v_s_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_fst_1660_; lean_object* v_snd_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1705_; 
v_fst_1660_ = lean_ctor_get(v_a_1659_, 0);
v_snd_1661_ = lean_ctor_get(v_a_1659_, 1);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_a_1659_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1663_ = v_a_1659_;
v_isShared_1664_ = v_isSharedCheck_1705_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snd_1661_);
lean_inc(v_fst_1660_);
lean_dec(v_a_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1705_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_pos_1665_; lean_object* v_stop_1666_; lean_object* v_col_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_pos_1665_ = lean_ctor_get(v_fst_1660_, 0);
v_stop_1666_ = lean_ctor_get(v_fst_1660_, 1);
v_col_1667_ = lean_ctor_get(v_fst_1660_, 2);
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_add(v_pos_1665_, v___x_1668_);
v___x_1670_ = lean_nat_dec_le(v___x_1669_, v_stop_1666_);
lean_dec(v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1672_; 
if (v_isShared_1664_ == 0)
{
v___x_1672_ = v___x_1663_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_fst_1660_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_snd_1661_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
else
{
lean_object* v_str_1674_; lean_object* v_startInclusive_1675_; lean_object* v___x_1676_; uint32_t v___x_1688_; uint32_t v___x_1701_; uint8_t v___x_1702_; 
v_str_1674_ = lean_ctor_get(v_s_1658_, 0);
v_startInclusive_1675_ = lean_ctor_get(v_s_1658_, 1);
v___x_1676_ = lean_nat_add(v_startInclusive_1675_, v_pos_1665_);
v___x_1688_ = lean_string_utf8_get_fast(v_str_1674_, v___x_1676_);
v___x_1701_ = 65;
v___x_1702_ = lean_uint32_dec_le(v___x_1701_, v___x_1688_);
if (v___x_1702_ == 0)
{
goto v___jp_1696_;
}
else
{
uint32_t v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = 90;
v___x_1704_ = lean_uint32_dec_le(v___x_1688_, v___x_1703_);
if (v___x_1704_ == 0)
{
goto v___jp_1696_;
}
else
{
lean_inc(v_col_1667_);
lean_inc(v_stop_1666_);
lean_dec(v_fst_1660_);
goto v___jp_1677_;
}
}
v___jp_1677_:
{
uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1678_ = 0;
v___x_1679_ = lean_nat_add(v_snd_1661_, v___x_1668_);
lean_dec(v_snd_1661_);
v___x_1680_ = lean_string_utf8_next_fast(v_str_1674_, v___x_1676_);
lean_dec(v___x_1676_);
v___x_1681_ = lean_nat_sub(v___x_1680_, v_startInclusive_1675_);
v___x_1682_ = lean_nat_add(v_col_1667_, v___x_1668_);
lean_dec(v_col_1667_);
v___x_1683_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v_stop_1666_);
lean_ctor_set(v___x_1683_, 2, v___x_1682_);
lean_ctor_set_uint8(v___x_1683_, sizeof(void*)*3, v___x_1678_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v___x_1679_);
lean_ctor_set(v___x_1663_, 0, v___x_1683_);
v___x_1685_ = v___x_1663_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1679_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v_a_1659_ = v___x_1685_;
goto _start;
}
}
v___jp_1689_:
{
uint32_t v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = 48;
v___x_1691_ = lean_uint32_dec_le(v___x_1690_, v___x_1688_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_dec(v___x_1676_);
lean_del_object(v___x_1663_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_fst_1660_);
lean_ctor_set(v___x_1692_, 1, v_snd_1661_);
return v___x_1692_;
}
else
{
uint32_t v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = 57;
v___x_1694_ = lean_uint32_dec_le(v___x_1688_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
lean_dec(v___x_1676_);
lean_del_object(v___x_1663_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_fst_1660_);
lean_ctor_set(v___x_1695_, 1, v_snd_1661_);
return v___x_1695_;
}
else
{
lean_inc(v_col_1667_);
lean_inc(v_stop_1666_);
lean_dec(v_fst_1660_);
goto v___jp_1677_;
}
}
}
v___jp_1696_:
{
uint32_t v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = 97;
v___x_1698_ = lean_uint32_dec_le(v___x_1697_, v___x_1688_);
if (v___x_1698_ == 0)
{
goto v___jp_1689_;
}
else
{
uint32_t v___x_1699_; uint8_t v___x_1700_; 
v___x_1699_ = 122;
v___x_1700_ = lean_uint32_dec_le(v___x_1688_, v___x_1699_);
if (v___x_1700_ == 0)
{
goto v___jp_1689_;
}
else
{
lean_inc(v_col_1667_);
lean_inc(v_stop_1666_);
lean_dec(v_fst_1660_);
goto v___jp_1677_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___redArg___boxed(lean_object* v_s_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___redArg(v_s_1706_, v_a_1707_);
lean_dec_ref(v_s_1706_);
return v_res_1708_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = 47;
v___x_1723_ = lean_box_uint32(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5___boxed__const__1;
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11___boxed__const__1(void){
_start:
{
uint32_t v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = 60;
v___x_1738_ = lean_box_uint32(v___x_1737_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11___boxed__const__1;
v___x_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f(lean_object* v_s_1741_, lean_object* v_line_1742_){
_start:
{
uint32_t v___y_1750_; lean_object* v_after_1757_; lean_object* v_indent_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1966_; 
v_after_1757_ = lean_ctor_get(v_line_1742_, 0);
v_indent_1758_ = lean_ctor_get(v_line_1742_, 1);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_line_1742_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1760_ = v_line_1742_;
v_isShared_1761_ = v_isSharedCheck_1966_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_indent_1758_);
lean_inc(v_after_1757_);
lean_dec(v_line_1742_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1966_;
goto v_resetjp_1759_;
}
v___jp_1743_:
{
lean_object* v___x_1744_; 
v___x_1744_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__0));
return v___x_1744_;
}
v___jp_1745_:
{
lean_object* v___x_1746_; 
v___x_1746_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__1));
return v___x_1746_;
}
v___jp_1747_:
{
lean_object* v___x_1748_; 
v___x_1748_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__2));
return v___x_1748_;
}
v___jp_1749_:
{
uint32_t v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = 97;
v___x_1752_ = lean_uint32_dec_le(v___x_1751_, v___y_1750_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_box(0);
return v___x_1753_;
}
else
{
uint32_t v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = 122;
v___x_1755_ = lean_uint32_dec_le(v___y_1750_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
else
{
goto v___jp_1747_;
}
}
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_unsigned_to_nat(3u);
v___x_1763_ = lean_nat_dec_le(v_indent_1758_, v___x_1762_);
lean_dec(v_indent_1758_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_del_object(v___x_1760_);
lean_dec_ref(v_after_1757_);
v___x_1764_ = lean_box(0);
return v___x_1764_;
}
else
{
lean_object* v_pos_1765_; lean_object* v_stop_1766_; lean_object* v_col_1767_; lean_object* v___y_1769_; uint8_t v___y_1770_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; uint8_t v___y_1784_; lean_object* v___y_1785_; uint8_t v___y_1786_; uint8_t v___y_1792_; lean_object* v___y_1793_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1803_; uint8_t v___y_1804_; lean_object* v___y_1805_; uint8_t v___y_1806_; uint32_t v___y_1832_; lean_object* v___y_1833_; uint8_t v___y_1834_; lean_object* v___y_1835_; uint8_t v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v_pos_1846_; lean_object* v_stop_1847_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1885_; lean_object* v_pos_1886_; lean_object* v_stop_1887_; lean_object* v___y_1894_; lean_object* v_pos_1895_; lean_object* v_stop_1896_; lean_object* v___y_1937_; lean_object* v___x_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_pos_1765_ = lean_ctor_get(v_after_1757_, 0);
lean_inc(v_pos_1765_);
v_stop_1766_ = lean_ctor_get(v_after_1757_, 1);
lean_inc(v_stop_1766_);
v_col_1767_ = lean_ctor_get(v_after_1757_, 2);
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_nat_add(v_pos_1765_, v___x_1961_);
v___x_1963_ = lean_nat_dec_le(v___x_1962_, v_stop_1766_);
lean_dec(v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_box(0);
v___y_1937_ = v___x_1964_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_1965_; 
v___x_1965_ = l_String_Slice_Pos_get_x3f(v_s_1741_, v_pos_1765_);
v___y_1937_ = v___x_1965_;
goto v___jp_1936_;
}
v___jp_1768_:
{
lean_object* v_pos_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_pos_1771_ = lean_ctor_get(v___y_1769_, 0);
lean_inc(v_pos_1771_);
lean_dec_ref(v___y_1769_);
v___x_1772_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1771_, v_stop_1766_);
v___x_1773_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_1772_);
v___x_1774_ = l_Lean_Markdown_InlineSource_ofLines(v_s_1741_, v___x_1773_);
v___x_1775_ = l_Lean_Markdown_InlineSource_startPos___redArg(v___x_1774_);
v___x_1776_ = l_Lean_Markdown_InlineSource_stopPos___redArg(v___x_1774_);
v___x_1777_ = l_Lean_Markdown_InlineSource_cursor___redArg(v___x_1774_, v___x_1775_, v___x_1776_);
v___x_1778_ = l_Lean_Markdown_parseCompleteTagLine_x3f(v_s_1741_, v___x_1777_);
if (lean_obj_tag(v___x_1778_) == 0)
{
if (v___y_1770_ == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_box(0);
return v___x_1779_;
}
else
{
goto v___jp_1743_;
}
}
else
{
lean_dec_ref_known(v___x_1778_, 1);
goto v___jp_1743_;
}
}
v___jp_1780_:
{
uint8_t v___x_1787_; 
v___x_1787_ = l_Lean_Markdown_isBlockTagName(v_s_1741_, v___y_1781_);
if (v___x_1787_ == 0)
{
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
v___y_1769_ = v___y_1785_;
v___y_1770_ = v___x_1787_;
goto v___jp_1768_;
}
else
{
if (v___y_1784_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1788_ = l_Lean_Markdown_subsliceClamped___redArg(v___y_1783_, v___y_1782_);
v___x_1789_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__3));
v___x_1790_ = l_Lean_Markdown_startsWithAscii(v_s_1741_, v___x_1788_, v___x_1789_, v___y_1786_);
if (v___x_1790_ == 0)
{
v___y_1769_ = v___y_1785_;
v___y_1770_ = v___x_1790_;
goto v___jp_1768_;
}
else
{
lean_dec_ref(v___y_1785_);
lean_dec(v_stop_1766_);
goto v___jp_1745_;
}
}
else
{
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v_stop_1766_);
goto v___jp_1745_;
}
}
}
v___jp_1791_:
{
if (v___y_1794_ == 0)
{
if (v___y_1792_ == 0)
{
v___y_1781_ = v___y_1793_;
v___y_1782_ = v___y_1795_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1798_;
v___y_1785_ = v___y_1796_;
v___y_1786_ = v___y_1792_;
goto v___jp_1780_;
}
else
{
if (v___y_1798_ == 0)
{
v___y_1781_ = v___y_1793_;
v___y_1782_ = v___y_1795_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1798_;
v___y_1785_ = v___y_1796_;
v___y_1786_ = v___y_1798_;
goto v___jp_1780_;
}
else
{
uint8_t v___x_1799_; 
lean_inc_ref(v___y_1793_);
v___x_1799_ = l_Lean_Markdown_isRawTextTagName(v_s_1741_, v___y_1793_);
if (v___x_1799_ == 0)
{
v___y_1781_ = v___y_1793_;
v___y_1782_ = v___y_1795_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1798_;
v___y_1785_ = v___y_1796_;
v___y_1786_ = v___x_1799_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1800_; 
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1793_);
lean_dec(v_stop_1766_);
v___x_1800_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__4));
return v___x_1800_;
}
}
}
}
else
{
uint8_t v___x_1801_; 
v___x_1801_ = 0;
v___y_1781_ = v___y_1793_;
v___y_1782_ = v___y_1795_;
v___y_1783_ = v___y_1797_;
v___y_1784_ = v___y_1798_;
v___y_1785_ = v___y_1796_;
v___y_1786_ = v___x_1801_;
goto v___jp_1780_;
}
}
v___jp_1802_:
{
lean_object* v_count_1807_; lean_object* v___x_1809_; 
v_count_1807_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___y_1803_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 1, v_count_1807_);
lean_ctor_set(v___x_1760_, 0, v___y_1803_);
v___x_1809_ = v___x_1760_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___y_1803_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_count_1807_);
v___x_1809_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; lean_object* v_fst_1811_; lean_object* v_pos_1812_; lean_object* v_pos_1813_; lean_object* v_stop_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1810_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___redArg(v_s_1741_, v___x_1809_);
v_fst_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_fst_1811_);
lean_dec_ref(v___x_1810_);
v_pos_1812_ = lean_ctor_get(v___y_1803_, 0);
lean_inc(v_pos_1812_);
lean_dec_ref(v___y_1803_);
v_pos_1813_ = lean_ctor_get(v_fst_1811_, 0);
lean_inc_n(v_pos_1813_, 2);
v_stop_1814_ = lean_ctor_get(v_fst_1811_, 1);
lean_inc(v_stop_1814_);
lean_dec(v_fst_1811_);
v___x_1815_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_1812_, v_pos_1813_);
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_nat_add(v_pos_1813_, v___x_1816_);
v___x_1818_ = lean_nat_dec_le(v___x_1817_, v_stop_1814_);
lean_dec(v___x_1817_);
if (v___x_1818_ == 0)
{
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1815_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v_stop_1814_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v_pos_1813_;
v___y_1798_ = v___x_1763_;
goto v___jp_1791_;
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = l_String_Slice_Pos_get_x3f(v_s_1741_, v_pos_1813_);
if (lean_obj_tag(v___x_1819_) == 0)
{
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1815_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v_stop_1814_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v_pos_1813_;
v___y_1798_ = v___x_1763_;
goto v___jp_1791_;
}
else
{
lean_object* v_val_1820_; uint32_t v___x_1821_; uint32_t v___x_1822_; uint8_t v___x_1823_; 
v_val_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_val_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v___x_1821_ = 32;
v___x_1822_ = lean_unbox_uint32(v_val_1820_);
v___x_1823_ = lean_uint32_dec_eq(v___x_1822_, v___x_1821_);
if (v___x_1823_ == 0)
{
uint32_t v___x_1824_; uint32_t v___x_1825_; uint8_t v___x_1826_; 
v___x_1824_ = 9;
v___x_1825_ = lean_unbox_uint32(v_val_1820_);
v___x_1826_ = lean_uint32_dec_eq(v___x_1825_, v___x_1824_);
if (v___x_1826_ == 0)
{
uint32_t v___x_1827_; uint32_t v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = 62;
v___x_1828_ = lean_unbox_uint32(v_val_1820_);
lean_dec(v_val_1820_);
v___x_1829_ = lean_uint32_dec_eq(v___x_1828_, v___x_1827_);
if (v___x_1829_ == 0)
{
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1815_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v_stop_1814_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v_pos_1813_;
v___y_1798_ = v___x_1829_;
goto v___jp_1791_;
}
else
{
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1815_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v_stop_1814_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v_pos_1813_;
v___y_1798_ = v___x_1763_;
goto v___jp_1791_;
}
}
else
{
lean_dec(v_val_1820_);
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1815_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v_stop_1814_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v_pos_1813_;
v___y_1798_ = v___x_1763_;
goto v___jp_1791_;
}
}
else
{
lean_dec(v_val_1820_);
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1815_;
v___y_1794_ = v___y_1804_;
v___y_1795_ = v_stop_1814_;
v___y_1796_ = v___y_1805_;
v___y_1797_ = v_pos_1813_;
v___y_1798_ = v___x_1763_;
goto v___jp_1791_;
}
}
}
}
}
v___jp_1831_:
{
uint32_t v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = 97;
v___x_1837_ = lean_uint32_dec_le(v___x_1836_, v___y_1832_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec_ref(v___y_1835_);
lean_dec_ref(v___y_1833_);
lean_dec(v_stop_1766_);
lean_del_object(v___x_1760_);
v___x_1838_ = lean_box(0);
return v___x_1838_;
}
else
{
uint32_t v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = 122;
v___x_1840_ = lean_uint32_dec_le(v___y_1832_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_dec_ref(v___y_1835_);
lean_dec_ref(v___y_1833_);
lean_dec(v_stop_1766_);
lean_del_object(v___x_1760_);
v___x_1841_ = lean_box(0);
return v___x_1841_;
}
else
{
v___y_1803_ = v___y_1833_;
v___y_1804_ = v___y_1834_;
v___y_1805_ = v___y_1835_;
v___y_1806_ = v___x_1840_;
goto v___jp_1802_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1848_ = lean_unsigned_to_nat(1u);
v___x_1849_ = lean_nat_add(v_pos_1846_, v___x_1848_);
v___x_1850_ = lean_nat_dec_le(v___x_1849_, v_stop_1847_);
lean_dec(v_stop_1847_);
lean_dec(v___x_1849_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
lean_dec(v_pos_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_stop_1766_);
lean_del_object(v___x_1760_);
v___x_1851_ = lean_box(0);
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; 
v___x_1852_ = l_String_Slice_Pos_get_x3f(v_s_1741_, v_pos_1846_);
lean_dec(v_pos_1846_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v_stop_1766_);
lean_del_object(v___x_1760_);
v___x_1853_ = lean_box(0);
return v___x_1853_;
}
else
{
lean_object* v_val_1854_; uint32_t v___x_1855_; uint32_t v___x_1856_; uint8_t v___x_1857_; 
v_val_1854_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_val_1854_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1855_ = 65;
v___x_1856_ = lean_unbox_uint32(v_val_1854_);
v___x_1857_ = lean_uint32_dec_le(v___x_1855_, v___x_1856_);
if (v___x_1857_ == 0)
{
uint32_t v___x_1858_; 
v___x_1858_ = lean_unbox_uint32(v_val_1854_);
lean_dec(v_val_1854_);
v___y_1832_ = v___x_1858_;
v___y_1833_ = v___y_1845_;
v___y_1834_ = v___y_1843_;
v___y_1835_ = v___y_1844_;
goto v___jp_1831_;
}
else
{
uint32_t v___x_1859_; uint32_t v___x_1860_; uint8_t v___x_1861_; 
v___x_1859_ = 90;
v___x_1860_ = lean_unbox_uint32(v_val_1854_);
v___x_1861_ = lean_uint32_dec_le(v___x_1860_, v___x_1859_);
if (v___x_1861_ == 0)
{
uint32_t v___x_1862_; 
v___x_1862_ = lean_unbox_uint32(v_val_1854_);
lean_dec(v_val_1854_);
v___y_1832_ = v___x_1862_;
v___y_1833_ = v___y_1845_;
v___y_1834_ = v___y_1843_;
v___y_1835_ = v___y_1844_;
goto v___jp_1831_;
}
else
{
lean_dec(v_val_1854_);
v___y_1803_ = v___y_1845_;
v___y_1804_ = v___y_1843_;
v___y_1805_ = v___y_1844_;
v___y_1806_ = v___x_1861_;
goto v___jp_1802_;
}
}
}
}
}
v___jp_1863_:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5);
v___x_1867_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___y_1865_, v___x_1866_);
lean_dec(v___y_1865_);
if (v___x_1867_ == 0)
{
lean_object* v_pos_1868_; lean_object* v_stop_1869_; 
v_pos_1868_ = lean_ctor_get(v___y_1864_, 0);
lean_inc(v_pos_1868_);
v_stop_1869_ = lean_ctor_get(v___y_1864_, 1);
lean_inc(v_stop_1869_);
lean_inc_ref(v___y_1864_);
v___y_1843_ = v___x_1867_;
v___y_1844_ = v___y_1864_;
v___y_1845_ = v___y_1864_;
v_pos_1846_ = v_pos_1868_;
v_stop_1847_ = v_stop_1869_;
goto v___jp_1842_;
}
else
{
lean_object* v_pos_1870_; lean_object* v_stop_1871_; lean_object* v_col_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_pos_1870_ = lean_ctor_get(v___y_1864_, 0);
v_stop_1871_ = lean_ctor_get(v___y_1864_, 1);
lean_inc(v_stop_1871_);
v_col_1872_ = lean_ctor_get(v___y_1864_, 2);
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_add(v_pos_1870_, v___x_1873_);
v___x_1875_ = lean_nat_dec_le(v___x_1874_, v_stop_1871_);
lean_dec(v___x_1874_);
if (v___x_1875_ == 0)
{
lean_inc(v_pos_1870_);
lean_inc_ref(v___y_1864_);
v___y_1843_ = v___x_1867_;
v___y_1844_ = v___y_1864_;
v___y_1845_ = v___y_1864_;
v_pos_1846_ = v_pos_1870_;
v_stop_1847_ = v_stop_1871_;
goto v___jp_1842_;
}
else
{
lean_object* v_str_1876_; lean_object* v_startInclusive_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; lean_object* v___x_1883_; 
v_str_1876_ = lean_ctor_get(v_s_1741_, 0);
v_startInclusive_1877_ = lean_ctor_get(v_s_1741_, 1);
v___x_1878_ = lean_nat_add(v_startInclusive_1877_, v_pos_1870_);
v___x_1879_ = lean_string_utf8_next_fast(v_str_1876_, v___x_1878_);
lean_dec(v___x_1878_);
v___x_1880_ = lean_nat_sub(v___x_1879_, v_startInclusive_1877_);
v___x_1881_ = lean_nat_add(v_col_1872_, v___x_1873_);
v___x_1882_ = 0;
lean_inc(v_stop_1871_);
lean_inc(v___x_1880_);
v___x_1883_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1883_, 0, v___x_1880_);
lean_ctor_set(v___x_1883_, 1, v_stop_1871_);
lean_ctor_set(v___x_1883_, 2, v___x_1881_);
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*3, v___x_1882_);
v___y_1843_ = v___x_1867_;
v___y_1844_ = v___y_1864_;
v___y_1845_ = v___x_1883_;
v_pos_1846_ = v___x_1880_;
v_stop_1847_ = v_stop_1871_;
goto v___jp_1842_;
}
}
}
v___jp_1884_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = lean_unsigned_to_nat(1u);
v___x_1889_ = lean_nat_add(v_pos_1886_, v___x_1888_);
v___x_1890_ = lean_nat_dec_le(v___x_1889_, v_stop_1887_);
lean_dec(v_stop_1887_);
lean_dec(v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec(v_pos_1886_);
v___x_1891_ = lean_box(0);
v___y_1864_ = v___y_1885_;
v___y_1865_ = v___x_1891_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1892_; 
v___x_1892_ = l_String_Slice_Pos_get_x3f(v_s_1741_, v_pos_1886_);
lean_dec(v_pos_1886_);
v___y_1864_ = v___y_1885_;
v___y_1865_ = v___x_1892_;
goto v___jp_1863_;
}
}
v___jp_1893_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = lean_nat_add(v_pos_1895_, v___x_1897_);
v___x_1899_ = lean_nat_dec_le(v___x_1898_, v_stop_1896_);
lean_dec(v___x_1898_);
if (v___x_1899_ == 0)
{
v___y_1885_ = v___y_1894_;
v_pos_1886_ = v_pos_1895_;
v_stop_1887_ = v_stop_1896_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = l_String_Slice_Pos_get_x3f(v_s_1741_, v_pos_1895_);
if (lean_obj_tag(v___x_1900_) == 1)
{
lean_object* v_val_1901_; uint32_t v___x_1902_; uint32_t v___x_1903_; uint8_t v___x_1904_; 
v_val_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = 33;
v___x_1903_ = lean_unbox_uint32(v_val_1901_);
v___x_1904_ = lean_uint32_dec_eq(v___x_1903_, v___x_1902_);
if (v___x_1904_ == 0)
{
uint32_t v___x_1905_; uint32_t v___x_1906_; uint8_t v___x_1907_; 
v___x_1905_ = 63;
v___x_1906_ = lean_unbox_uint32(v_val_1901_);
lean_dec(v_val_1901_);
v___x_1907_ = lean_uint32_dec_eq(v___x_1906_, v___x_1905_);
if (v___x_1907_ == 0)
{
v___y_1885_ = v___y_1894_;
v_pos_1886_ = v_pos_1895_;
v_stop_1887_ = v_stop_1896_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1908_; 
lean_dec(v_stop_1896_);
lean_dec(v_pos_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v_stop_1766_);
lean_del_object(v___x_1760_);
v___x_1908_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__6));
return v___x_1908_;
}
}
else
{
lean_object* v_str_1909_; lean_object* v_startInclusive_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; uint8_t v___x_1917_; 
lean_dec(v_val_1901_);
lean_dec_ref(v___y_1894_);
lean_dec(v_stop_1766_);
lean_del_object(v___x_1760_);
v_str_1909_ = lean_ctor_get(v_s_1741_, 0);
v_startInclusive_1910_ = lean_ctor_get(v_s_1741_, 1);
v___x_1911_ = lean_nat_add(v_startInclusive_1910_, v_pos_1895_);
lean_dec(v_pos_1895_);
v___x_1912_ = lean_string_utf8_next_fast(v_str_1909_, v___x_1911_);
lean_dec(v___x_1911_);
v___x_1913_ = lean_nat_sub(v___x_1912_, v_startInclusive_1910_);
lean_inc(v_stop_1896_);
lean_inc(v___x_1913_);
v___x_1914_ = l_Lean_Markdown_subsliceClamped___redArg(v___x_1913_, v_stop_1896_);
v___x_1915_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__7));
v___x_1916_ = 0;
lean_inc_ref(v___x_1914_);
v___x_1917_ = l_Lean_Markdown_startsWithAscii(v_s_1741_, v___x_1914_, v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1918_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__8));
v___x_1919_ = l_Lean_Markdown_startsWithAscii(v_s_1741_, v___x_1914_, v___x_1918_, v___x_1916_);
if (v___x_1919_ == 0)
{
lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1920_ = lean_nat_add(v___x_1913_, v___x_1897_);
v___x_1921_ = lean_nat_dec_le(v___x_1920_, v_stop_1896_);
lean_dec(v_stop_1896_);
lean_dec(v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; 
lean_dec(v___x_1913_);
v___x_1922_ = lean_box(0);
return v___x_1922_;
}
else
{
lean_object* v___x_1923_; 
v___x_1923_ = l_String_Slice_Pos_get_x3f(v_s_1741_, v___x_1913_);
lean_dec(v___x_1913_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_box(0);
return v___x_1924_;
}
else
{
lean_object* v_val_1925_; uint32_t v___x_1926_; uint32_t v___x_1927_; uint8_t v___x_1928_; 
v_val_1925_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v___x_1923_, 1);
v___x_1926_ = 65;
v___x_1927_ = lean_unbox_uint32(v_val_1925_);
v___x_1928_ = lean_uint32_dec_le(v___x_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
uint32_t v___x_1929_; 
v___x_1929_ = lean_unbox_uint32(v_val_1925_);
lean_dec(v_val_1925_);
v___y_1750_ = v___x_1929_;
goto v___jp_1749_;
}
else
{
uint32_t v___x_1930_; uint32_t v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = 90;
v___x_1931_ = lean_unbox_uint32(v_val_1925_);
v___x_1932_ = lean_uint32_dec_le(v___x_1931_, v___x_1930_);
if (v___x_1932_ == 0)
{
uint32_t v___x_1933_; 
v___x_1933_ = lean_unbox_uint32(v_val_1925_);
lean_dec(v_val_1925_);
v___y_1750_ = v___x_1933_;
goto v___jp_1749_;
}
else
{
lean_dec(v_val_1925_);
goto v___jp_1747_;
}
}
}
}
}
else
{
lean_object* v___x_1934_; 
lean_dec(v___x_1913_);
lean_dec(v_stop_1896_);
v___x_1934_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__9));
return v___x_1934_;
}
}
else
{
lean_object* v___x_1935_; 
lean_dec_ref(v___x_1914_);
lean_dec(v___x_1913_);
lean_dec(v_stop_1896_);
v___x_1935_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__10));
return v___x_1935_;
}
}
}
else
{
lean_dec(v___x_1900_);
v___y_1885_ = v___y_1894_;
v_pos_1886_ = v_pos_1895_;
v_stop_1887_ = v_stop_1896_;
goto v___jp_1884_;
}
}
}
v___jp_1936_:
{
lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1938_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11);
v___x_1939_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__0(v___y_1937_, v___x_1938_);
lean_dec(v___y_1937_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; 
lean_dec(v_stop_1766_);
lean_dec(v_pos_1765_);
lean_del_object(v___x_1760_);
lean_dec_ref(v_after_1757_);
v___x_1940_ = lean_box(0);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_nat_add(v_pos_1765_, v___x_1941_);
v___x_1943_ = lean_nat_dec_le(v___x_1942_, v_stop_1766_);
lean_dec(v___x_1942_);
if (v___x_1943_ == 0)
{
lean_inc(v_stop_1766_);
v___y_1894_ = v_after_1757_;
v_pos_1895_ = v_pos_1765_;
v_stop_1896_ = v_stop_1766_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1957_; 
lean_inc(v_col_1767_);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_after_1757_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; lean_object* v_unused_1959_; lean_object* v_unused_1960_; 
v_unused_1958_ = lean_ctor_get(v_after_1757_, 2);
lean_dec(v_unused_1958_);
v_unused_1959_ = lean_ctor_get(v_after_1757_, 1);
lean_dec(v_unused_1959_);
v_unused_1960_ = lean_ctor_get(v_after_1757_, 0);
lean_dec(v_unused_1960_);
v___x_1945_ = v_after_1757_;
v_isShared_1946_ = v_isSharedCheck_1957_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v_after_1757_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1957_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_str_1947_; lean_object* v_startInclusive_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1955_; 
v_str_1947_ = lean_ctor_get(v_s_1741_, 0);
v_startInclusive_1948_ = lean_ctor_get(v_s_1741_, 1);
v___x_1949_ = lean_nat_add(v_startInclusive_1948_, v_pos_1765_);
lean_dec(v_pos_1765_);
v___x_1950_ = lean_string_utf8_next_fast(v_str_1947_, v___x_1949_);
lean_dec(v___x_1949_);
v___x_1951_ = lean_nat_sub(v___x_1950_, v_startInclusive_1948_);
v___x_1952_ = lean_nat_add(v_col_1767_, v___x_1941_);
lean_dec(v_col_1767_);
v___x_1953_ = 0;
lean_inc(v_stop_1766_);
lean_inc(v___x_1951_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 2, v___x_1952_);
lean_ctor_set(v___x_1945_, 0, v___x_1951_);
v___x_1955_ = v___x_1945_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_stop_1766_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v___x_1952_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*3, v___x_1953_);
lean_inc(v_stop_1766_);
v___y_1894_ = v___x_1955_;
v_pos_1895_ = v___x_1951_;
v_stop_1896_ = v_stop_1766_;
goto v___jp_1893_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___boxed(lean_object* v_s_1967_, lean_object* v_line_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f(v_s_1967_, v_line_1968_);
lean_dec_ref(v_s_1967_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0(lean_object* v_s_1970_, lean_object* v_inst_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___redArg(v_s_1970_, v_a_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0___boxed(lean_object* v_s_1974_, lean_object* v_inst_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f_spec__0(v_s_1974_, v_inst_1975_, v_a_1976_);
lean_dec_ref(v_s_1974_);
return v_res_1977_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_listMarkerInterruptsParagraph(lean_object* v_s_1978_, lean_object* v_after_1979_, lean_object* v_kind_1980_){
_start:
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Markdown_Cursor_isBlank(v_s_1978_, v_after_1979_);
if (v___x_1981_ == 0)
{
if (lean_obj_tag(v_kind_1980_) == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = 1;
return v___x_1982_;
}
else
{
lean_object* v_start_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v_start_1983_ = lean_ctor_get(v_kind_1980_, 0);
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = lean_nat_dec_eq(v_start_1983_, v___x_1984_);
return v___x_1985_;
}
}
else
{
uint8_t v___x_1986_; 
v___x_1986_ = 0;
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_listMarkerInterruptsParagraph___boxed(lean_object* v_s_1987_, lean_object* v_after_1988_, lean_object* v_kind_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_listMarkerInterruptsParagraph(v_s_1987_, v_after_1988_, v_kind_1989_);
lean_dec_ref(v_kind_1989_);
lean_dec_ref(v_s_1987_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isInterrupt(lean_object* v_s_1992_, lean_object* v_line_1993_){
_start:
{
lean_object* v_after_1994_; lean_object* v_pos_1995_; lean_object* v_stop_1996_; uint8_t v___x_1997_; 
v_after_1994_ = lean_ctor_get(v_line_1993_, 0);
v_pos_1995_ = lean_ctor_get(v_after_1994_, 0);
v_stop_1996_ = lean_ctor_get(v_after_1994_, 1);
v___x_1997_ = lean_nat_dec_le(v_stop_1996_, v_pos_1995_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_inc_ref(v_line_1993_);
v___x_1998_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f(v_s_1992_, v_line_1993_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v___x_1999_; 
lean_inc_ref(v_line_1993_);
v___x_1999_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f(v_s_1992_, v_line_1993_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2000_; 
lean_inc_ref(v_line_1993_);
v___x_2000_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f(v_s_1992_, v_line_1993_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2001_; 
lean_inc_ref(v_line_1993_);
v___x_2001_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f(v_s_1992_, v_line_1993_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2002_; 
lean_inc_ref(v_line_1993_);
v___x_2002_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f(v_s_1992_, v_line_1993_);
if (lean_obj_tag(v___x_2002_) == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak(v_s_1992_, v_line_1993_);
return v___x_2003_;
}
else
{
lean_object* v_val_2004_; uint8_t v___x_2005_; uint8_t v___x_2006_; 
v_val_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2005_ = lean_unbox(v_val_2004_);
lean_dec(v_val_2004_);
v___x_2006_ = l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(v___x_2005_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak(v_s_1992_, v_line_1993_);
return v___x_2007_;
}
else
{
lean_dec_ref(v_line_1993_);
return v___x_2006_;
}
}
}
else
{
uint8_t v___x_2008_; 
lean_dec_ref_known(v___x_2001_, 1);
lean_dec_ref(v_line_1993_);
v___x_2008_ = 1;
return v___x_2008_;
}
}
else
{
uint8_t v___x_2009_; 
lean_dec_ref_known(v___x_2000_, 1);
lean_dec_ref(v_line_1993_);
v___x_2009_ = 1;
return v___x_2009_;
}
}
else
{
uint8_t v___x_2010_; 
lean_dec_ref_known(v___x_1999_, 1);
lean_dec_ref(v_line_1993_);
v___x_2010_ = 1;
return v___x_2010_;
}
}
else
{
uint8_t v___x_2011_; 
lean_dec_ref_known(v___x_1998_, 1);
lean_dec_ref(v_line_1993_);
v___x_2011_ = 1;
return v___x_2011_;
}
}
else
{
lean_dec_ref(v_line_1993_);
return v___x_1997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isInterrupt___boxed(lean_object* v_s_2012_, lean_object* v_line_2013_){
_start:
{
uint8_t v_res_2014_; lean_object* v_r_2015_; 
v_res_2014_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isInterrupt(v_s_2012_, v_line_2013_);
lean_dec_ref(v_s_2012_);
v_r_2015_ = lean_box(v_res_2014_);
return v_r_2015_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0(void){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Markdown_BlockZipper_empty___redArg();
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg(lean_object* v_a_2017_){
_start:
{
lean_object* v_cursor_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_cursor_2018_ = lean_ctor_get(v_a_2017_, 1);
v___x_2019_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
lean_inc_ref(v_cursor_2018_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_cursor_2018_);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2017_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState(lean_object* v_s_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_cursor_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_cursor_2024_ = lean_ctor_get(v_a_2023_, 1);
v___x_2025_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
lean_inc_ref(v_cursor_2024_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
lean_ctor_set(v___x_2026_, 1, v_cursor_2024_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_a_2023_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___boxed(lean_object* v_s_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState(v_s_2028_, v_a_2029_);
lean_dec_ref(v_s_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_takeState___redArg(lean_object* v_a_2031_){
_start:
{
lean_object* v_toLineState_2032_; lean_object* v_cursor_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2044_; 
v_toLineState_2032_ = lean_ctor_get(v_a_2031_, 0);
lean_inc_ref(v_toLineState_2032_);
v_cursor_2033_ = lean_ctor_get(v_toLineState_2032_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_toLineState_2032_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v_toLineState_2032_, 0);
lean_dec(v_unused_2045_);
v___x_2035_ = v_toLineState_2032_;
v_isShared_2036_ = v_isSharedCheck_2044_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_cursor_2033_);
lean_dec(v_toLineState_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2044_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_cursor_2033_);
v___x_2039_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v_a_2031_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_takeState(lean_object* v_s_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_toLineState_2048_; lean_object* v_cursor_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2060_; 
v_toLineState_2048_ = lean_ctor_get(v_a_2047_, 0);
lean_inc_ref(v_toLineState_2048_);
v_cursor_2049_ = lean_ctor_get(v_toLineState_2048_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_toLineState_2048_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v_toLineState_2048_, 0);
lean_dec(v_unused_2061_);
v___x_2051_ = v_toLineState_2048_;
v_isShared_2052_ = v_isSharedCheck_2060_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_cursor_2049_);
lean_dec(v_toLineState_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2060_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_cursor_2049_);
v___x_2055_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2055_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_a_2047_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_takeState___boxed(lean_object* v_s_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_takeState(v_s_2062_, v_a_2063_);
lean_dec_ref(v_s_2062_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLine___redArg(lean_object* v_inst_2065_, lean_object* v_z_2066_){
_start:
{
lean_object* v_throw_2067_; lean_object* v___x_2068_; 
v_throw_2067_ = lean_ctor_get(v_inst_2065_, 0);
lean_inc(v_throw_2067_);
lean_dec_ref(v_inst_2065_);
v___x_2068_ = lean_apply_2(v_throw_2067_, lean_box(0), v_z_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLine(lean_object* v_s_2069_, lean_object* v_m_2070_, lean_object* v_00_u03b1_2071_, lean_object* v_inst_2072_, lean_object* v_z_2073_){
_start:
{
lean_object* v_throw_2074_; lean_object* v___x_2075_; 
v_throw_2074_ = lean_ctor_get(v_inst_2072_, 0);
lean_inc(v_throw_2074_);
lean_dec_ref(v_inst_2072_);
v___x_2075_ = lean_apply_2(v_throw_2074_, lean_box(0), v_z_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLine___boxed(lean_object* v_s_2076_, lean_object* v_m_2077_, lean_object* v_00_u03b1_2078_, lean_object* v_inst_2079_, lean_object* v_z_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLine(v_s_2076_, v_m_2077_, v_00_u03b1_2078_, v_inst_2079_, v_z_2080_);
lean_dec_ref(v_s_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLineWith___redArg(lean_object* v_f_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_zipper_2084_; lean_object* v_cursor_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2095_; 
v_zipper_2084_ = lean_ctor_get(v_a_2083_, 0);
v_cursor_2085_ = lean_ctor_get(v_a_2083_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_a_2083_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2087_ = v_a_2083_;
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_cursor_2085_);
lean_inc(v_zipper_2084_);
lean_dec(v_a_2083_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2095_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_cursor_2085_);
v___x_2091_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = lean_apply_1(v_f_2082_, v_zipper_2084_);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
lean_ctor_set(v___x_2093_, 1, v___x_2091_);
return v___x_2093_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLineWith(lean_object* v_s_2096_, lean_object* v_f_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v_zipper_2099_; lean_object* v_cursor_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2110_; 
v_zipper_2099_ = lean_ctor_get(v_a_2098_, 0);
v_cursor_2100_ = lean_ctor_get(v_a_2098_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2098_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2102_ = v_a_2098_;
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_cursor_2100_);
lean_inc(v_zipper_2099_);
lean_dec(v_a_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_cursor_2100_);
v___x_2106_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = lean_apply_1(v_f_2097_, v_zipper_2099_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___x_2106_);
return v___x_2108_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLineWith___boxed(lean_object* v_s_2111_, lean_object* v_f_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishLineWith(v_s_2111_, v_f_2112_, v_a_2113_);
lean_dec_ref(v_s_2111_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_finishLineWith___redArg(lean_object* v_f_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_toLineState_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2137_; 
v_toLineState_2117_ = lean_ctor_get(v_a_2116_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v_a_2116_, 1);
lean_dec(v_unused_2138_);
v___x_2119_ = v_a_2116_;
v_isShared_2120_ = v_isSharedCheck_2137_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_toLineState_2117_);
lean_dec(v_a_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2137_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_zipper_2121_; lean_object* v_cursor_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2136_; 
v_zipper_2121_ = lean_ctor_get(v_toLineState_2117_, 0);
v_cursor_2122_ = lean_ctor_get(v_toLineState_2117_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_toLineState_2117_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2124_ = v_toLineState_2117_;
v_isShared_2125_ = v_isSharedCheck_2136_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_cursor_2122_);
lean_inc(v_zipper_2121_);
lean_dec(v_toLineState_2117_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2136_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2126_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2126_);
v___x_2128_ = v___x_2124_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_cursor_2122_);
v___x_2128_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_unsigned_to_nat(0u);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 1, v___x_2129_);
lean_ctor_set(v___x_2119_, 0, v___x_2128_);
v___x_2131_ = v___x_2119_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_apply_1(v_f_2115_, v_zipper_2121_);
v___x_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_2131_);
return v___x_2133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_finishLineWith(lean_object* v_s_2139_, lean_object* v_f_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_toLineState_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2162_; 
v_toLineState_2142_ = lean_ctor_get(v_a_2141_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v_a_2141_, 1);
lean_dec(v_unused_2163_);
v___x_2144_ = v_a_2141_;
v_isShared_2145_ = v_isSharedCheck_2162_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_toLineState_2142_);
lean_dec(v_a_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2162_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v_zipper_2146_; lean_object* v_cursor_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2161_; 
v_zipper_2146_ = lean_ctor_get(v_toLineState_2142_, 0);
v_cursor_2147_ = lean_ctor_get(v_toLineState_2142_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_toLineState_2142_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2149_ = v_toLineState_2142_;
v_isShared_2150_ = v_isSharedCheck_2161_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_cursor_2147_);
lean_inc(v_zipper_2146_);
lean_dec(v_toLineState_2142_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2161_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 0, v___x_2151_);
v___x_2153_ = v___x_2149_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_cursor_2147_);
v___x_2153_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v___x_2154_);
lean_ctor_set(v___x_2144_, 0, v___x_2153_);
v___x_2156_ = v___x_2144_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2153_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_apply_1(v_f_2140_, v_zipper_2146_);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v___x_2156_);
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_finishLineWith___boxed(lean_object* v_s_2164_, lean_object* v_f_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_ContainerM_finishLineWith(v_s_2164_, v_f_2165_, v_a_2166_);
lean_dec_ref(v_s_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_runContainerM___redArg(lean_object* v_act_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_cursor_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_cursor_2170_ = lean_ctor_get(v_a_2169_, 1);
lean_inc_ref(v_cursor_2170_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2169_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = lean_apply_1(v_act_2168_, v___x_2172_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2183_; 
lean_dec_ref(v_cursor_2170_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v___x_2173_, 0);
lean_dec(v_unused_2184_);
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2183_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_toLineState_2178_; lean_object* v_matched_2179_; lean_object* v___x_2181_; 
v_toLineState_2178_ = lean_ctor_get(v_a_2174_, 0);
lean_inc_ref(v_toLineState_2178_);
v_matched_2179_ = lean_ctor_get(v_a_2174_, 1);
lean_inc(v_matched_2179_);
lean_dec(v_a_2174_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v_toLineState_2178_);
lean_ctor_set(v___x_2176_, 0, v_matched_2179_);
v___x_2181_ = v___x_2176_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_matched_2179_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_toLineState_2178_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2194_; 
v_a_2185_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; 
v_unused_2195_ = lean_ctor_get(v___x_2173_, 1);
lean_dec(v_unused_2195_);
v___x_2187_ = v___x_2173_;
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2173_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2189_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v_cursor_2170_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v___x_2190_);
v___x_2192_ = v___x_2187_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2185_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_runContainerM(lean_object* v_s_2196_, lean_object* v_act_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_cursor_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v_cursor_2199_ = lean_ctor_get(v_a_2198_, 1);
lean_inc_ref(v_cursor_2199_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2198_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_apply_1(v_act_2197_, v___x_2201_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref(v_cursor_2199_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; 
v_unused_2213_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2213_);
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v_toLineState_2207_; lean_object* v_matched_2208_; lean_object* v___x_2210_; 
v_toLineState_2207_ = lean_ctor_get(v_a_2203_, 0);
lean_inc_ref(v_toLineState_2207_);
v_matched_2208_ = lean_ctor_get(v_a_2203_, 1);
lean_inc(v_matched_2208_);
lean_dec(v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 1, v_toLineState_2207_);
lean_ctor_set(v___x_2205_, 0, v_matched_2208_);
v___x_2210_ = v___x_2205_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_matched_2208_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_toLineState_2207_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2223_; 
v_a_2214_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v___x_2202_, 1);
lean_dec(v_unused_2224_);
v___x_2216_ = v___x_2202_;
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2202_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2223_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2218_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_cursor_2199_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v___x_2219_);
v___x_2221_ = v___x_2216_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_runContainerM___boxed(lean_object* v_s_2225_, lean_object* v_act_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_runContainerM(v_s_2225_, v_act_2226_, v_a_2227_);
lean_dec_ref(v_s_2225_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___redArg(lean_object* v_s_2229_, lean_object* v_a_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_toLineState_2232_; lean_object* v_zipper_2233_; lean_object* v_matched_2234_; lean_object* v_cursor_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2319_; 
v_toLineState_2232_ = lean_ctor_get(v_a_2230_, 0);
lean_inc_ref(v_toLineState_2232_);
v_zipper_2233_ = lean_ctor_get(v_toLineState_2232_, 0);
lean_inc_ref(v_zipper_2233_);
v_matched_2234_ = lean_ctor_get(v_a_2230_, 1);
v_cursor_2235_ = lean_ctor_get(v_toLineState_2232_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_toLineState_2232_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_toLineState_2232_, 0);
lean_dec(v_unused_2320_);
v___x_2237_ = v_toLineState_2232_;
v_isShared_2238_ = v_isSharedCheck_2319_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_cursor_2235_);
lean_dec(v_toLineState_2232_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2319_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_spine_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_spine_2239_ = lean_ctor_get(v_zipper_2233_, 1);
v___x_2240_ = lean_array_get_size(v_spine_2239_);
v___x_2241_ = lean_nat_dec_lt(v_matched_2234_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_del_object(v___x_2237_);
lean_dec_ref(v_cursor_2235_);
lean_dec_ref(v_zipper_2233_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2230_);
lean_ctor_set(v___x_2242_, 1, v___y_2231_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v_container_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2317_; 
v___x_2243_ = lean_array_fget(v_spine_2239_, v_matched_2234_);
v_container_2244_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v___x_2243_, 1);
lean_dec(v_unused_2318_);
v___x_2246_ = v___x_2243_;
v_isShared_2247_ = v_isSharedCheck_2317_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_container_2244_);
lean_dec(v___x_2243_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2317_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
if (lean_obj_tag(v_container_2244_) == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref_known(v_container_2244_, 1);
v___x_2248_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2229_, v_cursor_2235_);
v___x_2249_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f(v_s_2229_, v___x_2248_);
if (lean_obj_tag(v___x_2249_) == 1)
{
lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2266_; 
lean_inc(v_matched_2234_);
lean_del_object(v___x_2246_);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_a_2230_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; lean_object* v_unused_2268_; 
v_unused_2267_ = lean_ctor_get(v_a_2230_, 1);
lean_dec(v_unused_2267_);
v_unused_2268_ = lean_ctor_get(v_a_2230_, 0);
lean_dec(v_unused_2268_);
v___x_2251_ = v_a_2230_;
v_isShared_2252_ = v_isSharedCheck_2266_;
goto v_resetjp_2250_;
}
else
{
lean_dec(v_a_2230_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2266_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v_val_2253_; lean_object* v_fst_2254_; lean_object* v_snd_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v_val_2253_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v___x_2249_, 1);
v_fst_2254_ = lean_ctor_get(v_val_2253_, 0);
lean_inc(v_fst_2254_);
v_snd_2255_ = lean_ctor_get(v_val_2253_, 1);
lean_inc(v_snd_2255_);
lean_dec(v_val_2253_);
v___x_2256_ = l_Lean_Markdown_BlockZipper_pushBlockquoteMarker___redArg(v_zipper_2233_, v_matched_2234_, v_fst_2254_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v_snd_2255_);
lean_ctor_set(v___x_2237_, 0, v___x_2256_);
v___x_2258_ = v___x_2237_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2256_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_snd_2255_);
v___x_2258_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = lean_nat_add(v_matched_2234_, v___x_2259_);
lean_dec(v_matched_2234_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 1, v___x_2260_);
lean_ctor_set(v___x_2251_, 0, v___x_2258_);
v___x_2262_ = v___x_2251_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
v_a_2230_ = v___x_2262_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_2270_; 
lean_dec(v___x_2249_);
lean_del_object(v___x_2237_);
lean_dec_ref(v_zipper_2233_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___y_2231_);
lean_ctor_set(v___x_2246_, 0, v_a_2230_);
v___x_2270_ = v___x_2246_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2230_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v___y_2231_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v_contentColumn_2272_; lean_object* v___x_2273_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2246_);
v_contentColumn_2272_ = lean_ctor_get(v_container_2244_, 2);
lean_inc_n(v_contentColumn_2272_, 2);
lean_dec_ref_known(v_container_2244_, 3);
lean_inc_ref(v_cursor_2235_);
v___x_2273_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(v_s_2229_, v_cursor_2235_, v_contentColumn_2272_);
v_fst_2274_ = lean_ctor_get(v___x_2273_, 0);
v_snd_2275_ = lean_ctor_get(v___x_2273_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2277_ = v___x_2273_;
v_isShared_2278_ = v_isSharedCheck_2316_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_snd_2275_);
lean_inc(v_fst_2274_);
lean_dec(v___x_2273_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2316_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
uint8_t v___x_2279_; 
v___x_2279_ = lean_nat_dec_le(v_contentColumn_2272_, v_snd_2275_);
lean_dec(v_snd_2275_);
lean_dec(v_contentColumn_2272_);
if (v___x_2279_ == 0)
{
uint8_t v___x_2280_; 
lean_dec(v_fst_2274_);
lean_inc_ref(v_cursor_2235_);
v___x_2280_ = l_Lean_Markdown_Cursor_isBlank(v_s_2229_, v_cursor_2235_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2282_; 
lean_del_object(v___x_2237_);
lean_dec_ref(v_cursor_2235_);
lean_dec_ref(v_zipper_2233_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 1, v___y_2231_);
lean_ctor_set(v___x_2277_, 0, v_a_2230_);
v___x_2282_ = v___x_2277_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2230_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___y_2231_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2298_; 
lean_inc(v_matched_2234_);
lean_del_object(v___x_2277_);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_a_2230_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; lean_object* v_unused_2300_; 
v_unused_2299_ = lean_ctor_get(v_a_2230_, 1);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_a_2230_, 0);
lean_dec(v_unused_2300_);
v___x_2285_ = v_a_2230_;
v_isShared_2286_ = v_isSharedCheck_2298_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v_a_2230_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2298_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v_fst_2288_; lean_object* v___x_2290_; 
v___x_2287_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_countIndentCols(v_s_2229_, v_cursor_2235_);
v_fst_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_fst_2288_);
lean_dec_ref(v___x_2287_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v_fst_2288_);
v___x_2290_ = v___x_2237_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_zipper_2233_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_fst_2288_);
v___x_2290_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2291_ = lean_unsigned_to_nat(1u);
v___x_2292_ = lean_nat_add(v_matched_2234_, v___x_2291_);
lean_dec(v_matched_2234_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 1, v___x_2292_);
lean_ctor_set(v___x_2285_, 0, v___x_2290_);
v___x_2294_ = v___x_2285_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
v_a_2230_ = v___x_2294_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2313_; 
lean_inc(v_matched_2234_);
lean_del_object(v___x_2277_);
lean_dec_ref(v_cursor_2235_);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_a_2230_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2314_ = lean_ctor_get(v_a_2230_, 1);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_a_2230_, 0);
lean_dec(v_unused_2315_);
v___x_2302_ = v_a_2230_;
v_isShared_2303_ = v_isSharedCheck_2313_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v_a_2230_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2313_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 1, v_fst_2274_);
v___x_2305_ = v___x_2237_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_zipper_2233_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_fst_2274_);
v___x_2305_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = lean_unsigned_to_nat(1u);
v___x_2307_ = lean_nat_add(v_matched_2234_, v___x_2306_);
lean_dec(v_matched_2234_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2307_);
lean_ctor_set(v___x_2302_, 0, v___x_2305_);
v___x_2309_ = v___x_2302_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
v_a_2230_ = v___x_2309_;
goto _start;
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___redArg___boxed(lean_object* v_s_2321_, lean_object* v_a_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___redArg(v_s_2321_, v_a_2322_, v___y_2323_);
lean_dec_ref(v_s_2321_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers(lean_object* v_s_2325_, lean_object* v_a_2326_){
_start:
{
lean_object* v_toLineState_2327_; lean_object* v_cursor_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2358_; 
v_toLineState_2327_ = lean_ctor_get(v_a_2326_, 0);
lean_inc_ref(v_toLineState_2327_);
v_cursor_2328_ = lean_ctor_get(v_toLineState_2327_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_toLineState_2327_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v_toLineState_2327_, 0);
lean_dec(v_unused_2359_);
v___x_2330_ = v_toLineState_2327_;
v_isShared_2331_ = v_isSharedCheck_2358_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_cursor_2328_);
lean_dec(v_toLineState_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2358_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2332_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2332_);
v___x_2334_ = v___x_2330_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_cursor_2328_);
v___x_2334_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___redArg(v_s_2325_, v_a_2326_, v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2346_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v___x_2337_, 1);
lean_dec(v_unused_2347_);
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2346_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2342_ = lean_box(0);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 1, v_a_2338_);
lean_ctor_set(v___x_2340_, 0, v___x_2342_);
v___x_2344_ = v___x_2340_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_a_2338_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_a_2348_ = lean_ctor_get(v___x_2337_, 0);
v_a_2349_ = lean_ctor_get(v___x_2337_, 1);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2337_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_inc(v_a_2348_);
lean_dec(v___x_2337_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2348_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers___boxed(lean_object* v_s_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers(v_s_2360_, v_a_2361_);
lean_dec_ref(v_s_2360_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0(lean_object* v_s_2363_, lean_object* v_inst_2364_, lean_object* v_a_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___redArg(v_s_2363_, v_a_2365_, v___y_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0___boxed(lean_object* v_s_2368_, lean_object* v_inst_2369_, lean_object* v_a_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers_spec__0(v_s_2368_, v_inst_2369_, v_a_2370_, v___y_2371_);
lean_dec_ref(v_s_2368_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___lam__0(lean_object* v_s_2373_, lean_object* v_x1_2374_, lean_object* v_x2_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_2373_, v_x1_2374_, v_x2_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___lam__0___boxed(lean_object* v_s_2377_, lean_object* v_x1_2378_, lean_object* v_x2_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___lam__0(v_s_2377_, v_x1_2378_, v_x2_2379_);
lean_dec_ref(v_s_2377_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading(lean_object* v_s_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___y_2403_; lean_object* v_toLineState_2406_; lean_object* v_zipper_2407_; lean_object* v_matched_2408_; lean_object* v_cursor_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2490_; 
v_toLineState_2406_ = lean_ctor_get(v_a_2401_, 0);
lean_inc_ref(v_toLineState_2406_);
v_zipper_2407_ = lean_ctor_get(v_toLineState_2406_, 0);
lean_inc_ref(v_zipper_2407_);
v_matched_2408_ = lean_ctor_get(v_a_2401_, 1);
v_cursor_2409_ = lean_ctor_get(v_toLineState_2406_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_toLineState_2406_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v_toLineState_2406_, 0);
lean_dec(v_unused_2491_);
v___x_2411_ = v_toLineState_2406_;
v_isShared_2412_ = v_isSharedCheck_2490_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_cursor_2409_);
lean_dec(v_toLineState_2406_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2490_;
goto v_resetjp_2410_;
}
v___jp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v___y_2403_);
return v___x_2405_;
}
v_resetjp_2410_:
{
lean_object* v_document_2413_; lean_object* v_spine_2414_; lean_object* v_openLeaf_x3f_2415_; lean_object* v_blankLineFloor_x3f_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2489_; 
v_document_2413_ = lean_ctor_get(v_zipper_2407_, 0);
v_spine_2414_ = lean_ctor_get(v_zipper_2407_, 1);
v_openLeaf_x3f_2415_ = lean_ctor_get(v_zipper_2407_, 2);
v_blankLineFloor_x3f_2416_ = lean_ctor_get(v_zipper_2407_, 3);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_zipper_2407_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2418_ = v_zipper_2407_;
v_isShared_2419_ = v_isSharedCheck_2489_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_blankLineFloor_x3f_2416_);
lean_inc(v_openLeaf_x3f_2415_);
lean_inc(v_spine_2414_);
lean_inc(v_document_2413_);
lean_dec(v_zipper_2407_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2489_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = lean_array_get_size(v_spine_2414_);
v___x_2421_ = lean_nat_dec_eq(v___x_2420_, v_matched_2408_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_del_object(v___x_2418_);
lean_dec(v_blankLineFloor_x3f_2416_);
lean_dec(v_openLeaf_x3f_2415_);
lean_dec_ref(v_spine_2414_);
lean_dec_ref(v_document_2413_);
lean_del_object(v___x_2411_);
lean_dec_ref(v_cursor_2409_);
lean_dec_ref(v_s_2400_);
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set(v___x_2423_, 1, v_a_2401_);
return v___x_2423_;
}
else
{
if (lean_obj_tag(v_openLeaf_x3f_2415_) == 1)
{
lean_object* v_val_2424_; 
v_val_2424_ = lean_ctor_get(v_openLeaf_x3f_2415_, 0);
lean_inc(v_val_2424_);
lean_dec_ref_known(v_openLeaf_x3f_2415_, 1);
if (lean_obj_tag(v_val_2424_) == 0)
{
lean_object* v_lines_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2488_; 
v_lines_2425_ = lean_ctor_get(v_val_2424_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_val_2424_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2427_ = v_val_2424_;
v_isShared_2428_ = v_isSharedCheck_2488_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_lines_2425_);
lean_dec(v_val_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2488_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_inc_ref(v_cursor_2409_);
v___x_2429_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2400_, v_cursor_2409_);
v___x_2430_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f(v_s_2400_, v___x_2429_);
if (lean_obj_tag(v___x_2430_) == 1)
{
lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2483_; 
v_isSharedCheck_2483_ = !lean_is_exclusive(v_a_2401_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; lean_object* v_unused_2485_; 
v_unused_2484_ = lean_ctor_get(v_a_2401_, 1);
lean_dec(v_unused_2484_);
v_unused_2485_ = lean_ctor_get(v_a_2401_, 0);
lean_dec(v_unused_2485_);
v___x_2432_ = v_a_2401_;
v_isShared_2433_ = v_isSharedCheck_2483_;
goto v_resetjp_2431_;
}
else
{
lean_dec(v_a_2401_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2483_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_val_2434_; lean_object* v_fst_2435_; lean_object* v_snd_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_fst_2439_; lean_object* v_snd_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2482_; 
v_val_2434_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_val_2434_);
lean_dec_ref_known(v___x_2430_, 1);
v_fst_2435_ = lean_ctor_get(v_val_2434_, 0);
lean_inc(v_fst_2435_);
v_snd_2436_ = lean_ctor_get(v_val_2434_, 1);
lean_inc(v_snd_2436_);
lean_dec(v_val_2434_);
v___x_2437_ = l_Lean_Markdown_InlineSource_ofLines(v_s_2400_, v_lines_2425_);
v___x_2438_ = l_Lean_Markdown_extractRefDefs(v_s_2400_, v___x_2437_);
v_fst_2439_ = lean_ctor_get(v___x_2438_, 0);
v_snd_2440_ = lean_ctor_get(v___x_2438_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2442_ = v___x_2438_;
v_isShared_2443_ = v_isSharedCheck_2482_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snd_2440_);
lean_inc(v_fst_2439_);
lean_dec(v___x_2438_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2482_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v_pos_2444_; lean_object* v_stop_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v_pos_2444_ = lean_ctor_get(v_cursor_2409_, 0);
v_stop_2445_ = lean_ctor_get(v_cursor_2409_, 1);
lean_inc(v_stop_2445_);
lean_inc(v_pos_2444_);
v___x_2446_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_2444_, v_stop_2445_);
v___x_2447_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2447_);
v___x_2449_ = v___x_2411_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_cursor_2409_);
v___x_2449_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2450_ = lean_unsigned_to_nat(0u);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v___x_2450_);
lean_ctor_set(v___x_2432_, 0, v___x_2449_);
v___x_2452_ = v___x_2432_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___y_2454_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_box(0);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 2, v___x_2469_);
v___x_2471_ = v___x_2418_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_document_2413_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_spine_2414_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_blankLineFloor_x3f_2416_);
v___x_2471_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2470_;
}
v___jp_2453_:
{
if (lean_obj_tag(v_snd_2440_) == 0)
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
lean_dec(v_snd_2436_);
lean_dec(v_fst_2435_);
v___x_2455_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_2446_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2455_);
v___x_2457_ = v___x_2427_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2458_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_2400_, v___y_2454_, v___x_2457_);
lean_dec_ref(v_s_2400_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 1);
lean_ctor_set(v___x_2442_, 1, v___x_2452_);
lean_ctor_set(v___x_2442_, 0, v___x_2458_);
v___x_2460_ = v___x_2442_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2452_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
else
{
lean_object* v_val_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_dec_ref(v___x_2446_);
lean_del_object(v___x_2427_);
v_val_2463_ = lean_ctor_get(v_snd_2440_, 0);
lean_inc(v_val_2463_);
lean_dec_ref_known(v_snd_2440_, 1);
v___x_2464_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2464_, 0, v_fst_2435_);
lean_ctor_set(v___x_2464_, 1, v_val_2463_);
lean_ctor_set(v___x_2464_, 2, v_snd_2436_);
v___x_2465_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_2400_, v___y_2454_, v___x_2464_);
lean_dec_ref(v_s_2400_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set_tag(v___x_2442_, 1);
lean_ctor_set(v___x_2442_, 1, v___x_2452_);
lean_ctor_set(v___x_2442_, 0, v___x_2465_);
v___x_2467_ = v___x_2442_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v___x_2452_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2472_ = lean_array_get_size(v_fst_2439_);
v___x_2473_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___closed__9));
v___x_2474_ = lean_nat_dec_lt(v___x_2450_, v___x_2472_);
if (v___x_2474_ == 0)
{
lean_dec(v_fst_2439_);
v___y_2454_ = v___x_2471_;
goto v___jp_2453_;
}
else
{
lean_object* v___f_2475_; size_t v___x_2476_; size_t v___x_2477_; lean_object* v___x_2478_; 
lean_inc_ref(v_s_2400_);
v___f_2475_ = lean_alloc_closure((void*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trySetextHeading___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2475_, 0, v_s_2400_);
v___x_2476_ = ((size_t)0ULL);
v___x_2477_ = lean_usize_of_nat(v___x_2472_);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2473_, v___f_2475_, v_fst_2439_, v___x_2476_, v___x_2477_, v___x_2471_);
v___y_2454_ = v___x_2478_;
goto v___jp_2453_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec(v___x_2430_);
lean_del_object(v___x_2427_);
lean_dec_ref(v_lines_2425_);
lean_del_object(v___x_2418_);
lean_dec(v_blankLineFloor_x3f_2416_);
lean_dec_ref(v_spine_2414_);
lean_dec_ref(v_document_2413_);
lean_del_object(v___x_2411_);
lean_dec_ref(v_cursor_2409_);
lean_dec_ref(v_s_2400_);
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2486_);
lean_ctor_set(v___x_2487_, 1, v_a_2401_);
return v___x_2487_;
}
}
}
else
{
lean_dec(v_val_2424_);
lean_del_object(v___x_2418_);
lean_dec(v_blankLineFloor_x3f_2416_);
lean_dec_ref(v_spine_2414_);
lean_dec_ref(v_document_2413_);
lean_del_object(v___x_2411_);
lean_dec_ref(v_cursor_2409_);
lean_dec_ref(v_s_2400_);
v___y_2403_ = v_a_2401_;
goto v___jp_2402_;
}
}
else
{
lean_del_object(v___x_2418_);
lean_dec(v_blankLineFloor_x3f_2416_);
lean_dec(v_openLeaf_x3f_2415_);
lean_dec_ref(v_spine_2414_);
lean_dec_ref(v_document_2413_);
lean_del_object(v___x_2411_);
lean_dec_ref(v_cursor_2409_);
lean_dec_ref(v_s_2400_);
v___y_2403_ = v_a_2401_;
goto v___jp_2402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryLazyContinuation(lean_object* v_s_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v___y_2495_; lean_object* v_toLineState_2498_; lean_object* v_zipper_2499_; lean_object* v_matched_2500_; lean_object* v_cursor_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2535_; 
v_toLineState_2498_ = lean_ctor_get(v_a_2493_, 0);
lean_inc_ref(v_toLineState_2498_);
v_zipper_2499_ = lean_ctor_get(v_toLineState_2498_, 0);
lean_inc_ref(v_zipper_2499_);
v_matched_2500_ = lean_ctor_get(v_a_2493_, 1);
v_cursor_2501_ = lean_ctor_get(v_toLineState_2498_, 1);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_toLineState_2498_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v_toLineState_2498_, 0);
lean_dec(v_unused_2536_);
v___x_2503_ = v_toLineState_2498_;
v_isShared_2504_ = v_isSharedCheck_2535_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_cursor_2501_);
lean_dec(v_toLineState_2498_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2535_;
goto v_resetjp_2502_;
}
v___jp_2494_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___y_2495_);
return v___x_2497_;
}
v_resetjp_2502_:
{
lean_object* v_spine_2505_; lean_object* v_openLeaf_x3f_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v_spine_2505_ = lean_ctor_get(v_zipper_2499_, 1);
v_openLeaf_x3f_2506_ = lean_ctor_get(v_zipper_2499_, 2);
v___x_2507_ = lean_array_get_size(v_spine_2505_);
v___x_2508_ = lean_nat_dec_lt(v_matched_2500_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_del_object(v___x_2503_);
lean_dec_ref(v_cursor_2501_);
lean_dec_ref(v_zipper_2499_);
v___x_2509_ = lean_box(0);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
lean_ctor_set(v___x_2510_, 1, v_a_2493_);
return v___x_2510_;
}
else
{
if (lean_obj_tag(v_openLeaf_x3f_2506_) == 1)
{
lean_object* v_val_2511_; 
v_val_2511_ = lean_ctor_get(v_openLeaf_x3f_2506_, 0);
if (lean_obj_tag(v_val_2511_) == 0)
{
lean_object* v___x_2512_; uint8_t v___x_2513_; 
lean_inc_ref(v_cursor_2501_);
v___x_2512_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2492_, v_cursor_2501_);
v___x_2513_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isInterrupt(v_s_2492_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2530_; 
v_isSharedCheck_2530_ = !lean_is_exclusive(v_a_2493_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; lean_object* v_unused_2532_; 
v_unused_2531_ = lean_ctor_get(v_a_2493_, 1);
lean_dec(v_unused_2531_);
v_unused_2532_ = lean_ctor_get(v_a_2493_, 0);
lean_dec(v_unused_2532_);
v___x_2515_ = v_a_2493_;
v_isShared_2516_ = v_isSharedCheck_2530_;
goto v_resetjp_2514_;
}
else
{
lean_dec(v_a_2493_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2530_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_pos_2517_; lean_object* v_stop_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
v_pos_2517_ = lean_ctor_get(v_cursor_2501_, 0);
lean_inc(v_pos_2517_);
v_stop_2518_ = lean_ctor_get(v_cursor_2501_, 1);
lean_inc(v_stop_2518_);
v___x_2519_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2519_);
v___x_2521_ = v___x_2503_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_cursor_2501_);
v___x_2521_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2522_ = lean_unsigned_to_nat(0u);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 1, v___x_2522_);
lean_ctor_set(v___x_2515_, 0, v___x_2521_);
v___x_2524_ = v___x_2515_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_2517_, v_stop_2518_);
v___x_2526_ = l_Lean_Markdown_BlockZipper_extendParagraph___redArg(v_zipper_2499_, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___x_2524_);
return v___x_2527_;
}
}
}
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_del_object(v___x_2503_);
lean_dec_ref(v_cursor_2501_);
lean_dec_ref(v_zipper_2499_);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v_a_2493_);
return v___x_2534_;
}
}
else
{
lean_del_object(v___x_2503_);
lean_dec_ref(v_cursor_2501_);
lean_dec_ref(v_zipper_2499_);
v___y_2495_ = v_a_2493_;
goto v___jp_2494_;
}
}
else
{
lean_del_object(v___x_2503_);
lean_dec_ref(v_cursor_2501_);
lean_dec_ref(v_zipper_2499_);
v___y_2495_ = v_a_2493_;
goto v___jp_2494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryLazyContinuation___boxed(lean_object* v_s_2537_, lean_object* v_a_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryLazyContinuation(v_s_2537_, v_a_2538_);
lean_dec_ref(v_s_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg(lean_object* v_matched_2540_, lean_object* v_s_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_spine_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_spine_2543_ = lean_ctor_get(v_a_2542_, 1);
v___x_2544_ = lean_array_get_size(v_spine_2543_);
v___x_2545_ = lean_nat_dec_lt(v_matched_2540_, v___x_2544_);
if (v___x_2545_ == 0)
{
return v_a_2542_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_Markdown_BlockZipper_closeContainer(v_s_2541_, v_a_2542_);
v_a_2542_ = v___x_2546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg___boxed(lean_object* v_matched_2548_, lean_object* v_s_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg(v_matched_2548_, v_s_2549_, v_a_2550_);
lean_dec_ref(v_s_2549_);
lean_dec(v_matched_2548_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove(lean_object* v_s_2552_, lean_object* v_matched_2553_, lean_object* v_z_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg(v_matched_2553_, v_s_2552_, v_z_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove___boxed(lean_object* v_s_2556_, lean_object* v_matched_2557_, lean_object* v_z_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove(v_s_2556_, v_matched_2557_, v_z_2558_);
lean_dec(v_matched_2557_);
lean_dec_ref(v_s_2556_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0(lean_object* v_matched_2560_, lean_object* v_s_2561_, lean_object* v_inst_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg(v_matched_2560_, v_s_2561_, v_a_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___boxed(lean_object* v_matched_2565_, lean_object* v_s_2566_, lean_object* v_inst_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0(v_matched_2565_, v_s_2566_, v_inst_2567_, v_a_2568_);
lean_dec_ref(v_s_2566_);
lean_dec(v_matched_2565_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers(lean_object* v_s_2570_, lean_object* v_matched_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_zipper_2573_; lean_object* v_cursor_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2584_; 
v_zipper_2573_ = lean_ctor_get(v_a_2572_, 0);
v_cursor_2574_ = lean_ctor_get(v_a_2572_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_a_2572_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2576_ = v_a_2572_;
v_isShared_2577_ = v_isSharedCheck_2584_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_cursor_2574_);
lean_inc(v_zipper_2573_);
lean_dec(v_a_2572_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2584_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2578_ = lean_box(0);
v___x_2579_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg(v_matched_2571_, v_s_2570_, v_zipper_2573_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2579_);
v___x_2581_ = v___x_2576_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_cursor_2574_);
v___x_2581_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2578_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
return v___x_2582_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers___boxed(lean_object* v_s_2585_, lean_object* v_matched_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers(v_s_2585_, v_matched_2586_, v_a_2587_);
lean_dec(v_matched_2586_);
lean_dec_ref(v_s_2585_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeFencedCode(lean_object* v_s_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___y_2592_; lean_object* v_zipper_2595_; lean_object* v_openLeaf_x3f_2596_; 
v_zipper_2595_ = lean_ctor_get(v_a_2590_, 0);
v_openLeaf_x3f_2596_ = lean_ctor_get(v_zipper_2595_, 2);
if (lean_obj_tag(v_openLeaf_x3f_2596_) == 1)
{
lean_object* v_val_2597_; 
v_val_2597_ = lean_ctor_get(v_openLeaf_x3f_2596_, 0);
if (lean_obj_tag(v_val_2597_) == 1)
{
lean_object* v_cursor_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2631_; 
lean_inc_ref(v_zipper_2595_);
v_cursor_2598_ = lean_ctor_get(v_a_2590_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_a_2590_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v_a_2590_, 0);
lean_dec(v_unused_2632_);
v___x_2600_ = v_a_2590_;
v_isShared_2601_ = v_isSharedCheck_2631_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_cursor_2598_);
lean_dec(v_a_2590_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2631_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_info_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_info_2602_ = lean_ctor_get(v_val_2597_, 0);
lean_inc_ref(v_cursor_2598_);
v___x_2603_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2589_, v_cursor_2598_);
v___x_2604_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceClose_x3f(v_s_2589_, v___x_2603_, v_info_2602_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_openIndent_2605_; lean_object* v___x_2606_; lean_object* v_fst_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2621_; 
v_openIndent_2605_ = lean_ctor_get(v_info_2602_, 1);
lean_inc(v_openIndent_2605_);
lean_inc_ref(v_cursor_2598_);
v___x_2606_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(v_s_2589_, v_cursor_2598_, v_openIndent_2605_);
v_fst_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2606_, 1);
lean_dec(v_unused_2622_);
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2621_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_fst_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2621_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2611_);
v___x_2613_ = v___x_2600_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_cursor_2598_);
v___x_2613_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2614_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_2589_, v_fst_2607_);
v___x_2615_ = l_Lean_Markdown_BlockZipper_extendFencedCode___redArg(v_zipper_2595_, v___x_2614_);
v___x_2616_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_2615_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set_tag(v___x_2609_, 1);
lean_ctor_set(v___x_2609_, 1, v___x_2613_);
lean_ctor_set(v___x_2609_, 0, v___x_2616_);
v___x_2618_ = v___x_2609_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_val_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v_val_2623_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2624_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2624_);
v___x_2626_ = v___x_2600_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_cursor_2598_);
v___x_2626_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = l_Lean_Markdown_BlockZipper_closeFencedCode(v_s_2589_, v_zipper_2595_, v_val_2623_);
v___x_2628_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_2627_);
v___x_2629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
lean_ctor_set(v___x_2629_, 1, v___x_2626_);
return v___x_2629_;
}
}
}
}
else
{
v___y_2592_ = v_a_2590_;
goto v___jp_2591_;
}
}
else
{
v___y_2592_ = v_a_2590_;
goto v___jp_2591_;
}
v___jp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___y_2592_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeFencedCode___boxed(lean_object* v_s_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeFencedCode(v_s_2633_, v_a_2634_);
lean_dec_ref(v_s_2633_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeHtmlBlock(lean_object* v_s_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v___y_2639_; lean_object* v_zipper_2642_; lean_object* v_openLeaf_x3f_2643_; 
v_zipper_2642_ = lean_ctor_get(v_a_2637_, 0);
v_openLeaf_x3f_2643_ = lean_ctor_get(v_zipper_2642_, 2);
if (lean_obj_tag(v_openLeaf_x3f_2643_) == 1)
{
lean_object* v_val_2644_; 
v_val_2644_ = lean_ctor_get(v_openLeaf_x3f_2643_, 0);
if (lean_obj_tag(v_val_2644_) == 3)
{
lean_object* v_cursor_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2692_; 
lean_inc_ref(v_zipper_2642_);
v_cursor_2645_ = lean_ctor_get(v_a_2637_, 1);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_a_2637_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v_a_2637_, 0);
lean_dec(v_unused_2693_);
v___x_2647_ = v_a_2637_;
v_isShared_2648_ = v_isSharedCheck_2692_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_cursor_2645_);
lean_dec(v_a_2637_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2692_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
uint8_t v_kind_2649_; uint8_t v___x_2650_; 
v_kind_2649_ = lean_ctor_get_uint8(v_val_2644_, sizeof(void*)*1);
v___x_2650_ = l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine(v_kind_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v_source_2652_; uint8_t v___x_2653_; 
lean_inc_ref(v_cursor_2645_);
v___x_2651_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_2636_, v_cursor_2645_);
v_source_2652_ = lean_ctor_get(v___x_2651_, 0);
v___x_2653_ = l_Lean_Markdown_HtmlBlockKind_endConditionMet(v_s_2636_, v_kind_2649_, v_source_2652_);
if (v___x_2653_ == 0)
{
uint8_t v___x_2654_; 
lean_inc_ref(v_cursor_2645_);
v___x_2654_ = l_Lean_Markdown_Cursor_isBlank(v_s_2636_, v_cursor_2645_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; lean_object* v___x_2657_; 
v___x_2655_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2655_);
v___x_2657_ = v___x_2647_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_cursor_2645_);
v___x_2657_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_2642_, v___x_2651_);
v___x_2659_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_2658_);
v___x_2660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
lean_ctor_set(v___x_2660_, 1, v___x_2657_);
return v___x_2660_;
}
}
else
{
lean_object* v___x_2662_; lean_object* v___x_2664_; 
v___x_2662_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2662_);
v___x_2664_ = v___x_2647_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_cursor_2645_);
v___x_2664_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_2642_, v___x_2651_);
v___x_2666_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_2636_, v___x_2665_);
v___x_2667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
lean_ctor_set(v___x_2667_, 1, v___x_2664_);
return v___x_2667_;
}
}
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2669_);
v___x_2671_ = v___x_2647_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_cursor_2645_);
v___x_2671_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2672_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_2642_, v___x_2651_);
v___x_2673_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_2636_, v___x_2672_);
v___x_2674_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
lean_ctor_set(v___x_2675_, 1, v___x_2671_);
return v___x_2675_;
}
}
}
else
{
uint8_t v___x_2677_; 
lean_inc_ref(v_cursor_2645_);
v___x_2677_ = l_Lean_Markdown_Cursor_isBlank(v_s_2636_, v_cursor_2645_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2678_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
lean_inc_ref(v_cursor_2645_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2678_);
v___x_2680_ = v___x_2647_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_cursor_2645_);
v___x_2680_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2681_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_2636_, v_cursor_2645_);
v___x_2682_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_2642_, v___x_2681_);
v___x_2683_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v___x_2680_);
return v___x_2684_;
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2686_ = lean_box(0);
v___x_2687_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_2636_, v_zipper_2642_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2687_);
v___x_2689_ = v___x_2647_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_cursor_2645_);
v___x_2689_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; 
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2686_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
return v___x_2690_;
}
}
}
}
}
else
{
v___y_2639_ = v_a_2637_;
goto v___jp_2638_;
}
}
else
{
v___y_2639_ = v_a_2637_;
goto v___jp_2638_;
}
v___jp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
lean_ctor_set(v___x_2641_, 1, v___y_2639_);
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeHtmlBlock___boxed(lean_object* v_s_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeHtmlBlock(v_s_2694_, v_a_2695_);
lean_dec_ref(v_s_2694_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentedCode(lean_object* v_s_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___y_2700_; lean_object* v_zipper_2703_; lean_object* v_openLeaf_x3f_2704_; 
v_zipper_2703_ = lean_ctor_get(v_a_2698_, 0);
v_openLeaf_x3f_2704_ = lean_ctor_get(v_zipper_2703_, 2);
if (lean_obj_tag(v_openLeaf_x3f_2704_) == 1)
{
lean_object* v_val_2705_; 
v_val_2705_ = lean_ctor_get(v_openLeaf_x3f_2704_, 0);
if (lean_obj_tag(v_val_2705_) == 2)
{
lean_object* v_cursor_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2750_; 
lean_inc_ref(v_zipper_2703_);
v_cursor_2706_ = lean_ctor_get(v_a_2698_, 1);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_a_2698_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; 
v_unused_2751_ = lean_ctor_get(v_a_2698_, 0);
lean_dec(v_unused_2751_);
v___x_2708_ = v_a_2698_;
v_isShared_2709_ = v_isSharedCheck_2750_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_cursor_2706_);
lean_dec(v_a_2698_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2750_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v_after_2711_; lean_object* v_indent_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2749_; 
lean_inc_ref(v_cursor_2706_);
v___x_2710_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2697_, v_cursor_2706_);
v_after_2711_ = lean_ctor_get(v___x_2710_, 0);
v_indent_2712_ = lean_ctor_get(v___x_2710_, 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2714_ = v___x_2710_;
v_isShared_2715_ = v_isSharedCheck_2749_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_indent_2712_);
lean_inc(v_after_2711_);
lean_dec(v___x_2710_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2749_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v_pos_2716_; lean_object* v_stop_2717_; uint8_t v___x_2718_; 
v_pos_2716_ = lean_ctor_get(v_after_2711_, 0);
lean_inc(v_pos_2716_);
v_stop_2717_ = lean_ctor_get(v_after_2711_, 1);
lean_inc(v_stop_2717_);
lean_dec_ref(v_after_2711_);
v___x_2718_ = lean_nat_dec_le(v_stop_2717_, v_pos_2716_);
lean_dec(v_pos_2716_);
lean_dec(v_stop_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = lean_unsigned_to_nat(4u);
v___x_2720_ = lean_nat_dec_le(v___x_2719_, v_indent_2712_);
lean_dec(v_indent_2712_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = lean_box(0);
v___x_2722_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_2697_, v_zipper_2703_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2722_);
v___x_2724_ = v___x_2708_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_cursor_2706_);
v___x_2724_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
lean_object* v___x_2726_; 
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 1, v___x_2724_);
lean_ctor_set(v___x_2714_, 0, v___x_2721_);
v___x_2726_ = v___x_2714_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2729_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
lean_inc_ref(v_cursor_2706_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2729_);
v___x_2731_ = v___x_2708_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_cursor_2706_);
v___x_2731_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2732_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_2697_, v_cursor_2706_);
v___x_2733_ = l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg(v_zipper_2703_, v___x_2732_);
v___x_2734_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_2733_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 1);
lean_ctor_set(v___x_2714_, 1, v___x_2731_);
lean_ctor_set(v___x_2714_, 0, v___x_2734_);
v___x_2736_ = v___x_2714_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v___x_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
lean_dec(v_indent_2712_);
v___x_2739_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
lean_inc_ref(v_cursor_2706_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2739_);
v___x_2741_ = v___x_2708_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_cursor_2706_);
v___x_2741_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2742_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_2697_, v_cursor_2706_);
v___x_2743_ = l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___redArg(v_zipper_2703_, v___x_2742_);
v___x_2744_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_2697_, v___x_2743_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 1);
lean_ctor_set(v___x_2714_, 1, v___x_2741_);
lean_ctor_set(v___x_2714_, 0, v___x_2744_);
v___x_2746_ = v___x_2714_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v___x_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
}
}
else
{
v___y_2700_ = v_a_2698_;
goto v___jp_2699_;
}
}
else
{
v___y_2700_ = v_a_2698_;
goto v___jp_2699_;
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_box(0);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
lean_ctor_set(v___x_2702_, 1, v___y_2700_);
return v___x_2702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentedCode___boxed(lean_object* v_s_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentedCode(v_s_2752_, v_a_2753_);
lean_dec_ref(v_s_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0(lean_object* v_s_2755_, lean_object* v_fst_2756_, lean_object* v_fst_2757_, lean_object* v_____r_2758_, lean_object* v_breakScanFailedAt_x3f_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2761_; 
lean_inc(v_fst_2756_);
v___x_2761_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f(v_s_2755_, v_fst_2756_);
if (lean_obj_tag(v___x_2761_) == 1)
{
lean_object* v_val_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_fst_2756_);
v_val_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2794_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_val_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2794_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_fst_2766_; lean_object* v_snd_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2793_; 
v_fst_2766_ = lean_ctor_get(v_val_2762_, 0);
v_snd_2767_ = lean_ctor_get(v_val_2762_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_val_2762_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2769_ = v_val_2762_;
v_isShared_2770_ = v_isSharedCheck_2793_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_snd_2767_);
lean_inc(v_fst_2766_);
lean_dec(v_val_2762_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2793_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v_zipper_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2791_; 
v_zipper_2771_ = lean_ctor_get(v___y_2760_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___y_2760_);
if (v_isSharedCheck_2791_ == 0)
{
lean_object* v_unused_2792_; 
v_unused_2792_ = lean_ctor_get(v___y_2760_, 1);
lean_dec(v_unused_2792_);
v___x_2773_ = v___y_2760_;
v_isShared_2774_ = v_isSharedCheck_2791_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_zipper_2771_);
lean_dec(v___y_2760_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2791_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = lean_mk_empty_array_with_capacity(v___x_2775_);
v___x_2777_ = lean_array_push(v___x_2776_, v_fst_2766_);
v___x_2778_ = l_Lean_Markdown_BlockZipper_openBlockquote(v_s_2755_, v_zipper_2771_, v___x_2777_);
lean_inc(v_snd_2767_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v_snd_2767_);
lean_ctor_set(v___x_2773_, 0, v___x_2778_);
v___x_2780_ = v___x_2773_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_snd_2767_);
v___x_2780_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2781_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2755_, v_snd_2767_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v_breakScanFailedAt_x3f_2759_);
lean_ctor_set(v___x_2769_, 0, v_fst_2757_);
v___x_2783_ = v___x_2769_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_fst_2757_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v_breakScanFailedAt_x3f_2759_);
v___x_2783_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2781_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2784_);
v___x_2786_ = v___x_2764_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2786_);
lean_ctor_set(v___x_2787_, 1, v___x_2780_);
return v___x_2787_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2795_; 
lean_dec(v___x_2761_);
lean_inc(v_fst_2756_);
v___x_2795_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseListMarker_x3f(v_s_2755_, v_fst_2756_);
if (lean_obj_tag(v___x_2795_) == 1)
{
lean_object* v_val_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2833_; 
v_val_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2833_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_val_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2833_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v_zipper_2800_; lean_object* v_openLeaf_x3f_2817_; 
v_zipper_2800_ = lean_ctor_get(v___y_2760_, 0);
v_openLeaf_x3f_2817_ = lean_ctor_get(v_zipper_2800_, 2);
if (lean_obj_tag(v_openLeaf_x3f_2817_) == 1)
{
lean_object* v_val_2818_; 
v_val_2818_ = lean_ctor_get(v_openLeaf_x3f_2817_, 0);
lean_inc(v_val_2818_);
if (lean_obj_tag(v_val_2818_) == 0)
{
lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2831_; 
v_isSharedCheck_2831_ = !lean_is_exclusive(v_val_2818_);
if (v_isSharedCheck_2831_ == 0)
{
lean_object* v_unused_2832_; 
v_unused_2832_ = lean_ctor_get(v_val_2818_, 0);
lean_dec(v_unused_2832_);
v___x_2820_ = v_val_2818_;
v_isShared_2821_ = v_isSharedCheck_2831_;
goto v_resetjp_2819_;
}
else
{
lean_dec(v_val_2818_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2831_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_after_2822_; lean_object* v_kind_2823_; uint8_t v___x_2824_; 
v_after_2822_ = lean_ctor_get(v_val_2796_, 1);
v_kind_2823_ = lean_ctor_get(v_val_2796_, 2);
lean_inc_ref(v_after_2822_);
v___x_2824_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_listMarkerInterruptsParagraph(v_s_2755_, v_after_2822_, v_kind_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2828_; 
lean_del_object(v___x_2798_);
lean_dec(v_val_2796_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_fst_2757_);
lean_ctor_set(v___x_2825_, 1, v_breakScanFailedAt_x3f_2759_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v_fst_2756_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2826_);
v___x_2828_ = v___x_2820_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___y_2760_);
return v___x_2829_;
}
}
else
{
lean_inc_ref(v_zipper_2800_);
lean_del_object(v___x_2820_);
lean_dec_ref(v___y_2760_);
lean_dec(v_fst_2757_);
lean_dec(v_fst_2756_);
goto v___jp_2801_;
}
}
}
else
{
lean_inc_ref(v_zipper_2800_);
lean_dec(v_val_2818_);
lean_dec_ref(v___y_2760_);
lean_dec(v_fst_2757_);
lean_dec(v_fst_2756_);
goto v___jp_2801_;
}
}
else
{
lean_inc_ref(v_zipper_2800_);
lean_dec_ref(v___y_2760_);
lean_dec(v_fst_2757_);
lean_dec(v_fst_2756_);
goto v___jp_2801_;
}
v___jp_2801_:
{
lean_object* v_marker_2802_; lean_object* v_after_2803_; lean_object* v_kind_2804_; lean_object* v_contentColumn_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v_marker_2802_ = lean_ctor_get(v_val_2796_, 0);
lean_inc_ref(v_marker_2802_);
v_after_2803_ = lean_ctor_get(v_val_2796_, 1);
lean_inc_ref_n(v_after_2803_, 2);
v_kind_2804_ = lean_ctor_get(v_val_2796_, 2);
lean_inc_ref(v_kind_2804_);
v_contentColumn_2805_ = lean_ctor_get(v_val_2796_, 3);
lean_inc(v_contentColumn_2805_);
lean_dec(v_val_2796_);
v___x_2806_ = 1;
v___x_2807_ = l_Lean_Markdown_BlockZipper_openItem(v_s_2755_, v_zipper_2800_, v_kind_2804_, v_marker_2802_, v_contentColumn_2805_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v_after_2803_);
v___x_2809_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2755_, v_after_2803_);
v___x_2810_ = lean_box(v___x_2806_);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2810_);
lean_ctor_set(v___x_2811_, 1, v_breakScanFailedAt_x3f_2759_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2809_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2812_);
v___x_2814_ = v___x_2798_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v___x_2808_);
return v___x_2815_;
}
}
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_dec(v___x_2795_);
v___x_2834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_fst_2757_);
lean_ctor_set(v___x_2834_, 1, v_breakScanFailedAt_x3f_2759_);
v___x_2835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2835_, 0, v_fst_2756_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v___y_2760_);
return v___x_2837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0___boxed(lean_object* v_s_2838_, lean_object* v_fst_2839_, lean_object* v_fst_2840_, lean_object* v_____r_2841_, lean_object* v_breakScanFailedAt_x3f_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0(v_s_2838_, v_fst_2839_, v_fst_2840_, v_____r_2841_, v_breakScanFailedAt_x3f_2842_, v___y_2843_);
lean_dec_ref(v_s_2838_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg(lean_object* v_s_2845_, lean_object* v_a_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___y_2849_; lean_object* v_snd_2873_; lean_object* v_fst_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2913_; 
v_snd_2873_ = lean_ctor_get(v_a_2846_, 1);
v_fst_2874_ = lean_ctor_get(v_a_2846_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_a_2846_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2876_ = v_a_2846_;
v_isShared_2877_ = v_isSharedCheck_2913_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_snd_2873_);
lean_inc(v_fst_2874_);
lean_dec(v_a_2846_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2913_;
goto v_resetjp_2875_;
}
v___jp_2848_:
{
if (lean_obj_tag(v___y_2849_) == 0)
{
lean_object* v_a_2850_; 
v_a_2850_ = lean_ctor_get(v___y_2849_, 0);
lean_inc(v_a_2850_);
if (lean_obj_tag(v_a_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2859_; 
v_a_2851_ = lean_ctor_get(v___y_2849_, 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___y_2849_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v___y_2849_, 0);
lean_dec(v_unused_2860_);
v___x_2853_ = v___y_2849_;
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___y_2849_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v_a_2855_; lean_object* v___x_2857_; 
v_a_2855_ = lean_ctor_get(v_a_2850_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v_a_2850_, 1);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v_a_2855_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2855_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_a_2851_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v_a_2862_; 
v_a_2861_ = lean_ctor_get(v___y_2849_, 1);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___y_2849_, 2);
v_a_2862_ = lean_ctor_get(v_a_2850_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v_a_2850_, 1);
v_a_2846_ = v_a_2862_;
v___y_2847_ = v_a_2861_;
goto _start;
}
}
else
{
lean_object* v_a_2864_; lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_a_2864_ = lean_ctor_get(v___y_2849_, 0);
v_a_2865_ = lean_ctor_get(v___y_2849_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___y_2849_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___y_2849_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_inc(v_a_2864_);
lean_dec(v___y_2849_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2864_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
v_resetjp_2875_:
{
lean_object* v_fst_2878_; lean_object* v_snd_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2912_; 
v_fst_2878_ = lean_ctor_get(v_snd_2873_, 0);
v_snd_2879_ = lean_ctor_get(v_snd_2873_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_snd_2873_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2881_ = v_snd_2873_;
v_isShared_2882_ = v_isSharedCheck_2912_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_snd_2879_);
lean_inc(v_fst_2878_);
lean_dec(v_snd_2873_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2912_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
if (lean_obj_tag(v_snd_2879_) == 0)
{
goto v___jp_2883_;
}
else
{
lean_object* v_after_2904_; lean_object* v_val_2905_; lean_object* v_pos_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v_after_2904_ = lean_ctor_get(v_fst_2874_, 0);
v_val_2905_ = lean_ctor_get(v_snd_2879_, 0);
v_pos_2906_ = lean_ctor_get(v_after_2904_, 0);
v___x_2907_ = lean_unsigned_to_nat(1u);
v___x_2908_ = lean_nat_add(v_pos_2906_, v___x_2907_);
v___x_2909_ = lean_nat_dec_le(v___x_2908_, v_val_2905_);
lean_dec(v___x_2908_);
if (v___x_2909_ == 0)
{
goto v___jp_2883_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
lean_del_object(v___x_2881_);
lean_del_object(v___x_2876_);
v___x_2910_ = lean_box(0);
v___x_2911_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0(v_s_2845_, v_fst_2874_, v_fst_2878_, v___x_2910_, v_snd_2879_, v___y_2847_);
v___y_2849_ = v___x_2911_;
goto v___jp_2848_;
}
}
v___jp_2883_:
{
lean_object* v___x_2884_; 
lean_inc(v_fst_2874_);
v___x_2884_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_checkThematicBreak(v_s_2845_, v_fst_2874_);
switch(lean_obj_tag(v___x_2884_))
{
case 0:
{
lean_object* v___x_2886_; 
if (v_isShared_2882_ == 0)
{
v___x_2886_ = v___x_2881_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_fst_2878_);
lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_snd_2879_);
v___x_2886_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 1, v___x_2886_);
v___x_2888_ = v___x_2876_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_fst_2874_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___y_2847_);
return v___x_2889_;
}
}
}
case 1:
{
lean_object* v_pos_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2901_; 
lean_del_object(v___x_2881_);
lean_dec(v_snd_2879_);
lean_del_object(v___x_2876_);
v_pos_2892_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2894_ = v___x_2884_;
v_isShared_2895_ = v_isSharedCheck_2901_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_pos_2892_);
lean_dec(v___x_2884_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2901_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_pos_2892_);
v___x_2897_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_box(0);
v___x_2899_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0(v_s_2845_, v_fst_2874_, v_fst_2878_, v___x_2898_, v___x_2897_, v___y_2847_);
v___y_2849_ = v___x_2899_;
goto v___jp_2848_;
}
}
}
default: 
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
lean_del_object(v___x_2881_);
lean_del_object(v___x_2876_);
v___x_2902_ = lean_box(0);
v___x_2903_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___lam__0(v_s_2845_, v_fst_2874_, v_fst_2878_, v___x_2902_, v_snd_2879_, v___y_2847_);
v___y_2849_ = v___x_2903_;
goto v___jp_2848_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg___boxed(lean_object* v_s_2914_, lean_object* v_a_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg(v_s_2914_, v_a_2915_, v___y_2916_);
lean_dec_ref(v_s_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes(lean_object* v_s_2922_, lean_object* v_line_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes___closed__0));
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v_line_2923_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___x_2927_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg(v_s_2922_, v___x_2926_, v_a_2924_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v_snd_2929_; lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2947_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
v_snd_2929_ = lean_ctor_get(v_a_2928_, 1);
lean_inc(v_snd_2929_);
v_a_2930_ = lean_ctor_get(v___x_2927_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; 
v_unused_2948_ = lean_ctor_get(v___x_2927_, 0);
lean_dec(v_unused_2948_);
v___x_2932_ = v___x_2927_;
v_isShared_2933_ = v_isSharedCheck_2947_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2927_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2947_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v_fst_2934_; lean_object* v_fst_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2945_; 
v_fst_2934_ = lean_ctor_get(v_a_2928_, 0);
lean_inc(v_fst_2934_);
lean_dec(v_a_2928_);
v_fst_2935_ = lean_ctor_get(v_snd_2929_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v_snd_2929_);
if (v_isSharedCheck_2945_ == 0)
{
lean_object* v_unused_2946_; 
v_unused_2946_ = lean_ctor_get(v_snd_2929_, 1);
lean_dec(v_unused_2946_);
v___x_2937_ = v_snd_2929_;
v_isShared_2938_ = v_isSharedCheck_2945_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_fst_2935_);
lean_dec(v_snd_2929_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2945_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v_fst_2934_);
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_fst_2935_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_fst_2934_);
v___x_2940_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2942_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2940_);
v___x_2942_ = v___x_2932_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_a_2930_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2949_ = lean_ctor_get(v___x_2927_, 0);
v_a_2950_ = lean_ctor_get(v___x_2927_, 1);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2927_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_inc(v_a_2949_);
lean_dec(v___x_2927_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2949_);
lean_ctor_set(v_reuseFailAlloc_2956_, 1, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes___boxed(lean_object* v_s_2958_, lean_object* v_line_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes(v_s_2958_, v_line_2959_, v_a_2960_);
lean_dec_ref(v_s_2958_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0(lean_object* v_s_2962_, lean_object* v_inst_2963_, lean_object* v_a_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___redArg(v_s_2962_, v_a_2964_, v___y_2965_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0___boxed(lean_object* v_s_2967_, lean_object* v_inst_2968_, lean_object* v_a_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes_spec__0(v_s_2967_, v_inst_2968_, v_a_2969_, v___y_2970_);
lean_dec_ref(v_s_2967_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishThematicBreak(lean_object* v_s_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_zipper_2974_; lean_object* v_cursor_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2999_; 
v_zipper_2974_ = lean_ctor_get(v_a_2973_, 0);
v_cursor_2975_ = lean_ctor_get(v_a_2973_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_a_2973_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2977_ = v_a_2973_;
v_isShared_2978_ = v_isSharedCheck_2999_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_cursor_2975_);
lean_inc(v_zipper_2974_);
lean_dec(v_a_2973_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2999_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v_after_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2997_; 
lean_inc_ref(v_cursor_2975_);
v___x_2979_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_2972_, v_cursor_2975_);
v_after_2980_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v___x_2979_, 1);
lean_dec(v_unused_2998_);
v___x_2982_ = v___x_2979_;
v_isShared_2983_ = v_isSharedCheck_2997_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_after_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2997_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v_pos_2984_; lean_object* v_stop_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v_pos_2984_ = lean_ctor_get(v_after_2980_, 0);
lean_inc(v_pos_2984_);
v_stop_2985_ = lean_ctor_get(v_after_2980_, 1);
lean_inc(v_stop_2985_);
lean_dec_ref(v_after_2980_);
v___x_2986_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_2984_, v_stop_2985_);
v___x_2987_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(v_s_2972_, v___x_2986_);
v___x_2988_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2988_);
v___x_2990_ = v___x_2977_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_cursor_2975_);
v___x_2990_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2991_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2987_);
v___x_2992_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_2972_, v_zipper_2974_, v___x_2991_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 1);
lean_ctor_set(v___x_2982_, 1, v___x_2990_);
lean_ctor_set(v___x_2982_, 0, v___x_2992_);
v___x_2994_ = v___x_2982_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2990_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishThematicBreak___boxed(lean_object* v_s_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishThematicBreak(v_s_3000_, v_a_3001_);
lean_dec_ref(v_s_3000_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(uint8_t v_openedListItemThisLine_3003_, lean_object* v_s_3004_, lean_object* v_____r_3005_, lean_object* v_z_3006_){
_start:
{
if (v_openedListItemThisLine_3003_ == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_3004_, v_z_3006_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v_z_3006_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0___boxed(lean_object* v_openedListItemThisLine_3009_, lean_object* v_s_3010_, lean_object* v_____r_3011_, lean_object* v_z_3012_){
_start:
{
uint8_t v_openedListItemThisLine_boxed_3013_; lean_object* v_res_3014_; 
v_openedListItemThisLine_boxed_3013_ = lean_unbox(v_openedListItemThisLine_3009_);
v_res_3014_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(v_openedListItemThisLine_boxed_3013_, v_s_3010_, v_____r_3011_, v_z_3012_);
lean_dec_ref(v_s_3010_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine(lean_object* v_s_3015_, uint8_t v_openedListItemThisLine_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_zipper_3018_; lean_object* v_cursor_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3055_; 
v_zipper_3018_ = lean_ctor_get(v_a_3017_, 0);
v_cursor_3019_ = lean_ctor_get(v_a_3017_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_a_3017_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3021_ = v_a_3017_;
v_isShared_3022_ = v_isSharedCheck_3055_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_cursor_3019_);
lean_inc(v_zipper_3018_);
lean_dec(v_a_3017_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3055_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_cursor_3019_);
v___x_3025_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v_z_3026_; 
v_z_3026_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_3015_, v_zipper_3018_);
if (v_openedListItemThisLine_3016_ == 0)
{
lean_object* v_spine_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v_spine_3031_ = lean_ctor_get(v_z_3026_, 1);
v___x_3032_ = lean_array_get_size(v_spine_3031_);
v___x_3033_ = lean_unsigned_to_nat(1u);
v___x_3034_ = lean_nat_sub(v___x_3032_, v___x_3033_);
v___x_3035_ = lean_nat_dec_lt(v___x_3034_, v___x_3032_);
if (v___x_3035_ == 0)
{
lean_dec(v___x_3034_);
goto v___jp_3027_;
}
else
{
lean_object* v___x_3036_; lean_object* v_container_3037_; 
v___x_3036_ = lean_array_fget(v_spine_3031_, v___x_3034_);
lean_dec(v___x_3034_);
v_container_3037_ = lean_ctor_get(v___x_3036_, 0);
if (lean_obj_tag(v_container_3037_) == 1)
{
lean_object* v_children_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3049_; 
v_children_3038_ = lean_ctor_get(v___x_3036_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; 
v_unused_3050_ = lean_ctor_get(v___x_3036_, 0);
lean_dec(v_unused_3050_);
v___x_3040_ = v___x_3036_;
v_isShared_3041_ = v_isSharedCheck_3049_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_children_3038_);
lean_dec(v___x_3036_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3049_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
uint8_t v___x_3042_; 
v___x_3042_ = l_Lean_Markdown_Children_isEmpty___redArg(v_children_3038_);
lean_dec_ref(v_children_3038_);
if (v___x_3042_ == 0)
{
lean_del_object(v___x_3040_);
goto v___jp_3027_;
}
else
{
lean_object* v_z_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v_z_3043_ = l_Lean_Markdown_BlockZipper_closeContainer(v_s_3015_, v_z_3026_);
v___x_3044_ = lean_box(0);
v___x_3045_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(v_openedListItemThisLine_3016_, v_s_3015_, v___x_3044_, v_z_3043_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set_tag(v___x_3040_, 1);
lean_ctor_set(v___x_3040_, 1, v___x_3025_);
lean_ctor_set(v___x_3040_, 0, v___x_3045_);
v___x_3047_ = v___x_3040_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3025_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_dec(v___x_3036_);
goto v___jp_3027_;
}
}
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = lean_box(0);
v___x_3052_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(v_openedListItemThisLine_3016_, v_s_3015_, v___x_3051_, v_z_3026_);
v___x_3053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v___x_3025_);
return v___x_3053_;
}
v___jp_3027_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3028_ = lean_box(0);
v___x_3029_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(v_openedListItemThisLine_3016_, v_s_3015_, v___x_3028_, v_z_3026_);
v___x_3030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
lean_ctor_set(v___x_3030_, 1, v___x_3025_);
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___boxed(lean_object* v_s_3056_, lean_object* v_openedListItemThisLine_3057_, lean_object* v_a_3058_){
_start:
{
uint8_t v_openedListItemThisLine_boxed_3059_; lean_object* v_res_3060_; 
v_openedListItemThisLine_boxed_3059_ = lean_unbox(v_openedListItemThisLine_3057_);
v_res_3060_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine(v_s_3056_, v_openedListItemThisLine_boxed_3059_, v_a_3058_);
lean_dec_ref(v_s_3056_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryAtxHeading(lean_object* v_s_3061_, lean_object* v_line_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f(v_s_3061_, v_line_3062_);
if (lean_obj_tag(v___x_3064_) == 1)
{
lean_object* v_val_3065_; lean_object* v_level_3066_; lean_object* v_hashes_3067_; lean_object* v_content_3068_; lean_object* v_closeHashes_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3090_; 
v_val_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_val_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v_level_3066_ = lean_ctor_get(v_val_3065_, 0);
v_hashes_3067_ = lean_ctor_get(v_val_3065_, 1);
v_content_3068_ = lean_ctor_get(v_val_3065_, 2);
v_closeHashes_3069_ = lean_ctor_get(v_val_3065_, 3);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_val_3065_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3071_ = v_val_3065_;
v_isShared_3072_ = v_isSharedCheck_3090_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_closeHashes_3069_);
lean_inc(v_content_3068_);
lean_inc(v_hashes_3067_);
lean_inc(v_level_3066_);
lean_dec(v_val_3065_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3090_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_zipper_3073_; lean_object* v_cursor_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3089_; 
v_zipper_3073_ = lean_ctor_get(v_a_3063_, 0);
v_cursor_3074_ = lean_ctor_get(v_a_3063_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_a_3063_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3076_ = v_a_3063_;
v_isShared_3077_ = v_isSharedCheck_3089_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_cursor_3074_);
lean_inc(v_zipper_3073_);
lean_dec(v_a_3063_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3089_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v_content_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3078_ = l_Lean_Markdown_Lines_singleton___redArg(v_content_3068_);
v_content_3079_ = l_Lean_Markdown_InlineSource_ofLines(v_s_3061_, v___x_3078_);
v___x_3080_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3077_ == 0)
{
lean_ctor_set(v___x_3076_, 0, v___x_3080_);
v___x_3082_ = v___x_3076_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_cursor_3074_);
v___x_3082_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3084_; 
if (v_isShared_3072_ == 0)
{
lean_ctor_set_tag(v___x_3071_, 1);
lean_ctor_set(v___x_3071_, 2, v_content_3079_);
v___x_3084_ = v___x_3071_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_level_3066_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_hashes_3067_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_content_3079_);
lean_ctor_set(v_reuseFailAlloc_3087_, 3, v_closeHashes_3069_);
v___x_3084_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3061_, v_zipper_3073_, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
lean_ctor_set(v___x_3086_, 1, v___x_3082_);
return v___x_3086_;
}
}
}
}
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_dec(v___x_3064_);
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v_a_3063_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryAtxHeading___boxed(lean_object* v_s_3093_, lean_object* v_line_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryAtxHeading(v_s_3093_, v_line_3094_, v_a_3095_);
lean_dec_ref(v_s_3093_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener(lean_object* v_s_3099_, lean_object* v_line_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f(v_s_3099_, v_line_3100_);
if (lean_obj_tag(v___x_3102_) == 1)
{
lean_object* v_val_3103_; lean_object* v_fst_3104_; lean_object* v_snd_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3125_; 
v_val_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_val_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v_fst_3104_ = lean_ctor_get(v_val_3103_, 0);
v_snd_3105_ = lean_ctor_get(v_val_3103_, 1);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_val_3103_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3107_ = v_val_3103_;
v_isShared_3108_ = v_isSharedCheck_3125_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_snd_3105_);
lean_inc(v_fst_3104_);
lean_dec(v_val_3103_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3125_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v_zipper_3109_; lean_object* v_cursor_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3124_; 
v_zipper_3109_ = lean_ctor_get(v_a_3101_, 0);
v_cursor_3110_ = lean_ctor_get(v_a_3101_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_a_3101_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3112_ = v_a_3101_;
v_isShared_3113_ = v_isSharedCheck_3124_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_cursor_3110_);
lean_inc(v_zipper_3109_);
lean_dec(v_a_3101_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3124_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3114_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_cursor_3110_);
v___x_3116_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3117_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0));
v___x_3118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3118_, 0, v_fst_3104_);
lean_ctor_set(v___x_3118_, 1, v_snd_3105_);
lean_ctor_set(v___x_3118_, 2, v___x_3117_);
v___x_3119_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3099_, v_zipper_3109_, v___x_3118_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set_tag(v___x_3107_, 1);
lean_ctor_set(v___x_3107_, 1, v___x_3116_);
lean_ctor_set(v___x_3107_, 0, v___x_3119_);
v___x_3121_ = v___x_3107_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3116_);
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
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v___x_3102_);
v___x_3126_ = lean_box(0);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v_a_3101_);
return v___x_3127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___boxed(lean_object* v_s_3128_, lean_object* v_line_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener(v_s_3128_, v_line_3129_, v_a_3130_);
lean_dec_ref(v_s_3128_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryHtmlBlockOpener(lean_object* v_s_3132_, lean_object* v_line_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f(v_s_3132_, v_line_3133_);
if (lean_obj_tag(v___x_3135_) == 1)
{
lean_object* v_val_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3189_; 
v_val_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3189_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_val_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3189_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v_zipper_3140_; lean_object* v_cursor_3141_; lean_object* v___y_3143_; lean_object* v_openLeaf_x3f_3183_; 
v_zipper_3140_ = lean_ctor_get(v_a_3134_, 0);
v_cursor_3141_ = lean_ctor_get(v_a_3134_, 1);
v_openLeaf_x3f_3183_ = lean_ctor_get(v_zipper_3140_, 2);
if (lean_obj_tag(v_openLeaf_x3f_3183_) == 1)
{
lean_object* v_val_3184_; 
v_val_3184_ = lean_ctor_get(v_openLeaf_x3f_3183_, 0);
if (lean_obj_tag(v_val_3184_) == 0)
{
uint8_t v___x_3185_; uint8_t v___x_3186_; 
v___x_3185_ = lean_unbox(v_val_3136_);
v___x_3186_ = l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(v___x_3185_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
lean_del_object(v___x_3138_);
lean_dec(v_val_3136_);
v___x_3187_ = lean_box(0);
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
lean_ctor_set(v___x_3188_, 1, v_a_3134_);
return v___x_3188_;
}
else
{
lean_inc_ref(v_cursor_3141_);
v___y_3143_ = v_a_3134_;
goto v___jp_3142_;
}
}
else
{
lean_inc_ref(v_cursor_3141_);
v___y_3143_ = v_a_3134_;
goto v___jp_3142_;
}
}
else
{
lean_inc_ref(v_cursor_3141_);
v___y_3143_ = v_a_3134_;
goto v___jp_3142_;
}
v___jp_3142_:
{
lean_object* v___x_3144_; lean_object* v_source_3145_; uint8_t v___x_3146_; uint8_t v___x_3147_; 
v___x_3144_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_3132_, v_cursor_3141_);
v_source_3145_ = lean_ctor_get(v___x_3144_, 0);
v___x_3146_ = lean_unbox(v_val_3136_);
v___x_3147_ = l_Lean_Markdown_HtmlBlockKind_endConditionMet(v_s_3132_, v___x_3146_, v_source_3145_);
if (v___x_3147_ == 0)
{
lean_object* v_zipper_3148_; lean_object* v_cursor_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3164_; 
lean_del_object(v___x_3138_);
v_zipper_3148_ = lean_ctor_get(v___y_3143_, 0);
v_cursor_3149_ = lean_ctor_get(v___y_3143_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___y_3143_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3151_ = v___y_3143_;
v_isShared_3152_ = v_isSharedCheck_3164_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_cursor_3149_);
lean_inc(v_zipper_3148_);
lean_dec(v___y_3143_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3164_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3153_);
v___x_3155_ = v___x_3151_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3153_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_cursor_3149_);
v___x_3155_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3157_ = lean_mk_empty_array_with_capacity(v___x_3156_);
v___x_3158_ = lean_array_push(v___x_3157_, v___x_3144_);
v___x_3159_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
v___x_3160_ = lean_unbox(v_val_3136_);
lean_dec(v_val_3136_);
lean_ctor_set_uint8(v___x_3159_, sizeof(void*)*1, v___x_3160_);
v___x_3161_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3132_, v_zipper_3148_, v___x_3159_);
v___x_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
lean_ctor_set(v___x_3162_, 1, v___x_3155_);
return v___x_3162_;
}
}
}
else
{
lean_object* v_zipper_3165_; lean_object* v_cursor_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3182_; 
lean_dec(v_val_3136_);
v_zipper_3165_ = lean_ctor_get(v___y_3143_, 0);
v_cursor_3166_ = lean_ctor_get(v___y_3143_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___y_3143_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3168_ = v___y_3143_;
v_isShared_3169_ = v_isSharedCheck_3182_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_cursor_3166_);
lean_inc(v_zipper_3165_);
lean_dec(v___y_3143_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3182_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 0, v___x_3170_);
v___x_3172_ = v___x_3168_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_cursor_3166_);
v___x_3172_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3173_ = lean_unsigned_to_nat(1u);
v___x_3174_ = lean_mk_empty_array_with_capacity(v___x_3173_);
v___x_3175_ = lean_array_push(v___x_3174_, v___x_3144_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set_tag(v___x_3138_, 5);
lean_ctor_set(v___x_3138_, 0, v___x_3175_);
v___x_3177_ = v___x_3138_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3132_, v_zipper_3165_, v___x_3177_);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v___x_3172_);
return v___x_3179_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec(v___x_3135_);
v___x_3190_ = lean_box(0);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v_a_3134_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryHtmlBlockOpener___boxed(lean_object* v_s_3192_, lean_object* v_line_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryHtmlBlockOpener(v_s_3192_, v_line_3193_, v_a_3194_);
lean_dec_ref(v_s_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryIndentedCodeOpener(lean_object* v_s_3196_, lean_object* v_line_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_indent_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3230_; 
v_indent_3202_ = lean_ctor_get(v_line_3197_, 1);
v_isSharedCheck_3230_ = !lean_is_exclusive(v_line_3197_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v_line_3197_, 0);
lean_dec(v_unused_3231_);
v___x_3204_ = v_line_3197_;
v_isShared_3205_ = v_isSharedCheck_3230_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_indent_3202_);
lean_dec(v_line_3197_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3230_;
goto v_resetjp_3203_;
}
v___jp_3199_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v_a_3198_);
return v___x_3201_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; uint8_t v___x_3207_; 
v___x_3206_ = lean_unsigned_to_nat(4u);
v___x_3207_ = lean_nat_dec_le(v___x_3206_, v_indent_3202_);
lean_dec(v_indent_3202_);
if (v___x_3207_ == 0)
{
lean_del_object(v___x_3204_);
goto v___jp_3199_;
}
else
{
lean_object* v_zipper_3208_; lean_object* v_openLeaf_x3f_3209_; 
v_zipper_3208_ = lean_ctor_get(v_a_3198_, 0);
v_openLeaf_x3f_3209_ = lean_ctor_get(v_zipper_3208_, 2);
if (lean_obj_tag(v_openLeaf_x3f_3209_) == 0)
{
lean_object* v_cursor_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3228_; 
lean_inc_ref(v_zipper_3208_);
v_cursor_3210_ = lean_ctor_get(v_a_3198_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_a_3198_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v_a_3198_, 0);
lean_dec(v_unused_3229_);
v___x_3212_ = v_a_3198_;
v_isShared_3213_ = v_isSharedCheck_3228_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_cursor_3210_);
lean_dec(v_a_3198_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3228_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3214_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
lean_inc_ref(v_cursor_3210_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3214_);
v___x_3216_ = v___x_3212_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_cursor_3210_);
v___x_3216_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3217_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_3196_, v_cursor_3210_);
v___x_3218_ = lean_unsigned_to_nat(1u);
v___x_3219_ = lean_mk_empty_array_with_capacity(v___x_3218_);
v___x_3220_ = lean_array_push(v___x_3219_, v___x_3217_);
v___x_3221_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0));
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 2);
lean_ctor_set(v___x_3204_, 1, v___x_3221_);
lean_ctor_set(v___x_3204_, 0, v___x_3220_);
v___x_3223_ = v___x_3204_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3196_, v_zipper_3208_, v___x_3223_);
v___x_3225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3216_);
return v___x_3225_;
}
}
}
}
else
{
lean_del_object(v___x_3204_);
goto v___jp_3199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryIndentedCodeOpener___boxed(lean_object* v_s_3232_, lean_object* v_line_3233_, lean_object* v_a_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryIndentedCodeOpener(v_s_3232_, v_line_3233_, v_a_3234_);
lean_dec_ref(v_s_3232_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_emitParagraph(lean_object* v_s_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_cursor_3238_; lean_object* v_zipper_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3263_; 
v_cursor_3238_ = lean_ctor_get(v_a_3237_, 1);
v_zipper_3239_ = lean_ctor_get(v_a_3237_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_a_3237_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3241_ = v_a_3237_;
v_isShared_3242_ = v_isSharedCheck_3263_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_cursor_3238_);
lean_inc(v_zipper_3239_);
lean_dec(v_a_3237_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3263_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v_pos_3243_; lean_object* v_stop_3244_; lean_object* v_openLeaf_x3f_3245_; lean_object* v___x_3246_; lean_object* v_zipper_3248_; lean_object* v_cursor_3249_; 
v_pos_3243_ = lean_ctor_get(v_cursor_3238_, 0);
v_stop_3244_ = lean_ctor_get(v_cursor_3238_, 1);
v_openLeaf_x3f_3245_ = lean_ctor_get(v_zipper_3239_, 2);
lean_inc(v_stop_3244_);
lean_inc(v_pos_3243_);
v___x_3246_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_3243_, v_stop_3244_);
if (lean_obj_tag(v_openLeaf_x3f_3245_) == 1)
{
lean_object* v_val_3258_; 
v_val_3258_ = lean_ctor_get(v_openLeaf_x3f_3245_, 0);
if (lean_obj_tag(v_val_3258_) == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_del_object(v___x_3241_);
v___x_3259_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v_cursor_3238_);
v___x_3261_ = l_Lean_Markdown_BlockZipper_extendParagraph___redArg(v_zipper_3239_, v___x_3246_);
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v___x_3260_);
return v___x_3262_;
}
else
{
v_zipper_3248_ = v_zipper_3239_;
v_cursor_3249_ = v_cursor_3238_;
goto v___jp_3247_;
}
}
else
{
v_zipper_3248_ = v_zipper_3239_;
v_cursor_3249_ = v_cursor_3238_;
goto v___jp_3247_;
}
v___jp_3247_:
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3250_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v_cursor_3249_);
lean_ctor_set(v___x_3241_, 0, v___x_3250_);
v___x_3252_ = v___x_3241_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_cursor_3249_);
v___x_3252_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v___x_3253_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_3246_);
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3253_);
v___x_3255_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3236_, v_zipper_3248_, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v___x_3252_);
return v___x_3256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_emitParagraph___boxed(lean_object* v_s_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_emitParagraph(v_s_3264_, v_a_3265_);
lean_dec_ref(v_s_3264_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openLeafBlock(lean_object* v_s_3267_, uint8_t v_openedListItemThisLine_3268_, lean_object* v_line_3269_, lean_object* v_a_3270_){
_start:
{
lean_object* v___y_3272_; lean_object* v_zipper_3273_; lean_object* v_cursor_3274_; lean_object* v_zipper_3282_; lean_object* v_cursor_3283_; lean_object* v___y_3294_; lean_object* v_after_3350_; lean_object* v_indent_3351_; lean_object* v_pos_3352_; lean_object* v_stop_3353_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_after_3350_ = lean_ctor_get(v_line_3269_, 0);
v_indent_3351_ = lean_ctor_get(v_line_3269_, 1);
v_pos_3352_ = lean_ctor_get(v_after_3350_, 0);
v_stop_3353_ = lean_ctor_get(v_after_3350_, 1);
v___x_3395_ = lean_unsigned_to_nat(1u);
v___x_3396_ = lean_nat_add(v_pos_3352_, v___x_3395_);
v___x_3397_ = lean_nat_dec_le(v___x_3396_, v_stop_3353_);
lean_dec(v___x_3396_);
if (v___x_3397_ == 0)
{
lean_dec_ref(v_line_3269_);
goto v___jp_3360_;
}
else
{
lean_object* v___x_3398_; 
v___x_3398_ = l_String_Slice_Pos_get_x3f(v_s_3267_, v_pos_3352_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_dec_ref(v_line_3269_);
goto v___jp_3360_;
}
else
{
lean_object* v_val_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_val_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_val_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v___x_3400_ = lean_unsigned_to_nat(4u);
v___x_3401_ = lean_nat_dec_le(v___x_3400_, v_indent_3351_);
if (v___x_3401_ == 0)
{
uint32_t v___x_3402_; uint32_t v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = 35;
v___x_3403_ = lean_unbox_uint32(v_val_3399_);
v___x_3404_ = lean_uint32_dec_eq(v___x_3403_, v___x_3402_);
if (v___x_3404_ == 0)
{
uint32_t v___x_3405_; uint32_t v___x_3406_; uint8_t v___x_3407_; 
v___x_3405_ = 96;
v___x_3406_ = lean_unbox_uint32(v_val_3399_);
v___x_3407_ = lean_uint32_dec_eq(v___x_3406_, v___x_3405_);
if (v___x_3407_ == 0)
{
uint32_t v___x_3408_; uint32_t v___x_3409_; uint8_t v___x_3410_; 
v___x_3408_ = 126;
v___x_3409_ = lean_unbox_uint32(v_val_3399_);
v___x_3410_ = lean_uint32_dec_eq(v___x_3409_, v___x_3408_);
if (v___x_3410_ == 0)
{
uint32_t v___x_3411_; uint32_t v___x_3412_; uint8_t v___x_3413_; 
v___x_3411_ = 60;
v___x_3412_ = lean_unbox_uint32(v_val_3399_);
v___x_3413_ = lean_uint32_dec_eq(v___x_3412_, v___x_3411_);
if (v___x_3413_ == 0)
{
uint32_t v___x_3414_; uint32_t v___x_3415_; uint8_t v___x_3416_; 
v___x_3414_ = 42;
v___x_3415_ = lean_unbox_uint32(v_val_3399_);
v___x_3416_ = lean_uint32_dec_eq(v___x_3415_, v___x_3414_);
if (v___x_3416_ == 0)
{
uint32_t v___x_3417_; uint32_t v___x_3418_; uint8_t v___x_3419_; 
v___x_3417_ = 45;
v___x_3418_ = lean_unbox_uint32(v_val_3399_);
v___x_3419_ = lean_uint32_dec_eq(v___x_3418_, v___x_3417_);
if (v___x_3419_ == 0)
{
uint32_t v___x_3420_; uint32_t v___x_3421_; uint8_t v___x_3422_; 
v___x_3420_ = 95;
v___x_3421_ = lean_unbox_uint32(v_val_3399_);
lean_dec(v_val_3399_);
v___x_3422_ = lean_uint32_dec_eq(v___x_3421_, v___x_3420_);
if (v___x_3422_ == 0)
{
lean_dec_ref(v_line_3269_);
v___y_3294_ = v_a_3270_;
goto v___jp_3293_;
}
else
{
goto v___jp_3322_;
}
}
else
{
lean_dec(v_val_3399_);
goto v___jp_3322_;
}
}
else
{
lean_dec(v_val_3399_);
goto v___jp_3322_;
}
}
else
{
lean_object* v___x_3423_; 
lean_dec(v_val_3399_);
v___x_3423_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f(v_s_3267_, v_line_3269_);
if (lean_obj_tag(v___x_3423_) == 1)
{
lean_object* v_val_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3473_; 
v_val_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3473_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_val_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3473_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_zipper_3428_; lean_object* v_cursor_3429_; lean_object* v___y_3431_; lean_object* v_openLeaf_x3f_3469_; 
v_zipper_3428_ = lean_ctor_get(v_a_3270_, 0);
v_cursor_3429_ = lean_ctor_get(v_a_3270_, 1);
lean_inc_ref(v_cursor_3429_);
v_openLeaf_x3f_3469_ = lean_ctor_get(v_zipper_3428_, 2);
if (lean_obj_tag(v_openLeaf_x3f_3469_) == 1)
{
lean_object* v_val_3470_; 
v_val_3470_ = lean_ctor_get(v_openLeaf_x3f_3469_, 0);
if (lean_obj_tag(v_val_3470_) == 0)
{
uint8_t v___x_3471_; uint8_t v___x_3472_; 
v___x_3471_ = lean_unbox(v_val_3424_);
v___x_3472_ = l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(v___x_3471_);
if (v___x_3472_ == 0)
{
lean_inc_ref(v_zipper_3428_);
lean_del_object(v___x_3426_);
lean_dec(v_val_3424_);
lean_dec_ref(v_a_3270_);
v_zipper_3282_ = v_zipper_3428_;
v_cursor_3283_ = v_cursor_3429_;
goto v___jp_3281_;
}
else
{
v___y_3431_ = v_a_3270_;
goto v___jp_3430_;
}
}
else
{
v___y_3431_ = v_a_3270_;
goto v___jp_3430_;
}
}
else
{
v___y_3431_ = v_a_3270_;
goto v___jp_3430_;
}
v___jp_3430_:
{
lean_object* v___x_3432_; lean_object* v_source_3433_; uint8_t v___x_3434_; uint8_t v___x_3435_; 
v___x_3432_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_3267_, v_cursor_3429_);
v_source_3433_ = lean_ctor_get(v___x_3432_, 0);
v___x_3434_ = lean_unbox(v_val_3424_);
v___x_3435_ = l_Lean_Markdown_HtmlBlockKind_endConditionMet(v_s_3267_, v___x_3434_, v_source_3433_);
if (v___x_3435_ == 0)
{
lean_object* v_zipper_3436_; lean_object* v_cursor_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3451_; 
lean_del_object(v___x_3426_);
v_zipper_3436_ = lean_ctor_get(v___y_3431_, 0);
v_cursor_3437_ = lean_ctor_get(v___y_3431_, 1);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___y_3431_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3439_ = v___y_3431_;
v_isShared_3440_ = v_isSharedCheck_3451_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_cursor_3437_);
lean_inc(v_zipper_3436_);
lean_dec(v___y_3431_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3451_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3441_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3441_);
v___x_3443_ = v___x_3439_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v_cursor_3437_);
v___x_3443_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3444_ = lean_mk_empty_array_with_capacity(v___x_3395_);
v___x_3445_ = lean_array_push(v___x_3444_, v___x_3432_);
v___x_3446_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
v___x_3447_ = lean_unbox(v_val_3424_);
lean_dec(v_val_3424_);
lean_ctor_set_uint8(v___x_3446_, sizeof(void*)*1, v___x_3447_);
v___x_3448_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3267_, v_zipper_3436_, v___x_3446_);
v___x_3449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
lean_ctor_set(v___x_3449_, 1, v___x_3443_);
return v___x_3449_;
}
}
}
else
{
lean_object* v_zipper_3452_; lean_object* v_cursor_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3468_; 
lean_dec(v_val_3424_);
v_zipper_3452_ = lean_ctor_get(v___y_3431_, 0);
v_cursor_3453_ = lean_ctor_get(v___y_3431_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___y_3431_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3455_ = v___y_3431_;
v_isShared_3456_ = v_isSharedCheck_3468_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_cursor_3453_);
lean_inc(v_zipper_3452_);
lean_dec(v___y_3431_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3468_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3457_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3459_ = v___x_3455_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v_cursor_3453_);
v___x_3459_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3460_ = lean_mk_empty_array_with_capacity(v___x_3395_);
v___x_3461_ = lean_array_push(v___x_3460_, v___x_3432_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 5);
lean_ctor_set(v___x_3426_, 0, v___x_3461_);
v___x_3463_ = v___x_3426_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3267_, v_zipper_3452_, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v___x_3459_);
return v___x_3465_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_3423_);
v___y_3294_ = v_a_3270_;
goto v___jp_3293_;
}
}
}
else
{
lean_dec(v_val_3399_);
goto v___jp_3297_;
}
}
else
{
lean_dec(v_val_3399_);
goto v___jp_3297_;
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v_val_3399_);
v___x_3474_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f(v_s_3267_, v_line_3269_);
if (lean_obj_tag(v___x_3474_) == 1)
{
lean_object* v_val_3475_; lean_object* v_level_3476_; lean_object* v_hashes_3477_; lean_object* v_content_3478_; lean_object* v_closeHashes_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3500_; 
v_val_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_val_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v_level_3476_ = lean_ctor_get(v_val_3475_, 0);
v_hashes_3477_ = lean_ctor_get(v_val_3475_, 1);
v_content_3478_ = lean_ctor_get(v_val_3475_, 2);
v_closeHashes_3479_ = lean_ctor_get(v_val_3475_, 3);
v_isSharedCheck_3500_ = !lean_is_exclusive(v_val_3475_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3481_ = v_val_3475_;
v_isShared_3482_ = v_isSharedCheck_3500_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_closeHashes_3479_);
lean_inc(v_content_3478_);
lean_inc(v_hashes_3477_);
lean_inc(v_level_3476_);
lean_dec(v_val_3475_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3500_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_zipper_3483_; lean_object* v_cursor_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3499_; 
v_zipper_3483_ = lean_ctor_get(v_a_3270_, 0);
v_cursor_3484_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3486_ = v_a_3270_;
v_isShared_3487_ = v_isSharedCheck_3499_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_cursor_3484_);
lean_inc(v_zipper_3483_);
lean_dec(v_a_3270_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3499_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; lean_object* v_content_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3488_ = l_Lean_Markdown_Lines_singleton___redArg(v_content_3478_);
v_content_3489_ = l_Lean_Markdown_InlineSource_ofLines(v_s_3267_, v___x_3488_);
v___x_3490_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 0, v___x_3490_);
v___x_3492_ = v___x_3486_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3490_);
lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_cursor_3484_);
v___x_3492_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
lean_object* v___x_3494_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set_tag(v___x_3481_, 1);
lean_ctor_set(v___x_3481_, 2, v_content_3489_);
v___x_3494_ = v___x_3481_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_level_3476_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_hashes_3477_);
lean_ctor_set(v_reuseFailAlloc_3497_, 2, v_content_3489_);
lean_ctor_set(v_reuseFailAlloc_3497_, 3, v_closeHashes_3479_);
v___x_3494_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3267_, v_zipper_3483_, v___x_3494_);
v___x_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v___x_3492_);
return v___x_3496_;
}
}
}
}
}
else
{
lean_dec(v___x_3474_);
v___y_3294_ = v_a_3270_;
goto v___jp_3293_;
}
}
}
else
{
lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v_val_3399_);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_line_3269_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; lean_object* v_unused_3528_; 
v_unused_3527_ = lean_ctor_get(v_line_3269_, 1);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v_line_3269_, 0);
lean_dec(v_unused_3528_);
v___x_3502_ = v_line_3269_;
v_isShared_3503_ = v_isSharedCheck_3526_;
goto v_resetjp_3501_;
}
else
{
lean_dec(v_line_3269_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3526_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_zipper_3504_; lean_object* v_openLeaf_x3f_3505_; 
v_zipper_3504_ = lean_ctor_get(v_a_3270_, 0);
lean_inc_ref(v_zipper_3504_);
v_openLeaf_x3f_3505_ = lean_ctor_get(v_zipper_3504_, 2);
if (lean_obj_tag(v_openLeaf_x3f_3505_) == 0)
{
lean_object* v_cursor_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3523_; 
v_cursor_3506_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3523_ == 0)
{
lean_object* v_unused_3524_; 
v_unused_3524_ = lean_ctor_get(v_a_3270_, 0);
lean_dec(v_unused_3524_);
v___x_3508_ = v_a_3270_;
v_isShared_3509_ = v_isSharedCheck_3523_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_cursor_3506_);
lean_dec(v_a_3270_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3523_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3512_; 
v___x_3510_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
lean_inc_ref(v_cursor_3506_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3512_ = v___x_3508_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_cursor_3506_);
v___x_3512_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3513_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_3267_, v_cursor_3506_);
v___x_3514_ = lean_mk_empty_array_with_capacity(v___x_3395_);
v___x_3515_ = lean_array_push(v___x_3514_, v___x_3513_);
v___x_3516_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0));
if (v_isShared_3503_ == 0)
{
lean_ctor_set_tag(v___x_3502_, 2);
lean_ctor_set(v___x_3502_, 1, v___x_3516_);
lean_ctor_set(v___x_3502_, 0, v___x_3515_);
v___x_3518_ = v___x_3502_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3267_, v_zipper_3504_, v___x_3518_);
v___x_3520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___x_3512_);
return v___x_3520_;
}
}
}
}
else
{
lean_object* v_cursor_3525_; 
lean_del_object(v___x_3502_);
v_cursor_3525_ = lean_ctor_get(v_a_3270_, 1);
lean_inc_ref(v_cursor_3525_);
lean_dec_ref(v_a_3270_);
v_zipper_3282_ = v_zipper_3504_;
v_cursor_3283_ = v_cursor_3525_;
goto v___jp_3281_;
}
}
}
}
}
v___jp_3271_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3275_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
lean_ctor_set(v___x_3276_, 1, v_cursor_3274_);
v___x_3277_ = l_Lean_Markdown_Lines_singleton___redArg(v___y_3272_);
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
v___x_3279_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3267_, v_zipper_3273_, v___x_3278_);
v___x_3280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v___x_3276_);
return v___x_3280_;
}
v___jp_3281_:
{
lean_object* v_pos_3284_; lean_object* v_stop_3285_; lean_object* v_openLeaf_x3f_3286_; lean_object* v___x_3287_; 
v_pos_3284_ = lean_ctor_get(v_cursor_3283_, 0);
v_stop_3285_ = lean_ctor_get(v_cursor_3283_, 1);
v_openLeaf_x3f_3286_ = lean_ctor_get(v_zipper_3282_, 2);
lean_inc(v_stop_3285_);
lean_inc(v_pos_3284_);
v___x_3287_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_3284_, v_stop_3285_);
if (lean_obj_tag(v_openLeaf_x3f_3286_) == 1)
{
lean_object* v_val_3288_; 
v_val_3288_ = lean_ctor_get(v_openLeaf_x3f_3286_, 0);
if (lean_obj_tag(v_val_3288_) == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3289_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v_cursor_3283_);
v___x_3291_ = l_Lean_Markdown_BlockZipper_extendParagraph___redArg(v_zipper_3282_, v___x_3287_);
v___x_3292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
lean_ctor_set(v___x_3292_, 1, v___x_3290_);
return v___x_3292_;
}
else
{
v___y_3272_ = v___x_3287_;
v_zipper_3273_ = v_zipper_3282_;
v_cursor_3274_ = v_cursor_3283_;
goto v___jp_3271_;
}
}
else
{
v___y_3272_ = v___x_3287_;
v_zipper_3273_ = v_zipper_3282_;
v_cursor_3274_ = v_cursor_3283_;
goto v___jp_3271_;
}
}
v___jp_3293_:
{
lean_object* v_zipper_3295_; lean_object* v_cursor_3296_; 
v_zipper_3295_ = lean_ctor_get(v___y_3294_, 0);
lean_inc_ref(v_zipper_3295_);
v_cursor_3296_ = lean_ctor_get(v___y_3294_, 1);
lean_inc_ref(v_cursor_3296_);
lean_dec_ref(v___y_3294_);
v_zipper_3282_ = v_zipper_3295_;
v_cursor_3283_ = v_cursor_3296_;
goto v___jp_3281_;
}
v___jp_3297_:
{
lean_object* v___x_3298_; 
v___x_3298_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f(v_s_3267_, v_line_3269_);
if (lean_obj_tag(v___x_3298_) == 1)
{
lean_object* v_val_3299_; lean_object* v_fst_3300_; lean_object* v_snd_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3321_; 
v_val_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_val_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v_fst_3300_ = lean_ctor_get(v_val_3299_, 0);
v_snd_3301_ = lean_ctor_get(v_val_3299_, 1);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_val_3299_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3303_ = v_val_3299_;
v_isShared_3304_ = v_isSharedCheck_3321_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_snd_3301_);
lean_inc(v_fst_3300_);
lean_dec(v_val_3299_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3321_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v_zipper_3305_; lean_object* v_cursor_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3320_; 
v_zipper_3305_ = lean_ctor_get(v_a_3270_, 0);
v_cursor_3306_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3308_ = v_a_3270_;
v_isShared_3309_ = v_isSharedCheck_3320_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_cursor_3306_);
lean_inc(v_zipper_3305_);
lean_dec(v_a_3270_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3320_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3312_; 
v___x_3310_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3310_);
v___x_3312_ = v___x_3308_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_cursor_3306_);
v___x_3312_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3313_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0));
v___x_3314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3314_, 0, v_fst_3300_);
lean_ctor_set(v___x_3314_, 1, v_snd_3301_);
lean_ctor_set(v___x_3314_, 2, v___x_3313_);
v___x_3315_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3267_, v_zipper_3305_, v___x_3314_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set_tag(v___x_3303_, 1);
lean_ctor_set(v___x_3303_, 1, v___x_3312_);
lean_ctor_set(v___x_3303_, 0, v___x_3315_);
v___x_3317_ = v___x_3303_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v___x_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
else
{
lean_dec(v___x_3298_);
v___y_3294_ = v_a_3270_;
goto v___jp_3293_;
}
}
v___jp_3322_:
{
uint8_t v___x_3323_; 
v___x_3323_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak(v_s_3267_, v_line_3269_);
if (v___x_3323_ == 0)
{
v___y_3294_ = v_a_3270_;
goto v___jp_3293_;
}
else
{
lean_object* v_zipper_3324_; lean_object* v_cursor_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3349_; 
v_zipper_3324_ = lean_ctor_get(v_a_3270_, 0);
v_cursor_3325_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3327_ = v_a_3270_;
v_isShared_3328_ = v_isSharedCheck_3349_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_cursor_3325_);
lean_inc(v_zipper_3324_);
lean_dec(v_a_3270_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3349_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v_after_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3347_; 
lean_inc_ref(v_cursor_3325_);
v___x_3329_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_3267_, v_cursor_3325_);
v_after_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; 
v_unused_3348_ = lean_ctor_get(v___x_3329_, 1);
lean_dec(v_unused_3348_);
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3347_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_after_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3347_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_pos_3334_; lean_object* v_stop_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3340_; 
v_pos_3334_ = lean_ctor_get(v_after_3330_, 0);
lean_inc(v_pos_3334_);
v_stop_3335_ = lean_ctor_get(v_after_3330_, 1);
lean_inc(v_stop_3335_);
lean_dec_ref(v_after_3330_);
v___x_3336_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_3334_, v_stop_3335_);
v___x_3337_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(v_s_3267_, v___x_3336_);
v___x_3338_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 0, v___x_3338_);
v___x_3340_ = v___x_3327_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3338_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_cursor_3325_);
v___x_3340_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3341_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3337_);
v___x_3342_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3267_, v_zipper_3324_, v___x_3341_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set_tag(v___x_3332_, 1);
lean_ctor_set(v___x_3332_, 1, v___x_3340_);
lean_ctor_set(v___x_3332_, 0, v___x_3342_);
v___x_3344_ = v___x_3332_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v___x_3340_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
}
v___jp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3357_ = lean_box(0);
v___x_3358_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(v_openedListItemThisLine_3268_, v_s_3267_, v___x_3357_, v___y_3355_);
v___x_3359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
lean_ctor_set(v___x_3359_, 1, v___y_3356_);
return v___x_3359_;
}
v___jp_3360_:
{
lean_object* v_zipper_3361_; lean_object* v_cursor_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3394_; 
v_zipper_3361_ = lean_ctor_get(v_a_3270_, 0);
v_cursor_3362_ = lean_ctor_get(v_a_3270_, 1);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_a_3270_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3364_ = v_a_3270_;
v_isShared_3365_ = v_isSharedCheck_3394_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_cursor_3362_);
lean_inc(v_zipper_3361_);
lean_dec(v_a_3270_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3394_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3366_);
v___x_3368_ = v___x_3364_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v_cursor_3362_);
v___x_3368_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v_z_3369_; 
v_z_3369_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_3267_, v_zipper_3361_);
if (v_openedListItemThisLine_3268_ == 0)
{
lean_object* v_spine_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v_spine_3370_ = lean_ctor_get(v_z_3369_, 1);
v___x_3371_ = lean_array_get_size(v_spine_3370_);
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_nat_sub(v___x_3371_, v___x_3372_);
v___x_3374_ = lean_nat_dec_lt(v___x_3373_, v___x_3371_);
if (v___x_3374_ == 0)
{
lean_dec(v___x_3373_);
v___y_3355_ = v_z_3369_;
v___y_3356_ = v___x_3368_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3375_; lean_object* v_container_3376_; 
v___x_3375_ = lean_array_fget(v_spine_3370_, v___x_3373_);
lean_dec(v___x_3373_);
v_container_3376_ = lean_ctor_get(v___x_3375_, 0);
if (lean_obj_tag(v_container_3376_) == 1)
{
lean_object* v_children_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3388_; 
v_children_3377_ = lean_ctor_get(v___x_3375_, 1);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; 
v_unused_3389_ = lean_ctor_get(v___x_3375_, 0);
lean_dec(v_unused_3389_);
v___x_3379_ = v___x_3375_;
v_isShared_3380_ = v_isSharedCheck_3388_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_children_3377_);
lean_dec(v___x_3375_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3388_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
uint8_t v___x_3381_; 
v___x_3381_ = l_Lean_Markdown_Children_isEmpty___redArg(v_children_3377_);
lean_dec_ref(v_children_3377_);
if (v___x_3381_ == 0)
{
lean_del_object(v___x_3379_);
v___y_3355_ = v_z_3369_;
v___y_3356_ = v___x_3368_;
goto v___jp_3354_;
}
else
{
lean_object* v_z_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v_z_3382_ = l_Lean_Markdown_BlockZipper_closeContainer(v_s_3267_, v_z_3369_);
v___x_3383_ = lean_box(0);
v___x_3384_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(v_openedListItemThisLine_3268_, v_s_3267_, v___x_3383_, v_z_3382_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set_tag(v___x_3379_, 1);
lean_ctor_set(v___x_3379_, 1, v___x_3368_);
lean_ctor_set(v___x_3379_, 0, v___x_3384_);
v___x_3386_ = v___x_3379_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3368_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_dec(v___x_3375_);
v___y_3355_ = v_z_3369_;
v___y_3356_ = v___x_3368_;
goto v___jp_3354_;
}
}
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3390_ = lean_box(0);
v___x_3391_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_finishBlankLine___lam__0(v_openedListItemThisLine_3268_, v_s_3267_, v___x_3390_, v_z_3369_);
v___x_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v___x_3368_);
return v___x_3392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openLeafBlock___boxed(lean_object* v_s_3529_, lean_object* v_openedListItemThisLine_3530_, lean_object* v_line_3531_, lean_object* v_a_3532_){
_start:
{
uint8_t v_openedListItemThisLine_boxed_3533_; lean_object* v_res_3534_; 
v_openedListItemThisLine_boxed_3533_ = lean_unbox(v_openedListItemThisLine_3530_);
v_res_3534_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openLeafBlock(v_s_3529_, v_openedListItemThisLine_boxed_3533_, v_line_3531_, v_a_3532_);
lean_dec_ref(v_s_3529_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine_spec__0(lean_object* v_s_3535_, lean_object* v_as_3536_, size_t v_i_3537_, size_t v_stop_3538_, lean_object* v_b_3539_){
_start:
{
uint8_t v___x_3540_; 
v___x_3540_ = lean_usize_dec_eq(v_i_3537_, v_stop_3538_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; lean_object* v___x_3542_; size_t v___x_3543_; size_t v___x_3544_; 
v___x_3541_ = lean_array_uget_borrowed(v_as_3536_, v_i_3537_);
lean_inc(v___x_3541_);
v___x_3542_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3535_, v_b_3539_, v___x_3541_);
v___x_3543_ = ((size_t)1ULL);
v___x_3544_ = lean_usize_add(v_i_3537_, v___x_3543_);
v_i_3537_ = v___x_3544_;
v_b_3539_ = v___x_3542_;
goto _start;
}
else
{
return v_b_3539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine_spec__0___boxed(lean_object* v_s_3546_, lean_object* v_as_3547_, lean_object* v_i_3548_, lean_object* v_stop_3549_, lean_object* v_b_3550_){
_start:
{
size_t v_i_boxed_3551_; size_t v_stop_boxed_3552_; lean_object* v_res_3553_; 
v_i_boxed_3551_ = lean_unbox_usize(v_i_3548_);
lean_dec(v_i_3548_);
v_stop_boxed_3552_ = lean_unbox_usize(v_stop_3549_);
lean_dec(v_stop_3549_);
v_res_3553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine_spec__0(v_s_3546_, v_as_3547_, v_i_boxed_3551_, v_stop_boxed_3552_, v_b_3550_);
lean_dec_ref(v_as_3547_);
lean_dec_ref(v_s_3546_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine(lean_object* v_s_3554_, lean_object* v_z_3555_, lean_object* v_line_3556_){
_start:
{
lean_object* v___y_3558_; lean_object* v_zipper_3559_; lean_object* v_zipper_3564_; lean_object* v_cursor_3565_; lean_object* v___y_3573_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3602_; uint8_t v___y_3603_; uint8_t v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v_a_3641_; lean_object* v_cursor_3642_; lean_object* v_a_3734_; lean_object* v_zipper_3735_; lean_object* v_val_3736_; lean_object* v_cursor_3737_; lean_object* v_a_3761_; lean_object* v_zipper_3762_; lean_object* v_openLeaf_x3f_3763_; lean_object* v_cursor_3764_; lean_object* v_a_3767_; lean_object* v_zipper_3768_; lean_object* v_val_3769_; lean_object* v_cursor_3770_; lean_object* v_zipper_3792_; lean_object* v_cursor_3793_; lean_object* v_matched_3794_; lean_object* v_zipper_3813_; lean_object* v_spine_3814_; lean_object* v_openLeaf_x3f_3815_; lean_object* v_cursor_3816_; lean_object* v_matched_3817_; lean_object* v_startInclusive_3827_; lean_object* v_endExclusive_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3897_; 
v_startInclusive_3827_ = lean_ctor_get(v_line_3556_, 0);
v_endExclusive_3828_ = lean_ctor_get(v_line_3556_, 1);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_line_3556_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3830_ = v_line_3556_;
v_isShared_3831_ = v_isSharedCheck_3897_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_endExclusive_3828_);
lean_inc(v_startInclusive_3827_);
lean_dec(v_line_3556_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3897_;
goto v_resetjp_3829_;
}
v___jp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = l_Lean_Markdown_Lines_singleton___redArg(v___y_3558_);
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
v___x_3562_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3554_, v_zipper_3559_, v___x_3561_);
return v___x_3562_;
}
v___jp_3563_:
{
lean_object* v_pos_3566_; lean_object* v_stop_3567_; lean_object* v_openLeaf_x3f_3568_; lean_object* v___x_3569_; 
v_pos_3566_ = lean_ctor_get(v_cursor_3565_, 0);
lean_inc(v_pos_3566_);
v_stop_3567_ = lean_ctor_get(v_cursor_3565_, 1);
lean_inc(v_stop_3567_);
lean_dec_ref(v_cursor_3565_);
v_openLeaf_x3f_3568_ = lean_ctor_get(v_zipper_3564_, 2);
v___x_3569_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_3566_, v_stop_3567_);
if (lean_obj_tag(v_openLeaf_x3f_3568_) == 1)
{
lean_object* v_val_3570_; 
v_val_3570_ = lean_ctor_get(v_openLeaf_x3f_3568_, 0);
if (lean_obj_tag(v_val_3570_) == 0)
{
lean_object* v___x_3571_; 
v___x_3571_ = l_Lean_Markdown_BlockZipper_extendParagraph___redArg(v_zipper_3564_, v___x_3569_);
return v___x_3571_;
}
else
{
v___y_3558_ = v___x_3569_;
v_zipper_3559_ = v_zipper_3564_;
goto v___jp_3557_;
}
}
else
{
v___y_3558_ = v___x_3569_;
v_zipper_3559_ = v_zipper_3564_;
goto v___jp_3557_;
}
}
v___jp_3572_:
{
lean_object* v_zipper_3574_; lean_object* v_cursor_3575_; 
v_zipper_3574_ = lean_ctor_get(v___y_3573_, 0);
lean_inc_ref(v_zipper_3574_);
v_cursor_3575_ = lean_ctor_get(v___y_3573_, 1);
lean_inc_ref(v_cursor_3575_);
lean_dec_ref(v___y_3573_);
v_zipper_3564_ = v_zipper_3574_;
v_cursor_3565_ = v_cursor_3575_;
goto v___jp_3563_;
}
v___jp_3576_:
{
uint8_t v___x_3579_; 
v___x_3579_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isThematicBreak(v_s_3554_, v___y_3578_);
if (v___x_3579_ == 0)
{
v___y_3573_ = v___y_3577_;
goto v___jp_3572_;
}
else
{
lean_object* v_zipper_3580_; lean_object* v_cursor_3581_; lean_object* v___x_3582_; lean_object* v_after_3583_; lean_object* v_pos_3584_; lean_object* v_stop_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v_zipper_3580_ = lean_ctor_get(v___y_3577_, 0);
lean_inc_ref(v_zipper_3580_);
v_cursor_3581_ = lean_ctor_get(v___y_3577_, 1);
lean_inc_ref(v_cursor_3581_);
lean_dec_ref(v___y_3577_);
v___x_3582_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_3554_, v_cursor_3581_);
v_after_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc_ref(v_after_3583_);
lean_dec_ref(v___x_3582_);
v_pos_3584_ = lean_ctor_get(v_after_3583_, 0);
lean_inc(v_pos_3584_);
v_stop_3585_ = lean_ctor_get(v_after_3583_, 1);
lean_inc(v_stop_3585_);
lean_dec_ref(v_after_3583_);
v___x_3586_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_3584_, v_stop_3585_);
v___x_3587_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_trimTrailingWs(v_s_3554_, v___x_3586_);
v___x_3588_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
v___x_3589_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3554_, v_zipper_3580_, v___x_3588_);
return v___x_3589_;
}
}
v___jp_3590_:
{
lean_object* v___x_3593_; 
v___x_3593_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceOpen_x3f(v_s_3554_, v___y_3592_);
if (lean_obj_tag(v___x_3593_) == 1)
{
lean_object* v_val_3594_; lean_object* v_fst_3595_; lean_object* v_snd_3596_; lean_object* v_zipper_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v_val_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_val_3594_);
lean_dec_ref_known(v___x_3593_, 1);
v_fst_3595_ = lean_ctor_get(v_val_3594_, 0);
lean_inc(v_fst_3595_);
v_snd_3596_ = lean_ctor_get(v_val_3594_, 1);
lean_inc(v_snd_3596_);
lean_dec(v_val_3594_);
v_zipper_3597_ = lean_ctor_get(v___y_3591_, 0);
lean_inc_ref(v_zipper_3597_);
lean_dec_ref(v___y_3591_);
v___x_3598_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0));
v___x_3599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3599_, 0, v_fst_3595_);
lean_ctor_set(v___x_3599_, 1, v_snd_3596_);
lean_ctor_set(v___x_3599_, 2, v___x_3598_);
v___x_3600_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3554_, v_zipper_3597_, v___x_3599_);
return v___x_3600_;
}
else
{
lean_dec(v___x_3593_);
v___y_3573_ = v___y_3591_;
goto v___jp_3572_;
}
}
v___jp_3601_:
{
lean_object* v_zipper_3604_; lean_object* v_z_3605_; 
v_zipper_3604_ = lean_ctor_get(v___y_3602_, 0);
lean_inc_ref(v_zipper_3604_);
lean_dec_ref(v___y_3602_);
v_z_3605_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_3554_, v_zipper_3604_);
if (v___y_3603_ == 0)
{
lean_object* v_spine_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v_spine_3606_ = lean_ctor_get(v_z_3605_, 1);
v___x_3607_ = lean_array_get_size(v_spine_3606_);
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_sub(v___x_3607_, v___x_3608_);
v___x_3610_ = lean_nat_dec_lt(v___x_3609_, v___x_3607_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
lean_dec(v___x_3609_);
v___x_3611_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_3554_, v_z_3605_);
return v___x_3611_;
}
else
{
lean_object* v___x_3612_; lean_object* v_container_3613_; 
v___x_3612_ = lean_array_fget_borrowed(v_spine_3606_, v___x_3609_);
lean_dec(v___x_3609_);
v_container_3613_ = lean_ctor_get(v___x_3612_, 0);
if (lean_obj_tag(v_container_3613_) == 1)
{
lean_object* v_children_3614_; uint8_t v___x_3615_; 
v_children_3614_ = lean_ctor_get(v___x_3612_, 1);
v___x_3615_ = l_Lean_Markdown_Children_isEmpty___redArg(v_children_3614_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_3554_, v_z_3605_);
return v___x_3616_;
}
else
{
lean_object* v_z_3617_; lean_object* v___x_3618_; 
v_z_3617_ = l_Lean_Markdown_BlockZipper_closeContainer(v_s_3554_, v_z_3605_);
v___x_3618_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_3554_, v_z_3617_);
return v___x_3618_;
}
}
else
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_3554_, v_z_3605_);
return v___x_3619_;
}
}
}
else
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v_z_3605_);
return v___x_3620_;
}
}
v___jp_3621_:
{
lean_object* v___x_3625_; lean_object* v_source_3626_; uint8_t v___x_3627_; 
v___x_3625_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_3554_, v___y_3623_);
v_source_3626_ = lean_ctor_get(v___x_3625_, 0);
v___x_3627_ = l_Lean_Markdown_HtmlBlockKind_endConditionMet(v_s_3554_, v___y_3622_, v_source_3626_);
if (v___x_3627_ == 0)
{
lean_object* v_zipper_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v_zipper_3628_ = lean_ctor_get(v___y_3624_, 0);
lean_inc_ref(v_zipper_3628_);
lean_dec_ref(v___y_3624_);
v___x_3629_ = lean_unsigned_to_nat(1u);
v___x_3630_ = lean_mk_empty_array_with_capacity(v___x_3629_);
v___x_3631_ = lean_array_push(v___x_3630_, v___x_3625_);
v___x_3632_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
lean_ctor_set_uint8(v___x_3632_, sizeof(void*)*1, v___y_3622_);
v___x_3633_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3554_, v_zipper_3628_, v___x_3632_);
return v___x_3633_;
}
else
{
lean_object* v_zipper_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_zipper_3634_ = lean_ctor_get(v___y_3624_, 0);
lean_inc_ref(v_zipper_3634_);
lean_dec_ref(v___y_3624_);
v___x_3635_ = lean_unsigned_to_nat(1u);
v___x_3636_ = lean_mk_empty_array_with_capacity(v___x_3635_);
v___x_3637_ = lean_array_push(v___x_3636_, v___x_3625_);
v___x_3638_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
v___x_3639_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3554_, v_zipper_3634_, v___x_3638_);
return v___x_3639_;
}
}
v___jp_3640_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_3554_, v_cursor_3642_);
v___x_3644_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_openContainerPrefixes(v_s_3554_, v___x_3643_, v_a_3641_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v_snd_3646_; lean_object* v_after_3647_; lean_object* v_a_3648_; lean_object* v_fst_3649_; lean_object* v_indent_3650_; lean_object* v_pos_3651_; lean_object* v_stop_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
v_snd_3646_ = lean_ctor_get(v_a_3645_, 1);
lean_inc(v_snd_3646_);
v_after_3647_ = lean_ctor_get(v_snd_3646_, 0);
v_a_3648_ = lean_ctor_get(v___x_3644_, 1);
lean_inc(v_a_3648_);
lean_dec_ref_known(v___x_3644_, 2);
v_fst_3649_ = lean_ctor_get(v_a_3645_, 0);
lean_inc(v_fst_3649_);
lean_dec(v_a_3645_);
v_indent_3650_ = lean_ctor_get(v_snd_3646_, 1);
v_pos_3651_ = lean_ctor_get(v_after_3647_, 0);
v_stop_3652_ = lean_ctor_get(v_after_3647_, 1);
v___x_3653_ = lean_unsigned_to_nat(1u);
v___x_3654_ = lean_nat_add(v_pos_3651_, v___x_3653_);
v___x_3655_ = lean_nat_dec_le(v___x_3654_, v_stop_3652_);
lean_dec(v___x_3654_);
if (v___x_3655_ == 0)
{
uint8_t v___x_3656_; 
lean_dec(v_snd_3646_);
v___x_3656_ = lean_unbox(v_fst_3649_);
lean_dec(v_fst_3649_);
v___y_3602_ = v_a_3648_;
v___y_3603_ = v___x_3656_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3657_; 
v___x_3657_ = l_String_Slice_Pos_get_x3f(v_s_3554_, v_pos_3651_);
if (lean_obj_tag(v___x_3657_) == 0)
{
uint8_t v___x_3658_; 
lean_dec(v_snd_3646_);
v___x_3658_ = lean_unbox(v_fst_3649_);
lean_dec(v_fst_3649_);
v___y_3602_ = v_a_3648_;
v___y_3603_ = v___x_3658_;
goto v___jp_3601_;
}
else
{
lean_object* v_val_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
lean_dec(v_fst_3649_);
v_val_3659_ = lean_ctor_get(v___x_3657_, 0);
lean_inc(v_val_3659_);
lean_dec_ref_known(v___x_3657_, 1);
v___x_3660_ = lean_unsigned_to_nat(4u);
v___x_3661_ = lean_nat_dec_le(v___x_3660_, v_indent_3650_);
if (v___x_3661_ == 0)
{
uint32_t v___x_3662_; uint32_t v___x_3663_; uint8_t v___x_3664_; 
v___x_3662_ = 35;
v___x_3663_ = lean_unbox_uint32(v_val_3659_);
v___x_3664_ = lean_uint32_dec_eq(v___x_3663_, v___x_3662_);
if (v___x_3664_ == 0)
{
uint32_t v___x_3665_; uint32_t v___x_3666_; uint8_t v___x_3667_; 
v___x_3665_ = 96;
v___x_3666_ = lean_unbox_uint32(v_val_3659_);
v___x_3667_ = lean_uint32_dec_eq(v___x_3666_, v___x_3665_);
if (v___x_3667_ == 0)
{
uint32_t v___x_3668_; uint32_t v___x_3669_; uint8_t v___x_3670_; 
v___x_3668_ = 126;
v___x_3669_ = lean_unbox_uint32(v_val_3659_);
v___x_3670_ = lean_uint32_dec_eq(v___x_3669_, v___x_3668_);
if (v___x_3670_ == 0)
{
uint32_t v___x_3671_; uint32_t v___x_3672_; uint8_t v___x_3673_; 
v___x_3671_ = 60;
v___x_3672_ = lean_unbox_uint32(v_val_3659_);
v___x_3673_ = lean_uint32_dec_eq(v___x_3672_, v___x_3671_);
if (v___x_3673_ == 0)
{
uint32_t v___x_3674_; uint32_t v___x_3675_; uint8_t v___x_3676_; 
v___x_3674_ = 42;
v___x_3675_ = lean_unbox_uint32(v_val_3659_);
v___x_3676_ = lean_uint32_dec_eq(v___x_3675_, v___x_3674_);
if (v___x_3676_ == 0)
{
uint32_t v___x_3677_; uint32_t v___x_3678_; uint8_t v___x_3679_; 
v___x_3677_ = 45;
v___x_3678_ = lean_unbox_uint32(v_val_3659_);
v___x_3679_ = lean_uint32_dec_eq(v___x_3678_, v___x_3677_);
if (v___x_3679_ == 0)
{
uint32_t v___x_3680_; uint32_t v___x_3681_; uint8_t v___x_3682_; 
v___x_3680_ = 95;
v___x_3681_ = lean_unbox_uint32(v_val_3659_);
lean_dec(v_val_3659_);
v___x_3682_ = lean_uint32_dec_eq(v___x_3681_, v___x_3680_);
if (v___x_3682_ == 0)
{
lean_dec(v_snd_3646_);
v___y_3573_ = v_a_3648_;
goto v___jp_3572_;
}
else
{
v___y_3577_ = v_a_3648_;
v___y_3578_ = v_snd_3646_;
goto v___jp_3576_;
}
}
else
{
lean_dec(v_val_3659_);
v___y_3577_ = v_a_3648_;
v___y_3578_ = v_snd_3646_;
goto v___jp_3576_;
}
}
else
{
lean_dec(v_val_3659_);
v___y_3577_ = v_a_3648_;
v___y_3578_ = v_snd_3646_;
goto v___jp_3576_;
}
}
else
{
lean_object* v___x_3683_; 
lean_dec(v_val_3659_);
v___x_3683_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f(v_s_3554_, v_snd_3646_);
if (lean_obj_tag(v___x_3683_) == 1)
{
lean_object* v_zipper_3684_; lean_object* v_openLeaf_x3f_3685_; 
v_zipper_3684_ = lean_ctor_get(v_a_3648_, 0);
v_openLeaf_x3f_3685_ = lean_ctor_get(v_zipper_3684_, 2);
if (lean_obj_tag(v_openLeaf_x3f_3685_) == 1)
{
lean_object* v_val_3686_; 
v_val_3686_ = lean_ctor_get(v_openLeaf_x3f_3685_, 0);
if (lean_obj_tag(v_val_3686_) == 0)
{
lean_object* v_val_3687_; lean_object* v_cursor_3688_; uint8_t v___x_3689_; uint8_t v___x_3690_; 
v_val_3687_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_val_3687_);
lean_dec_ref_known(v___x_3683_, 1);
v_cursor_3688_ = lean_ctor_get(v_a_3648_, 1);
lean_inc_ref(v_cursor_3688_);
v___x_3689_ = lean_unbox(v_val_3687_);
v___x_3690_ = l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(v___x_3689_);
if (v___x_3690_ == 0)
{
lean_inc_ref(v_zipper_3684_);
lean_dec(v_val_3687_);
lean_dec(v_a_3648_);
v_zipper_3564_ = v_zipper_3684_;
v_cursor_3565_ = v_cursor_3688_;
goto v___jp_3563_;
}
else
{
uint8_t v___x_3691_; 
v___x_3691_ = lean_unbox(v_val_3687_);
lean_dec(v_val_3687_);
v___y_3622_ = v___x_3691_;
v___y_3623_ = v_cursor_3688_;
v___y_3624_ = v_a_3648_;
goto v___jp_3621_;
}
}
else
{
lean_object* v_val_3692_; lean_object* v_cursor_3693_; uint8_t v___x_3694_; 
v_val_3692_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_val_3692_);
lean_dec_ref_known(v___x_3683_, 1);
v_cursor_3693_ = lean_ctor_get(v_a_3648_, 1);
lean_inc_ref(v_cursor_3693_);
v___x_3694_ = lean_unbox(v_val_3692_);
lean_dec(v_val_3692_);
v___y_3622_ = v___x_3694_;
v___y_3623_ = v_cursor_3693_;
v___y_3624_ = v_a_3648_;
goto v___jp_3621_;
}
}
else
{
lean_object* v_val_3695_; lean_object* v_cursor_3696_; uint8_t v___x_3697_; 
v_val_3695_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_val_3695_);
lean_dec_ref_known(v___x_3683_, 1);
v_cursor_3696_ = lean_ctor_get(v_a_3648_, 1);
lean_inc_ref(v_cursor_3696_);
v___x_3697_ = lean_unbox(v_val_3695_);
lean_dec(v_val_3695_);
v___y_3622_ = v___x_3697_;
v___y_3623_ = v_cursor_3696_;
v___y_3624_ = v_a_3648_;
goto v___jp_3621_;
}
}
else
{
lean_dec(v___x_3683_);
v___y_3573_ = v_a_3648_;
goto v___jp_3572_;
}
}
}
else
{
lean_dec(v_val_3659_);
v___y_3591_ = v_a_3648_;
v___y_3592_ = v_snd_3646_;
goto v___jp_3590_;
}
}
else
{
lean_dec(v_val_3659_);
v___y_3591_ = v_a_3648_;
v___y_3592_ = v_snd_3646_;
goto v___jp_3590_;
}
}
else
{
lean_object* v___x_3698_; 
lean_dec(v_val_3659_);
v___x_3698_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f(v_s_3554_, v_snd_3646_);
if (lean_obj_tag(v___x_3698_) == 1)
{
lean_object* v_val_3699_; lean_object* v_level_3700_; lean_object* v_hashes_3701_; lean_object* v_content_3702_; lean_object* v_closeHashes_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3714_; 
v_val_3699_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v___x_3698_, 1);
v_level_3700_ = lean_ctor_get(v_val_3699_, 0);
v_hashes_3701_ = lean_ctor_get(v_val_3699_, 1);
v_content_3702_ = lean_ctor_get(v_val_3699_, 2);
v_closeHashes_3703_ = lean_ctor_get(v_val_3699_, 3);
v_isSharedCheck_3714_ = !lean_is_exclusive(v_val_3699_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3705_ = v_val_3699_;
v_isShared_3706_ = v_isSharedCheck_3714_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_closeHashes_3703_);
lean_inc(v_content_3702_);
lean_inc(v_hashes_3701_);
lean_inc(v_level_3700_);
lean_dec(v_val_3699_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3714_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v_zipper_3707_; lean_object* v___x_3708_; lean_object* v_content_3709_; lean_object* v___x_3711_; 
v_zipper_3707_ = lean_ctor_get(v_a_3648_, 0);
lean_inc_ref(v_zipper_3707_);
lean_dec(v_a_3648_);
v___x_3708_ = l_Lean_Markdown_Lines_singleton___redArg(v_content_3702_);
v_content_3709_ = l_Lean_Markdown_InlineSource_ofLines(v_s_3554_, v___x_3708_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set_tag(v___x_3705_, 1);
lean_ctor_set(v___x_3705_, 2, v_content_3709_);
v___x_3711_ = v___x_3705_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_level_3700_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_hashes_3701_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_content_3709_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_closeHashes_3703_);
v___x_3711_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3554_, v_zipper_3707_, v___x_3711_);
return v___x_3712_;
}
}
}
else
{
lean_dec(v___x_3698_);
v___y_3573_ = v_a_3648_;
goto v___jp_3572_;
}
}
}
else
{
lean_object* v_zipper_3715_; lean_object* v_openLeaf_x3f_3716_; 
lean_dec(v_val_3659_);
lean_dec(v_snd_3646_);
v_zipper_3715_ = lean_ctor_get(v_a_3648_, 0);
lean_inc_ref(v_zipper_3715_);
v_openLeaf_x3f_3716_ = lean_ctor_get(v_zipper_3715_, 2);
if (lean_obj_tag(v_openLeaf_x3f_3716_) == 0)
{
lean_object* v_cursor_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3729_; 
v_cursor_3717_ = lean_ctor_get(v_a_3648_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_a_3648_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_a_3648_, 0);
lean_dec(v_unused_3730_);
v___x_3719_ = v_a_3648_;
v_isShared_3720_ = v_isSharedCheck_3729_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_cursor_3717_);
lean_dec(v_a_3648_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3729_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3721_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_3554_, v_cursor_3717_);
v___x_3722_ = lean_mk_empty_array_with_capacity(v___x_3653_);
v___x_3723_ = lean_array_push(v___x_3722_, v___x_3721_);
v___x_3724_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_tryFencedCodeOpener___closed__0));
if (v_isShared_3720_ == 0)
{
lean_ctor_set_tag(v___x_3719_, 2);
lean_ctor_set(v___x_3719_, 1, v___x_3724_);
lean_ctor_set(v___x_3719_, 0, v___x_3723_);
v___x_3726_ = v___x_3719_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3554_, v_zipper_3715_, v___x_3726_);
return v___x_3727_;
}
}
}
else
{
lean_object* v_cursor_3731_; 
v_cursor_3731_ = lean_ctor_get(v_a_3648_, 1);
lean_inc_ref(v_cursor_3731_);
lean_dec(v_a_3648_);
v_zipper_3564_ = v_zipper_3715_;
v_cursor_3565_ = v_cursor_3731_;
goto v___jp_3563_;
}
}
}
}
}
else
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3644_, 2);
return v_a_3732_;
}
}
v___jp_3733_:
{
if (lean_obj_tag(v_val_3736_) == 2)
{
lean_object* v___x_3738_; lean_object* v_after_3739_; lean_object* v_indent_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref_known(v_val_3736_, 2);
lean_dec_ref(v_a_3734_);
lean_inc_ref(v_cursor_3737_);
v___x_3738_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_3554_, v_cursor_3737_);
v_after_3739_ = lean_ctor_get(v___x_3738_, 0);
v_indent_3740_ = lean_ctor_get(v___x_3738_, 1);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3742_ = v___x_3738_;
v_isShared_3743_ = v_isSharedCheck_3759_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_indent_3740_);
lean_inc(v_after_3739_);
lean_dec(v___x_3738_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3759_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v_pos_3744_; lean_object* v_stop_3745_; uint8_t v___x_3746_; 
v_pos_3744_ = lean_ctor_get(v_after_3739_, 0);
lean_inc(v_pos_3744_);
v_stop_3745_ = lean_ctor_get(v_after_3739_, 1);
lean_inc(v_stop_3745_);
lean_dec_ref(v_after_3739_);
v___x_3746_ = lean_nat_dec_le(v_stop_3745_, v_pos_3744_);
lean_dec(v_pos_3744_);
lean_dec(v_stop_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; uint8_t v___x_3748_; 
v___x_3747_ = lean_unsigned_to_nat(4u);
v___x_3748_ = lean_nat_dec_le(v___x_3747_, v_indent_3740_);
lean_dec(v_indent_3740_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; lean_object* v___x_3751_; 
v___x_3749_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_3554_, v_zipper_3735_);
lean_inc_ref(v_cursor_3737_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 1, v_cursor_3737_);
lean_ctor_set(v___x_3742_, 0, v___x_3749_);
v___x_3751_ = v___x_3742_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_cursor_3737_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
v_a_3641_ = v___x_3751_;
v_cursor_3642_ = v_cursor_3737_;
goto v___jp_3640_;
}
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
lean_del_object(v___x_3742_);
v___x_3753_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_3554_, v_cursor_3737_);
v___x_3754_ = l_Lean_Markdown_BlockZipper_indentedCodeAddLine___redArg(v_zipper_3735_, v___x_3753_);
v___x_3755_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_3754_);
return v___x_3755_;
}
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_del_object(v___x_3742_);
lean_dec(v_indent_3740_);
v___x_3756_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_indentedCodeLine(v_s_3554_, v_cursor_3737_);
v___x_3757_ = l_Lean_Markdown_BlockZipper_indentedCodeAddBlank___redArg(v_zipper_3735_, v___x_3756_);
v___x_3758_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_3554_, v___x_3757_);
return v___x_3758_;
}
}
}
else
{
lean_dec_ref(v_val_3736_);
lean_dec_ref(v_zipper_3735_);
v_a_3641_ = v_a_3734_;
v_cursor_3642_ = v_cursor_3737_;
goto v___jp_3640_;
}
}
v___jp_3760_:
{
if (lean_obj_tag(v_openLeaf_x3f_3763_) == 1)
{
lean_object* v_val_3765_; 
v_val_3765_ = lean_ctor_get(v_openLeaf_x3f_3763_, 0);
lean_inc(v_val_3765_);
lean_dec_ref_known(v_openLeaf_x3f_3763_, 1);
v_a_3734_ = v_a_3761_;
v_zipper_3735_ = v_zipper_3762_;
v_val_3736_ = v_val_3765_;
v_cursor_3737_ = v_cursor_3764_;
goto v___jp_3733_;
}
else
{
lean_dec(v_openLeaf_x3f_3763_);
lean_dec_ref(v_zipper_3762_);
v_a_3641_ = v_a_3761_;
v_cursor_3642_ = v_cursor_3764_;
goto v___jp_3640_;
}
}
v___jp_3766_:
{
if (lean_obj_tag(v_val_3769_) == 3)
{
uint8_t v_kind_3771_; uint8_t v___x_3772_; 
lean_dec_ref(v_a_3767_);
v_kind_3771_ = lean_ctor_get_uint8(v_val_3769_, sizeof(void*)*1);
lean_dec_ref_known(v_val_3769_, 1);
v___x_3772_ = l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine(v_kind_3771_);
if (v___x_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v_source_3774_; uint8_t v___x_3775_; 
lean_inc_ref(v_cursor_3770_);
v___x_3773_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_3554_, v_cursor_3770_);
v_source_3774_ = lean_ctor_get(v___x_3773_, 0);
v___x_3775_ = l_Lean_Markdown_HtmlBlockKind_endConditionMet(v_s_3554_, v_kind_3771_, v_source_3774_);
if (v___x_3775_ == 0)
{
uint8_t v___x_3776_; 
v___x_3776_ = l_Lean_Markdown_Cursor_isBlank(v_s_3554_, v_cursor_3770_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_3768_, v___x_3773_);
v___x_3778_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_3777_);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3779_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_3768_, v___x_3773_);
v___x_3780_ = l_Lean_Markdown_BlockZipper_recordBlankLine(v_s_3554_, v___x_3779_);
return v___x_3780_;
}
}
else
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
lean_dec_ref(v_cursor_3770_);
v___x_3781_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_3768_, v___x_3773_);
v___x_3782_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_3554_, v___x_3781_);
v___x_3783_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_3782_);
return v___x_3783_;
}
}
else
{
uint8_t v___x_3784_; 
lean_inc_ref(v_cursor_3770_);
v___x_3784_ = l_Lean_Markdown_Cursor_isBlank(v_s_3554_, v_cursor_3770_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_3554_, v_cursor_3770_);
v___x_3786_ = l_Lean_Markdown_BlockZipper_extendHtml___redArg(v_zipper_3768_, v___x_3785_);
v___x_3787_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_3786_);
return v___x_3787_;
}
else
{
lean_object* v___x_3788_; lean_object* v_openLeaf_x3f_3789_; lean_object* v___x_3790_; 
v___x_3788_ = l_Lean_Markdown_BlockZipper_closeLeaf(v_s_3554_, v_zipper_3768_);
v_openLeaf_x3f_3789_ = lean_ctor_get(v___x_3788_, 2);
lean_inc(v_openLeaf_x3f_3789_);
lean_inc_ref(v_cursor_3770_);
lean_inc_ref(v___x_3788_);
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v_cursor_3770_);
v_a_3761_ = v___x_3790_;
v_zipper_3762_ = v___x_3788_;
v_openLeaf_x3f_3763_ = v_openLeaf_x3f_3789_;
v_cursor_3764_ = v_cursor_3770_;
goto v___jp_3760_;
}
}
}
else
{
v_a_3734_ = v_a_3767_;
v_zipper_3735_ = v_zipper_3768_;
v_val_3736_ = v_val_3769_;
v_cursor_3737_ = v_cursor_3770_;
goto v___jp_3733_;
}
}
v___jp_3791_:
{
lean_object* v___x_3795_; lean_object* v_openLeaf_x3f_3796_; lean_object* v___x_3797_; 
v___x_3795_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_closeNonContinuingContainers_closeAbove_spec__0___redArg(v_matched_3794_, v_s_3554_, v_zipper_3792_);
lean_dec(v_matched_3794_);
v_openLeaf_x3f_3796_ = lean_ctor_get(v___x_3795_, 2);
lean_inc_ref(v_cursor_3793_);
lean_inc_ref(v___x_3795_);
v___x_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v_cursor_3793_);
if (lean_obj_tag(v_openLeaf_x3f_3796_) == 1)
{
lean_object* v_val_3798_; 
v_val_3798_ = lean_ctor_get(v_openLeaf_x3f_3796_, 0);
if (lean_obj_tag(v_val_3798_) == 1)
{
lean_object* v_info_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec_ref_known(v___x_3797_, 2);
v_info_3799_ = lean_ctor_get(v_val_3798_, 0);
lean_inc_ref(v_cursor_3793_);
v___x_3800_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_3554_, v_cursor_3793_);
v___x_3801_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseFenceClose_x3f(v_s_3554_, v___x_3800_, v_info_3799_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_openIndent_3802_; lean_object* v___x_3803_; lean_object* v_fst_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v_openIndent_3802_ = lean_ctor_get(v_info_3799_, 1);
lean_inc(v_openIndent_3802_);
v___x_3803_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_consumeIndentCapped(v_s_3554_, v_cursor_3793_, v_openIndent_3802_);
v_fst_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_fst_3804_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = l_Lean_Markdown_Cursor_verbatimLine(v_s_3554_, v_fst_3804_);
v___x_3806_ = l_Lean_Markdown_BlockZipper_extendFencedCode___redArg(v___x_3795_, v___x_3805_);
v___x_3807_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_3806_);
return v___x_3807_;
}
else
{
lean_object* v_val_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
lean_dec_ref(v_cursor_3793_);
v_val_3808_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_val_3808_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3809_ = l_Lean_Markdown_BlockZipper_closeFencedCode(v_s_3554_, v___x_3795_, v_val_3808_);
v___x_3810_ = l_Lean_Markdown_BlockZipper_recordContentLine___redArg(v___x_3809_);
return v___x_3810_;
}
}
else
{
lean_inc(v_val_3798_);
v_a_3767_ = v___x_3797_;
v_zipper_3768_ = v___x_3795_;
v_val_3769_ = v_val_3798_;
v_cursor_3770_ = v_cursor_3793_;
goto v___jp_3766_;
}
}
else
{
if (lean_obj_tag(v_openLeaf_x3f_3796_) == 1)
{
lean_object* v_val_3811_; 
v_val_3811_ = lean_ctor_get(v_openLeaf_x3f_3796_, 0);
lean_inc(v_val_3811_);
v_a_3767_ = v___x_3797_;
v_zipper_3768_ = v___x_3795_;
v_val_3769_ = v_val_3811_;
v_cursor_3770_ = v_cursor_3793_;
goto v___jp_3766_;
}
else
{
lean_inc(v_openLeaf_x3f_3796_);
v_a_3761_ = v___x_3797_;
v_zipper_3762_ = v___x_3795_;
v_openLeaf_x3f_3763_ = v_openLeaf_x3f_3796_;
v_cursor_3764_ = v_cursor_3793_;
goto v___jp_3760_;
}
}
}
v___jp_3812_:
{
lean_object* v___x_3818_; uint8_t v___x_3819_; 
v___x_3818_ = lean_array_get_size(v_spine_3814_);
lean_dec_ref(v_spine_3814_);
v___x_3819_ = lean_nat_dec_lt(v_matched_3817_, v___x_3818_);
if (v___x_3819_ == 0)
{
lean_dec(v_openLeaf_x3f_3815_);
v_zipper_3792_ = v_zipper_3813_;
v_cursor_3793_ = v_cursor_3816_;
v_matched_3794_ = v_matched_3817_;
goto v___jp_3791_;
}
else
{
if (lean_obj_tag(v_openLeaf_x3f_3815_) == 1)
{
lean_object* v_val_3820_; 
v_val_3820_ = lean_ctor_get(v_openLeaf_x3f_3815_, 0);
lean_inc(v_val_3820_);
lean_dec_ref_known(v_openLeaf_x3f_3815_, 1);
if (lean_obj_tag(v_val_3820_) == 0)
{
lean_object* v___x_3821_; uint8_t v___x_3822_; 
lean_dec_ref_known(v_val_3820_, 1);
lean_inc_ref(v_cursor_3816_);
v___x_3821_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_3554_, v_cursor_3816_);
v___x_3822_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_isInterrupt(v_s_3554_, v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v_pos_3823_; lean_object* v_stop_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec(v_matched_3817_);
v_pos_3823_ = lean_ctor_get(v_cursor_3816_, 0);
lean_inc(v_pos_3823_);
v_stop_3824_ = lean_ctor_get(v_cursor_3816_, 1);
lean_inc(v_stop_3824_);
lean_dec_ref(v_cursor_3816_);
v___x_3825_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_3823_, v_stop_3824_);
v___x_3826_ = l_Lean_Markdown_BlockZipper_extendParagraph___redArg(v_zipper_3813_, v___x_3825_);
return v___x_3826_;
}
else
{
v_zipper_3792_ = v_zipper_3813_;
v_cursor_3793_ = v_cursor_3816_;
v_matched_3794_ = v_matched_3817_;
goto v___jp_3791_;
}
}
else
{
lean_dec(v_val_3820_);
v_zipper_3792_ = v_zipper_3813_;
v_cursor_3793_ = v_cursor_3816_;
v_matched_3794_ = v_matched_3817_;
goto v___jp_3791_;
}
}
else
{
lean_dec(v_openLeaf_x3f_3815_);
v_zipper_3792_ = v_zipper_3813_;
v_cursor_3793_ = v_cursor_3816_;
v_matched_3794_ = v_matched_3817_;
goto v___jp_3791_;
}
}
}
v_resetjp_3829_:
{
lean_object* v___x_3832_; uint8_t v___x_3833_; lean_object* v___x_3834_; lean_object* v_init_3836_; 
v___x_3832_ = lean_unsigned_to_nat(0u);
v___x_3833_ = 0;
v___x_3834_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3834_, 0, v_startInclusive_3827_);
lean_ctor_set(v___x_3834_, 1, v_endExclusive_3828_);
lean_ctor_set(v___x_3834_, 2, v___x_3832_);
lean_ctor_set_uint8(v___x_3834_, sizeof(void*)*3, v___x_3833_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set(v___x_3830_, 1, v___x_3834_);
lean_ctor_set(v___x_3830_, 0, v_z_3555_);
v_init_3836_ = v___x_3830_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_z_3555_);
lean_ctor_set(v_reuseFailAlloc_3896_, 1, v___x_3834_);
v_init_3836_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v_init_3836_);
lean_ctor_set(v___x_3837_, 1, v___x_3832_);
v___x_3838_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_continueContainers(v_s_3554_, v___x_3837_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v_toLineState_3840_; lean_object* v_zipper_3841_; lean_object* v_matched_3842_; lean_object* v_cursor_3843_; lean_object* v_document_3844_; lean_object* v_spine_3845_; lean_object* v_openLeaf_x3f_3846_; lean_object* v_blankLineFloor_x3f_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 1);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 2);
v_toLineState_3840_ = lean_ctor_get(v_a_3839_, 0);
lean_inc_ref(v_toLineState_3840_);
v_zipper_3841_ = lean_ctor_get(v_toLineState_3840_, 0);
lean_inc_ref(v_zipper_3841_);
v_matched_3842_ = lean_ctor_get(v_a_3839_, 1);
lean_inc(v_matched_3842_);
lean_dec(v_a_3839_);
v_cursor_3843_ = lean_ctor_get(v_toLineState_3840_, 1);
lean_inc_ref(v_cursor_3843_);
lean_dec_ref(v_toLineState_3840_);
v_document_3844_ = lean_ctor_get(v_zipper_3841_, 0);
v_spine_3845_ = lean_ctor_get(v_zipper_3841_, 1);
lean_inc_ref(v_spine_3845_);
v_openLeaf_x3f_3846_ = lean_ctor_get(v_zipper_3841_, 2);
v_blankLineFloor_x3f_3847_ = lean_ctor_get(v_zipper_3841_, 3);
v___x_3848_ = lean_array_get_size(v_spine_3845_);
v___x_3849_ = lean_nat_dec_eq(v___x_3848_, v_matched_3842_);
if (v___x_3849_ == 0)
{
lean_inc(v_openLeaf_x3f_3846_);
v_zipper_3813_ = v_zipper_3841_;
v_spine_3814_ = v_spine_3845_;
v_openLeaf_x3f_3815_ = v_openLeaf_x3f_3846_;
v_cursor_3816_ = v_cursor_3843_;
v_matched_3817_ = v_matched_3842_;
goto v___jp_3812_;
}
else
{
if (lean_obj_tag(v_openLeaf_x3f_3846_) == 1)
{
lean_object* v_val_3850_; 
v_val_3850_ = lean_ctor_get(v_openLeaf_x3f_3846_, 0);
lean_inc(v_val_3850_);
if (lean_obj_tag(v_val_3850_) == 0)
{
lean_object* v_lines_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3894_; 
v_lines_3851_ = lean_ctor_get(v_val_3850_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_val_3850_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3853_ = v_val_3850_;
v_isShared_3854_ = v_isSharedCheck_3894_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_lines_3851_);
lean_dec(v_val_3850_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3894_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_inc_ref(v_cursor_3843_);
v___x_3855_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_Cursor_skipIndent(v_s_3554_, v_cursor_3843_);
v___x_3856_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseSetextUnderline_x3f(v_s_3554_, v___x_3855_);
if (lean_obj_tag(v___x_3856_) == 1)
{
lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3889_; 
lean_inc(v_blankLineFloor_x3f_3847_);
lean_inc_ref(v_document_3844_);
lean_dec(v_matched_3842_);
v_isSharedCheck_3889_ = !lean_is_exclusive(v_zipper_3841_);
if (v_isSharedCheck_3889_ == 0)
{
lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; lean_object* v_unused_3893_; 
v_unused_3890_ = lean_ctor_get(v_zipper_3841_, 3);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_zipper_3841_, 2);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_zipper_3841_, 1);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_zipper_3841_, 0);
lean_dec(v_unused_3893_);
v___x_3858_ = v_zipper_3841_;
v_isShared_3859_ = v_isSharedCheck_3889_;
goto v_resetjp_3857_;
}
else
{
lean_dec(v_zipper_3841_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3889_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v_val_3860_; lean_object* v_fst_3861_; lean_object* v_snd_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v_fst_3865_; lean_object* v_snd_3866_; lean_object* v_pos_3867_; lean_object* v_stop_3868_; lean_object* v___x_3869_; lean_object* v___y_3871_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
v_val_3860_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_val_3860_);
lean_dec_ref_known(v___x_3856_, 1);
v_fst_3861_ = lean_ctor_get(v_val_3860_, 0);
lean_inc(v_fst_3861_);
v_snd_3862_ = lean_ctor_get(v_val_3860_, 1);
lean_inc(v_snd_3862_);
lean_dec(v_val_3860_);
v___x_3863_ = l_Lean_Markdown_InlineSource_ofLines(v_s_3554_, v_lines_3851_);
v___x_3864_ = l_Lean_Markdown_extractRefDefs(v_s_3554_, v___x_3863_);
v_fst_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_fst_3865_);
v_snd_3866_ = lean_ctor_get(v___x_3864_, 1);
lean_inc(v_snd_3866_);
lean_dec_ref(v___x_3864_);
v_pos_3867_ = lean_ctor_get(v_cursor_3843_, 0);
lean_inc(v_pos_3867_);
v_stop_3868_ = lean_ctor_get(v_cursor_3843_, 1);
lean_inc(v_stop_3868_);
lean_dec_ref(v_cursor_3843_);
v___x_3869_ = l_Lean_Markdown_subsliceClamped___redArg(v_pos_3867_, v_stop_3868_);
v___x_3880_ = lean_box(0);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 2, v___x_3880_);
v___x_3882_ = v___x_3858_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_document_3844_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_spine_3845_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3888_, 3, v_blankLineFloor_x3f_3847_);
v___x_3882_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3881_;
}
v___jp_3870_:
{
if (lean_obj_tag(v_snd_3866_) == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_dec(v_snd_3862_);
lean_dec(v_fst_3861_);
v___x_3872_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_3869_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v___x_3872_);
v___x_3874_ = v___x_3853_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Markdown_BlockZipper_openLeaf(v_s_3554_, v___y_3871_, v___x_3874_);
return v___x_3875_;
}
}
else
{
lean_object* v_val_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec_ref(v___x_3869_);
lean_del_object(v___x_3853_);
v_val_3877_ = lean_ctor_get(v_snd_3866_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v_snd_3866_, 1);
v___x_3878_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3878_, 0, v_fst_3861_);
lean_ctor_set(v___x_3878_, 1, v_val_3877_);
lean_ctor_set(v___x_3878_, 2, v_snd_3862_);
v___x_3879_ = l_Lean_Markdown_BlockZipper_addBlock(v_s_3554_, v___y_3871_, v___x_3878_);
return v___x_3879_;
}
}
v_reusejp_3881_:
{
lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3883_ = lean_array_get_size(v_fst_3865_);
v___x_3884_ = lean_nat_dec_lt(v___x_3832_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_dec(v_fst_3865_);
v___y_3871_ = v___x_3882_;
goto v___jp_3870_;
}
else
{
size_t v___x_3885_; size_t v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = ((size_t)0ULL);
v___x_3886_ = lean_usize_of_nat(v___x_3883_);
v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine_spec__0(v_s_3554_, v_fst_3865_, v___x_3885_, v___x_3886_, v___x_3882_);
lean_dec(v_fst_3865_);
v___y_3871_ = v___x_3887_;
goto v___jp_3870_;
}
}
}
}
else
{
lean_inc_ref(v_openLeaf_x3f_3846_);
lean_dec(v___x_3856_);
lean_del_object(v___x_3853_);
lean_dec_ref(v_lines_3851_);
v_zipper_3813_ = v_zipper_3841_;
v_spine_3814_ = v_spine_3845_;
v_openLeaf_x3f_3815_ = v_openLeaf_x3f_3846_;
v_cursor_3816_ = v_cursor_3843_;
v_matched_3817_ = v_matched_3842_;
goto v___jp_3812_;
}
}
}
else
{
lean_inc_ref(v_openLeaf_x3f_3846_);
lean_dec(v_val_3850_);
v_zipper_3813_ = v_zipper_3841_;
v_spine_3814_ = v_spine_3845_;
v_openLeaf_x3f_3815_ = v_openLeaf_x3f_3846_;
v_cursor_3816_ = v_cursor_3843_;
v_matched_3817_ = v_matched_3842_;
goto v___jp_3812_;
}
}
else
{
lean_inc(v_openLeaf_x3f_3846_);
v_zipper_3813_ = v_zipper_3841_;
v_spine_3814_ = v_spine_3845_;
v_openLeaf_x3f_3815_ = v_openLeaf_x3f_3846_;
v_cursor_3816_ = v_cursor_3843_;
v_matched_3817_ = v_matched_3842_;
goto v___jp_3812_;
}
}
}
else
{
lean_object* v_a_3895_; 
v_a_3895_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3838_, 2);
return v_a_3895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine___boxed(lean_object* v_s_3898_, lean_object* v_z_3899_, lean_object* v_line_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine(v_s_3898_, v_z_3899_, v_line_3900_);
lean_dec_ref(v_s_3898_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw_spec__0(lean_object* v_s_3902_, lean_object* v_indent_3903_, lean_object* v_as_3904_, size_t v_sz_3905_, size_t v_i_3906_, lean_object* v_b_3907_){
_start:
{
uint8_t v___x_3908_; 
v___x_3908_ = lean_usize_dec_lt(v_i_3906_, v_sz_3905_);
if (v___x_3908_ == 0)
{
return v_b_3907_;
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; size_t v___x_3912_; size_t v___x_3913_; 
v_a_3909_ = lean_array_uget_borrowed(v_as_3904_, v_i_3906_);
lean_inc(v_a_3909_);
v___x_3910_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_dropIndent(v_s_3902_, v_a_3909_, v_indent_3903_);
v___x_3911_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_processLine(v_s_3902_, v_b_3907_, v___x_3910_);
v___x_3912_ = ((size_t)1ULL);
v___x_3913_ = lean_usize_add(v_i_3906_, v___x_3912_);
v_i_3906_ = v___x_3913_;
v_b_3907_ = v___x_3911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw_spec__0___boxed(lean_object* v_s_3915_, lean_object* v_indent_3916_, lean_object* v_as_3917_, lean_object* v_sz_3918_, lean_object* v_i_3919_, lean_object* v_b_3920_){
_start:
{
size_t v_sz_boxed_3921_; size_t v_i_boxed_3922_; lean_object* v_res_3923_; 
v_sz_boxed_3921_ = lean_unbox_usize(v_sz_3918_);
lean_dec(v_sz_3918_);
v_i_boxed_3922_ = lean_unbox_usize(v_i_3919_);
lean_dec(v_i_3919_);
v_res_3923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw_spec__0(v_s_3915_, v_indent_3916_, v_as_3917_, v_sz_boxed_3921_, v_i_boxed_3922_, v_b_3920_);
lean_dec_ref(v_as_3917_);
lean_dec(v_indent_3916_);
lean_dec_ref(v_s_3915_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw(lean_object* v_s_3924_, lean_object* v_indent_3925_){
_start:
{
lean_object* v_startInclusive_3926_; lean_object* v_endExclusive_3927_; lean_object* v_z_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; size_t v_sz_3933_; size_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v_startInclusive_3926_ = lean_ctor_get(v_s_3924_, 1);
v_endExclusive_3927_ = lean_ctor_get(v_s_3924_, 2);
v_z_3928_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0, &l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_takeState___redArg___closed__0);
v___x_3929_ = lean_unsigned_to_nat(0u);
v___x_3930_ = lean_nat_sub(v_endExclusive_3927_, v_startInclusive_3926_);
v___x_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3929_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_splitLines(v_s_3924_, v___x_3931_);
v_sz_3933_ = lean_array_size(v___x_3932_);
v___x_3934_ = ((size_t)0ULL);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw_spec__0(v_s_3924_, v_indent_3925_, v___x_3932_, v_sz_3933_, v___x_3934_, v_z_3928_);
lean_dec_ref(v___x_3932_);
v___x_3936_ = l_Lean_Markdown_BlockZipper_finalize(v_s_3924_, v___x_3935_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw___boxed(lean_object* v_s_3937_, lean_object* v_indent_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw(v_s_3937_, v_indent_3938_);
lean_dec(v_indent_3938_);
lean_dec_ref(v_s_3937_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(lean_object* v_snd_3940_, lean_object* v_____r_3941_, lean_object* v_out_3942_){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3943_ = lean_unsigned_to_nat(1u);
v___x_3944_ = lean_nat_add(v_snd_3940_, v___x_3943_);
v___x_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3945_, 0, v_out_3942_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0___boxed(lean_object* v_snd_3947_, lean_object* v_____r_3948_, lean_object* v_out_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(v_snd_3947_, v_____r_3948_, v_out_3949_);
lean_dec(v_snd_3947_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg(lean_object* v_blocks_3956_, lean_object* v_s_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v___y_3960_; lean_object* v_fst_3964_; lean_object* v_snd_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_4036_; 
v_fst_3964_ = lean_ctor_get(v_a_3958_, 0);
v_snd_3965_ = lean_ctor_get(v_a_3958_, 1);
v_isSharedCheck_4036_ = !lean_is_exclusive(v_a_3958_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_3967_ = v_a_3958_;
v_isShared_3968_ = v_isSharedCheck_4036_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_snd_3965_);
lean_inc(v_fst_3964_);
lean_dec(v_a_3958_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_4036_;
goto v_resetjp_3966_;
}
v___jp_3959_:
{
if (lean_obj_tag(v___y_3960_) == 0)
{
lean_object* v_a_3961_; 
v_a_3961_ = lean_ctor_get(v___y_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___y_3960_, 1);
return v_a_3961_;
}
else
{
lean_object* v_a_3962_; 
v_a_3962_ = lean_ctor_get(v___y_3960_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___y_3960_, 1);
v_a_3958_ = v_a_3962_;
goto _start;
}
}
v_resetjp_3966_:
{
lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3969_ = lean_array_get_size(v_blocks_3956_);
v___x_3970_ = lean_nat_dec_lt(v_snd_3965_, v___x_3969_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3972_; 
if (v_isShared_3968_ == 0)
{
v___x_3972_ = v___x_3967_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_fst_3964_);
lean_ctor_set(v_reuseFailAlloc_3973_, 1, v_snd_3965_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
else
{
lean_object* v___x_3974_; 
lean_del_object(v___x_3967_);
v___x_3974_ = lean_array_fget(v_blocks_3956_, v_snd_3965_);
switch(lean_obj_tag(v___x_3974_))
{
case 0:
{
lean_object* v_content_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3992_; 
v_content_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_3992_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_content_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3992_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v_fst_3980_; lean_object* v_snd_3981_; lean_object* v___x_3982_; 
v___x_3979_ = l_Lean_Markdown_extractRefDefs(v_s_3957_, v_content_3975_);
v_fst_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_fst_3980_);
v_snd_3981_ = lean_ctor_get(v___x_3979_, 1);
lean_inc(v_snd_3981_);
lean_dec_ref(v___x_3979_);
v___x_3982_ = l_Array_append___redArg(v_fst_3964_, v_fst_3980_);
lean_dec(v_fst_3980_);
if (lean_obj_tag(v_snd_3981_) == 1)
{
lean_object* v_val_3983_; lean_object* v___x_3985_; 
v_val_3983_ = lean_ctor_get(v_snd_3981_, 0);
lean_inc(v_val_3983_);
lean_dec_ref_known(v_snd_3981_, 1);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v_val_3983_);
v___x_3985_ = v___x_3977_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_val_3983_);
v___x_3985_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = lean_array_push(v___x_3982_, v___x_3985_);
v___x_3987_ = lean_box(0);
v___x_3988_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(v_snd_3965_, v___x_3987_, v___x_3986_);
lean_dec(v_snd_3965_);
v___y_3960_ = v___x_3988_;
goto v___jp_3959_;
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec(v_snd_3981_);
lean_del_object(v___x_3977_);
v___x_3990_ = lean_box(0);
v___x_3991_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(v_snd_3965_, v___x_3990_, v___x_3982_);
lean_dec(v_snd_3965_);
v___y_3960_ = v___x_3991_;
goto v___jp_3959_;
}
}
}
case 6:
{
lean_object* v_markers_3993_; lean_object* v_children_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4005_; 
v_markers_3993_ = lean_ctor_get(v___x_3974_, 0);
v_children_3994_ = lean_ctor_get(v___x_3974_, 1);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3996_ = v___x_3974_;
v_isShared_3997_ = v_isSharedCheck_4005_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_children_3994_);
lean_inc(v_markers_3993_);
lean_dec(v___x_3974_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4005_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3998_; lean_object* v___x_4000_; 
v___x_3998_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs(v_s_3957_, v_children_3994_);
lean_dec_ref(v_children_3994_);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 1, v___x_3998_);
v___x_4000_ = v___x_3996_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_markers_3993_);
lean_ctor_set(v_reuseFailAlloc_4004_, 1, v___x_3998_);
v___x_4000_ = v_reuseFailAlloc_4004_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_array_push(v_fst_3964_, v___x_4000_);
v___x_4002_ = lean_box(0);
v___x_4003_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(v_snd_3965_, v___x_4002_, v___x_4001_);
lean_dec(v_snd_3965_);
v___y_3960_ = v___x_4003_;
goto v___jp_3959_;
}
}
}
case 7:
{
lean_object* v_kind_4006_; uint8_t v_tight_4007_; lean_object* v_items_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4019_; 
v_kind_4006_ = lean_ctor_get(v___x_3974_, 0);
v_tight_4007_ = lean_ctor_get_uint8(v___x_3974_, sizeof(void*)*2);
v_items_4008_ = lean_ctor_get(v___x_3974_, 1);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4010_ = v___x_3974_;
v_isShared_4011_ = v_isSharedCheck_4019_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_items_4008_);
lean_inc(v_kind_4006_);
lean_dec(v___x_3974_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4019_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4014_; 
v___x_4012_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs(v_s_3957_, v_items_4008_);
lean_dec_ref(v_items_4008_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 1, v___x_4012_);
v___x_4014_ = v___x_4010_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(7, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_kind_4006_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v___x_4012_);
lean_ctor_set_uint8(v_reuseFailAlloc_4018_, sizeof(void*)*2, v_tight_4007_);
v___x_4014_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = lean_array_push(v_fst_3964_, v___x_4014_);
v___x_4016_ = lean_box(0);
v___x_4017_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(v_snd_3965_, v___x_4016_, v___x_4015_);
lean_dec(v_snd_3965_);
v___y_3960_ = v___x_4017_;
goto v___jp_3959_;
}
}
}
case 8:
{
lean_object* v_marker_4020_; lean_object* v_children_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4032_; 
v_marker_4020_ = lean_ctor_get(v___x_3974_, 0);
v_children_4021_ = lean_ctor_get(v___x_3974_, 1);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4023_ = v___x_3974_;
v_isShared_4024_ = v_isSharedCheck_4032_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_children_4021_);
lean_inc(v_marker_4020_);
lean_dec(v___x_3974_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4032_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4025_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs(v_s_3957_, v_children_4021_);
lean_dec_ref(v_children_4021_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 1, v___x_4025_);
v___x_4027_ = v___x_4023_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_marker_4020_);
lean_ctor_set(v_reuseFailAlloc_4031_, 1, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4028_ = lean_array_push(v_fst_3964_, v___x_4027_);
v___x_4029_ = lean_box(0);
v___x_4030_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(v_snd_3965_, v___x_4029_, v___x_4028_);
lean_dec(v_snd_3965_);
v___y_3960_ = v___x_4030_;
goto v___jp_3959_;
}
}
}
default: 
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4033_ = lean_array_push(v_fst_3964_, v___x_3974_);
v___x_4034_ = lean_box(0);
v___x_4035_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___lam__0(v_snd_3965_, v___x_4034_, v___x_4033_);
lean_dec(v_snd_3965_);
v___y_3960_ = v___x_4035_;
goto v___jp_3959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs(lean_object* v_s_4037_, lean_object* v_blocks_4038_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v_fst_4041_; 
v___x_4039_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___closed__1));
v___x_4040_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg(v_blocks_4038_, v_s_4037_, v___x_4039_);
v_fst_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_fst_4041_);
lean_dec_ref(v___x_4040_);
return v_fst_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs___boxed(lean_object* v_s_4042_, lean_object* v_blocks_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs(v_s_4042_, v_blocks_4043_);
lean_dec_ref(v_blocks_4043_);
lean_dec_ref(v_s_4042_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg___boxed(lean_object* v_blocks_4045_, lean_object* v_s_4046_, lean_object* v_a_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg(v_blocks_4045_, v_s_4046_, v_a_4047_);
lean_dec_ref(v_s_4046_);
lean_dec_ref(v_blocks_4045_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0(lean_object* v_blocks_4049_, lean_object* v_s_4050_, lean_object* v_inst_4051_, lean_object* v_a_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___redArg(v_blocks_4049_, v_s_4050_, v_a_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0___boxed(lean_object* v_blocks_4054_, lean_object* v_s_4055_, lean_object* v_inst_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs_spec__0(v_blocks_4054_, v_s_4055_, v_inst_4056_, v_a_4057_);
lean_dec_ref(v_s_4055_);
lean_dec_ref(v_blocks_4054_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_4059_, lean_object* v_x_4060_){
_start:
{
if (lean_obj_tag(v_x_4060_) == 0)
{
return v_x_4059_;
}
else
{
lean_object* v_key_4061_; lean_object* v_value_4062_; lean_object* v_tail_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4086_; 
v_key_4061_ = lean_ctor_get(v_x_4060_, 0);
v_value_4062_ = lean_ctor_get(v_x_4060_, 1);
v_tail_4063_ = lean_ctor_get(v_x_4060_, 2);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_x_4060_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4065_ = v_x_4060_;
v_isShared_4066_ = v_isSharedCheck_4086_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_tail_4063_);
lean_inc(v_value_4062_);
lean_inc(v_key_4061_);
lean_dec(v_x_4060_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4086_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; uint64_t v___x_4068_; uint64_t v___x_4069_; uint64_t v___x_4070_; uint64_t v_fold_4071_; uint64_t v___x_4072_; uint64_t v___x_4073_; uint64_t v___x_4074_; size_t v___x_4075_; size_t v___x_4076_; size_t v___x_4077_; size_t v___x_4078_; size_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4082_; 
v___x_4067_ = lean_array_get_size(v_x_4059_);
v___x_4068_ = l_Lean_Markdown_instHashableLinkLabel_hash(v_key_4061_);
v___x_4069_ = 32ULL;
v___x_4070_ = lean_uint64_shift_right(v___x_4068_, v___x_4069_);
v_fold_4071_ = lean_uint64_xor(v___x_4068_, v___x_4070_);
v___x_4072_ = 16ULL;
v___x_4073_ = lean_uint64_shift_right(v_fold_4071_, v___x_4072_);
v___x_4074_ = lean_uint64_xor(v_fold_4071_, v___x_4073_);
v___x_4075_ = lean_uint64_to_usize(v___x_4074_);
v___x_4076_ = lean_usize_of_nat(v___x_4067_);
v___x_4077_ = ((size_t)1ULL);
v___x_4078_ = lean_usize_sub(v___x_4076_, v___x_4077_);
v___x_4079_ = lean_usize_land(v___x_4075_, v___x_4078_);
v___x_4080_ = lean_array_uget_borrowed(v_x_4059_, v___x_4079_);
lean_inc(v___x_4080_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 2, v___x_4080_);
v___x_4082_ = v___x_4065_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_key_4061_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_value_4062_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v___x_4080_);
v___x_4082_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4083_; 
v___x_4083_ = lean_array_uset(v_x_4059_, v___x_4079_, v___x_4082_);
v_x_4059_ = v___x_4083_;
v_x_4060_ = v_tail_4063_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2___redArg(lean_object* v_i_4087_, lean_object* v_source_4088_, lean_object* v_target_4089_){
_start:
{
lean_object* v___x_4090_; uint8_t v___x_4091_; 
v___x_4090_ = lean_array_get_size(v_source_4088_);
v___x_4091_ = lean_nat_dec_lt(v_i_4087_, v___x_4090_);
if (v___x_4091_ == 0)
{
lean_dec_ref(v_source_4088_);
lean_dec(v_i_4087_);
return v_target_4089_;
}
else
{
lean_object* v_es_4092_; lean_object* v___x_4093_; lean_object* v_source_4094_; lean_object* v_target_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_es_4092_ = lean_array_fget(v_source_4088_, v_i_4087_);
v___x_4093_ = lean_box(0);
v_source_4094_ = lean_array_fset(v_source_4088_, v_i_4087_, v___x_4093_);
v_target_4095_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2_spec__4___redArg(v_target_4089_, v_es_4092_);
v___x_4096_ = lean_unsigned_to_nat(1u);
v___x_4097_ = lean_nat_add(v_i_4087_, v___x_4096_);
lean_dec(v_i_4087_);
v_i_4087_ = v___x_4097_;
v_source_4088_ = v_source_4094_;
v_target_4089_ = v_target_4095_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1___redArg(lean_object* v_data_4099_){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v_nbuckets_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4100_ = lean_array_get_size(v_data_4099_);
v___x_4101_ = lean_unsigned_to_nat(2u);
v_nbuckets_4102_ = lean_nat_mul(v___x_4100_, v___x_4101_);
v___x_4103_ = lean_unsigned_to_nat(0u);
v___x_4104_ = lean_box(0);
v___x_4105_ = lean_mk_array(v_nbuckets_4102_, v___x_4104_);
v___x_4106_ = lean_array_propagate_mark(v_data_4099_, v___x_4105_);
v___x_4107_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2___redArg(v___x_4103_, v_data_4099_, v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg(lean_object* v_a_4108_, lean_object* v_x_4109_){
_start:
{
if (lean_obj_tag(v_x_4109_) == 0)
{
uint8_t v___x_4110_; 
v___x_4110_ = 0;
return v___x_4110_;
}
else
{
lean_object* v_key_4111_; lean_object* v_tail_4112_; uint8_t v___x_4113_; 
v_key_4111_ = lean_ctor_get(v_x_4109_, 0);
v_tail_4112_ = lean_ctor_get(v_x_4109_, 2);
v___x_4113_ = l_Lean_Markdown_instBEqLinkLabel_beq(v_key_4111_, v_a_4108_);
if (v___x_4113_ == 0)
{
v_x_4109_ = v_tail_4112_;
goto _start;
}
else
{
return v___x_4113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_4115_, lean_object* v_x_4116_){
_start:
{
uint8_t v_res_4117_; lean_object* v_r_4118_; 
v_res_4117_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg(v_a_4115_, v_x_4116_);
lean_dec(v_x_4116_);
lean_dec_ref(v_a_4115_);
v_r_4118_ = lean_box(v_res_4117_);
return v_r_4118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0___redArg(lean_object* v_m_4119_, lean_object* v_a_4120_, lean_object* v_b_4121_){
_start:
{
lean_object* v_size_4122_; lean_object* v_buckets_4123_; lean_object* v___x_4124_; uint64_t v___x_4125_; uint64_t v___x_4126_; uint64_t v___x_4127_; uint64_t v_fold_4128_; uint64_t v___x_4129_; uint64_t v___x_4130_; uint64_t v___x_4131_; size_t v___x_4132_; size_t v___x_4133_; size_t v___x_4134_; size_t v___x_4135_; size_t v___x_4136_; lean_object* v_bkt_4137_; uint8_t v___x_4138_; 
v_size_4122_ = lean_ctor_get(v_m_4119_, 0);
v_buckets_4123_ = lean_ctor_get(v_m_4119_, 1);
v___x_4124_ = lean_array_get_size(v_buckets_4123_);
v___x_4125_ = l_Lean_Markdown_instHashableLinkLabel_hash(v_a_4120_);
v___x_4126_ = 32ULL;
v___x_4127_ = lean_uint64_shift_right(v___x_4125_, v___x_4126_);
v_fold_4128_ = lean_uint64_xor(v___x_4125_, v___x_4127_);
v___x_4129_ = 16ULL;
v___x_4130_ = lean_uint64_shift_right(v_fold_4128_, v___x_4129_);
v___x_4131_ = lean_uint64_xor(v_fold_4128_, v___x_4130_);
v___x_4132_ = lean_uint64_to_usize(v___x_4131_);
v___x_4133_ = lean_usize_of_nat(v___x_4124_);
v___x_4134_ = ((size_t)1ULL);
v___x_4135_ = lean_usize_sub(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_usize_land(v___x_4132_, v___x_4135_);
v_bkt_4137_ = lean_array_uget_borrowed(v_buckets_4123_, v___x_4136_);
v___x_4138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg(v_a_4120_, v_bkt_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4159_; 
lean_inc_ref(v_buckets_4123_);
lean_inc(v_size_4122_);
v_isSharedCheck_4159_ = !lean_is_exclusive(v_m_4119_);
if (v_isSharedCheck_4159_ == 0)
{
lean_object* v_unused_4160_; lean_object* v_unused_4161_; 
v_unused_4160_ = lean_ctor_get(v_m_4119_, 1);
lean_dec(v_unused_4160_);
v_unused_4161_ = lean_ctor_get(v_m_4119_, 0);
lean_dec(v_unused_4161_);
v___x_4140_ = v_m_4119_;
v_isShared_4141_ = v_isSharedCheck_4159_;
goto v_resetjp_4139_;
}
else
{
lean_dec(v_m_4119_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4159_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4142_; lean_object* v_size_x27_4143_; lean_object* v___x_4144_; lean_object* v_buckets_x27_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; uint8_t v___x_4151_; 
v___x_4142_ = lean_unsigned_to_nat(1u);
v_size_x27_4143_ = lean_nat_add(v_size_4122_, v___x_4142_);
lean_dec(v_size_4122_);
lean_inc(v_bkt_4137_);
v___x_4144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4144_, 0, v_a_4120_);
lean_ctor_set(v___x_4144_, 1, v_b_4121_);
lean_ctor_set(v___x_4144_, 2, v_bkt_4137_);
v_buckets_x27_4145_ = lean_array_uset(v_buckets_4123_, v___x_4136_, v___x_4144_);
v___x_4146_ = lean_unsigned_to_nat(4u);
v___x_4147_ = lean_nat_mul(v_size_x27_4143_, v___x_4146_);
v___x_4148_ = lean_unsigned_to_nat(3u);
v___x_4149_ = lean_nat_div(v___x_4147_, v___x_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_array_get_size(v_buckets_x27_4145_);
v___x_4151_ = lean_nat_dec_le(v___x_4149_, v___x_4150_);
lean_dec(v___x_4149_);
if (v___x_4151_ == 0)
{
lean_object* v_val_4152_; lean_object* v___x_4154_; 
v_val_4152_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1___redArg(v_buckets_x27_4145_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 1, v_val_4152_);
lean_ctor_set(v___x_4140_, 0, v_size_x27_4143_);
v___x_4154_ = v___x_4140_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_size_x27_4143_);
lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_val_4152_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
else
{
lean_object* v___x_4157_; 
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 1, v_buckets_x27_4145_);
lean_ctor_set(v___x_4140_, 0, v_size_x27_4143_);
v___x_4157_ = v___x_4140_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_size_x27_4143_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_buckets_x27_4145_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_dec(v_b_4121_);
lean_dec_ref(v_a_4120_);
return v_m_4119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__1(lean_object* v_s_4162_, lean_object* v_as_4163_, size_t v_i_4164_, size_t v_stop_4165_, lean_object* v_b_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v_fst_4169_; lean_object* v_snd_4170_; lean_object* v___y_4175_; uint8_t v___x_4178_; 
v___x_4178_ = lean_usize_dec_eq(v_i_4164_, v_stop_4165_);
if (v___x_4178_ == 0)
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_array_uget(v_as_4163_, v_i_4164_);
switch(lean_obj_tag(v___x_4179_))
{
case 9:
{
lean_object* v_m_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4191_; 
v_m_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4191_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_m_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4191_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v_label_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4188_; 
v_label_4184_ = lean_ctor_get(v_m_4180_, 1);
v___x_4185_ = lean_box(0);
v___x_4186_ = l_Lean_Markdown_normalizeLabel(v_s_4162_, v_label_4184_);
if (v_isShared_4183_ == 0)
{
lean_ctor_set_tag(v___x_4182_, 0);
v___x_4188_ = v___x_4182_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_m_4180_);
v___x_4188_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0___redArg(v___y_4167_, v___x_4186_, v___x_4188_);
v_fst_4169_ = v___x_4185_;
v_snd_4170_ = v___x_4189_;
goto v___jp_4168_;
}
}
}
case 6:
{
lean_object* v_children_4192_; lean_object* v___x_4193_; 
v_children_4192_ = lean_ctor_get(v___x_4179_, 1);
lean_inc_ref(v_children_4192_);
lean_dec_ref_known(v___x_4179_, 2);
v___x_4193_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go(v_s_4162_, v_children_4192_, v___y_4167_);
lean_dec_ref(v_children_4192_);
v___y_4175_ = v___x_4193_;
goto v___jp_4174_;
}
case 7:
{
lean_object* v_items_4194_; lean_object* v___x_4195_; 
v_items_4194_ = lean_ctor_get(v___x_4179_, 1);
lean_inc_ref(v_items_4194_);
lean_dec_ref_known(v___x_4179_, 2);
v___x_4195_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go(v_s_4162_, v_items_4194_, v___y_4167_);
lean_dec_ref(v_items_4194_);
v___y_4175_ = v___x_4195_;
goto v___jp_4174_;
}
case 8:
{
lean_object* v_children_4196_; lean_object* v___x_4197_; 
v_children_4196_ = lean_ctor_get(v___x_4179_, 1);
lean_inc_ref(v_children_4196_);
lean_dec_ref_known(v___x_4179_, 2);
v___x_4197_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go(v_s_4162_, v_children_4196_, v___y_4167_);
lean_dec_ref(v_children_4196_);
v___y_4175_ = v___x_4197_;
goto v___jp_4174_;
}
default: 
{
lean_object* v___x_4198_; 
lean_dec(v___x_4179_);
v___x_4198_ = lean_box(0);
v_fst_4169_ = v___x_4198_;
v_snd_4170_ = v___y_4167_;
goto v___jp_4168_;
}
}
}
else
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4199_, 0, v_b_4166_);
lean_ctor_set(v___x_4199_, 1, v___y_4167_);
return v___x_4199_;
}
v___jp_4168_:
{
size_t v___x_4171_; size_t v___x_4172_; 
v___x_4171_ = ((size_t)1ULL);
v___x_4172_ = lean_usize_add(v_i_4164_, v___x_4171_);
v_i_4164_ = v___x_4172_;
v_b_4166_ = v_fst_4169_;
v___y_4167_ = v_snd_4170_;
goto _start;
}
v___jp_4174_:
{
lean_object* v_fst_4176_; lean_object* v_snd_4177_; 
v_fst_4176_ = lean_ctor_get(v___y_4175_, 0);
lean_inc(v_fst_4176_);
v_snd_4177_ = lean_ctor_get(v___y_4175_, 1);
lean_inc(v_snd_4177_);
lean_dec_ref(v___y_4175_);
v_fst_4169_ = v_fst_4176_;
v_snd_4170_ = v_snd_4177_;
goto v___jp_4168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go(lean_object* v_s_4200_, lean_object* v_bs_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_array_get_size(v_bs_4201_);
v___x_4205_ = lean_box(0);
v___x_4206_ = lean_nat_dec_lt(v___x_4203_, v___x_4204_);
if (v___x_4206_ == 0)
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v_a_4202_);
return v___x_4207_;
}
else
{
size_t v___x_4208_; size_t v___x_4209_; lean_object* v___x_4210_; 
v___x_4208_ = ((size_t)0ULL);
v___x_4209_ = lean_usize_of_nat(v___x_4204_);
v___x_4210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__1(v_s_4200_, v_bs_4201_, v___x_4208_, v___x_4209_, v___x_4205_, v_a_4202_);
return v___x_4210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go___boxed(lean_object* v_s_4211_, lean_object* v_bs_4212_, lean_object* v_a_4213_){
_start:
{
lean_object* v_res_4214_; 
v_res_4214_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go(v_s_4211_, v_bs_4212_, v_a_4213_);
lean_dec_ref(v_bs_4212_);
lean_dec_ref(v_s_4211_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__1___boxed(lean_object* v_s_4215_, lean_object* v_as_4216_, lean_object* v_i_4217_, lean_object* v_stop_4218_, lean_object* v_b_4219_, lean_object* v___y_4220_){
_start:
{
size_t v_i_boxed_4221_; size_t v_stop_boxed_4222_; lean_object* v_res_4223_; 
v_i_boxed_4221_ = lean_unbox_usize(v_i_4217_);
lean_dec(v_i_4217_);
v_stop_boxed_4222_ = lean_unbox_usize(v_stop_4218_);
lean_dec(v_stop_4218_);
v_res_4223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__1(v_s_4215_, v_as_4216_, v_i_boxed_4221_, v_stop_boxed_4222_, v_b_4219_, v___y_4220_);
lean_dec_ref(v_as_4216_);
lean_dec_ref(v_s_4215_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0(lean_object* v_00_u03b2_4224_, lean_object* v_m_4225_, lean_object* v_a_4226_, lean_object* v_b_4227_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0___redArg(v_m_4225_, v_a_4226_, v_b_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0(lean_object* v_00_u03b2_4229_, lean_object* v_a_4230_, lean_object* v_x_4231_){
_start:
{
uint8_t v___x_4232_; 
v___x_4232_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg(v_a_4230_, v_x_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4233_, lean_object* v_a_4234_, lean_object* v_x_4235_){
_start:
{
uint8_t v_res_4236_; lean_object* v_r_4237_; 
v_res_4236_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0(v_00_u03b2_4233_, v_a_4234_, v_x_4235_);
lean_dec(v_x_4235_);
lean_dec_ref(v_a_4234_);
v_r_4237_ = lean_box(v_res_4236_);
return v_r_4237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1(lean_object* v_00_u03b2_4238_, lean_object* v_data_4239_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1___redArg(v_data_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4241_, lean_object* v_i_4242_, lean_object* v_source_4243_, lean_object* v_target_4244_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2___redArg(v_i_4242_, v_source_4243_, v_target_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_4246_, lean_object* v_x_4247_, lean_object* v_x_4248_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1_spec__2_spec__4___redArg(v_x_4247_, v_x_4248_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___redArg(lean_object* v_hi_4250_, lean_object* v_pivot_4251_, lean_object* v_as_4252_, lean_object* v_i_4253_, lean_object* v_k_4254_){
_start:
{
uint8_t v___x_4255_; 
v___x_4255_ = lean_nat_dec_lt(v_k_4254_, v_hi_4250_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
lean_dec(v_k_4254_);
v___x_4256_ = lean_array_fswap(v_as_4252_, v_i_4253_, v_hi_4250_);
v___x_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4257_, 0, v_i_4253_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
return v___x_4257_;
}
else
{
lean_object* v___x_4258_; lean_object* v_fst_4259_; lean_object* v_fst_4260_; uint8_t v___x_4261_; 
v___x_4258_ = lean_array_fget_borrowed(v_as_4252_, v_k_4254_);
v_fst_4259_ = lean_ctor_get(v___x_4258_, 0);
v_fst_4260_ = lean_ctor_get(v_pivot_4251_, 0);
v___x_4261_ = lean_string_dec_lt(v_fst_4259_, v_fst_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = lean_nat_add(v_k_4254_, v___x_4262_);
lean_dec(v_k_4254_);
v_k_4254_ = v___x_4263_;
goto _start;
}
else
{
lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4265_ = lean_array_fswap(v_as_4252_, v_i_4253_, v_k_4254_);
v___x_4266_ = lean_unsigned_to_nat(1u);
v___x_4267_ = lean_nat_add(v_i_4253_, v___x_4266_);
lean_dec(v_i_4253_);
v___x_4268_ = lean_nat_add(v_k_4254_, v___x_4266_);
lean_dec(v_k_4254_);
v_as_4252_ = v___x_4265_;
v_i_4253_ = v___x_4267_;
v_k_4254_ = v___x_4268_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___redArg___boxed(lean_object* v_hi_4270_, lean_object* v_pivot_4271_, lean_object* v_as_4272_, lean_object* v_i_4273_, lean_object* v_k_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___redArg(v_hi_4270_, v_pivot_4271_, v_as_4272_, v_i_4273_, v_k_4274_);
lean_dec_ref(v_pivot_4271_);
lean_dec(v_hi_4270_);
return v_res_4275_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0(lean_object* v_x1_4276_, lean_object* v_x2_4277_){
_start:
{
lean_object* v_fst_4278_; lean_object* v_fst_4279_; uint8_t v___x_4280_; 
v_fst_4278_ = lean_ctor_get(v_x1_4276_, 0);
v_fst_4279_ = lean_ctor_get(v_x2_4277_, 0);
v___x_4280_ = lean_string_dec_lt(v_fst_4278_, v_fst_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0___boxed(lean_object* v_x1_4281_, lean_object* v_x2_4282_){
_start:
{
uint8_t v_res_4283_; lean_object* v_r_4284_; 
v_res_4283_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0(v_x1_4281_, v_x2_4282_);
lean_dec_ref(v_x2_4282_);
lean_dec_ref(v_x1_4281_);
v_r_4284_ = lean_box(v_res_4283_);
return v_r_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg(lean_object* v_n_4285_, lean_object* v_as_4286_, lean_object* v_lo_4287_, lean_object* v_hi_4288_){
_start:
{
lean_object* v___y_4290_; uint8_t v___x_4300_; 
v___x_4300_ = lean_nat_dec_lt(v_lo_4287_, v_hi_4288_);
if (v___x_4300_ == 0)
{
lean_dec(v_lo_4287_);
return v_as_4286_;
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v_mid_4303_; lean_object* v___y_4305_; lean_object* v___y_4311_; lean_object* v___x_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; 
v___x_4301_ = lean_nat_add(v_lo_4287_, v_hi_4288_);
v___x_4302_ = lean_unsigned_to_nat(1u);
v_mid_4303_ = lean_nat_shiftr(v___x_4301_, v___x_4302_);
lean_dec(v___x_4301_);
v___x_4316_ = lean_array_fget_borrowed(v_as_4286_, v_mid_4303_);
v___x_4317_ = lean_array_fget_borrowed(v_as_4286_, v_lo_4287_);
v___x_4318_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0(v___x_4316_, v___x_4317_);
if (v___x_4318_ == 0)
{
v___y_4311_ = v_as_4286_;
goto v___jp_4310_;
}
else
{
lean_object* v___x_4319_; 
v___x_4319_ = lean_array_fswap(v_as_4286_, v_lo_4287_, v_mid_4303_);
v___y_4311_ = v___x_4319_;
goto v___jp_4310_;
}
v___jp_4304_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; 
v___x_4306_ = lean_array_fget_borrowed(v___y_4305_, v_mid_4303_);
v___x_4307_ = lean_array_fget_borrowed(v___y_4305_, v_hi_4288_);
v___x_4308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0(v___x_4306_, v___x_4307_);
if (v___x_4308_ == 0)
{
lean_dec(v_mid_4303_);
v___y_4290_ = v___y_4305_;
goto v___jp_4289_;
}
else
{
lean_object* v___x_4309_; 
v___x_4309_ = lean_array_fswap(v___y_4305_, v_mid_4303_, v_hi_4288_);
lean_dec(v_mid_4303_);
v___y_4290_ = v___x_4309_;
goto v___jp_4289_;
}
}
v___jp_4310_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v___x_4312_ = lean_array_fget_borrowed(v___y_4311_, v_hi_4288_);
v___x_4313_ = lean_array_fget_borrowed(v___y_4311_, v_lo_4287_);
v___x_4314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___lam__0(v___x_4312_, v___x_4313_);
if (v___x_4314_ == 0)
{
v___y_4305_ = v___y_4311_;
goto v___jp_4304_;
}
else
{
lean_object* v___x_4315_; 
v___x_4315_ = lean_array_fswap(v___y_4311_, v_lo_4287_, v_hi_4288_);
v___y_4305_ = v___x_4315_;
goto v___jp_4304_;
}
}
}
v___jp_4289_:
{
lean_object* v_pivot_4291_; lean_object* v___x_4292_; lean_object* v_fst_4293_; lean_object* v_snd_4294_; uint8_t v___x_4295_; 
v_pivot_4291_ = lean_array_fget(v___y_4290_, v_hi_4288_);
lean_inc_n(v_lo_4287_, 2);
v___x_4292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___redArg(v_hi_4288_, v_pivot_4291_, v___y_4290_, v_lo_4287_, v_lo_4287_);
lean_dec(v_pivot_4291_);
v_fst_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_fst_4293_);
v_snd_4294_ = lean_ctor_get(v___x_4292_, 1);
lean_inc(v_snd_4294_);
lean_dec_ref(v___x_4292_);
v___x_4295_ = lean_nat_dec_le(v_hi_4288_, v_fst_4293_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4296_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg(v_n_4285_, v_snd_4294_, v_lo_4287_, v_fst_4293_);
v___x_4297_ = lean_unsigned_to_nat(1u);
v___x_4298_ = lean_nat_add(v_fst_4293_, v___x_4297_);
lean_dec(v_fst_4293_);
v_as_4286_ = v___x_4296_;
v_lo_4287_ = v___x_4298_;
goto _start;
}
else
{
lean_dec(v_fst_4293_);
lean_dec(v_lo_4287_);
return v_snd_4294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg___boxed(lean_object* v_n_4320_, lean_object* v_as_4321_, lean_object* v_lo_4322_, lean_object* v_hi_4323_){
_start:
{
lean_object* v_res_4324_; 
v_res_4324_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg(v_n_4320_, v_as_4321_, v_lo_4322_, v_hi_4323_);
lean_dec(v_hi_4323_);
lean_dec(v_n_4320_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__5(lean_object* v_x_4325_, lean_object* v_x_4326_){
_start:
{
if (lean_obj_tag(v_x_4326_) == 0)
{
return v_x_4325_;
}
else
{
lean_object* v_key_4327_; lean_object* v_value_4328_; lean_object* v_tail_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; 
v_key_4327_ = lean_ctor_get(v_x_4326_, 0);
v_value_4328_ = lean_ctor_get(v_x_4326_, 1);
v_tail_4329_ = lean_ctor_get(v_x_4326_, 2);
lean_inc(v_value_4328_);
lean_inc(v_key_4327_);
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v_key_4327_);
lean_ctor_set(v___x_4330_, 1, v_value_4328_);
v___x_4331_ = lean_array_push(v_x_4325_, v___x_4330_);
v_x_4325_ = v___x_4331_;
v_x_4326_ = v_tail_4329_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__5___boxed(lean_object* v_x_4333_, lean_object* v_x_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__5(v_x_4333_, v_x_4334_);
lean_dec(v_x_4334_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__6(lean_object* v_as_4336_, size_t v_i_4337_, size_t v_stop_4338_, lean_object* v_b_4339_){
_start:
{
uint8_t v___x_4340_; 
v___x_4340_ = lean_usize_dec_eq(v_i_4337_, v_stop_4338_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4341_; lean_object* v___x_4342_; size_t v___x_4343_; size_t v___x_4344_; 
v___x_4341_ = lean_array_uget_borrowed(v_as_4336_, v_i_4337_);
v___x_4342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__5(v_b_4339_, v___x_4341_);
v___x_4343_ = ((size_t)1ULL);
v___x_4344_ = lean_usize_add(v_i_4337_, v___x_4343_);
v_i_4337_ = v___x_4344_;
v_b_4339_ = v___x_4342_;
goto _start;
}
else
{
return v_b_4339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__6___boxed(lean_object* v_as_4346_, lean_object* v_i_4347_, lean_object* v_stop_4348_, lean_object* v_b_4349_){
_start:
{
size_t v_i_boxed_4350_; size_t v_stop_boxed_4351_; lean_object* v_res_4352_; 
v_i_boxed_4350_ = lean_unbox_usize(v_i_4347_);
lean_dec(v_i_4347_);
v_stop_boxed_4351_ = lean_unbox_usize(v_stop_4348_);
lean_dec(v_stop_4348_);
v_res_4352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__6(v_as_4346_, v_i_boxed_4350_, v_stop_boxed_4351_, v_b_4349_);
lean_dec_ref(v_as_4346_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__3(lean_object* v_as_4353_, size_t v_i_4354_, size_t v_stop_4355_, lean_object* v_b_4356_){
_start:
{
uint8_t v___x_4357_; 
v___x_4357_ = lean_usize_dec_eq(v_i_4354_, v_stop_4355_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v_fst_4359_; lean_object* v_snd_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; size_t v___x_4363_; size_t v___x_4364_; 
v___x_4358_ = lean_array_uget_borrowed(v_as_4353_, v_i_4354_);
v_fst_4359_ = lean_ctor_get(v___x_4358_, 0);
v_snd_4360_ = lean_ctor_get(v___x_4358_, 1);
lean_inc(v_fst_4359_);
v___x_4361_ = l_Lean_Markdown_LinkLabel_ofString(v_fst_4359_);
lean_inc(v_snd_4360_);
v___x_4362_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0___redArg(v_b_4356_, v___x_4361_, v_snd_4360_);
v___x_4363_ = ((size_t)1ULL);
v___x_4364_ = lean_usize_add(v_i_4354_, v___x_4363_);
v_i_4354_ = v___x_4364_;
v_b_4356_ = v___x_4362_;
goto _start;
}
else
{
return v_b_4356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__3___boxed(lean_object* v_as_4366_, lean_object* v_i_4367_, lean_object* v_stop_4368_, lean_object* v_b_4369_){
_start:
{
size_t v_i_boxed_4370_; size_t v_stop_boxed_4371_; lean_object* v_res_4372_; 
v_i_boxed_4370_ = lean_unbox_usize(v_i_4367_);
lean_dec(v_i_4367_);
v_stop_boxed_4371_ = lean_unbox_usize(v_stop_4368_);
lean_dec(v_stop_4368_);
v_res_4372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__3(v_as_4366_, v_i_boxed_4370_, v_stop_boxed_4371_, v_b_4369_);
lean_dec_ref(v_as_4366_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0_spec__0___redArg(lean_object* v_a_4373_, lean_object* v_b_4374_, lean_object* v_x_4375_){
_start:
{
if (lean_obj_tag(v_x_4375_) == 0)
{
lean_dec(v_b_4374_);
lean_dec_ref(v_a_4373_);
return v_x_4375_;
}
else
{
lean_object* v_key_4376_; lean_object* v_value_4377_; lean_object* v_tail_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4390_; 
v_key_4376_ = lean_ctor_get(v_x_4375_, 0);
v_value_4377_ = lean_ctor_get(v_x_4375_, 1);
v_tail_4378_ = lean_ctor_get(v_x_4375_, 2);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_x_4375_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4380_ = v_x_4375_;
v_isShared_4381_ = v_isSharedCheck_4390_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_tail_4378_);
lean_inc(v_value_4377_);
lean_inc(v_key_4376_);
lean_dec(v_x_4375_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4390_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
uint8_t v___x_4382_; 
v___x_4382_ = l_Lean_Markdown_instBEqLinkLabel_beq(v_key_4376_, v_a_4373_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4385_; 
v___x_4383_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0_spec__0___redArg(v_a_4373_, v_b_4374_, v_tail_4378_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 2, v___x_4383_);
v___x_4385_ = v___x_4380_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_key_4376_);
lean_ctor_set(v_reuseFailAlloc_4386_, 1, v_value_4377_);
lean_ctor_set(v_reuseFailAlloc_4386_, 2, v___x_4383_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
else
{
lean_object* v___x_4388_; 
lean_dec(v_value_4377_);
lean_dec(v_key_4376_);
if (v_isShared_4381_ == 0)
{
lean_ctor_set(v___x_4380_, 1, v_b_4374_);
lean_ctor_set(v___x_4380_, 0, v_a_4373_);
v___x_4388_ = v___x_4380_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4373_);
lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_b_4374_);
lean_ctor_set(v_reuseFailAlloc_4389_, 2, v_tail_4378_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0___redArg(lean_object* v_m_4391_, lean_object* v_a_4392_, lean_object* v_b_4393_){
_start:
{
lean_object* v_size_4394_; lean_object* v_buckets_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4438_; 
v_size_4394_ = lean_ctor_get(v_m_4391_, 0);
v_buckets_4395_ = lean_ctor_get(v_m_4391_, 1);
v_isSharedCheck_4438_ = !lean_is_exclusive(v_m_4391_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4397_ = v_m_4391_;
v_isShared_4398_ = v_isSharedCheck_4438_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_buckets_4395_);
lean_inc(v_size_4394_);
lean_dec(v_m_4391_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4438_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; uint64_t v___x_4400_; uint64_t v___x_4401_; uint64_t v___x_4402_; uint64_t v_fold_4403_; uint64_t v___x_4404_; uint64_t v___x_4405_; uint64_t v___x_4406_; size_t v___x_4407_; size_t v___x_4408_; size_t v___x_4409_; size_t v___x_4410_; size_t v___x_4411_; lean_object* v_bkt_4412_; uint8_t v___x_4413_; 
v___x_4399_ = lean_array_get_size(v_buckets_4395_);
v___x_4400_ = l_Lean_Markdown_instHashableLinkLabel_hash(v_a_4392_);
v___x_4401_ = 32ULL;
v___x_4402_ = lean_uint64_shift_right(v___x_4400_, v___x_4401_);
v_fold_4403_ = lean_uint64_xor(v___x_4400_, v___x_4402_);
v___x_4404_ = 16ULL;
v___x_4405_ = lean_uint64_shift_right(v_fold_4403_, v___x_4404_);
v___x_4406_ = lean_uint64_xor(v_fold_4403_, v___x_4405_);
v___x_4407_ = lean_uint64_to_usize(v___x_4406_);
v___x_4408_ = lean_usize_of_nat(v___x_4399_);
v___x_4409_ = ((size_t)1ULL);
v___x_4410_ = lean_usize_sub(v___x_4408_, v___x_4409_);
v___x_4411_ = lean_usize_land(v___x_4407_, v___x_4410_);
v_bkt_4412_ = lean_array_uget_borrowed(v_buckets_4395_, v___x_4411_);
v___x_4413_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__0___redArg(v_a_4392_, v_bkt_4412_);
if (v___x_4413_ == 0)
{
lean_object* v___x_4414_; lean_object* v_size_x27_4415_; lean_object* v___x_4416_; lean_object* v_buckets_x27_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4414_ = lean_unsigned_to_nat(1u);
v_size_x27_4415_ = lean_nat_add(v_size_4394_, v___x_4414_);
lean_dec(v_size_4394_);
lean_inc(v_bkt_4412_);
v___x_4416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4416_, 0, v_a_4392_);
lean_ctor_set(v___x_4416_, 1, v_b_4393_);
lean_ctor_set(v___x_4416_, 2, v_bkt_4412_);
v_buckets_x27_4417_ = lean_array_uset(v_buckets_4395_, v___x_4411_, v___x_4416_);
v___x_4418_ = lean_unsigned_to_nat(4u);
v___x_4419_ = lean_nat_mul(v_size_x27_4415_, v___x_4418_);
v___x_4420_ = lean_unsigned_to_nat(3u);
v___x_4421_ = lean_nat_div(v___x_4419_, v___x_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_array_get_size(v_buckets_x27_4417_);
v___x_4423_ = lean_nat_dec_le(v___x_4421_, v___x_4422_);
lean_dec(v___x_4421_);
if (v___x_4423_ == 0)
{
lean_object* v_val_4424_; lean_object* v___x_4426_; 
v_val_4424_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0_spec__1___redArg(v_buckets_x27_4417_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 1, v_val_4424_);
lean_ctor_set(v___x_4397_, 0, v_size_x27_4415_);
v___x_4426_ = v___x_4397_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_size_x27_4415_);
lean_ctor_set(v_reuseFailAlloc_4427_, 1, v_val_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
else
{
lean_object* v___x_4429_; 
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 1, v_buckets_x27_4417_);
lean_ctor_set(v___x_4397_, 0, v_size_x27_4415_);
v___x_4429_ = v___x_4397_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_size_x27_4415_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v_buckets_x27_4417_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
else
{
lean_object* v___x_4431_; lean_object* v_buckets_x27_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
lean_inc(v_bkt_4412_);
v___x_4431_ = lean_box(0);
v_buckets_x27_4432_ = lean_array_uset(v_buckets_4395_, v___x_4411_, v___x_4431_);
v___x_4433_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0_spec__0___redArg(v_a_4392_, v_b_4393_, v_bkt_4412_);
v___x_4434_ = lean_array_uset(v_buckets_x27_4432_, v___x_4411_, v___x_4433_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 1, v___x_4434_);
v___x_4436_ = v___x_4397_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_size_4394_);
lean_ctor_set(v_reuseFailAlloc_4437_, 1, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1___redArg(lean_object* v_x_4439_, lean_object* v_x_4440_){
_start:
{
if (lean_obj_tag(v_x_4440_) == 0)
{
return v_x_4439_;
}
else
{
lean_object* v_value_4441_; uint8_t v_overrideDocument_4442_; 
v_value_4441_ = lean_ctor_get(v_x_4440_, 1);
lean_inc(v_value_4441_);
v_overrideDocument_4442_ = lean_ctor_get_uint8(v_value_4441_, sizeof(void*)*2);
if (v_overrideDocument_4442_ == 0)
{
lean_object* v_key_4443_; lean_object* v_tail_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_key_4443_ = lean_ctor_get(v_x_4440_, 0);
lean_inc(v_key_4443_);
v_tail_4444_ = lean_ctor_get(v_x_4440_, 2);
lean_inc(v_tail_4444_);
lean_dec_ref_known(v_x_4440_, 3);
v___x_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4445_, 0, v_value_4441_);
v___x_4446_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go_spec__0___redArg(v_x_4439_, v_key_4443_, v___x_4445_);
v_x_4439_ = v___x_4446_;
v_x_4440_ = v_tail_4444_;
goto _start;
}
else
{
lean_object* v_key_4448_; lean_object* v_tail_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v_key_4448_ = lean_ctor_get(v_x_4440_, 0);
lean_inc(v_key_4448_);
v_tail_4449_ = lean_ctor_get(v_x_4440_, 2);
lean_inc(v_tail_4449_);
lean_dec_ref_known(v_x_4440_, 3);
v___x_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4450_, 0, v_value_4441_);
v___x_4451_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0___redArg(v_x_4439_, v_key_4448_, v___x_4450_);
v_x_4439_ = v___x_4451_;
v_x_4440_ = v_tail_4449_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__2(lean_object* v_s_4453_, lean_object* v_as_4454_, size_t v_i_4455_, size_t v_stop_4456_, lean_object* v_b_4457_){
_start:
{
uint8_t v___x_4458_; 
v___x_4458_ = lean_usize_dec_eq(v_i_4455_, v_stop_4456_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4459_; lean_object* v___x_4460_; size_t v___x_4461_; size_t v___x_4462_; 
v___x_4459_ = lean_array_uget_borrowed(v_as_4454_, v_i_4455_);
lean_inc(v___x_4459_);
v___x_4460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1___redArg(v_b_4457_, v___x_4459_);
v___x_4461_ = ((size_t)1ULL);
v___x_4462_ = lean_usize_add(v_i_4455_, v___x_4461_);
v_i_4455_ = v___x_4462_;
v_b_4457_ = v___x_4460_;
goto _start;
}
else
{
return v_b_4457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__2___boxed(lean_object* v_s_4464_, lean_object* v_as_4465_, lean_object* v_i_4466_, lean_object* v_stop_4467_, lean_object* v_b_4468_){
_start:
{
size_t v_i_boxed_4469_; size_t v_stop_boxed_4470_; lean_object* v_res_4471_; 
v_i_boxed_4469_ = lean_unbox_usize(v_i_4466_);
lean_dec(v_i_4466_);
v_stop_boxed_4470_ = lean_unbox_usize(v_stop_4467_);
lean_dec(v_stop_4467_);
v_res_4471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__2(v_s_4464_, v_as_4465_, v_i_boxed_4469_, v_stop_boxed_4470_, v_b_4468_);
lean_dec_ref(v_as_4465_);
lean_dec_ref(v_s_4464_);
return v_res_4471_;
}
}
static lean_object* _init_l_Lean_Markdown_buildRefTable___closed__0(void){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = lean_box(0);
v___x_4473_ = lean_unsigned_to_nat(16u);
v___x_4474_ = lean_mk_array(v___x_4473_, v___x_4472_);
return v___x_4474_;
}
}
static lean_object* _init_l_Lean_Markdown_buildRefTable___closed__1(void){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = lean_obj_once(&l_Lean_Markdown_buildRefTable___closed__0, &l_Lean_Markdown_buildRefTable___closed__0_once, _init_l_Lean_Markdown_buildRefTable___closed__0);
v___x_4476_ = lean_unsigned_to_nat(0u);
v___x_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
lean_ctor_set(v___x_4477_, 1, v___x_4475_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_buildRefTable(lean_object* v_s_4478_, lean_object* v_blocks_4479_, lean_object* v_externalRefs_4480_){
_start:
{
lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v_snd_4485_; lean_object* v_buckets_4487_; lean_object* v___y_4494_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4514_; lean_object* v_size_4520_; lean_object* v_buckets_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; uint8_t v___x_4524_; 
v___x_4481_ = lean_unsigned_to_nat(0u);
v___x_4482_ = lean_obj_once(&l_Lean_Markdown_buildRefTable___closed__0, &l_Lean_Markdown_buildRefTable___closed__0_once, _init_l_Lean_Markdown_buildRefTable___closed__0);
v___x_4483_ = lean_obj_once(&l_Lean_Markdown_buildRefTable___closed__1, &l_Lean_Markdown_buildRefTable___closed__1_once, _init_l_Lean_Markdown_buildRefTable___closed__1);
v___x_4484_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_buildRefTable_go(v_s_4478_, v_blocks_4479_, v___x_4483_);
v_snd_4485_ = lean_ctor_get(v___x_4484_, 1);
lean_inc(v_snd_4485_);
lean_dec_ref(v___x_4484_);
v_size_4520_ = lean_ctor_get(v_externalRefs_4480_, 0);
v_buckets_4521_ = lean_ctor_get(v_externalRefs_4480_, 1);
v___x_4522_ = lean_mk_empty_array_with_capacity(v_size_4520_);
v___x_4523_ = lean_array_get_size(v_buckets_4521_);
v___x_4524_ = lean_nat_dec_lt(v___x_4481_, v___x_4523_);
if (v___x_4524_ == 0)
{
v___y_4514_ = v___x_4522_;
goto v___jp_4513_;
}
else
{
size_t v___x_4525_; size_t v___x_4526_; lean_object* v___x_4527_; 
v___x_4525_ = ((size_t)0ULL);
v___x_4526_ = lean_usize_of_nat(v___x_4523_);
v___x_4527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__6(v_buckets_4521_, v___x_4525_, v___x_4526_, v___x_4522_);
v___y_4514_ = v___x_4527_;
goto v___jp_4513_;
}
v___jp_4486_:
{
lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4488_ = lean_array_get_size(v_buckets_4487_);
v___x_4489_ = lean_nat_dec_lt(v___x_4481_, v___x_4488_);
if (v___x_4489_ == 0)
{
lean_dec_ref(v_buckets_4487_);
return v_snd_4485_;
}
else
{
size_t v___x_4490_; size_t v___x_4491_; lean_object* v___x_4492_; 
v___x_4490_ = ((size_t)0ULL);
v___x_4491_ = lean_usize_of_nat(v___x_4488_);
v___x_4492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__2(v_s_4478_, v_buckets_4487_, v___x_4490_, v___x_4491_, v_snd_4485_);
lean_dec_ref(v_buckets_4487_);
return v___x_4492_;
}
}
v___jp_4493_:
{
lean_object* v___x_4495_; uint8_t v___x_4496_; 
v___x_4495_ = lean_array_get_size(v___y_4494_);
v___x_4496_ = lean_nat_dec_lt(v___x_4481_, v___x_4495_);
if (v___x_4496_ == 0)
{
lean_dec_ref(v___y_4494_);
v_buckets_4487_ = v___x_4482_;
goto v___jp_4486_;
}
else
{
size_t v___x_4497_; size_t v___x_4498_; lean_object* v___x_4499_; lean_object* v_buckets_4500_; 
v___x_4497_ = ((size_t)0ULL);
v___x_4498_ = lean_usize_of_nat(v___x_4495_);
v___x_4499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_buildRefTable_spec__3(v___y_4494_, v___x_4497_, v___x_4498_, v___x_4483_);
lean_dec_ref(v___y_4494_);
v_buckets_4500_ = lean_ctor_get(v___x_4499_, 1);
lean_inc_ref(v_buckets_4500_);
lean_dec_ref(v___x_4499_);
v_buckets_4487_ = v_buckets_4500_;
goto v___jp_4486_;
}
}
v___jp_4501_:
{
lean_object* v___x_4506_; 
v___x_4506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg(v___y_4504_, v___y_4502_, v___y_4503_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec(v___y_4504_);
v___y_4494_ = v___x_4506_;
goto v___jp_4493_;
}
v___jp_4507_:
{
uint8_t v___x_4512_; 
v___x_4512_ = lean_nat_dec_le(v___y_4511_, v___y_4509_);
if (v___x_4512_ == 0)
{
lean_dec(v___y_4509_);
lean_inc(v___y_4511_);
v___y_4502_ = v___y_4508_;
v___y_4503_ = v___y_4511_;
v___y_4504_ = v___y_4510_;
v___y_4505_ = v___y_4511_;
goto v___jp_4501_;
}
else
{
v___y_4502_ = v___y_4508_;
v___y_4503_ = v___y_4511_;
v___y_4504_ = v___y_4510_;
v___y_4505_ = v___y_4509_;
goto v___jp_4501_;
}
}
v___jp_4513_:
{
lean_object* v___x_4515_; uint8_t v___x_4516_; 
v___x_4515_ = lean_array_get_size(v___y_4514_);
v___x_4516_ = lean_nat_dec_eq(v___x_4515_, v___x_4481_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4517_ = lean_unsigned_to_nat(1u);
v___x_4518_ = lean_nat_sub(v___x_4515_, v___x_4517_);
v___x_4519_ = lean_nat_dec_le(v___x_4481_, v___x_4518_);
if (v___x_4519_ == 0)
{
lean_inc(v___x_4518_);
v___y_4508_ = v___y_4514_;
v___y_4509_ = v___x_4518_;
v___y_4510_ = v___x_4515_;
v___y_4511_ = v___x_4518_;
goto v___jp_4507_;
}
else
{
v___y_4508_ = v___y_4514_;
v___y_4509_ = v___x_4518_;
v___y_4510_ = v___x_4515_;
v___y_4511_ = v___x_4481_;
goto v___jp_4507_;
}
}
else
{
v___y_4494_ = v___y_4514_;
goto v___jp_4493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_buildRefTable___boxed(lean_object* v_s_4528_, lean_object* v_blocks_4529_, lean_object* v_externalRefs_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_Markdown_buildRefTable(v_s_4528_, v_blocks_4529_, v_externalRefs_4530_);
lean_dec_ref(v_externalRefs_4530_);
lean_dec_ref(v_blocks_4529_);
lean_dec_ref(v_s_4528_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0(lean_object* v_00_u03b2_4532_, lean_object* v_m_4533_, lean_object* v_a_4534_, lean_object* v_b_4535_){
_start:
{
lean_object* v___x_4536_; 
v___x_4536_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0___redArg(v_m_4533_, v_a_4534_, v_b_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1(lean_object* v_s_4537_, lean_object* v_x_4538_, lean_object* v_x_4539_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1___redArg(v_x_4538_, v_x_4539_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1___boxed(lean_object* v_s_4541_, lean_object* v_x_4542_, lean_object* v_x_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Markdown_buildRefTable_spec__1(v_s_4541_, v_x_4542_, v_x_4543_);
lean_dec_ref(v_s_4541_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4(lean_object* v_n_4545_, lean_object* v_as_4546_, lean_object* v_lo_4547_, lean_object* v_hi_4548_, lean_object* v_w_4549_, lean_object* v_hlo_4550_, lean_object* v_hhi_4551_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___redArg(v_n_4545_, v_as_4546_, v_lo_4547_, v_hi_4548_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4___boxed(lean_object* v_n_4553_, lean_object* v_as_4554_, lean_object* v_lo_4555_, lean_object* v_hi_4556_, lean_object* v_w_4557_, lean_object* v_hlo_4558_, lean_object* v_hhi_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4(v_n_4553_, v_as_4554_, v_lo_4555_, v_hi_4556_, v_w_4557_, v_hlo_4558_, v_hhi_4559_);
lean_dec(v_hi_4556_);
lean_dec(v_n_4553_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0_spec__0(lean_object* v_00_u03b2_4561_, lean_object* v_a_4562_, lean_object* v_b_4563_, lean_object* v_x_4564_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Markdown_buildRefTable_spec__0_spec__0___redArg(v_a_4562_, v_b_4563_, v_x_4564_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5(lean_object* v_n_4566_, lean_object* v_lo_4567_, lean_object* v_hi_4568_, lean_object* v_hhi_4569_, lean_object* v_pivot_4570_, lean_object* v_as_4571_, lean_object* v_i_4572_, lean_object* v_k_4573_, lean_object* v_ilo_4574_, lean_object* v_ik_4575_, lean_object* v_w_4576_){
_start:
{
lean_object* v___x_4577_; 
v___x_4577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___redArg(v_hi_4568_, v_pivot_4570_, v_as_4571_, v_i_4572_, v_k_4573_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5___boxed(lean_object* v_n_4578_, lean_object* v_lo_4579_, lean_object* v_hi_4580_, lean_object* v_hhi_4581_, lean_object* v_pivot_4582_, lean_object* v_as_4583_, lean_object* v_i_4584_, lean_object* v_k_4585_, lean_object* v_ilo_4586_, lean_object* v_ik_4587_, lean_object* v_w_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Markdown_buildRefTable_spec__4_spec__5(v_n_4578_, v_lo_4579_, v_hi_4580_, v_hhi_4581_, v_pivot_4582_, v_as_4583_, v_i_4584_, v_k_4585_, v_ilo_4586_, v_ik_4587_, v_w_4588_);
lean_dec_ref(v_pivot_4582_);
lean_dec(v_hi_4580_);
lean_dec(v_lo_4579_);
lean_dec(v_n_4578_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseBlocks(lean_object* v_s_4590_, lean_object* v_indent_4591_){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlocksRaw(v_s_4590_, v_indent_4591_);
v___x_4593_ = l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_postProcessRefDefs(v_s_4590_, v___x_4592_);
lean_dec_ref(v___x_4592_);
return v___x_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseBlocks___boxed(lean_object* v_s_4594_, lean_object* v_indent_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Markdown_parseBlocks(v_s_4594_, v_indent_4595_);
lean_dec(v_indent_4595_);
lean_dec_ref(v_s_4594_);
return v_res_4596_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_QSort_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_RefDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Cursor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_BlockZipper(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Html(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Block(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_RefDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Cursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_BlockZipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Html(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0___boxed__const__1 = _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f_spec__1___redArg___closed__0___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__0___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseAtxHeading_x3f___closed__1___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseBlockquoteMarker_x3f___closed__0___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__5___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Block_0__Lean_Markdown_parseHtmlBlockStart_x3f___closed__11___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_Block(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_Array_QSort_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Compare(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Block(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_RefDef(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_Cursor(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_BlockZipper(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_Html(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_Block(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_RefDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_Cursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_BlockZipper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_Html(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_Block(builtin);
}
#ifdef __cplusplus
}
#endif
