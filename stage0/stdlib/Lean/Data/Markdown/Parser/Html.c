// Lean compiler output
// Module: Lean.Data.Markdown.Parser.Html
// Imports: public import Init.While public import Init.Control.Option public import Init.Control.State import Init.Data.String.Iterate public import Lean.Data.Markdown.InlineCursor
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
lean_object* l_Lean_Markdown_InlineCursor_front_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineCursor_drop1(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_InlineCursor_isEmpty___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isTagNameChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isTagNameChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameStart(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameStart___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isUnquotedValueChar(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isUnquotedValueChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlM_ofOption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlM_ofOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlM_ofOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseOpenTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseOpenTag_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseClosingTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseClosingTag_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseProcessingInstruction_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseProcessingInstruction_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__0;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2___boxed__const__1;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3___boxed__const__1;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4___boxed__const__1;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6___boxed__const__1;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7___boxed__const__1;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7;
static lean_once_cell_t l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_startsWithAscii(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_startsWithAscii___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Markdown_isRawTextTagName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Markdown_isRawTextTagName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_isRawTextTagName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__0 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__0_value;
static const lean_string_object l_Lean_Markdown_isRawTextTagName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "script"};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__1 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__1_value;
static const lean_string_object l_Lean_Markdown_isRawTextTagName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "style"};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__2 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__2_value;
static const lean_string_object l_Lean_Markdown_isRawTextTagName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "textarea"};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__3 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__3_value;
static const lean_ctor_object l_Lean_Markdown_isRawTextTagName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__4 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__4_value;
static const lean_ctor_object l_Lean_Markdown_isRawTextTagName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__2_value),((lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__4_value)}};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__5 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__5_value;
static const lean_ctor_object l_Lean_Markdown_isRawTextTagName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__1_value),((lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__5_value)}};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__6 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__6_value;
static const lean_ctor_object l_Lean_Markdown_isRawTextTagName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__0_value),((lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__6_value)}};
static const lean_object* l_Lean_Markdown_isRawTextTagName___closed__7 = (const lean_object*)&l_Lean_Markdown_isRawTextTagName___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_isRawTextTagName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_isRawTextTagName___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__0_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "tr"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__1 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__1_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "track"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__2 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__2_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__3 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__3_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__4 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__4_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__2_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__4_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__5 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__5_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__1_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__5_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__6 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__6_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__0_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__6_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__7 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__7_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "td"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__8 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__8_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tfoot"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__9 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__9_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "th"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__10 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__10_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "thead"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__11 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__11_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__11_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__7_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__12 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__12_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__10_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__12_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__13 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__13_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__9_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__13_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__14 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__14_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__8_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__14_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__15 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__15_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "section"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__16 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__16_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "summary"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__17 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__17_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "table"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__18 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__18_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tbody"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__19 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__19_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__19_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__15_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__20 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__20_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__18_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__20_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__21 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__21_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__17_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__21_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__22 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__22_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__16_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__22_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__23 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__23_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "option"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__24 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__24_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__25 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__25_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__26 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__26_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__27 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__27_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__27_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__23_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__28 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__28_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__26_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__28_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__29 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__29_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__25_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__29_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__30 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__30_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__24_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__30_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__31 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__31_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nav"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__32 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__32_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "noframes"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__33 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__33_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__34 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__34_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optgroup"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__35 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__35_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__35_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__31_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__36 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__36_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__34_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__36_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__37 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__37_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__33_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__37_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__38 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__38_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__32_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__38_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__39 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__39_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__40 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__40_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__41 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__41_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "menu"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__42 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__42_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "menuitem"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__43 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__43_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__43_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__39_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__44 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__44_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__42_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__44_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__45 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__45_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__41_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__45_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__46 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__46_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__40_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__46_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__47 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__47_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "head"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__48 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__48_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__49 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__49_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "hr"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__50 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__50_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "html"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__51 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__51_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "iframe"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__52 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__52_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "legend"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__53 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__53_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "li"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__54 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__54_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__54_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__47_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__55 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__55_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__53_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__55_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__56 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__56_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__52_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__56_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__57 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__57_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__51_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__57_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__58 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__58_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__50_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__58_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__59 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__59_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__49_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__59_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__60 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__60_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__48_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__60_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__61 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__61_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "h3"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__62 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__62_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "h4"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__63 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__63_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "h5"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__64 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__64_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "h6"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__65 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__65_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__65_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__61_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__66 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__66_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__64_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__66_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__67 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__67_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__63_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__67_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__68 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__68_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__62_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__68_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__69 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__69_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "frame"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__70 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__70_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "frameset"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__71 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__71_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "h1"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__72 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__72_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "h2"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__73 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__73_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__73_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__69_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__74 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__74_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__72_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__74_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__75 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__75_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__71_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__75_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__76 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__76_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__70_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__76_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__77 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__77_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "figcaption"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__78 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__78_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "figure"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__79 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__79_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "footer"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__80 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__80_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "form"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__81 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__81_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__81_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__77_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__82 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__82_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__80_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__82_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__83 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__83_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__79_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__83_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__84 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__84_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__78_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__84_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__85 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__85_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "div"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__86 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__86_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__87 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__87_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dt"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__88 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__88_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldset"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__89 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__89_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__89_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__85_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__90 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__90_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__88_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__90_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__91 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__91_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__87_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__91_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__92 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__92_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__86_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__92_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__93 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__93_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dd"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__94 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__94_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "details"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__95 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__95_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dialog"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__96 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__96_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dir"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__97 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__97_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__97_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__93_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__98 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__98_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__96_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__98_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__99 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__99_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__95_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__99_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__100 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__100_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__94_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__100_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__101 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__101_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caption"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__102 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__102_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "center"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__103 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__103_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "col"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__104 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__104_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "colgroup"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__105 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__105_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__105_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__101_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__106 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__106_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__104_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__106_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__107 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__107_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__103_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__107_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__108 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__108_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__102_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__108_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__109 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__109_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "address"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__110 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__110_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "article"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__111 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__111_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "aside"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__112 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__112_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "base"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__113 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__113_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basefont"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__114 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__114_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__115 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__115_value;
static const lean_string_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__116 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__116_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__116_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__109_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__117 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__117_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__115_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__117_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__118 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__118_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__114_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__118_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__119 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__119_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__113_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__119_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__120 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__120_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__112_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__120_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__121 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__121_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__111_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__121_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__122 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__122_value;
static const lean_ctor_object l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__110_value),((lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__122_value)}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__123 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__123_value;
LEAN_EXPORT const lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames___closed__123_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_isBlockTagName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_isBlockTagName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseCompleteTagLine_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseCompleteTagLine_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Markdown.HtmlBlockKind.rawText"};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__1 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__1_value;
static const lean_string_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Markdown.HtmlBlockKind.comment"};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__2 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__2_value;
static const lean_ctor_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__2_value)}};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__3 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__3_value;
static const lean_string_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Lean.Markdown.HtmlBlockKind.processingInstruction"};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__4 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__4_value;
static const lean_ctor_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__4_value)}};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__5 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__5_value;
static const lean_string_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Markdown.HtmlBlockKind.declaration"};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__6 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__6_value;
static const lean_ctor_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__6_value)}};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__7 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__7_value;
static const lean_string_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Markdown.HtmlBlockKind.cdata"};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__8 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__8_value;
static const lean_ctor_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__8_value)}};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__9 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__9_value;
static const lean_string_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Markdown.HtmlBlockKind.blockTag"};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__10 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__10_value;
static const lean_ctor_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__10_value)}};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__11 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__11_value;
static const lean_string_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Markdown.HtmlBlockKind.completeTag"};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__12 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__12_value;
static const lean_ctor_object l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__12_value)}};
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__13 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__13_value;
static lean_once_cell_t l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14;
static lean_once_cell_t l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15;
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instReprHtmlBlockKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instReprHtmlBlockKind_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instReprHtmlBlockKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instReprHtmlBlockKind = (const lean_object*)&l_Lean_Markdown_instReprHtmlBlockKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqHtmlBlockKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqHtmlBlockKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instBEqHtmlBlockKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instBEqHtmlBlockKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instBEqHtmlBlockKind___closed__0 = (const lean_object*)&l_Lean_Markdown_instBEqHtmlBlockKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instBEqHtmlBlockKind = (const lean_object*)&l_Lean_Markdown_instBEqHtmlBlockKind___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_instInhabitedHtmlBlockKind_default;
LEAN_EXPORT uint8_t l_Lean_Markdown_instInhabitedHtmlBlockKind;
LEAN_EXPORT uint8_t l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_interruptsParagraph___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Markdown_HtmlBlockKind_endConditionMet_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Markdown_HtmlBlockKind_endConditionMet_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "</pre>"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__0 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__0_value;
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "</script>"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__1 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__1_value;
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "</style>"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__2 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__2_value;
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "</textarea>"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__3 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__3_value;
static const lean_ctor_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__4 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__4_value;
static const lean_ctor_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__2_value),((lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__4_value)}};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__5 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__5_value;
static const lean_ctor_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__1_value),((lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__5_value)}};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__6 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__6_value;
static const lean_ctor_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__0_value),((lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__6_value)}};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__7 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__7_value;
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-->"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__8 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__8_value;
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\?>"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__9 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__9_value;
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__10 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__10_value;
static const lean_string_object l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]]>"};
static const lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__11 = (const lean_object*)&l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__11_value;
LEAN_EXPORT uint8_t l_Lean_Markdown_HtmlBlockKind_endConditionMet(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isTagNameChar(uint32_t v_c_1_){
_start:
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 65;
v___x_16_ = lean_uint32_dec_le(v___x_15_, v_c_1_);
if (v___x_16_ == 0)
{
goto v___jp_10_;
}
else
{
uint32_t v___x_17_; uint8_t v___x_18_; 
v___x_17_ = 90;
v___x_18_ = lean_uint32_dec_le(v_c_1_, v___x_17_);
if (v___x_18_ == 0)
{
goto v___jp_10_;
}
else
{
return v___x_18_;
}
}
v___jp_2_:
{
uint32_t v___x_3_; uint8_t v___x_4_; 
v___x_3_ = 45;
v___x_4_ = lean_uint32_dec_eq(v_c_1_, v___x_3_);
return v___x_4_;
}
v___jp_5_:
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 48;
v___x_7_ = lean_uint32_dec_le(v___x_6_, v_c_1_);
if (v___x_7_ == 0)
{
goto v___jp_2_;
}
else
{
uint32_t v___x_8_; uint8_t v___x_9_; 
v___x_8_ = 57;
v___x_9_ = lean_uint32_dec_le(v_c_1_, v___x_8_);
if (v___x_9_ == 0)
{
goto v___jp_2_;
}
else
{
return v___x_9_;
}
}
}
v___jp_10_:
{
uint32_t v___x_11_; uint8_t v___x_12_; 
v___x_11_ = 97;
v___x_12_ = lean_uint32_dec_le(v___x_11_, v_c_1_);
if (v___x_12_ == 0)
{
goto v___jp_5_;
}
else
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 122;
v___x_14_ = lean_uint32_dec_le(v_c_1_, v___x_13_);
if (v___x_14_ == 0)
{
goto v___jp_5_;
}
else
{
return v___x_14_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isTagNameChar___boxed(lean_object* v_c_19_){
_start:
{
uint32_t v_c_boxed_20_; uint8_t v_res_21_; lean_object* v_r_22_; 
v_c_boxed_20_ = lean_unbox_uint32(v_c_19_);
lean_dec(v_c_19_);
v_res_21_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isTagNameChar(v_c_boxed_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameStart(uint32_t v_c_23_){
_start:
{
uint32_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = 65;
v___x_35_ = lean_uint32_dec_le(v___x_34_, v_c_23_);
if (v___x_35_ == 0)
{
goto v___jp_29_;
}
else
{
uint32_t v___x_36_; uint8_t v___x_37_; 
v___x_36_ = 90;
v___x_37_ = lean_uint32_dec_le(v_c_23_, v___x_36_);
if (v___x_37_ == 0)
{
goto v___jp_29_;
}
else
{
return v___x_37_;
}
}
v___jp_24_:
{
uint32_t v___x_25_; uint8_t v___x_26_; 
v___x_25_ = 95;
v___x_26_ = lean_uint32_dec_eq(v_c_23_, v___x_25_);
if (v___x_26_ == 0)
{
uint32_t v___x_27_; uint8_t v___x_28_; 
v___x_27_ = 58;
v___x_28_ = lean_uint32_dec_eq(v_c_23_, v___x_27_);
return v___x_28_;
}
else
{
return v___x_26_;
}
}
v___jp_29_:
{
uint32_t v___x_30_; uint8_t v___x_31_; 
v___x_30_ = 97;
v___x_31_ = lean_uint32_dec_le(v___x_30_, v_c_23_);
if (v___x_31_ == 0)
{
goto v___jp_24_;
}
else
{
uint32_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = 122;
v___x_33_ = lean_uint32_dec_le(v_c_23_, v___x_32_);
if (v___x_33_ == 0)
{
goto v___jp_24_;
}
else
{
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameStart___boxed(lean_object* v_c_38_){
_start:
{
uint32_t v_c_boxed_39_; uint8_t v_res_40_; lean_object* v_r_41_; 
v_c_boxed_39_ = lean_unbox_uint32(v_c_38_);
lean_dec(v_c_38_);
v_res_40_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameStart(v_c_boxed_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameChar(uint32_t v_c_42_){
_start:
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 65;
v___x_63_ = lean_uint32_dec_le(v___x_62_, v_c_42_);
if (v___x_63_ == 0)
{
goto v___jp_57_;
}
else
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 90;
v___x_65_ = lean_uint32_dec_le(v_c_42_, v___x_64_);
if (v___x_65_ == 0)
{
goto v___jp_57_;
}
else
{
return v___x_65_;
}
}
v___jp_43_:
{
uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_44_ = 95;
v___x_45_ = lean_uint32_dec_eq(v_c_42_, v___x_44_);
if (v___x_45_ == 0)
{
uint32_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 46;
v___x_47_ = lean_uint32_dec_eq(v_c_42_, v___x_46_);
if (v___x_47_ == 0)
{
uint32_t v___x_48_; uint8_t v___x_49_; 
v___x_48_ = 58;
v___x_49_ = lean_uint32_dec_eq(v_c_42_, v___x_48_);
if (v___x_49_ == 0)
{
uint32_t v___x_50_; uint8_t v___x_51_; 
v___x_50_ = 45;
v___x_51_ = lean_uint32_dec_eq(v_c_42_, v___x_50_);
return v___x_51_;
}
else
{
return v___x_49_;
}
}
else
{
return v___x_47_;
}
}
else
{
return v___x_45_;
}
}
v___jp_52_:
{
uint32_t v___x_53_; uint8_t v___x_54_; 
v___x_53_ = 48;
v___x_54_ = lean_uint32_dec_le(v___x_53_, v_c_42_);
if (v___x_54_ == 0)
{
goto v___jp_43_;
}
else
{
uint32_t v___x_55_; uint8_t v___x_56_; 
v___x_55_ = 57;
v___x_56_ = lean_uint32_dec_le(v_c_42_, v___x_55_);
if (v___x_56_ == 0)
{
goto v___jp_43_;
}
else
{
return v___x_56_;
}
}
}
v___jp_57_:
{
uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_58_ = 97;
v___x_59_ = lean_uint32_dec_le(v___x_58_, v_c_42_);
if (v___x_59_ == 0)
{
goto v___jp_52_;
}
else
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 122;
v___x_61_ = lean_uint32_dec_le(v_c_42_, v___x_60_);
if (v___x_61_ == 0)
{
goto v___jp_52_;
}
else
{
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameChar___boxed(lean_object* v_c_66_){
_start:
{
uint32_t v_c_boxed_67_; uint8_t v_res_68_; lean_object* v_r_69_; 
v_c_boxed_67_ = lean_unbox_uint32(v_c_66_);
lean_dec(v_c_66_);
v_res_68_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameChar(v_c_boxed_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isUnquotedValueChar(uint32_t v_c_70_){
_start:
{
uint32_t v___x_71_; uint8_t v___x_72_; 
v___x_71_ = 32;
v___x_72_ = lean_uint32_dec_eq(v_c_70_, v___x_71_);
if (v___x_72_ == 0)
{
uint32_t v___x_73_; uint8_t v___x_74_; 
v___x_73_ = 9;
v___x_74_ = lean_uint32_dec_eq(v_c_70_, v___x_73_);
if (v___x_74_ == 0)
{
uint32_t v___x_75_; uint8_t v___x_76_; 
v___x_75_ = 13;
v___x_76_ = lean_uint32_dec_eq(v_c_70_, v___x_75_);
if (v___x_76_ == 0)
{
uint32_t v___x_77_; uint8_t v___x_78_; 
v___x_77_ = 10;
v___x_78_ = lean_uint32_dec_eq(v_c_70_, v___x_77_);
if (v___x_78_ == 0)
{
uint32_t v___x_79_; uint8_t v___x_80_; 
v___x_79_ = 34;
v___x_80_ = lean_uint32_dec_eq(v_c_70_, v___x_79_);
if (v___x_80_ == 0)
{
uint32_t v___x_81_; uint8_t v___x_82_; 
v___x_81_ = 39;
v___x_82_ = lean_uint32_dec_eq(v_c_70_, v___x_81_);
if (v___x_82_ == 0)
{
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 61;
v___x_84_ = lean_uint32_dec_eq(v_c_70_, v___x_83_);
if (v___x_84_ == 0)
{
uint32_t v___x_85_; uint8_t v___x_86_; 
v___x_85_ = 60;
v___x_86_ = lean_uint32_dec_eq(v_c_70_, v___x_85_);
if (v___x_86_ == 0)
{
uint32_t v___x_87_; uint8_t v___x_88_; 
v___x_87_ = 62;
v___x_88_ = lean_uint32_dec_eq(v_c_70_, v___x_87_);
if (v___x_88_ == 0)
{
uint32_t v___x_89_; uint8_t v___x_90_; 
v___x_89_ = 96;
v___x_90_ = lean_uint32_dec_eq(v_c_70_, v___x_89_);
if (v___x_90_ == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
return v___x_88_;
}
}
else
{
return v___x_86_;
}
}
else
{
return v___x_84_;
}
}
else
{
return v___x_82_;
}
}
else
{
return v___x_80_;
}
}
else
{
return v___x_78_;
}
}
else
{
return v___x_76_;
}
}
else
{
return v___x_74_;
}
}
else
{
return v___x_72_;
}
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isUnquotedValueChar___boxed(lean_object* v_c_93_){
_start:
{
uint32_t v_c_boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_c_boxed_94_ = lean_unbox_uint32(v_c_93_);
lean_dec(v_c_93_);
v_res_95_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isUnquotedValueChar(v_c_boxed_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__0(lean_object* v_s_97_, lean_object* v_fst_98_, lean_object* v_snd_99_, lean_object* v_x_100_){
_start:
{
lean_object* v___x_101_; 
lean_inc(v_fst_98_);
v___x_101_ = l_Lean_Markdown_InlineCursor_parseLineEnding_x3f(v_s_97_, v_fst_98_);
if (lean_obj_tag(v___x_101_) == 1)
{
lean_object* v_val_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_133_; 
v_val_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_133_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_133_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_val_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_133_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
uint8_t v___x_106_; 
v___x_106_ = lean_unbox(v_snd_99_);
if (v___x_106_ == 0)
{
lean_object* v_snd_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_119_; 
lean_dec(v_snd_99_);
lean_dec(v_fst_98_);
v_snd_107_ = lean_ctor_get(v_val_102_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_val_102_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v_val_102_, 0);
lean_dec(v_unused_120_);
v___x_109_ = v_val_102_;
v_isShared_110_ = v_isSharedCheck_119_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_snd_107_);
lean_dec(v_val_102_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_119_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_111_ = 1;
v___x_112_ = lean_box(v___x_111_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_112_);
lean_ctor_set(v___x_109_, 0, v_snd_107_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_snd_107_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_118_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_116_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_114_);
v___x_116_ = v___x_104_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
else
{
lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_130_; 
v_isSharedCheck_130_ = !lean_is_exclusive(v_val_102_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; lean_object* v_unused_132_; 
v_unused_131_ = lean_ctor_get(v_val_102_, 1);
lean_dec(v_unused_131_);
v_unused_132_ = lean_ctor_get(v_val_102_, 0);
lean_dec(v_unused_132_);
v___x_122_ = v_val_102_;
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
else
{
lean_dec(v_val_102_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_130_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v_snd_99_);
lean_ctor_set(v___x_122_, 0, v_fst_98_);
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_fst_98_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_snd_99_);
v___x_125_ = v_reuseFailAlloc_129_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_127_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 0);
lean_ctor_set(v___x_104_, 0, v___x_125_);
v___x_127_ = v___x_104_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v___x_101_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_fst_98_);
lean_ctor_set(v___x_134_, 1, v_snd_99_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__0___boxed(lean_object* v_s_136_, lean_object* v_fst_137_, lean_object* v_snd_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__0(v_s_136_, v_fst_137_, v_snd_138_, v_x_139_);
lean_dec(v_x_139_);
lean_dec_ref(v_s_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__1(lean_object* v_s_141_, lean_object* v_fst_142_, lean_object* v_snd_143_, lean_object* v_00___144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = l_Lean_Markdown_InlineCursor_drop1(v_s_141_, v_fst_142_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v_snd_143_);
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__1___boxed(lean_object* v_s_148_, lean_object* v_fst_149_, lean_object* v_snd_150_, lean_object* v_00___151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__1(v_s_148_, v_fst_149_, v_snd_150_, v_00___151_);
lean_dec_ref(v_s_148_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg(lean_object* v_s_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___y_156_; lean_object* v_fst_160_; lean_object* v_snd_161_; lean_object* v___x_162_; 
v_fst_160_ = lean_ctor_get(v_a_154_, 0);
lean_inc(v_fst_160_);
v_snd_161_ = lean_ctor_get(v_a_154_, 1);
lean_inc(v_snd_161_);
lean_dec_ref(v_a_154_);
v___x_162_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_153_, v_fst_160_);
if (lean_obj_tag(v___x_162_) == 1)
{
lean_object* v_val_163_; uint32_t v___x_164_; uint32_t v___x_165_; uint8_t v___x_166_; 
v_val_163_ = lean_ctor_get(v___x_162_, 0);
v___x_164_ = 32;
v___x_165_ = lean_unbox_uint32(v_val_163_);
v___x_166_ = lean_uint32_dec_eq(v___x_165_, v___x_164_);
if (v___x_166_ == 0)
{
uint32_t v___x_167_; uint32_t v___x_168_; uint8_t v___x_169_; 
v___x_167_ = 9;
v___x_168_ = lean_unbox_uint32(v_val_163_);
v___x_169_ = lean_uint32_dec_eq(v___x_168_, v___x_167_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__0(v_s_153_, v_fst_160_, v_snd_161_, v___x_162_);
lean_dec_ref_known(v___x_162_, 1);
v___y_156_ = v___x_170_;
goto v___jp_155_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref_known(v___x_162_, 1);
v___x_171_ = lean_box(0);
v___x_172_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__1(v_s_153_, v_fst_160_, v_snd_161_, v___x_171_);
v___y_156_ = v___x_172_;
goto v___jp_155_;
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec_ref_known(v___x_162_, 1);
v___x_173_ = lean_box(0);
v___x_174_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__1(v_s_153_, v_fst_160_, v_snd_161_, v___x_173_);
v___y_156_ = v___x_174_;
goto v___jp_155_;
}
}
else
{
lean_object* v___x_175_; 
v___x_175_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___lam__0(v_s_153_, v_fst_160_, v_snd_161_, v___x_162_);
lean_dec(v___x_162_);
v___y_156_ = v___x_175_;
goto v___jp_155_;
}
v___jp_155_:
{
if (lean_obj_tag(v___y_156_) == 0)
{
lean_object* v_a_157_; 
v_a_157_ = lean_ctor_get(v___y_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___y_156_, 1);
return v_a_157_;
}
else
{
lean_object* v_a_158_; 
v_a_158_ = lean_ctor_get(v___y_156_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___y_156_, 1);
v_a_154_ = v_a_158_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg___boxed(lean_object* v_s_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg(v_s_176_, v_a_177_);
lean_dec_ref(v_s_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace(lean_object* v_s_179_, lean_object* v_cur_180_){
_start:
{
uint8_t v_sawLineEnding_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_fst_185_; 
v_sawLineEnding_181_ = 0;
v___x_182_ = lean_box(v_sawLineEnding_181_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_cur_180_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg(v_s_179_, v___x_183_);
v_fst_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_fst_185_);
lean_dec_ref(v___x_184_);
return v_fst_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace___boxed(lean_object* v_s_186_, lean_object* v_cur_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace(v_s_186_, v_cur_187_);
lean_dec_ref(v_s_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0(lean_object* v_s_189_, lean_object* v_inst_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___redArg(v_s_189_, v_a_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0___boxed(lean_object* v_s_193_, lean_object* v_inst_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace_spec__0(v_s_193_, v_inst_194_, v_a_195_);
lean_dec_ref(v_s_193_);
return v_res_196_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
if (lean_obj_tag(v_x_197_) == 0)
{
if (lean_obj_tag(v_x_198_) == 0)
{
uint8_t v___x_199_; 
v___x_199_ = 1;
return v___x_199_;
}
else
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
}
else
{
if (lean_obj_tag(v_x_198_) == 0)
{
uint8_t v___x_201_; 
v___x_201_ = 0;
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v_val_203_; uint32_t v___x_204_; uint32_t v___x_205_; uint8_t v___x_206_; 
v_val_202_ = lean_ctor_get(v_x_197_, 0);
v_val_203_ = lean_ctor_get(v_x_198_, 0);
v___x_204_ = lean_unbox_uint32(v_val_202_);
v___x_205_ = lean_unbox_uint32(v_val_203_);
v___x_206_ = lean_uint32_dec_eq(v___x_204_, v___x_205_);
return v___x_206_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0___boxed(lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v_x_207_, v_x_208_);
lean_dec(v_x_208_);
lean_dec(v_x_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(lean_object* v_s_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v_x_212_);
return v___x_214_;
}
else
{
lean_object* v_head_215_; lean_object* v_tail_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_head_215_ = lean_ctor_get(v_x_213_, 0);
v_tail_216_ = lean_ctor_get(v_x_213_, 1);
v___x_217_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_211_, v_x_212_);
lean_inc(v_head_215_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v_head_215_);
v___x_219_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v___x_217_, v___x_218_);
lean_dec_ref_known(v___x_218_, 1);
lean_dec(v___x_217_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
lean_dec_ref(v_x_212_);
v___x_220_ = lean_box(0);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Markdown_InlineCursor_drop1(v_s_211_, v_x_212_);
v_x_212_ = v___x_221_;
v_x_213_ = v_tail_216_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1___boxed(lean_object* v_s_223_, lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(v_s_223_, v_x_224_, v_x_225_);
lean_dec(v_x_225_);
lean_dec_ref(v_s_223_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars(lean_object* v_s_227_, lean_object* v_cur_228_, lean_object* v_pat_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(v_s_227_, v_cur_228_, v_pat_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars___boxed(lean_object* v_s_231_, lean_object* v_cur_232_, lean_object* v_pat_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars(v_s_231_, v_cur_232_, v_pat_233_);
lean_dec(v_pat_233_);
lean_dec_ref(v_s_231_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___redArg(lean_object* v_s_235_, lean_object* v_pat_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_snd_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_257_; 
v_snd_238_ = lean_ctor_get(v_a_237_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_a_237_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v_a_237_, 0);
lean_dec(v_unused_258_);
v___x_240_ = v_a_237_;
v_isShared_241_ = v_isSharedCheck_257_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_snd_238_);
lean_dec(v_a_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_257_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_box(0);
v___x_243_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_snd_238_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_inc(v_snd_238_);
v___x_244_ = l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(v_s_235_, v_snd_238_, v_pat_236_);
if (lean_obj_tag(v___x_244_) == 1)
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_245_);
v___x_247_ = v___x_240_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_snd_238_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_251_; 
lean_dec(v___x_244_);
v___x_249_ = l_Lean_Markdown_InlineCursor_drop1(v_s_235_, v_snd_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v___x_249_);
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_251_ = v___x_240_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_249_);
v___x_251_ = v_reuseFailAlloc_253_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
v_a_237_ = v___x_251_;
goto _start;
}
}
}
else
{
lean_object* v___x_255_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_255_ = v___x_240_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_snd_238_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___redArg___boxed(lean_object* v_s_259_, lean_object* v_pat_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___redArg(v_s_259_, v_pat_260_, v_a_261_);
lean_dec(v_pat_260_);
lean_dec_ref(v_s_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast(lean_object* v_s_263_, lean_object* v_cur_264_, lean_object* v_pat_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_fst_269_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_cur_264_);
v___x_268_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___redArg(v_s_263_, v_pat_265_, v___x_267_);
v_fst_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_fst_269_);
lean_dec_ref(v___x_268_);
if (lean_obj_tag(v_fst_269_) == 0)
{
return v___x_266_;
}
else
{
lean_object* v_val_270_; 
v_val_270_ = lean_ctor_get(v_fst_269_, 0);
lean_inc(v_val_270_);
lean_dec_ref_known(v_fst_269_, 1);
return v_val_270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast___boxed(lean_object* v_s_271_, lean_object* v_cur_272_, lean_object* v_pat_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast(v_s_271_, v_cur_272_, v_pat_273_);
lean_dec(v_pat_273_);
lean_dec_ref(v_s_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0(lean_object* v_s_275_, lean_object* v_pat_276_, lean_object* v_inst_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___redArg(v_s_275_, v_pat_276_, v_a_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0___boxed(lean_object* v_s_280_, lean_object* v_pat_281_, lean_object* v_inst_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast_spec__0(v_s_280_, v_pat_281_, v_inst_282_, v_a_283_);
lean_dec(v_pat_281_);
lean_dec_ref(v_s_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorIdx___impl(uint8_t v_x_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_box(v_x_285_);
v___x_287_ = lean_obj_tag_nat(v___x_286_);
lean_dec(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorIdx___impl___boxed(lean_object* v_x_288_){
_start:
{
uint8_t v_x_4__boxed_289_; lean_object* v_res_290_; 
v_x_4__boxed_289_ = lean_unbox(v_x_288_);
v_res_290_ = l_Lean_Markdown_HtmlCloser_ctorIdx___impl(v_x_4__boxed_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim___redArg(lean_object* v_k_291_){
_start:
{
lean_inc(v_k_291_);
return v_k_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim___redArg___boxed(lean_object* v_k_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Markdown_HtmlCloser_ctorElim___redArg(v_k_292_);
lean_dec(v_k_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim(lean_object* v_motive_294_, lean_object* v_ctorIdx_295_, uint8_t v_t_296_, lean_object* v_h_297_, lean_object* v_k_298_){
_start:
{
lean_inc(v_k_298_);
return v_k_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_ctorElim___boxed(lean_object* v_motive_299_, lean_object* v_ctorIdx_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_k_303_){
_start:
{
uint8_t v_t_boxed_304_; lean_object* v_res_305_; 
v_t_boxed_304_ = lean_unbox(v_t_301_);
v_res_305_ = l_Lean_Markdown_HtmlCloser_ctorElim(v_motive_299_, v_ctorIdx_300_, v_t_boxed_304_, v_h_302_, v_k_303_);
lean_dec(v_k_303_);
lean_dec(v_ctorIdx_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim___redArg(lean_object* v_comment_306_){
_start:
{
lean_inc(v_comment_306_);
return v_comment_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim___redArg___boxed(lean_object* v_comment_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Markdown_HtmlCloser_comment_elim___redArg(v_comment_307_);
lean_dec(v_comment_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim(lean_object* v_motive_309_, uint8_t v_t_310_, lean_object* v_h_311_, lean_object* v_comment_312_){
_start:
{
lean_inc(v_comment_312_);
return v_comment_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_comment_elim___boxed(lean_object* v_motive_313_, lean_object* v_t_314_, lean_object* v_h_315_, lean_object* v_comment_316_){
_start:
{
uint8_t v_t_boxed_317_; lean_object* v_res_318_; 
v_t_boxed_317_ = lean_unbox(v_t_314_);
v_res_318_ = l_Lean_Markdown_HtmlCloser_comment_elim(v_motive_313_, v_t_boxed_317_, v_h_315_, v_comment_316_);
lean_dec(v_comment_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim___redArg(lean_object* v_processingInstruction_319_){
_start:
{
lean_inc(v_processingInstruction_319_);
return v_processingInstruction_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim___redArg___boxed(lean_object* v_processingInstruction_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Markdown_HtmlCloser_processingInstruction_elim___redArg(v_processingInstruction_320_);
lean_dec(v_processingInstruction_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim(lean_object* v_motive_322_, uint8_t v_t_323_, lean_object* v_h_324_, lean_object* v_processingInstruction_325_){
_start:
{
lean_inc(v_processingInstruction_325_);
return v_processingInstruction_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_processingInstruction_elim___boxed(lean_object* v_motive_326_, lean_object* v_t_327_, lean_object* v_h_328_, lean_object* v_processingInstruction_329_){
_start:
{
uint8_t v_t_boxed_330_; lean_object* v_res_331_; 
v_t_boxed_330_ = lean_unbox(v_t_327_);
v_res_331_ = l_Lean_Markdown_HtmlCloser_processingInstruction_elim(v_motive_326_, v_t_boxed_330_, v_h_328_, v_processingInstruction_329_);
lean_dec(v_processingInstruction_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim___redArg(lean_object* v_cdata_332_){
_start:
{
lean_inc(v_cdata_332_);
return v_cdata_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim___redArg___boxed(lean_object* v_cdata_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Markdown_HtmlCloser_cdata_elim___redArg(v_cdata_333_);
lean_dec(v_cdata_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim(lean_object* v_motive_335_, uint8_t v_t_336_, lean_object* v_h_337_, lean_object* v_cdata_338_){
_start:
{
lean_inc(v_cdata_338_);
return v_cdata_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_cdata_elim___boxed(lean_object* v_motive_339_, lean_object* v_t_340_, lean_object* v_h_341_, lean_object* v_cdata_342_){
_start:
{
uint8_t v_t_boxed_343_; lean_object* v_res_344_; 
v_t_boxed_343_ = lean_unbox(v_t_340_);
v_res_344_ = l_Lean_Markdown_HtmlCloser_cdata_elim(v_motive_339_, v_t_boxed_343_, v_h_341_, v_cdata_342_);
lean_dec(v_cdata_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim___redArg(lean_object* v_declaration_345_){
_start:
{
lean_inc(v_declaration_345_);
return v_declaration_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim___redArg___boxed(lean_object* v_declaration_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Markdown_HtmlCloser_declaration_elim___redArg(v_declaration_346_);
lean_dec(v_declaration_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim(lean_object* v_motive_348_, uint8_t v_t_349_, lean_object* v_h_350_, lean_object* v_declaration_351_){
_start:
{
lean_inc(v_declaration_351_);
return v_declaration_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlCloser_declaration_elim___boxed(lean_object* v_motive_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_declaration_355_){
_start:
{
uint8_t v_t_boxed_356_; lean_object* v_res_357_; 
v_t_boxed_356_ = lean_unbox(v_t_353_);
v_res_357_ = l_Lean_Markdown_HtmlCloser_declaration_elim(v_motive_352_, v_t_boxed_356_, v_h_354_, v_declaration_355_);
lean_dec(v_declaration_355_);
return v_res_357_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_358_; lean_object* v___x_359_; 
v___x_358_ = 62;
v___x_359_ = lean_box_uint32(v___x_358_);
return v___x_359_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_box(0);
v___x_361_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0___boxed__const__1;
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_363_; lean_object* v___x_364_; 
v___x_363_ = 45;
v___x_364_ = lean_box_uint32(v___x_363_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0);
v___x_366_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1;
v___x_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__2(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1);
v___x_369_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1;
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
return v___x_370_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_371_; lean_object* v___x_372_; 
v___x_371_ = 63;
v___x_372_ = lean_box_uint32(v___x_371_);
return v___x_372_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0);
v___x_374_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3___boxed__const__1;
v___x_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_376_; lean_object* v___x_377_; 
v___x_376_ = 93;
v___x_377_ = lean_box_uint32(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_378_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0);
v___x_379_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4___boxed__const__1;
v___x_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_378_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__5(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4);
v___x_382_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4___boxed__const__1;
v___x_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars(uint8_t v_x_384_){
_start:
{
switch(v_x_384_)
{
case 0:
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__2, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__2_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__2);
return v___x_385_;
}
case 1:
{
lean_object* v___x_386_; 
v___x_386_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3);
return v___x_386_;
}
case 2:
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__5, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__5_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__5);
return v___x_387_;
}
default: 
{
lean_object* v___x_388_; 
v___x_388_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0);
return v___x_388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___boxed(lean_object* v_x_389_){
_start:
{
uint8_t v_x_123__boxed_390_; lean_object* v_res_391_; 
v_x_123__boxed_390_ = lean_unbox(v_x_389_);
v_res_391_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars(v_x_123__boxed_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___redArg(lean_object* v_memo_392_, uint8_t v_x_393_){
_start:
{
switch(v_x_393_)
{
case 0:
{
lean_object* v_comment_x3f_394_; 
v_comment_x3f_394_ = lean_ctor_get(v_memo_392_, 0);
lean_inc(v_comment_x3f_394_);
return v_comment_x3f_394_;
}
case 1:
{
lean_object* v_processingInstruction_x3f_395_; 
v_processingInstruction_x3f_395_ = lean_ctor_get(v_memo_392_, 1);
lean_inc(v_processingInstruction_x3f_395_);
return v_processingInstruction_x3f_395_;
}
case 2:
{
lean_object* v_cdata_x3f_396_; 
v_cdata_x3f_396_ = lean_ctor_get(v_memo_392_, 2);
lean_inc(v_cdata_x3f_396_);
return v_cdata_x3f_396_;
}
default: 
{
lean_object* v_declaration_x3f_397_; 
v_declaration_x3f_397_ = lean_ctor_get(v_memo_392_, 3);
lean_inc(v_declaration_x3f_397_);
return v_declaration_x3f_397_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___redArg___boxed(lean_object* v_memo_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_x_34__boxed_400_; lean_object* v_res_401_; 
v_x_34__boxed_400_ = lean_unbox(v_x_399_);
v_res_401_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___redArg(v_memo_398_, v_x_34__boxed_400_);
lean_dec_ref(v_memo_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f(lean_object* v_s_402_, lean_object* v_memo_403_, uint8_t v_x_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___redArg(v_memo_403_, v_x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___boxed(lean_object* v_s_406_, lean_object* v_memo_407_, lean_object* v_x_408_){
_start:
{
uint8_t v_x_37__boxed_409_; lean_object* v_res_410_; 
v_x_37__boxed_409_ = lean_unbox(v_x_408_);
v_res_410_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f(v_s_406_, v_memo_407_, v_x_37__boxed_409_);
lean_dec_ref(v_memo_407_);
lean_dec_ref(v_s_406_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___redArg(lean_object* v_memo_411_, uint8_t v_closer_412_, lean_object* v_start_413_){
_start:
{
switch(v_closer_412_)
{
case 0:
{
lean_object* v_processingInstruction_x3f_414_; lean_object* v_cdata_x3f_415_; lean_object* v_declaration_x3f_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_424_; 
v_processingInstruction_x3f_414_ = lean_ctor_get(v_memo_411_, 1);
v_cdata_x3f_415_ = lean_ctor_get(v_memo_411_, 2);
v_declaration_x3f_416_ = lean_ctor_get(v_memo_411_, 3);
v_isSharedCheck_424_ = !lean_is_exclusive(v_memo_411_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v_memo_411_, 0);
lean_dec(v_unused_425_);
v___x_418_ = v_memo_411_;
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_declaration_x3f_416_);
lean_inc(v_cdata_x3f_415_);
lean_inc(v_processingInstruction_x3f_414_);
lean_dec(v_memo_411_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_424_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_420_, 0, v_start_413_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_420_);
v___x_422_ = v___x_418_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_processingInstruction_x3f_414_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_cdata_x3f_415_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_declaration_x3f_416_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
case 1:
{
lean_object* v_comment_x3f_426_; lean_object* v_cdata_x3f_427_; lean_object* v_declaration_x3f_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_comment_x3f_426_ = lean_ctor_get(v_memo_411_, 0);
v_cdata_x3f_427_ = lean_ctor_get(v_memo_411_, 2);
v_declaration_x3f_428_ = lean_ctor_get(v_memo_411_, 3);
v_isSharedCheck_436_ = !lean_is_exclusive(v_memo_411_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v_memo_411_, 1);
lean_dec(v_unused_437_);
v___x_430_ = v_memo_411_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_declaration_x3f_428_);
lean_inc(v_cdata_x3f_427_);
lean_inc(v_comment_x3f_426_);
lean_dec(v_memo_411_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_432_, 0, v_start_413_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_comment_x3f_426_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_cdata_x3f_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_declaration_x3f_428_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
case 2:
{
lean_object* v_comment_x3f_438_; lean_object* v_processingInstruction_x3f_439_; lean_object* v_declaration_x3f_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_448_; 
v_comment_x3f_438_ = lean_ctor_get(v_memo_411_, 0);
v_processingInstruction_x3f_439_ = lean_ctor_get(v_memo_411_, 1);
v_declaration_x3f_440_ = lean_ctor_get(v_memo_411_, 3);
v_isSharedCheck_448_ = !lean_is_exclusive(v_memo_411_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v_memo_411_, 2);
lean_dec(v_unused_449_);
v___x_442_ = v_memo_411_;
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_declaration_x3f_440_);
lean_inc(v_processingInstruction_x3f_439_);
lean_inc(v_comment_x3f_438_);
lean_dec(v_memo_411_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_448_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_start_413_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 2, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_comment_x3f_438_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_processingInstruction_x3f_439_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_declaration_x3f_440_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
default: 
{
lean_object* v_comment_x3f_450_; lean_object* v_processingInstruction_x3f_451_; lean_object* v_cdata_x3f_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_460_; 
v_comment_x3f_450_ = lean_ctor_get(v_memo_411_, 0);
v_processingInstruction_x3f_451_ = lean_ctor_get(v_memo_411_, 1);
v_cdata_x3f_452_ = lean_ctor_get(v_memo_411_, 2);
v_isSharedCheck_460_ = !lean_is_exclusive(v_memo_411_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_memo_411_, 3);
lean_dec(v_unused_461_);
v___x_454_ = v_memo_411_;
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_cdata_x3f_452_);
lean_inc(v_processingInstruction_x3f_451_);
lean_inc(v_comment_x3f_450_);
lean_dec(v_memo_411_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v_start_413_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 3, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_comment_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_processingInstruction_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_cdata_x3f_452_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___redArg___boxed(lean_object* v_memo_462_, lean_object* v_closer_463_, lean_object* v_start_464_){
_start:
{
uint8_t v_closer_boxed_465_; lean_object* v_res_466_; 
v_closer_boxed_465_ = lean_unbox(v_closer_463_);
v_res_466_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___redArg(v_memo_462_, v_closer_boxed_465_, v_start_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure(lean_object* v_s_467_, lean_object* v_memo_468_, uint8_t v_closer_469_, lean_object* v_start_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___redArg(v_memo_468_, v_closer_469_, v_start_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___boxed(lean_object* v_s_472_, lean_object* v_memo_473_, lean_object* v_closer_474_, lean_object* v_start_475_){
_start:
{
uint8_t v_closer_boxed_476_; lean_object* v_res_477_; 
v_closer_boxed_476_ = lean_unbox(v_closer_474_);
v_res_477_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure(v_s_472_, v_memo_473_, v_closer_boxed_476_, v_start_475_);
lean_dec_ref(v_s_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlM_ofOption___redArg(lean_object* v_x_x3f_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_x_x3f_478_);
lean_ctor_set(v___x_480_, 1, v_a_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlM_ofOption(lean_object* v_s_481_, lean_object* v_00_u03b1_482_, lean_object* v_x_x3f_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_x_x3f_483_);
lean_ctor_set(v___x_485_, 1, v_a_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlM_ofOption___boxed(lean_object* v_s_486_, lean_object* v_00_u03b1_487_, lean_object* v_x_x3f_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Markdown_HtmlM_ofOption(v_s_486_, v_00_u03b1_487_, v_x_x3f_488_, v_a_489_);
lean_dec_ref(v_s_486_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser(lean_object* v_s_491_, lean_object* v_cur_492_, uint8_t v_closer_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_failedFrom_x3f___redArg(v_a_494_, v_closer_493_);
if (lean_obj_tag(v___x_503_) == 0)
{
goto v___jp_495_;
}
else
{
lean_object* v_val_504_; lean_object* v_startPos_505_; uint8_t v___x_506_; 
v_val_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_val_504_);
lean_dec_ref_known(v___x_503_, 1);
v_startPos_505_ = lean_ctor_get(v_cur_492_, 2);
v___x_506_ = lean_nat_dec_le(v_val_504_, v_startPos_505_);
lean_dec(v_val_504_);
if (v___x_506_ == 0)
{
goto v___jp_495_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref(v_cur_492_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_a_494_);
return v___x_508_;
}
}
v___jp_495_:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars(v_closer_493_);
lean_inc_ref(v_cur_492_);
v___x_497_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast(v_s_491_, v_cur_492_, v___x_496_);
lean_dec(v___x_496_);
if (lean_obj_tag(v___x_497_) == 1)
{
lean_object* v___x_498_; 
lean_dec_ref(v_cur_492_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_a_494_);
return v___x_498_;
}
else
{
lean_object* v_startPos_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec(v___x_497_);
v_startPos_499_ = lean_ctor_get(v_cur_492_, 2);
lean_inc(v_startPos_499_);
lean_dec_ref(v_cur_492_);
v___x_500_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlScanMemo_recordFailure___redArg(v_a_494_, v_closer_493_, v_startPos_499_);
v___x_501_ = lean_box(0);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser___boxed(lean_object* v_s_509_, lean_object* v_cur_510_, lean_object* v_closer_511_, lean_object* v_a_512_){
_start:
{
uint8_t v_closer_boxed_513_; lean_object* v_res_514_; 
v_closer_boxed_513_ = lean_unbox(v_closer_511_);
v_res_514_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser(v_s_509_, v_cur_510_, v_closer_boxed_513_, v_a_512_);
lean_dec_ref(v_s_509_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0_spec__0(lean_object* v_s_515_, lean_object* v_q_516_, lean_object* v_lineEnd_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_q_516_, v___x_518_);
v___x_520_ = lean_nat_dec_le(v___x_519_, v_lineEnd_517_);
lean_dec(v___x_519_);
if (v___x_520_ == 0)
{
return v_q_516_;
}
else
{
lean_object* v_str_521_; lean_object* v_startInclusive_522_; lean_object* v___x_523_; uint32_t v___x_524_; uint8_t v___x_525_; 
v_str_521_ = lean_ctor_get(v_s_515_, 0);
v_startInclusive_522_ = lean_ctor_get(v_s_515_, 1);
v___x_523_ = lean_nat_add(v_startInclusive_522_, v_q_516_);
v___x_524_ = lean_string_utf8_get_fast(v_str_521_, v___x_523_);
v___x_525_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isUnquotedValueChar(v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v___x_523_);
return v_q_516_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v_q_516_);
v___x_526_ = lean_string_utf8_next_fast(v_str_521_, v___x_523_);
lean_dec(v___x_523_);
v___x_527_ = lean_nat_sub(v___x_526_, v_startInclusive_522_);
v_q_516_ = v___x_527_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0_spec__0___boxed(lean_object* v_s_529_, lean_object* v_q_530_, lean_object* v_lineEnd_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0_spec__0(v_s_529_, v_q_530_, v_lineEnd_531_);
lean_dec(v_lineEnd_531_);
lean_dec_ref(v_s_529_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0(lean_object* v_s_533_, lean_object* v_cur_534_){
_start:
{
lean_object* v_source_535_; lean_object* v_line_536_; lean_object* v_startPos_537_; lean_object* v_stopPos_538_; lean_object* v___y_540_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_source_535_ = lean_ctor_get(v_cur_534_, 0);
v_line_536_ = lean_ctor_get(v_cur_534_, 1);
v_startPos_537_ = lean_ctor_get(v_cur_534_, 2);
v_stopPos_538_ = lean_ctor_get(v_cur_534_, 3);
v___x_583_ = lean_array_get_size(v_source_535_);
v___x_584_ = lean_nat_dec_lt(v_line_536_, v___x_583_);
if (v___x_584_ == 0)
{
lean_inc(v_stopPos_538_);
v___y_540_ = v_stopPos_538_;
goto v___jp_539_;
}
else
{
lean_object* v___x_585_; lean_object* v_endExclusive_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_585_ = lean_array_fget_borrowed(v_source_535_, v_line_536_);
v_endExclusive_586_ = lean_ctor_get(v___x_585_, 1);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = lean_nat_add(v_endExclusive_586_, v___x_587_);
v___x_589_ = lean_nat_dec_le(v___x_588_, v_stopPos_538_);
lean_dec(v___x_588_);
if (v___x_589_ == 0)
{
lean_inc(v_stopPos_538_);
v___y_540_ = v_stopPos_538_;
goto v___jp_539_;
}
else
{
lean_inc(v_endExclusive_586_);
v___y_540_ = v_endExclusive_586_;
goto v___jp_539_;
}
}
v___jp_539_:
{
lean_object* v_pos_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
lean_inc(v_startPos_537_);
v_pos_541_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0_spec__0(v_s_533_, v_startPos_537_, v___y_540_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_pos_541_, v___x_542_);
v___x_544_ = lean_nat_dec_le(v___x_543_, v___y_540_);
lean_dec(v___x_543_);
if (v___x_544_ == 0)
{
uint8_t v_decide_545_; 
v_decide_545_ = lean_nat_dec_eq(v___y_540_, v_stopPos_538_);
if (v_decide_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v_pos_541_);
v___x_546_ = l_String_Slice_Pos_prev_x3f(v_s_533_, v___y_540_);
lean_dec(v___y_540_);
if (lean_obj_tag(v___x_546_) == 0)
{
return v_cur_534_;
}
else
{
lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_556_; 
lean_inc(v_stopPos_538_);
lean_inc(v_line_536_);
lean_inc_ref(v_source_535_);
v_isSharedCheck_556_ = !lean_is_exclusive(v_cur_534_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; lean_object* v_unused_558_; lean_object* v_unused_559_; lean_object* v_unused_560_; 
v_unused_557_ = lean_ctor_get(v_cur_534_, 3);
lean_dec(v_unused_557_);
v_unused_558_ = lean_ctor_get(v_cur_534_, 2);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_cur_534_, 1);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v_cur_534_, 0);
lean_dec(v_unused_560_);
v___x_548_ = v_cur_534_;
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
else
{
lean_dec(v_cur_534_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_556_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v_val_550_; lean_object* v___x_552_; 
v_val_550_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_val_550_);
lean_dec_ref_known(v___x_546_, 1);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v_val_550_);
v___x_552_ = v___x_548_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_source_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_line_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_val_550_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_stopPos_538_);
v___x_552_ = v_reuseFailAlloc_555_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Markdown_InlineCursor_drop1(v_s_533_, v___x_552_);
v_cur_534_ = v___x_553_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_inc(v_stopPos_538_);
lean_inc(v_line_536_);
lean_inc_ref(v_source_535_);
lean_dec(v___y_540_);
v_isSharedCheck_567_ = !lean_is_exclusive(v_cur_534_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; lean_object* v_unused_571_; 
v_unused_568_ = lean_ctor_get(v_cur_534_, 3);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_cur_534_, 2);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_cur_534_, 1);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_cur_534_, 0);
lean_dec(v_unused_571_);
v___x_562_ = v_cur_534_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_dec(v_cur_534_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 2, v_pos_541_);
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_source_535_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_line_536_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v_pos_541_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v_stopPos_538_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_inc(v_stopPos_538_);
lean_inc(v_line_536_);
lean_inc_ref(v_source_535_);
lean_dec(v___y_540_);
v_isSharedCheck_578_ = !lean_is_exclusive(v_cur_534_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; lean_object* v_unused_580_; lean_object* v_unused_581_; lean_object* v_unused_582_; 
v_unused_579_ = lean_ctor_get(v_cur_534_, 3);
lean_dec(v_unused_579_);
v_unused_580_ = lean_ctor_get(v_cur_534_, 2);
lean_dec(v_unused_580_);
v_unused_581_ = lean_ctor_get(v_cur_534_, 1);
lean_dec(v_unused_581_);
v_unused_582_ = lean_ctor_get(v_cur_534_, 0);
lean_dec(v_unused_582_);
v___x_573_ = v_cur_534_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_dec(v_cur_534_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 2, v_pos_541_);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_source_535_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_line_536_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_pos_541_);
lean_ctor_set(v_reuseFailAlloc_577_, 3, v_stopPos_538_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0___boxed(lean_object* v_s_590_, lean_object* v_cur_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0(v_s_590_, v_cur_591_);
lean_dec_ref(v_s_590_);
return v_res_592_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_593_; lean_object* v___x_594_; 
v___x_593_ = 39;
v___x_594_ = lean_box_uint32(v___x_593_);
return v___x_594_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
v___x_596_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0___boxed__const__1;
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_598_; lean_object* v___x_599_; 
v___x_598_ = 34;
v___x_599_ = lean_box_uint32(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1___boxed__const__1;
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f(lean_object* v_s_603_, lean_object* v_cur_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_603_, v_cur_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_606_; 
lean_dec_ref(v_cur_604_);
v___x_606_ = lean_box(0);
return v___x_606_;
}
else
{
lean_object* v_val_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_630_; 
v_val_607_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_630_ == 0)
{
v___x_609_ = v___x_605_;
v_isShared_610_ = v_isSharedCheck_630_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_val_607_);
lean_dec(v___x_605_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_630_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
uint32_t v___x_611_; uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_611_ = 34;
v___x_612_ = lean_unbox_uint32(v_val_607_);
v___x_613_ = lean_uint32_dec_eq(v___x_612_, v___x_611_);
if (v___x_613_ == 0)
{
uint32_t v___x_614_; uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_614_ = 39;
v___x_615_ = lean_unbox_uint32(v_val_607_);
v___x_616_ = lean_uint32_dec_eq(v___x_615_, v___x_614_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_unbox_uint32(v_val_607_);
lean_dec(v_val_607_);
v___x_618_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isUnquotedValueChar(v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_del_object(v___x_609_);
lean_dec_ref(v_cur_604_);
v___x_619_ = lean_box(0);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_620_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f_spec__0(v_s_603_, v_cur_604_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_620_);
v___x_622_ = v___x_609_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_609_);
lean_dec(v_val_607_);
v___x_624_ = l_Lean_Markdown_InlineCursor_drop1(v_s_603_, v_cur_604_);
v___x_625_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0);
v___x_626_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast(v_s_603_, v___x_624_, v___x_625_);
return v___x_626_;
}
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
lean_del_object(v___x_609_);
lean_dec(v_val_607_);
v___x_627_ = l_Lean_Markdown_InlineCursor_drop1(v_s_603_, v_cur_604_);
v___x_628_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1);
v___x_629_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePast(v_s_603_, v___x_627_, v___x_628_);
return v___x_629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___boxed(lean_object* v_s_631_, lean_object* v_cur_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f(v_s_631_, v_cur_632_);
lean_dec_ref(v_s_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1_spec__2(lean_object* v_s_634_, lean_object* v_q_635_, lean_object* v_lineEnd_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v_q_635_, v___x_637_);
v___x_639_ = lean_nat_dec_le(v___x_638_, v_lineEnd_636_);
lean_dec(v___x_638_);
if (v___x_639_ == 0)
{
return v_q_635_;
}
else
{
lean_object* v_str_640_; lean_object* v_startInclusive_641_; lean_object* v___x_642_; uint32_t v___x_643_; uint8_t v___x_644_; 
v_str_640_ = lean_ctor_get(v_s_634_, 0);
v_startInclusive_641_ = lean_ctor_get(v_s_634_, 1);
v___x_642_ = lean_nat_add(v_startInclusive_641_, v_q_635_);
v___x_643_ = lean_string_utf8_get_fast(v_str_640_, v___x_642_);
v___x_644_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameChar(v___x_643_);
if (v___x_644_ == 0)
{
lean_dec(v___x_642_);
return v_q_635_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_q_635_);
v___x_645_ = lean_string_utf8_next_fast(v_str_640_, v___x_642_);
lean_dec(v___x_642_);
v___x_646_ = lean_nat_sub(v___x_645_, v_startInclusive_641_);
v_q_635_ = v___x_646_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1_spec__2___boxed(lean_object* v_s_648_, lean_object* v_q_649_, lean_object* v_lineEnd_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1_spec__2(v_s_648_, v_q_649_, v_lineEnd_650_);
lean_dec(v_lineEnd_650_);
lean_dec_ref(v_s_648_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1(lean_object* v_s_652_, lean_object* v_cur_653_){
_start:
{
lean_object* v_source_654_; lean_object* v_line_655_; lean_object* v_startPos_656_; lean_object* v_stopPos_657_; lean_object* v___y_659_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_source_654_ = lean_ctor_get(v_cur_653_, 0);
v_line_655_ = lean_ctor_get(v_cur_653_, 1);
v_startPos_656_ = lean_ctor_get(v_cur_653_, 2);
v_stopPos_657_ = lean_ctor_get(v_cur_653_, 3);
v___x_702_ = lean_array_get_size(v_source_654_);
v___x_703_ = lean_nat_dec_lt(v_line_655_, v___x_702_);
if (v___x_703_ == 0)
{
lean_inc(v_stopPos_657_);
v___y_659_ = v_stopPos_657_;
goto v___jp_658_;
}
else
{
lean_object* v___x_704_; lean_object* v_endExclusive_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_704_ = lean_array_fget_borrowed(v_source_654_, v_line_655_);
v_endExclusive_705_ = lean_ctor_get(v___x_704_, 1);
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = lean_nat_add(v_endExclusive_705_, v___x_706_);
v___x_708_ = lean_nat_dec_le(v___x_707_, v_stopPos_657_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
lean_inc(v_stopPos_657_);
v___y_659_ = v_stopPos_657_;
goto v___jp_658_;
}
else
{
lean_inc(v_endExclusive_705_);
v___y_659_ = v_endExclusive_705_;
goto v___jp_658_;
}
}
v___jp_658_:
{
lean_object* v_pos_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
lean_inc(v_startPos_656_);
v_pos_660_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1_spec__2(v_s_652_, v_startPos_656_, v___y_659_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_add(v_pos_660_, v___x_661_);
v___x_663_ = lean_nat_dec_le(v___x_662_, v___y_659_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
uint8_t v_decide_664_; 
v_decide_664_ = lean_nat_dec_eq(v___y_659_, v_stopPos_657_);
if (v_decide_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v_pos_660_);
v___x_665_ = l_String_Slice_Pos_prev_x3f(v_s_652_, v___y_659_);
lean_dec(v___y_659_);
if (lean_obj_tag(v___x_665_) == 0)
{
return v_cur_653_;
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_675_; 
lean_inc(v_stopPos_657_);
lean_inc(v_line_655_);
lean_inc_ref(v_source_654_);
v_isSharedCheck_675_ = !lean_is_exclusive(v_cur_653_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; lean_object* v_unused_678_; lean_object* v_unused_679_; 
v_unused_676_ = lean_ctor_get(v_cur_653_, 3);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_cur_653_, 2);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_cur_653_, 1);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_cur_653_, 0);
lean_dec(v_unused_679_);
v___x_667_ = v_cur_653_;
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
else
{
lean_dec(v_cur_653_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_675_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_val_669_; lean_object* v___x_671_; 
v_val_669_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_665_, 1);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 2, v_val_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_source_654_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_line_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_val_669_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_stopPos_657_);
v___x_671_ = v_reuseFailAlloc_674_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Markdown_InlineCursor_drop1(v_s_652_, v___x_671_);
v_cur_653_ = v___x_672_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_inc(v_stopPos_657_);
lean_inc(v_line_655_);
lean_inc_ref(v_source_654_);
lean_dec(v___y_659_);
v_isSharedCheck_686_ = !lean_is_exclusive(v_cur_653_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; lean_object* v_unused_690_; 
v_unused_687_ = lean_ctor_get(v_cur_653_, 3);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_cur_653_, 2);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_cur_653_, 1);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_cur_653_, 0);
lean_dec(v_unused_690_);
v___x_681_ = v_cur_653_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_cur_653_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v_pos_660_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_source_654_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_line_655_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v_pos_660_);
lean_ctor_set(v_reuseFailAlloc_685_, 3, v_stopPos_657_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_inc(v_stopPos_657_);
lean_inc(v_line_655_);
lean_inc_ref(v_source_654_);
lean_dec(v___y_659_);
v_isSharedCheck_697_ = !lean_is_exclusive(v_cur_653_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; lean_object* v_unused_699_; lean_object* v_unused_700_; lean_object* v_unused_701_; 
v_unused_698_ = lean_ctor_get(v_cur_653_, 3);
lean_dec(v_unused_698_);
v_unused_699_ = lean_ctor_get(v_cur_653_, 2);
lean_dec(v_unused_699_);
v_unused_700_ = lean_ctor_get(v_cur_653_, 1);
lean_dec(v_unused_700_);
v_unused_701_ = lean_ctor_get(v_cur_653_, 0);
lean_dec(v_unused_701_);
v___x_692_ = v_cur_653_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_dec(v_cur_653_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 2, v_pos_660_);
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_source_654_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_line_655_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_pos_660_);
lean_ctor_set(v_reuseFailAlloc_696_, 3, v_stopPos_657_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1___boxed(lean_object* v_s_709_, lean_object* v_cur_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1(v_s_709_, v_cur_710_);
lean_dec_ref(v_s_709_);
return v_res_711_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0___boxed__const__1;
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_714_; lean_object* v___x_715_; 
v___x_714_ = 47;
v___x_715_ = lean_box_uint32(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1___boxed__const__1;
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_718_; lean_object* v___x_719_; 
v___x_718_ = 61;
v___x_719_ = lean_box_uint32(v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2___boxed__const__1;
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg(lean_object* v_s_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_snd_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_768_; 
v_snd_724_ = lean_ctor_get(v_a_723_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_a_723_, 0);
lean_dec(v_unused_769_);
v___x_726_ = v_a_723_;
v_isShared_727_ = v_isSharedCheck_768_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_snd_724_);
lean_dec(v_a_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_768_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___y_729_; lean_object* v___x_740_; lean_object* v_startPos_746_; lean_object* v_startPos_747_; uint8_t v_decide_748_; 
lean_inc(v_snd_724_);
v___x_740_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace(v_s_722_, v_snd_724_);
v_startPos_746_ = lean_ctor_get(v___x_740_, 2);
v_startPos_747_ = lean_ctor_get(v_snd_724_, 2);
v_decide_748_ = lean_nat_dec_eq(v_startPos_746_, v_startPos_747_);
if (v_decide_748_ == 0)
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_722_, v___x_740_);
if (lean_obj_tag(v___x_749_) == 0)
{
goto v___jp_741_;
}
else
{
lean_object* v_val_750_; uint32_t v___x_751_; uint8_t v___x_752_; 
v_val_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = lean_unbox_uint32(v_val_750_);
lean_dec(v_val_750_);
v___x_752_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isAttributeNameStart(v___x_751_);
if (v___x_752_ == 0)
{
goto v___jp_741_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
lean_del_object(v___x_726_);
lean_dec(v_snd_724_);
v___x_753_ = lean_box(0);
v___x_754_ = l_Lean_Markdown_InlineCursor_drop1(v_s_722_, v___x_740_);
v___x_755_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__1(v_s_722_, v___x_754_);
lean_inc_ref(v___x_755_);
v___x_756_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace(v_s_722_, v___x_755_);
v___x_757_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_722_, v___x_756_);
v___x_758_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2);
v___x_759_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v___x_757_, v___x_758_);
lean_dec(v___x_757_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; 
lean_dec_ref(v___x_756_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_753_);
lean_ctor_set(v___x_760_, 1, v___x_755_);
v_a_723_ = v___x_760_;
goto _start;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_dec_ref(v___x_755_);
v___x_762_ = l_Lean_Markdown_InlineCursor_drop1(v_s_722_, v___x_756_);
v___x_763_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace(v_s_722_, v___x_762_);
v___x_764_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f(v_s_722_, v___x_763_);
if (lean_obj_tag(v___x_764_) == 0)
{
return v___x_753_;
}
else
{
lean_object* v_val_765_; lean_object* v___x_766_; 
v_val_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_val_765_);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_753_);
lean_ctor_set(v___x_766_, 1, v_val_765_);
v_a_723_ = v___x_766_;
goto _start;
}
}
}
}
}
else
{
goto v___jp_741_;
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_722_, v___y_729_);
v___x_731_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0);
v___x_732_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v___x_730_, v___x_731_);
lean_dec(v___x_730_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec_ref(v___y_729_);
lean_del_object(v___x_726_);
lean_dec(v_snd_724_);
v___x_733_ = lean_box(0);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_734_ = l_Lean_Markdown_InlineCursor_drop1(v_s_722_, v___y_729_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v___x_735_);
v___x_737_ = v___x_726_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_724_);
v___x_737_ = v_reuseFailAlloc_739_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
v___jp_741_:
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_722_, v___x_740_);
v___x_743_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1);
v___x_744_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v___x_742_, v___x_743_);
lean_dec(v___x_742_);
if (v___x_744_ == 0)
{
v___y_729_ = v___x_740_;
goto v___jp_728_;
}
else
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Markdown_InlineCursor_drop1(v_s_722_, v___x_740_);
v___y_729_ = v___x_745_;
goto v___jp_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___boxed(lean_object* v_s_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg(v_s_770_, v_a_771_);
lean_dec_ref(v_s_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0_spec__0(lean_object* v_s_773_, lean_object* v_q_774_, lean_object* v_lineEnd_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = lean_nat_add(v_q_774_, v___x_776_);
v___x_778_ = lean_nat_dec_le(v___x_777_, v_lineEnd_775_);
lean_dec(v___x_777_);
if (v___x_778_ == 0)
{
return v_q_774_;
}
else
{
lean_object* v_str_779_; lean_object* v_startInclusive_780_; lean_object* v___x_781_; uint32_t v___x_782_; uint8_t v___x_783_; 
v_str_779_ = lean_ctor_get(v_s_773_, 0);
v_startInclusive_780_ = lean_ctor_get(v_s_773_, 1);
v___x_781_ = lean_nat_add(v_startInclusive_780_, v_q_774_);
v___x_782_ = lean_string_utf8_get_fast(v_str_779_, v___x_781_);
v___x_783_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_isTagNameChar(v___x_782_);
if (v___x_783_ == 0)
{
lean_dec(v___x_781_);
return v_q_774_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec(v_q_774_);
v___x_784_ = lean_string_utf8_next_fast(v_str_779_, v___x_781_);
lean_dec(v___x_781_);
v___x_785_ = lean_nat_sub(v___x_784_, v_startInclusive_780_);
v_q_774_ = v___x_785_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0_spec__0___boxed(lean_object* v_s_787_, lean_object* v_q_788_, lean_object* v_lineEnd_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0_spec__0(v_s_787_, v_q_788_, v_lineEnd_789_);
lean_dec(v_lineEnd_789_);
lean_dec_ref(v_s_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0(lean_object* v_s_791_, lean_object* v_cur_792_){
_start:
{
lean_object* v_source_793_; lean_object* v_line_794_; lean_object* v_startPos_795_; lean_object* v_stopPos_796_; lean_object* v___y_798_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_source_793_ = lean_ctor_get(v_cur_792_, 0);
v_line_794_ = lean_ctor_get(v_cur_792_, 1);
v_startPos_795_ = lean_ctor_get(v_cur_792_, 2);
v_stopPos_796_ = lean_ctor_get(v_cur_792_, 3);
v___x_841_ = lean_array_get_size(v_source_793_);
v___x_842_ = lean_nat_dec_lt(v_line_794_, v___x_841_);
if (v___x_842_ == 0)
{
lean_inc(v_stopPos_796_);
v___y_798_ = v_stopPos_796_;
goto v___jp_797_;
}
else
{
lean_object* v___x_843_; lean_object* v_endExclusive_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_843_ = lean_array_fget_borrowed(v_source_793_, v_line_794_);
v_endExclusive_844_ = lean_ctor_get(v___x_843_, 1);
v___x_845_ = lean_unsigned_to_nat(1u);
v___x_846_ = lean_nat_add(v_endExclusive_844_, v___x_845_);
v___x_847_ = lean_nat_dec_le(v___x_846_, v_stopPos_796_);
lean_dec(v___x_846_);
if (v___x_847_ == 0)
{
lean_inc(v_stopPos_796_);
v___y_798_ = v_stopPos_796_;
goto v___jp_797_;
}
else
{
lean_inc(v_endExclusive_844_);
v___y_798_ = v_endExclusive_844_;
goto v___jp_797_;
}
}
v___jp_797_:
{
lean_object* v_pos_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
lean_inc(v_startPos_795_);
v_pos_799_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0_spec__0(v_s_791_, v_startPos_795_, v___y_798_);
v___x_800_ = lean_unsigned_to_nat(1u);
v___x_801_ = lean_nat_add(v_pos_799_, v___x_800_);
v___x_802_ = lean_nat_dec_le(v___x_801_, v___y_798_);
lean_dec(v___x_801_);
if (v___x_802_ == 0)
{
uint8_t v_decide_803_; 
v_decide_803_ = lean_nat_dec_eq(v___y_798_, v_stopPos_796_);
if (v_decide_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_pos_799_);
v___x_804_ = l_String_Slice_Pos_prev_x3f(v_s_791_, v___y_798_);
lean_dec(v___y_798_);
if (lean_obj_tag(v___x_804_) == 0)
{
return v_cur_792_;
}
else
{
lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_814_; 
lean_inc(v_stopPos_796_);
lean_inc(v_line_794_);
lean_inc_ref(v_source_793_);
v_isSharedCheck_814_ = !lean_is_exclusive(v_cur_792_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; lean_object* v_unused_816_; lean_object* v_unused_817_; lean_object* v_unused_818_; 
v_unused_815_ = lean_ctor_get(v_cur_792_, 3);
lean_dec(v_unused_815_);
v_unused_816_ = lean_ctor_get(v_cur_792_, 2);
lean_dec(v_unused_816_);
v_unused_817_ = lean_ctor_get(v_cur_792_, 1);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_cur_792_, 0);
lean_dec(v_unused_818_);
v___x_806_ = v_cur_792_;
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
else
{
lean_dec(v_cur_792_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_val_808_; lean_object* v___x_810_; 
v_val_808_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___x_804_, 1);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 2, v_val_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_source_793_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_line_794_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_val_808_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_stopPos_796_);
v___x_810_ = v_reuseFailAlloc_813_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Markdown_InlineCursor_drop1(v_s_791_, v___x_810_);
v_cur_792_ = v___x_811_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_inc(v_stopPos_796_);
lean_inc(v_line_794_);
lean_inc_ref(v_source_793_);
lean_dec(v___y_798_);
v_isSharedCheck_825_ = !lean_is_exclusive(v_cur_792_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; lean_object* v_unused_827_; lean_object* v_unused_828_; lean_object* v_unused_829_; 
v_unused_826_ = lean_ctor_get(v_cur_792_, 3);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_cur_792_, 2);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_cur_792_, 1);
lean_dec(v_unused_828_);
v_unused_829_ = lean_ctor_get(v_cur_792_, 0);
lean_dec(v_unused_829_);
v___x_820_ = v_cur_792_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_dec(v_cur_792_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 2, v_pos_799_);
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_source_793_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_line_794_);
lean_ctor_set(v_reuseFailAlloc_824_, 2, v_pos_799_);
lean_ctor_set(v_reuseFailAlloc_824_, 3, v_stopPos_796_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_inc(v_stopPos_796_);
lean_inc(v_line_794_);
lean_inc_ref(v_source_793_);
lean_dec(v___y_798_);
v_isSharedCheck_836_ = !lean_is_exclusive(v_cur_792_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; 
v_unused_837_ = lean_ctor_get(v_cur_792_, 3);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_cur_792_, 2);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_cur_792_, 1);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_cur_792_, 0);
lean_dec(v_unused_840_);
v___x_831_ = v_cur_792_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_cur_792_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 2, v_pos_799_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_source_793_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_line_794_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_pos_799_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_stopPos_796_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0___boxed(lean_object* v_s_848_, lean_object* v_cur_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0(v_s_848_, v_cur_849_);
lean_dec_ref(v_s_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseOpenTag_x3f(lean_object* v_s_851_, lean_object* v_cur_852_){
_start:
{
lean_object* v___x_853_; lean_object* v_cur_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = l_Lean_Markdown_InlineCursor_drop1(v_s_851_, v_cur_852_);
v_cur_854_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0(v_s_851_, v___x_853_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_cur_854_);
v___x_857_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg(v_s_851_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
return v___x_855_;
}
else
{
lean_object* v_val_858_; lean_object* v_fst_859_; 
v_val_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___x_857_, 1);
v_fst_859_ = lean_ctor_get(v_val_858_, 0);
lean_inc(v_fst_859_);
lean_dec(v_val_858_);
if (lean_obj_tag(v_fst_859_) == 0)
{
return v___x_855_;
}
else
{
return v_fst_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseOpenTag_x3f___boxed(lean_object* v_s_860_, lean_object* v_cur_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Markdown_parseOpenTag_x3f(v_s_860_, v_cur_861_);
lean_dec_ref(v_s_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2(lean_object* v_s_863_, lean_object* v_inst_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg(v_s_863_, v_a_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___boxed(lean_object* v_s_867_, lean_object* v_inst_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2(v_s_867_, v_inst_868_, v_a_869_);
lean_dec_ref(v_s_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseClosingTag_x3f(lean_object* v_s_871_, lean_object* v_cur_872_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_871_, v_cur_872_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v_cur_872_);
v___x_884_ = lean_box(0);
return v___x_884_;
}
else
{
lean_object* v_val_885_; uint32_t v___x_895_; uint32_t v___x_896_; uint8_t v___x_897_; 
v_val_885_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v___x_883_, 1);
v___x_895_ = 65;
v___x_896_ = lean_unbox_uint32(v_val_885_);
v___x_897_ = lean_uint32_dec_le(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
goto v___jp_886_;
}
else
{
uint32_t v___x_898_; uint32_t v___x_899_; uint8_t v___x_900_; 
v___x_898_ = 90;
v___x_899_ = lean_unbox_uint32(v_val_885_);
v___x_900_ = lean_uint32_dec_le(v___x_899_, v___x_898_);
if (v___x_900_ == 0)
{
goto v___jp_886_;
}
else
{
lean_dec(v_val_885_);
goto v___jp_873_;
}
}
v___jp_886_:
{
uint32_t v___x_887_; uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_887_ = 97;
v___x_888_ = lean_unbox_uint32(v_val_885_);
v___x_889_ = lean_uint32_dec_le(v___x_887_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_val_885_);
lean_dec_ref(v_cur_872_);
v___x_890_ = lean_box(0);
return v___x_890_;
}
else
{
uint32_t v___x_891_; uint32_t v___x_892_; uint8_t v___x_893_; 
v___x_891_ = 122;
v___x_892_ = lean_unbox_uint32(v_val_885_);
lean_dec(v_val_885_);
v___x_893_ = lean_uint32_dec_le(v___x_892_, v___x_891_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
lean_dec_ref(v_cur_872_);
v___x_894_ = lean_box(0);
return v___x_894_;
}
else
{
goto v___jp_873_;
}
}
}
}
v___jp_873_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_874_ = l_Lean_Markdown_InlineCursor_drop1(v_s_871_, v_cur_872_);
v___x_875_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseOpenTag_x3f_spec__0(v_s_871_, v___x_874_);
v___x_876_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_skipTagWhitespace(v_s_871_, v___x_875_);
v___x_877_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_871_, v___x_876_);
v___x_878_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0);
v___x_879_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v___x_877_, v___x_878_);
lean_dec(v___x_877_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
lean_dec_ref(v___x_876_);
v___x_880_ = lean_box(0);
return v___x_880_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = l_Lean_Markdown_InlineCursor_drop1(v_s_871_, v___x_876_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseClosingTag_x3f___boxed(lean_object* v_s_901_, lean_object* v_cur_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Markdown_parseClosingTag_x3f(v_s_901_, v_cur_902_);
lean_dec_ref(v_s_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseProcessingInstruction_x3f(lean_object* v_s_904_, lean_object* v_cur_905_, lean_object* v_a_906_){
_start:
{
uint8_t v___x_907_; lean_object* v___x_908_; 
v___x_907_ = 1;
v___x_908_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser(v_s_904_, v_cur_905_, v___x_907_, v_a_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseProcessingInstruction_x3f___boxed(lean_object* v_s_909_, lean_object* v_cur_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Markdown_parseProcessingInstruction_x3f(v_s_909_, v_cur_910_, v_a_911_);
lean_dec_ref(v_s_909_);
return v_res_912_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(0);
v___x_914_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1;
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__0, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__0_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__0);
v___x_917_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1;
v___x_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_919_; lean_object* v___x_920_; 
v___x_919_ = 91;
v___x_920_ = lean_box_uint32(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_box(0);
v___x_922_ = l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2___boxed__const__1;
v___x_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_924_; lean_object* v___x_925_; 
v___x_924_ = 65;
v___x_925_ = lean_box_uint32(v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2);
v___x_927_ = l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3___boxed__const__1;
v___x_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_926_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4___boxed__const__1(void){
_start:
{
uint32_t v___x_929_; lean_object* v___x_930_; 
v___x_929_ = 84;
v___x_930_ = lean_box_uint32(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3);
v___x_932_ = l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4___boxed__const__1;
v___x_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__5(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4);
v___x_935_ = l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3___boxed__const__1;
v___x_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6___boxed__const__1(void){
_start:
{
uint32_t v___x_937_; lean_object* v___x_938_; 
v___x_937_ = 68;
v___x_938_ = lean_box_uint32(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__5, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__5_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__5);
v___x_940_ = l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6___boxed__const__1;
v___x_941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7___boxed__const__1(void){
_start:
{
uint32_t v___x_942_; lean_object* v___x_943_; 
v___x_942_ = 67;
v___x_943_ = lean_box_uint32(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6);
v___x_945_ = l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7___boxed__const__1;
v___x_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__8(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7);
v___x_948_ = l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2___boxed__const__1;
v___x_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f(lean_object* v_s_950_, lean_object* v_cur_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__1, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__1_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__1);
lean_inc_ref(v_cur_951_);
v___x_961_ = l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(v_s_950_, v_cur_951_, v___x_960_);
if (lean_obj_tag(v___x_961_) == 1)
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v_cur_951_);
v_val_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_979_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_979_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_979_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_966_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_950_, v_val_962_);
v___x_967_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__0);
v___x_968_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v___x_966_, v___x_967_);
lean_dec(v___x_966_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_del_object(v___x_964_);
v___x_969_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1, &l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1_once, _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1);
lean_inc(v_val_962_);
v___x_970_ = l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(v_s_950_, v_val_962_, v___x_969_);
if (lean_obj_tag(v___x_970_) == 1)
{
lean_object* v___x_971_; 
lean_dec(v_val_962_);
v___x_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set(v___x_971_, 1, v_a_952_);
return v___x_971_;
}
else
{
uint8_t v___x_972_; lean_object* v___x_973_; 
lean_dec(v___x_970_);
v___x_972_ = 0;
v___x_973_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser(v_s_950_, v_val_962_, v___x_972_, v_a_952_);
return v___x_973_;
}
}
else
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = l_Lean_Markdown_InlineCursor_drop1(v_s_950_, v_val_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_974_);
v___x_976_ = v___x_964_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_978_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v_a_952_);
return v___x_977_;
}
}
}
}
else
{
uint32_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
lean_dec(v___x_961_);
v___x_980_ = 65;
v___x_981_ = lean_obj_once(&l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__8, &l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__8_once, _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__8);
lean_inc_ref(v_cur_951_);
v___x_982_ = l_List_foldlM___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__1(v_s_950_, v_cur_951_, v___x_981_);
if (lean_obj_tag(v___x_982_) == 1)
{
lean_object* v_val_983_; uint8_t v___x_984_; lean_object* v___x_985_; 
lean_dec_ref(v_cur_951_);
v_val_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_val_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = 2;
v___x_985_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser(v_s_950_, v_val_983_, v___x_984_, v_a_952_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; 
lean_dec(v___x_982_);
v___x_986_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_950_, v_cur_951_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_dec_ref(v_cur_951_);
goto v___jp_957_;
}
else
{
lean_object* v_val_987_; uint32_t v___x_995_; uint8_t v___x_996_; 
v_val_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v___x_986_, 1);
v___x_995_ = lean_unbox_uint32(v_val_987_);
v___x_996_ = lean_uint32_dec_le(v___x_980_, v___x_995_);
if (v___x_996_ == 0)
{
goto v___jp_988_;
}
else
{
uint32_t v___x_997_; uint32_t v___x_998_; uint8_t v___x_999_; 
v___x_997_ = 90;
v___x_998_ = lean_unbox_uint32(v_val_987_);
v___x_999_ = lean_uint32_dec_le(v___x_998_, v___x_997_);
if (v___x_999_ == 0)
{
goto v___jp_988_;
}
else
{
lean_dec(v_val_987_);
goto v___jp_953_;
}
}
v___jp_988_:
{
uint32_t v___x_989_; uint32_t v___x_990_; uint8_t v___x_991_; 
v___x_989_ = 97;
v___x_990_ = lean_unbox_uint32(v_val_987_);
v___x_991_ = lean_uint32_dec_le(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_val_987_);
lean_dec_ref(v_cur_951_);
goto v___jp_957_;
}
else
{
uint32_t v___x_992_; uint32_t v___x_993_; uint8_t v___x_994_; 
v___x_992_ = 122;
v___x_993_ = lean_unbox_uint32(v_val_987_);
lean_dec(v_val_987_);
v___x_994_ = lean_uint32_dec_le(v___x_993_, v___x_992_);
if (v___x_994_ == 0)
{
lean_dec_ref(v_cur_951_);
goto v___jp_957_;
}
else
{
goto v___jp_953_;
}
}
}
}
}
}
v___jp_953_:
{
lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
v___x_954_ = l_Lean_Markdown_InlineCursor_drop1(v_s_950_, v_cur_951_);
v___x_955_ = 3;
v___x_956_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_advancePastCloser(v_s_950_, v___x_954_, v___x_955_, v_a_952_);
return v___x_956_;
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_box(0);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v_a_952_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseMarkupDeclaration_x3f___boxed(lean_object* v_s_1000_, lean_object* v_cur_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Markdown_parseMarkupDeclaration_x3f(v_s_1000_, v_cur_1001_, v_a_1002_);
lean_dec_ref(v_s_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg(lean_object* v_s_1008_, lean_object* v_input_1009_, uint8_t v_ignoreCase_1010_, lean_object* v___x_1011_, lean_object* v_needle_1012_, lean_object* v_a_1013_, lean_object* v_b_1014_){
_start:
{
uint8_t v_decide_1015_; 
v_decide_1015_ = lean_nat_dec_eq(v_a_1013_, v___x_1011_);
if (v_decide_1015_ == 0)
{
lean_object* v_snd_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1055_; 
v_snd_1016_ = lean_ctor_get(v_b_1014_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_b_1014_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_b_1014_, 0);
lean_dec(v_unused_1056_);
v___x_1018_ = v_b_1014_;
v_isShared_1019_ = v_isSharedCheck_1055_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_snd_1016_);
lean_dec(v_b_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1055_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_endExclusive_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_endExclusive_1020_ = lean_ctor_get(v_input_1009_, 1);
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_nat_add(v_snd_1016_, v___x_1021_);
v___x_1023_ = lean_nat_dec_le(v___x_1022_, v_endExclusive_1020_);
lean_dec(v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_dec(v_a_1013_);
v___x_1024_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__0));
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1024_);
v___x_1026_ = v___x_1018_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_snd_1016_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
else
{
lean_object* v_str_1028_; lean_object* v_startInclusive_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint32_t v___x_1032_; uint32_t v___y_1034_; lean_object* v___x_1047_; uint32_t v___x_1048_; 
v_str_1028_ = lean_ctor_get(v_s_1008_, 0);
v_startInclusive_1029_ = lean_ctor_get(v_s_1008_, 1);
v___x_1030_ = lean_box(0);
v___x_1031_ = lean_string_utf8_next_fast(v_needle_1012_, v_a_1013_);
v___x_1032_ = lean_string_utf8_get_fast(v_needle_1012_, v_a_1013_);
lean_dec(v_a_1013_);
v___x_1047_ = lean_nat_add(v_startInclusive_1029_, v_snd_1016_);
v___x_1048_ = lean_string_utf8_get_fast(v_str_1028_, v___x_1047_);
lean_dec(v___x_1047_);
if (v_ignoreCase_1010_ == 0)
{
v___y_1034_ = v___x_1048_;
goto v___jp_1033_;
}
else
{
uint32_t v___x_1049_; uint8_t v___x_1050_; 
v___x_1049_ = 65;
v___x_1050_ = lean_uint32_dec_le(v___x_1049_, v___x_1048_);
if (v___x_1050_ == 0)
{
v___y_1034_ = v___x_1048_;
goto v___jp_1033_;
}
else
{
uint32_t v___x_1051_; uint8_t v___x_1052_; 
v___x_1051_ = 90;
v___x_1052_ = lean_uint32_dec_le(v___x_1048_, v___x_1051_);
if (v___x_1052_ == 0)
{
v___y_1034_ = v___x_1048_;
goto v___jp_1033_;
}
else
{
uint32_t v___x_1053_; uint32_t v___x_1054_; 
v___x_1053_ = 32;
v___x_1054_ = lean_uint32_add(v___x_1048_, v___x_1053_);
v___y_1034_ = v___x_1054_;
goto v___jp_1033_;
}
}
}
v___jp_1033_:
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_uint32_dec_eq(v___y_1034_, v___x_1032_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___closed__1));
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1036_);
v___x_1038_ = v___x_1018_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_snd_1016_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1040_ = lean_nat_add(v_startInclusive_1029_, v_snd_1016_);
lean_dec(v_snd_1016_);
v___x_1041_ = lean_string_utf8_next_fast(v_str_1028_, v___x_1040_);
lean_dec(v___x_1040_);
v___x_1042_ = lean_nat_sub(v___x_1041_, v_startInclusive_1029_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1042_);
lean_ctor_set(v___x_1018_, 0, v___x_1030_);
v___x_1044_ = v___x_1018_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
v_a_1013_ = v___x_1031_;
v_b_1014_ = v___x_1044_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec(v_a_1013_);
return v_b_1014_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg___boxed(lean_object* v_s_1057_, lean_object* v_input_1058_, lean_object* v_ignoreCase_1059_, lean_object* v___x_1060_, lean_object* v_needle_1061_, lean_object* v_a_1062_, lean_object* v_b_1063_){
_start:
{
uint8_t v_ignoreCase_boxed_1064_; lean_object* v_res_1065_; 
v_ignoreCase_boxed_1064_ = lean_unbox(v_ignoreCase_1059_);
v_res_1065_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg(v_s_1057_, v_input_1058_, v_ignoreCase_boxed_1064_, v___x_1060_, v_needle_1061_, v_a_1062_, v_b_1063_);
lean_dec_ref(v_needle_1061_);
lean_dec(v___x_1060_);
lean_dec_ref(v_input_1058_);
lean_dec_ref(v_s_1057_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f(lean_object* v_s_1066_, lean_object* v_input_1067_, lean_object* v_p_1068_, lean_object* v_needle_1069_, uint8_t v_ignoreCase_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_fst_1076_; 
v___x_1071_ = lean_string_utf8_byte_size(v_needle_1069_);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_p_1068_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg(v_s_1066_, v_input_1067_, v_ignoreCase_1070_, v___x_1071_, v_needle_1069_, v___x_1074_, v___x_1073_);
v_fst_1076_ = lean_ctor_get(v___x_1075_, 0);
if (lean_obj_tag(v_fst_1076_) == 0)
{
lean_object* v_snd_1077_; lean_object* v___x_1078_; 
v_snd_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc(v_snd_1077_);
lean_dec_ref(v___x_1075_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_snd_1077_);
return v___x_1078_;
}
else
{
lean_object* v_val_1079_; 
lean_inc_ref(v_fst_1076_);
lean_dec_ref(v___x_1075_);
v_val_1079_ = lean_ctor_get(v_fst_1076_, 0);
lean_inc(v_val_1079_);
lean_dec_ref_known(v_fst_1076_, 1);
return v_val_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f___boxed(lean_object* v_s_1080_, lean_object* v_input_1081_, lean_object* v_p_1082_, lean_object* v_needle_1083_, lean_object* v_ignoreCase_1084_){
_start:
{
uint8_t v_ignoreCase_boxed_1085_; lean_object* v_res_1086_; 
v_ignoreCase_boxed_1085_ = lean_unbox(v_ignoreCase_1084_);
v_res_1086_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f(v_s_1080_, v_input_1081_, v_p_1082_, v_needle_1083_, v_ignoreCase_boxed_1085_);
lean_dec_ref(v_needle_1083_);
lean_dec_ref(v_input_1081_);
lean_dec_ref(v_s_1080_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0(lean_object* v_s_1087_, lean_object* v_input_1088_, uint8_t v_ignoreCase_1089_, lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v_needle_1092_, lean_object* v_inst_1093_, lean_object* v_R_1094_, lean_object* v_a_1095_, lean_object* v_b_1096_, lean_object* v_c_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___redArg(v_s_1087_, v_input_1088_, v_ignoreCase_1089_, v___x_1090_, v_needle_1092_, v_a_1095_, v_b_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0___boxed(lean_object* v_s_1099_, lean_object* v_input_1100_, lean_object* v_ignoreCase_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v_needle_1104_, lean_object* v_inst_1105_, lean_object* v_R_1106_, lean_object* v_a_1107_, lean_object* v_b_1108_, lean_object* v_c_1109_){
_start:
{
uint8_t v_ignoreCase_boxed_1110_; lean_object* v_res_1111_; 
v_ignoreCase_boxed_1110_ = lean_unbox(v_ignoreCase_1101_);
v_res_1111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f_spec__0(v_s_1099_, v_input_1100_, v_ignoreCase_boxed_1110_, v___x_1102_, v___x_1103_, v_needle_1104_, v_inst_1105_, v_R_1106_, v_a_1107_, v_b_1108_, v_c_1109_);
lean_dec_ref(v_needle_1104_);
lean_dec_ref(v___x_1103_);
lean_dec(v___x_1102_);
lean_dec_ref(v_input_1100_);
lean_dec_ref(v_s_1099_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_startsWithAscii(lean_object* v_s_1112_, lean_object* v_text_1113_, lean_object* v_needle_1114_, uint8_t v_ignoreCase_1115_){
_start:
{
lean_object* v_startInclusive_1116_; lean_object* v___x_1117_; 
v_startInclusive_1116_ = lean_ctor_get(v_text_1113_, 0);
lean_inc(v_startInclusive_1116_);
v___x_1117_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f(v_s_1112_, v_text_1113_, v_startInclusive_1116_, v_needle_1114_, v_ignoreCase_1115_);
lean_dec_ref(v_text_1113_);
if (lean_obj_tag(v___x_1117_) == 0)
{
uint8_t v___x_1118_; 
v___x_1118_ = 0;
return v___x_1118_;
}
else
{
uint8_t v___x_1119_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = 1;
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_startsWithAscii___boxed(lean_object* v_s_1120_, lean_object* v_text_1121_, lean_object* v_needle_1122_, lean_object* v_ignoreCase_1123_){
_start:
{
uint8_t v_ignoreCase_boxed_1124_; uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_ignoreCase_boxed_1124_ = lean_unbox(v_ignoreCase_1123_);
v_res_1125_ = l_Lean_Markdown_startsWithAscii(v_s_1120_, v_text_1121_, v_needle_1122_, v_ignoreCase_boxed_1124_);
lean_dec_ref(v_needle_1122_);
lean_dec_ref(v_s_1120_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___redArg(lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
if (lean_obj_tag(v_x_1128_) == 0)
{
uint8_t v___x_1129_; 
v___x_1129_ = 1;
return v___x_1129_;
}
else
{
uint8_t v___x_1130_; 
v___x_1130_ = 0;
return v___x_1130_;
}
}
else
{
if (lean_obj_tag(v_x_1128_) == 0)
{
uint8_t v___x_1131_; 
v___x_1131_ = 0;
return v___x_1131_;
}
else
{
lean_object* v_val_1132_; lean_object* v_val_1133_; uint8_t v_decide_1134_; 
v_val_1132_ = lean_ctor_get(v_x_1127_, 0);
v_val_1133_ = lean_ctor_get(v_x_1128_, 0);
v_decide_1134_ = lean_nat_dec_eq(v_val_1132_, v_val_1133_);
return v_decide_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___redArg___boxed(lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___redArg(v_x_1135_, v_x_1136_);
lean_dec(v_x_1136_);
lean_dec(v_x_1135_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0(lean_object* v_s_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___redArg(v_x_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___boxed(lean_object* v_s_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0(v_s_1143_, v_x_1144_, v_x_1145_);
lean_dec(v_x_1145_);
lean_dec(v_x_1144_);
lean_dec_ref(v_s_1143_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii(lean_object* v_s_1148_, lean_object* v_text_1149_, lean_object* v_needle_1150_, uint8_t v_ignoreCase_1151_){
_start:
{
lean_object* v_startInclusive_1152_; lean_object* v_endExclusive_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_startInclusive_1152_ = lean_ctor_get(v_text_1149_, 0);
lean_inc(v_startInclusive_1152_);
v_endExclusive_1153_ = lean_ctor_get(v_text_1149_, 1);
lean_inc(v_endExclusive_1153_);
v___x_1154_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f(v_s_1148_, v_text_1149_, v_startInclusive_1152_, v_needle_1150_, v_ignoreCase_1151_);
lean_dec_ref(v_text_1149_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_endExclusive_1153_);
v___x_1156_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii_spec__0___redArg(v___x_1154_, v___x_1155_);
lean_dec_ref_known(v___x_1155_, 1);
lean_dec(v___x_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii___boxed(lean_object* v_s_1157_, lean_object* v_text_1158_, lean_object* v_needle_1159_, lean_object* v_ignoreCase_1160_){
_start:
{
uint8_t v_ignoreCase_boxed_1161_; uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_ignoreCase_boxed_1161_ = lean_unbox(v_ignoreCase_1160_);
v_res_1162_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii(v_s_1157_, v_text_1158_, v_needle_1159_, v_ignoreCase_boxed_1161_);
lean_dec_ref(v_needle_1159_);
lean_dec_ref(v_s_1157_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___redArg(lean_object* v_text_1164_, lean_object* v_s_1165_, lean_object* v_needle_1166_, uint8_t v_ignoreCase_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_snd_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1203_; 
v_snd_1169_ = lean_ctor_get(v_a_1168_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1168_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_a_1168_, 0);
lean_dec(v_unused_1204_);
v___x_1171_ = v_a_1168_;
v_isShared_1172_ = v_isSharedCheck_1203_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_snd_1169_);
lean_dec(v_a_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1203_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_endExclusive_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_endExclusive_1173_ = lean_ctor_get(v_text_1164_, 1);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_unsigned_to_nat(1u);
v___x_1176_ = lean_nat_add(v_snd_1169_, v___x_1175_);
v___x_1177_ = lean_nat_dec_le(v___x_1176_, v_endExclusive_1173_);
lean_dec(v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1179_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1174_);
v___x_1179_ = v___x_1171_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_snd_1169_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
else
{
lean_object* v___x_1181_; 
lean_inc(v_snd_1169_);
v___x_1181_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_matchAscii_x3f(v_s_1165_, v_text_1164_, v_snd_1169_, v_needle_1166_, v_ignoreCase_1167_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_str_1182_; lean_object* v_startInclusive_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v_str_1182_ = lean_ctor_get(v_s_1165_, 0);
v_startInclusive_1183_ = lean_ctor_get(v_s_1165_, 1);
v___x_1184_ = lean_nat_add(v_startInclusive_1183_, v_snd_1169_);
lean_dec(v_snd_1169_);
v___x_1185_ = lean_string_utf8_next_fast(v_str_1182_, v___x_1184_);
lean_dec(v___x_1184_);
v___x_1186_ = lean_nat_sub(v___x_1185_, v_startInclusive_1183_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v___x_1186_);
lean_ctor_set(v___x_1171_, 0, v___x_1174_);
v___x_1188_ = v___x_1171_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
v_a_1168_ = v___x_1188_;
goto _start;
}
}
else
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1201_; 
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1181_, 0);
lean_dec(v_unused_1202_);
v___x_1192_ = v___x_1181_;
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1181_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_box(v___x_1177_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1196_);
v___x_1198_ = v___x_1171_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_snd_1169_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___redArg___boxed(lean_object* v_text_1205_, lean_object* v_s_1206_, lean_object* v_needle_1207_, lean_object* v_ignoreCase_1208_, lean_object* v_a_1209_){
_start:
{
uint8_t v_ignoreCase_boxed_1210_; lean_object* v_res_1211_; 
v_ignoreCase_boxed_1210_ = lean_unbox(v_ignoreCase_1208_);
v_res_1211_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___redArg(v_text_1205_, v_s_1206_, v_needle_1207_, v_ignoreCase_boxed_1210_, v_a_1209_);
lean_dec_ref(v_needle_1207_);
lean_dec_ref(v_s_1206_);
lean_dec_ref(v_text_1205_);
return v_res_1211_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(lean_object* v_s_1212_, lean_object* v_text_1213_, lean_object* v_needle_1214_, uint8_t v_ignoreCase_1215_){
_start:
{
lean_object* v_startInclusive_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v_fst_1220_; 
v_startInclusive_1216_ = lean_ctor_get(v_text_1213_, 0);
v___x_1217_ = lean_box(0);
lean_inc(v_startInclusive_1216_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_startInclusive_1216_);
v___x_1219_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___redArg(v_text_1213_, v_s_1212_, v_needle_1214_, v_ignoreCase_1215_, v___x_1218_);
v_fst_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_fst_1220_);
lean_dec_ref(v___x_1219_);
if (lean_obj_tag(v_fst_1220_) == 0)
{
uint8_t v___x_1221_; 
v___x_1221_ = 0;
return v___x_1221_;
}
else
{
lean_object* v_val_1222_; uint8_t v___x_1223_; 
v_val_1222_ = lean_ctor_get(v_fst_1220_, 0);
lean_inc(v_val_1222_);
lean_dec_ref_known(v_fst_1220_, 1);
v___x_1223_ = lean_unbox(v_val_1222_);
lean_dec(v_val_1222_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii___boxed(lean_object* v_s_1224_, lean_object* v_text_1225_, lean_object* v_needle_1226_, lean_object* v_ignoreCase_1227_){
_start:
{
uint8_t v_ignoreCase_boxed_1228_; uint8_t v_res_1229_; lean_object* v_r_1230_; 
v_ignoreCase_boxed_1228_ = lean_unbox(v_ignoreCase_1227_);
v_res_1229_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(v_s_1224_, v_text_1225_, v_needle_1226_, v_ignoreCase_boxed_1228_);
lean_dec_ref(v_needle_1226_);
lean_dec_ref(v_text_1225_);
lean_dec_ref(v_s_1224_);
v_r_1230_ = lean_box(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0(lean_object* v_text_1231_, lean_object* v_s_1232_, lean_object* v_needle_1233_, uint8_t v_ignoreCase_1234_, lean_object* v_inst_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___redArg(v_text_1231_, v_s_1232_, v_needle_1233_, v_ignoreCase_1234_, v_a_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0___boxed(lean_object* v_text_1238_, lean_object* v_s_1239_, lean_object* v_needle_1240_, lean_object* v_ignoreCase_1241_, lean_object* v_inst_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_ignoreCase_boxed_1244_; lean_object* v_res_1245_; 
v_ignoreCase_boxed_1244_ = lean_unbox(v_ignoreCase_1241_);
v_res_1245_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii_spec__0(v_text_1238_, v_s_1239_, v_needle_1240_, v_ignoreCase_boxed_1244_, v_inst_1242_, v_a_1243_);
lean_dec_ref(v_needle_1240_);
lean_dec_ref(v_s_1239_);
lean_dec_ref(v_text_1238_);
return v_res_1245_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Markdown_isRawTextTagName_spec__0(lean_object* v_s_1246_, lean_object* v_name_1247_, lean_object* v_x_1248_){
_start:
{
if (lean_obj_tag(v_x_1248_) == 0)
{
uint8_t v___x_1249_; 
lean_dec_ref(v_name_1247_);
v___x_1249_ = 0;
return v___x_1249_;
}
else
{
lean_object* v_head_1250_; lean_object* v_tail_1251_; uint8_t v___x_1252_; uint8_t v___x_1253_; 
v_head_1250_ = lean_ctor_get(v_x_1248_, 0);
v_tail_1251_ = lean_ctor_get(v_x_1248_, 1);
v___x_1252_ = 1;
lean_inc_ref(v_name_1247_);
v___x_1253_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_equalsAscii(v_s_1246_, v_name_1247_, v_head_1250_, v___x_1252_);
if (v___x_1253_ == 0)
{
v_x_1248_ = v_tail_1251_;
goto _start;
}
else
{
lean_dec_ref(v_name_1247_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Markdown_isRawTextTagName_spec__0___boxed(lean_object* v_s_1255_, lean_object* v_name_1256_, lean_object* v_x_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_List_any___at___00Lean_Markdown_isRawTextTagName_spec__0(v_s_1255_, v_name_1256_, v_x_1257_);
lean_dec(v_x_1257_);
lean_dec_ref(v_s_1255_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_isRawTextTagName(lean_object* v_s_1276_, lean_object* v_name_1277_){
_start:
{
lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = ((lean_object*)(l_Lean_Markdown_isRawTextTagName___closed__7));
v___x_1279_ = l_List_any___at___00Lean_Markdown_isRawTextTagName_spec__0(v_s_1276_, v_name_1277_, v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_isRawTextTagName___boxed(lean_object* v_s_1280_, lean_object* v_name_1281_){
_start:
{
uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = l_Lean_Markdown_isRawTextTagName(v_s_1280_, v_name_1281_);
lean_dec_ref(v_s_1280_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_isBlockTagName(lean_object* v_s_1533_, lean_object* v_name_1534_){
_start:
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_blockTagNames));
v___x_1536_ = l_List_any___at___00Lean_Markdown_isRawTextTagName_spec__0(v_s_1533_, v_name_1534_, v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_isBlockTagName___boxed(lean_object* v_s_1537_, lean_object* v_name_1538_){
_start:
{
uint8_t v_res_1539_; lean_object* v_r_1540_; 
v_res_1539_ = l_Lean_Markdown_isBlockTagName(v_s_1537_, v_name_1538_);
lean_dec_ref(v_s_1537_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0_spec__0(lean_object* v_s_1541_, lean_object* v_q_1542_, lean_object* v_lineEnd_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = lean_nat_add(v_q_1542_, v___x_1544_);
v___x_1546_ = lean_nat_dec_le(v___x_1545_, v_lineEnd_1543_);
lean_dec(v___x_1545_);
if (v___x_1546_ == 0)
{
return v_q_1542_;
}
else
{
lean_object* v_str_1547_; lean_object* v_startInclusive_1548_; lean_object* v___x_1549_; uint32_t v___x_1554_; uint32_t v___x_1555_; uint8_t v___x_1556_; 
v_str_1547_ = lean_ctor_get(v_s_1541_, 0);
v_startInclusive_1548_ = lean_ctor_get(v_s_1541_, 1);
v___x_1549_ = lean_nat_add(v_startInclusive_1548_, v_q_1542_);
v___x_1554_ = lean_string_utf8_get_fast(v_str_1547_, v___x_1549_);
v___x_1555_ = 32;
v___x_1556_ = lean_uint32_dec_eq(v___x_1554_, v___x_1555_);
if (v___x_1556_ == 0)
{
uint32_t v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = 9;
v___x_1558_ = lean_uint32_dec_eq(v___x_1554_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec(v___x_1549_);
return v_q_1542_;
}
else
{
lean_dec(v_q_1542_);
goto v___jp_1550_;
}
}
else
{
lean_dec(v_q_1542_);
goto v___jp_1550_;
}
v___jp_1550_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_string_utf8_next_fast(v_str_1547_, v___x_1549_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_nat_sub(v___x_1551_, v_startInclusive_1548_);
v_q_1542_ = v___x_1552_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0_spec__0___boxed(lean_object* v_s_1559_, lean_object* v_q_1560_, lean_object* v_lineEnd_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0_spec__0(v_s_1559_, v_q_1560_, v_lineEnd_1561_);
lean_dec(v_lineEnd_1561_);
lean_dec_ref(v_s_1559_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0(lean_object* v_s_1563_, lean_object* v_cur_1564_){
_start:
{
lean_object* v_source_1565_; lean_object* v_line_1566_; lean_object* v_startPos_1567_; lean_object* v_stopPos_1568_; lean_object* v___y_1570_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_source_1565_ = lean_ctor_get(v_cur_1564_, 0);
v_line_1566_ = lean_ctor_get(v_cur_1564_, 1);
v_startPos_1567_ = lean_ctor_get(v_cur_1564_, 2);
v_stopPos_1568_ = lean_ctor_get(v_cur_1564_, 3);
v___x_1613_ = lean_array_get_size(v_source_1565_);
v___x_1614_ = lean_nat_dec_lt(v_line_1566_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_inc(v_stopPos_1568_);
v___y_1570_ = v_stopPos_1568_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1615_; lean_object* v_endExclusive_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1615_ = lean_array_fget_borrowed(v_source_1565_, v_line_1566_);
v_endExclusive_1616_ = lean_ctor_get(v___x_1615_, 1);
v___x_1617_ = lean_unsigned_to_nat(1u);
v___x_1618_ = lean_nat_add(v_endExclusive_1616_, v___x_1617_);
v___x_1619_ = lean_nat_dec_le(v___x_1618_, v_stopPos_1568_);
lean_dec(v___x_1618_);
if (v___x_1619_ == 0)
{
lean_inc(v_stopPos_1568_);
v___y_1570_ = v_stopPos_1568_;
goto v___jp_1569_;
}
else
{
lean_inc(v_endExclusive_1616_);
v___y_1570_ = v_endExclusive_1616_;
goto v___jp_1569_;
}
}
v___jp_1569_:
{
lean_object* v_pos_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
lean_inc(v_startPos_1567_);
v_pos_1571_ = l___private_Lean_Data_Markdown_InlineCursor_0__Lean_Markdown_InlineCursor_skipWhile_go___at___00Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0_spec__0(v_s_1563_, v_startPos_1567_, v___y_1570_);
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_add(v_pos_1571_, v___x_1572_);
v___x_1574_ = lean_nat_dec_le(v___x_1573_, v___y_1570_);
lean_dec(v___x_1573_);
if (v___x_1574_ == 0)
{
uint8_t v_decide_1575_; 
v_decide_1575_ = lean_nat_dec_eq(v___y_1570_, v_stopPos_1568_);
if (v_decide_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec(v_pos_1571_);
v___x_1576_ = l_String_Slice_Pos_prev_x3f(v_s_1563_, v___y_1570_);
lean_dec(v___y_1570_);
if (lean_obj_tag(v___x_1576_) == 0)
{
return v_cur_1564_;
}
else
{
lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1586_; 
lean_inc(v_stopPos_1568_);
lean_inc(v_line_1566_);
lean_inc_ref(v_source_1565_);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_cur_1564_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; 
v_unused_1587_ = lean_ctor_get(v_cur_1564_, 3);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_cur_1564_, 2);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_cur_1564_, 1);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_cur_1564_, 0);
lean_dec(v_unused_1590_);
v___x_1578_ = v_cur_1564_;
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
else
{
lean_dec(v_cur_1564_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1586_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_val_1580_; lean_object* v___x_1582_; 
v_val_1580_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v___x_1576_, 1);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 2, v_val_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_source_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_line_1566_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_val_1580_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_stopPos_1568_);
v___x_1582_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Markdown_InlineCursor_drop1(v_s_1563_, v___x_1582_);
v_cur_1564_ = v___x_1583_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_inc(v_stopPos_1568_);
lean_inc(v_line_1566_);
lean_inc_ref(v_source_1565_);
lean_dec(v___y_1570_);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_cur_1564_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1598_ = lean_ctor_get(v_cur_1564_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_cur_1564_, 2);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_cur_1564_, 1);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_cur_1564_, 0);
lean_dec(v_unused_1601_);
v___x_1592_ = v_cur_1564_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_cur_1564_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 2, v_pos_1571_);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_source_1565_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_line_1566_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_stopPos_1568_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_inc(v_stopPos_1568_);
lean_inc(v_line_1566_);
lean_inc_ref(v_source_1565_);
lean_dec(v___y_1570_);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_cur_1564_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1609_ = lean_ctor_get(v_cur_1564_, 3);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_cur_1564_, 2);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_cur_1564_, 1);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_cur_1564_, 0);
lean_dec(v_unused_1612_);
v___x_1603_ = v_cur_1564_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v_cur_1564_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 2, v_pos_1571_);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_source_1565_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_line_1566_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_pos_1571_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_stopPos_1568_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0___boxed(lean_object* v_s_1620_, lean_object* v_cur_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0(v_s_1620_, v_cur_1621_);
lean_dec_ref(v_s_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseCompleteTagLine_x3f(lean_object* v_s_1623_, lean_object* v_cur_1624_){
_start:
{
lean_object* v_afterTag_1626_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = l_Lean_Markdown_InlineCursor_front_x3f(v_s_1623_, v_cur_1624_);
v___x_1635_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1);
v___x_1636_ = l_instBEqOption_beq___at___00__private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_startsWithChars_spec__0(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v_cur_1624_);
v___x_1637_ = lean_box(0);
return v___x_1637_;
}
else
{
lean_object* v_val_1638_; uint32_t v___x_1648_; uint32_t v___x_1649_; uint8_t v___x_1650_; 
v_val_1638_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1648_ = 65;
v___x_1649_ = lean_unbox_uint32(v_val_1638_);
v___x_1650_ = lean_uint32_dec_le(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
goto v___jp_1639_;
}
else
{
uint32_t v___x_1651_; uint32_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = 90;
v___x_1652_ = lean_unbox_uint32(v_val_1638_);
v___x_1653_ = lean_uint32_dec_le(v___x_1652_, v___x_1651_);
if (v___x_1653_ == 0)
{
goto v___jp_1639_;
}
else
{
lean_dec(v_val_1638_);
goto v___jp_1631_;
}
}
v___jp_1639_:
{
uint32_t v___x_1640_; uint32_t v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = 97;
v___x_1641_ = lean_unbox_uint32(v_val_1638_);
v___x_1642_ = lean_uint32_dec_le(v___x_1640_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; 
lean_dec(v_val_1638_);
lean_dec_ref(v_cur_1624_);
v___x_1643_ = lean_box(0);
return v___x_1643_;
}
else
{
uint32_t v___x_1644_; uint32_t v___x_1645_; uint8_t v___x_1646_; 
v___x_1644_ = 122;
v___x_1645_ = lean_unbox_uint32(v_val_1638_);
lean_dec(v_val_1638_);
v___x_1646_ = lean_uint32_dec_le(v___x_1645_, v___x_1644_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v_cur_1624_);
v___x_1647_ = lean_box(0);
return v___x_1647_;
}
else
{
goto v___jp_1631_;
}
}
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v___x_1634_);
v___x_1654_ = l_Lean_Markdown_InlineCursor_drop1(v_s_1623_, v_cur_1624_);
v___x_1655_ = l_Lean_Markdown_parseClosingTag_x3f(v_s_1623_, v___x_1654_);
if (lean_obj_tag(v___x_1655_) == 0)
{
return v___x_1655_;
}
else
{
lean_object* v_val_1656_; 
v_val_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v_afterTag_1626_ = v_val_1656_;
goto v___jp_1625_;
}
}
v___jp_1625_:
{
lean_object* v_atEnd_1627_; uint8_t v___x_1628_; 
v_atEnd_1627_ = l_Lean_Markdown_InlineCursor_skipWhile___at___00Lean_Markdown_parseCompleteTagLine_x3f_spec__0(v_s_1623_, v_afterTag_1626_);
v___x_1628_ = l_Lean_Markdown_InlineCursor_isEmpty___redArg(v_atEnd_1627_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_dec_ref(v_atEnd_1627_);
v___x_1629_ = lean_box(0);
return v___x_1629_;
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_atEnd_1627_);
return v___x_1630_;
}
}
v___jp_1631_:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Markdown_parseOpenTag_x3f(v_s_1623_, v_cur_1624_);
if (lean_obj_tag(v___x_1632_) == 0)
{
return v___x_1632_;
}
else
{
lean_object* v_val_1633_; 
v_val_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v_afterTag_1626_ = v_val_1633_;
goto v___jp_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseCompleteTagLine_x3f___boxed(lean_object* v_s_1657_, lean_object* v_cur_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Markdown_parseCompleteTagLine_x3f(v_s_1657_, v_cur_1658_);
lean_dec_ref(v_s_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorIdx___impl(uint8_t v_x_1660_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_box(v_x_1660_);
v___x_1662_ = lean_obj_tag_nat(v___x_1661_);
lean_dec(v___x_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorIdx___impl___boxed(lean_object* v_x_1663_){
_start:
{
uint8_t v_x_4__boxed_1664_; lean_object* v_res_1665_; 
v_x_4__boxed_1664_ = lean_unbox(v_x_1663_);
v_res_1665_ = l_Lean_Markdown_HtmlBlockKind_ctorIdx___impl(v_x_4__boxed_1664_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim___redArg(lean_object* v_k_1666_){
_start:
{
lean_inc(v_k_1666_);
return v_k_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim___redArg___boxed(lean_object* v_k_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Markdown_HtmlBlockKind_ctorElim___redArg(v_k_1667_);
lean_dec(v_k_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim(lean_object* v_motive_1669_, lean_object* v_ctorIdx_1670_, uint8_t v_t_1671_, lean_object* v_h_1672_, lean_object* v_k_1673_){
_start:
{
lean_inc(v_k_1673_);
return v_k_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_ctorElim___boxed(lean_object* v_motive_1674_, lean_object* v_ctorIdx_1675_, lean_object* v_t_1676_, lean_object* v_h_1677_, lean_object* v_k_1678_){
_start:
{
uint8_t v_t_boxed_1679_; lean_object* v_res_1680_; 
v_t_boxed_1679_ = lean_unbox(v_t_1676_);
v_res_1680_ = l_Lean_Markdown_HtmlBlockKind_ctorElim(v_motive_1674_, v_ctorIdx_1675_, v_t_boxed_1679_, v_h_1677_, v_k_1678_);
lean_dec(v_k_1678_);
lean_dec(v_ctorIdx_1675_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim___redArg(lean_object* v_rawText_1681_){
_start:
{
lean_inc(v_rawText_1681_);
return v_rawText_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim___redArg___boxed(lean_object* v_rawText_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Markdown_HtmlBlockKind_rawText_elim___redArg(v_rawText_1682_);
lean_dec(v_rawText_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim(lean_object* v_motive_1684_, uint8_t v_t_1685_, lean_object* v_h_1686_, lean_object* v_rawText_1687_){
_start:
{
lean_inc(v_rawText_1687_);
return v_rawText_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_rawText_elim___boxed(lean_object* v_motive_1688_, lean_object* v_t_1689_, lean_object* v_h_1690_, lean_object* v_rawText_1691_){
_start:
{
uint8_t v_t_boxed_1692_; lean_object* v_res_1693_; 
v_t_boxed_1692_ = lean_unbox(v_t_1689_);
v_res_1693_ = l_Lean_Markdown_HtmlBlockKind_rawText_elim(v_motive_1688_, v_t_boxed_1692_, v_h_1690_, v_rawText_1691_);
lean_dec(v_rawText_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim___redArg(lean_object* v_comment_1694_){
_start:
{
lean_inc(v_comment_1694_);
return v_comment_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim___redArg___boxed(lean_object* v_comment_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_Markdown_HtmlBlockKind_comment_elim___redArg(v_comment_1695_);
lean_dec(v_comment_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim(lean_object* v_motive_1697_, uint8_t v_t_1698_, lean_object* v_h_1699_, lean_object* v_comment_1700_){
_start:
{
lean_inc(v_comment_1700_);
return v_comment_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_comment_elim___boxed(lean_object* v_motive_1701_, lean_object* v_t_1702_, lean_object* v_h_1703_, lean_object* v_comment_1704_){
_start:
{
uint8_t v_t_boxed_1705_; lean_object* v_res_1706_; 
v_t_boxed_1705_ = lean_unbox(v_t_1702_);
v_res_1706_ = l_Lean_Markdown_HtmlBlockKind_comment_elim(v_motive_1701_, v_t_boxed_1705_, v_h_1703_, v_comment_1704_);
lean_dec(v_comment_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim___redArg(lean_object* v_processingInstruction_1707_){
_start:
{
lean_inc(v_processingInstruction_1707_);
return v_processingInstruction_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim___redArg___boxed(lean_object* v_processingInstruction_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim___redArg(v_processingInstruction_1708_);
lean_dec(v_processingInstruction_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim(lean_object* v_motive_1710_, uint8_t v_t_1711_, lean_object* v_h_1712_, lean_object* v_processingInstruction_1713_){
_start:
{
lean_inc(v_processingInstruction_1713_);
return v_processingInstruction_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim___boxed(lean_object* v_motive_1714_, lean_object* v_t_1715_, lean_object* v_h_1716_, lean_object* v_processingInstruction_1717_){
_start:
{
uint8_t v_t_boxed_1718_; lean_object* v_res_1719_; 
v_t_boxed_1718_ = lean_unbox(v_t_1715_);
v_res_1719_ = l_Lean_Markdown_HtmlBlockKind_processingInstruction_elim(v_motive_1714_, v_t_boxed_1718_, v_h_1716_, v_processingInstruction_1717_);
lean_dec(v_processingInstruction_1717_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim___redArg(lean_object* v_declaration_1720_){
_start:
{
lean_inc(v_declaration_1720_);
return v_declaration_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim___redArg___boxed(lean_object* v_declaration_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Markdown_HtmlBlockKind_declaration_elim___redArg(v_declaration_1721_);
lean_dec(v_declaration_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim(lean_object* v_motive_1723_, uint8_t v_t_1724_, lean_object* v_h_1725_, lean_object* v_declaration_1726_){
_start:
{
lean_inc(v_declaration_1726_);
return v_declaration_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_declaration_elim___boxed(lean_object* v_motive_1727_, lean_object* v_t_1728_, lean_object* v_h_1729_, lean_object* v_declaration_1730_){
_start:
{
uint8_t v_t_boxed_1731_; lean_object* v_res_1732_; 
v_t_boxed_1731_ = lean_unbox(v_t_1728_);
v_res_1732_ = l_Lean_Markdown_HtmlBlockKind_declaration_elim(v_motive_1727_, v_t_boxed_1731_, v_h_1729_, v_declaration_1730_);
lean_dec(v_declaration_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim___redArg(lean_object* v_cdata_1733_){
_start:
{
lean_inc(v_cdata_1733_);
return v_cdata_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim___redArg___boxed(lean_object* v_cdata_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Markdown_HtmlBlockKind_cdata_elim___redArg(v_cdata_1734_);
lean_dec(v_cdata_1734_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim(lean_object* v_motive_1736_, uint8_t v_t_1737_, lean_object* v_h_1738_, lean_object* v_cdata_1739_){
_start:
{
lean_inc(v_cdata_1739_);
return v_cdata_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_cdata_elim___boxed(lean_object* v_motive_1740_, lean_object* v_t_1741_, lean_object* v_h_1742_, lean_object* v_cdata_1743_){
_start:
{
uint8_t v_t_boxed_1744_; lean_object* v_res_1745_; 
v_t_boxed_1744_ = lean_unbox(v_t_1741_);
v_res_1745_ = l_Lean_Markdown_HtmlBlockKind_cdata_elim(v_motive_1740_, v_t_boxed_1744_, v_h_1742_, v_cdata_1743_);
lean_dec(v_cdata_1743_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim___redArg(lean_object* v_blockTag_1746_){
_start:
{
lean_inc(v_blockTag_1746_);
return v_blockTag_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim___redArg___boxed(lean_object* v_blockTag_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Markdown_HtmlBlockKind_blockTag_elim___redArg(v_blockTag_1747_);
lean_dec(v_blockTag_1747_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim(lean_object* v_motive_1749_, uint8_t v_t_1750_, lean_object* v_h_1751_, lean_object* v_blockTag_1752_){
_start:
{
lean_inc(v_blockTag_1752_);
return v_blockTag_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_blockTag_elim___boxed(lean_object* v_motive_1753_, lean_object* v_t_1754_, lean_object* v_h_1755_, lean_object* v_blockTag_1756_){
_start:
{
uint8_t v_t_boxed_1757_; lean_object* v_res_1758_; 
v_t_boxed_1757_ = lean_unbox(v_t_1754_);
v_res_1758_ = l_Lean_Markdown_HtmlBlockKind_blockTag_elim(v_motive_1753_, v_t_boxed_1757_, v_h_1755_, v_blockTag_1756_);
lean_dec(v_blockTag_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim___redArg(lean_object* v_completeTag_1759_){
_start:
{
lean_inc(v_completeTag_1759_);
return v_completeTag_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim___redArg___boxed(lean_object* v_completeTag_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Markdown_HtmlBlockKind_completeTag_elim___redArg(v_completeTag_1760_);
lean_dec(v_completeTag_1760_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim(lean_object* v_motive_1762_, uint8_t v_t_1763_, lean_object* v_h_1764_, lean_object* v_completeTag_1765_){
_start:
{
lean_inc(v_completeTag_1765_);
return v_completeTag_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_completeTag_elim___boxed(lean_object* v_motive_1766_, lean_object* v_t_1767_, lean_object* v_h_1768_, lean_object* v_completeTag_1769_){
_start:
{
uint8_t v_t_boxed_1770_; lean_object* v_res_1771_; 
v_t_boxed_1770_ = lean_unbox(v_t_1767_);
v_res_1771_ = l_Lean_Markdown_HtmlBlockKind_completeTag_elim(v_motive_1766_, v_t_boxed_1770_, v_h_1768_, v_completeTag_1769_);
lean_dec(v_completeTag_1769_);
return v_res_1771_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_unsigned_to_nat(2u);
v___x_1794_ = lean_nat_to_int(v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_unsigned_to_nat(1u);
v___x_1796_ = lean_nat_to_int(v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr(uint8_t v_x_1797_, lean_object* v_prec_1798_){
_start:
{
lean_object* v___y_1800_; lean_object* v___y_1807_; lean_object* v___y_1814_; lean_object* v___y_1821_; lean_object* v___y_1828_; lean_object* v___y_1835_; lean_object* v___y_1842_; 
switch(v_x_1797_)
{
case 0:
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = lean_unsigned_to_nat(1024u);
v___x_1849_ = lean_nat_dec_le(v___x_1848_, v_prec_1798_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14);
v___y_1800_ = v___x_1850_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15);
v___y_1800_ = v___x_1851_;
goto v___jp_1799_;
}
}
case 1:
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = lean_unsigned_to_nat(1024u);
v___x_1853_ = lean_nat_dec_le(v___x_1852_, v_prec_1798_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14);
v___y_1807_ = v___x_1854_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15);
v___y_1807_ = v___x_1855_;
goto v___jp_1806_;
}
}
case 2:
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = lean_unsigned_to_nat(1024u);
v___x_1857_ = lean_nat_dec_le(v___x_1856_, v_prec_1798_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14);
v___y_1814_ = v___x_1858_;
goto v___jp_1813_;
}
else
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15);
v___y_1814_ = v___x_1859_;
goto v___jp_1813_;
}
}
case 3:
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = lean_unsigned_to_nat(1024u);
v___x_1861_ = lean_nat_dec_le(v___x_1860_, v_prec_1798_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14);
v___y_1821_ = v___x_1862_;
goto v___jp_1820_;
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15);
v___y_1821_ = v___x_1863_;
goto v___jp_1820_;
}
}
case 4:
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_unsigned_to_nat(1024u);
v___x_1865_ = lean_nat_dec_le(v___x_1864_, v_prec_1798_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14);
v___y_1828_ = v___x_1866_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15);
v___y_1828_ = v___x_1867_;
goto v___jp_1827_;
}
}
case 5:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_unsigned_to_nat(1024u);
v___x_1869_ = lean_nat_dec_le(v___x_1868_, v_prec_1798_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14);
v___y_1835_ = v___x_1870_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15);
v___y_1835_ = v___x_1871_;
goto v___jp_1834_;
}
}
default: 
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = lean_unsigned_to_nat(1024u);
v___x_1873_ = lean_nat_dec_le(v___x_1872_, v_prec_1798_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__14);
v___y_1842_ = v___x_1874_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1875_; 
v___x_1875_ = lean_obj_once(&l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15, &l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15_once, _init_l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__15);
v___y_1842_ = v___x_1875_;
goto v___jp_1841_;
}
}
}
v___jp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1801_ = ((lean_object*)(l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__1));
lean_inc(v___y_1800_);
v___x_1802_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___y_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = 0;
v___x_1804_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*1, v___x_1803_);
v___x_1805_ = l_Repr_addAppParen(v___x_1804_, v_prec_1798_);
return v___x_1805_;
}
v___jp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1808_ = ((lean_object*)(l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__3));
lean_inc(v___y_1807_);
v___x_1809_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___y_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = 0;
v___x_1811_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set_uint8(v___x_1811_, sizeof(void*)*1, v___x_1810_);
v___x_1812_ = l_Repr_addAppParen(v___x_1811_, v_prec_1798_);
return v___x_1812_;
}
v___jp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1815_ = ((lean_object*)(l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__5));
lean_inc(v___y_1814_);
v___x_1816_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___y_1814_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = 0;
v___x_1818_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set_uint8(v___x_1818_, sizeof(void*)*1, v___x_1817_);
v___x_1819_ = l_Repr_addAppParen(v___x_1818_, v_prec_1798_);
return v___x_1819_;
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1822_ = ((lean_object*)(l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__7));
lean_inc(v___y_1821_);
v___x_1823_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___y_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = 0;
v___x_1825_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set_uint8(v___x_1825_, sizeof(void*)*1, v___x_1824_);
v___x_1826_ = l_Repr_addAppParen(v___x_1825_, v_prec_1798_);
return v___x_1826_;
}
v___jp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1829_ = ((lean_object*)(l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__9));
lean_inc(v___y_1828_);
v___x_1830_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___y_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = 0;
v___x_1832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*1, v___x_1831_);
v___x_1833_ = l_Repr_addAppParen(v___x_1832_, v_prec_1798_);
return v___x_1833_;
}
v___jp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1836_ = ((lean_object*)(l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__11));
lean_inc(v___y_1835_);
v___x_1837_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___y_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = 0;
v___x_1839_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set_uint8(v___x_1839_, sizeof(void*)*1, v___x_1838_);
v___x_1840_ = l_Repr_addAppParen(v___x_1839_, v_prec_1798_);
return v___x_1840_;
}
v___jp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1843_ = ((lean_object*)(l_Lean_Markdown_instReprHtmlBlockKind_repr___closed__13));
lean_inc(v___y_1842_);
v___x_1844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___y_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = 0;
v___x_1846_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*1, v___x_1845_);
v___x_1847_ = l_Repr_addAppParen(v___x_1846_, v_prec_1798_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprHtmlBlockKind_repr___boxed(lean_object* v_x_1876_, lean_object* v_prec_1877_){
_start:
{
uint8_t v_x_387__boxed_1878_; lean_object* v_res_1879_; 
v_x_387__boxed_1878_ = lean_unbox(v_x_1876_);
v_res_1879_ = l_Lean_Markdown_instReprHtmlBlockKind_repr(v_x_387__boxed_1878_, v_prec_1877_);
lean_dec(v_prec_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqHtmlBlockKind_beq(uint8_t v_x_1882_, uint8_t v_y_1883_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1884_ = lean_box(v_x_1882_);
v___x_1885_ = lean_obj_tag_nat(v___x_1884_);
lean_dec(v___x_1884_);
v___x_1886_ = lean_box(v_y_1883_);
v___x_1887_ = lean_obj_tag_nat(v___x_1886_);
lean_dec(v___x_1886_);
v___x_1888_ = lean_nat_dec_eq(v___x_1885_, v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqHtmlBlockKind_beq___boxed(lean_object* v_x_1889_, lean_object* v_y_1890_){
_start:
{
uint8_t v_x_24__boxed_1891_; uint8_t v_y_25__boxed_1892_; uint8_t v_res_1893_; lean_object* v_r_1894_; 
v_x_24__boxed_1891_ = lean_unbox(v_x_1889_);
v_y_25__boxed_1892_ = lean_unbox(v_y_1890_);
v_res_1893_ = l_Lean_Markdown_instBEqHtmlBlockKind_beq(v_x_24__boxed_1891_, v_y_25__boxed_1892_);
v_r_1894_ = lean_box(v_res_1893_);
return v_r_1894_;
}
}
static uint8_t _init_l_Lean_Markdown_instInhabitedHtmlBlockKind_default(void){
_start:
{
uint8_t v___x_1897_; 
v___x_1897_ = 0;
return v___x_1897_;
}
}
static uint8_t _init_l_Lean_Markdown_instInhabitedHtmlBlockKind(void){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = 0;
return v___x_1898_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine(uint8_t v_x_1899_){
_start:
{
switch(v_x_1899_)
{
case 5:
{
uint8_t v___x_1900_; 
v___x_1900_ = 1;
return v___x_1900_;
}
case 6:
{
uint8_t v___x_1901_; 
v___x_1901_ = 1;
return v___x_1901_;
}
default: 
{
uint8_t v___x_1902_; 
v___x_1902_ = 0;
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine___boxed(lean_object* v_x_1903_){
_start:
{
uint8_t v_x_22__boxed_1904_; uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_x_22__boxed_1904_ = lean_unbox(v_x_1903_);
v_res_1905_ = l_Lean_Markdown_HtmlBlockKind_endsAtBlankLine(v_x_22__boxed_1904_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(uint8_t v_x_1907_){
_start:
{
if (v_x_1907_ == 6)
{
uint8_t v___x_1908_; 
v___x_1908_ = 0;
return v___x_1908_;
}
else
{
uint8_t v___x_1909_; 
v___x_1909_ = 1;
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_interruptsParagraph___boxed(lean_object* v_x_1910_){
_start:
{
uint8_t v_x_17__boxed_1911_; uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_x_17__boxed_1911_ = lean_unbox(v_x_1910_);
v_res_1912_ = l_Lean_Markdown_HtmlBlockKind_interruptsParagraph(v_x_17__boxed_1911_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Markdown_HtmlBlockKind_endConditionMet_spec__0(lean_object* v_s_1914_, lean_object* v_line_1915_, lean_object* v_x_1916_){
_start:
{
if (lean_obj_tag(v_x_1916_) == 0)
{
uint8_t v___x_1917_; 
v___x_1917_ = 0;
return v___x_1917_;
}
else
{
lean_object* v_head_1918_; lean_object* v_tail_1919_; uint8_t v___x_1920_; uint8_t v___x_1921_; 
v_head_1918_ = lean_ctor_get(v_x_1916_, 0);
v_tail_1919_ = lean_ctor_get(v_x_1916_, 1);
v___x_1920_ = 1;
v___x_1921_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(v_s_1914_, v_line_1915_, v_head_1918_, v___x_1920_);
if (v___x_1921_ == 0)
{
v_x_1916_ = v_tail_1919_;
goto _start;
}
else
{
return v___x_1921_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Markdown_HtmlBlockKind_endConditionMet_spec__0___boxed(lean_object* v_s_1923_, lean_object* v_line_1924_, lean_object* v_x_1925_){
_start:
{
uint8_t v_res_1926_; lean_object* v_r_1927_; 
v_res_1926_ = l_List_any___at___00Lean_Markdown_HtmlBlockKind_endConditionMet_spec__0(v_s_1923_, v_line_1924_, v_x_1925_);
lean_dec(v_x_1925_);
lean_dec_ref(v_line_1924_);
lean_dec_ref(v_s_1923_);
v_r_1927_ = lean_box(v_res_1926_);
return v_r_1927_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_HtmlBlockKind_endConditionMet(lean_object* v_s_1948_, uint8_t v_kind_1949_, lean_object* v_line_1950_){
_start:
{
switch(v_kind_1949_)
{
case 0:
{
lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__7));
v___x_1952_ = l_List_any___at___00Lean_Markdown_HtmlBlockKind_endConditionMet_spec__0(v_s_1948_, v_line_1950_, v___x_1951_);
return v___x_1952_;
}
case 1:
{
lean_object* v___x_1953_; uint8_t v___x_1954_; uint8_t v___x_1955_; 
v___x_1953_ = ((lean_object*)(l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__8));
v___x_1954_ = 0;
v___x_1955_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(v_s_1948_, v_line_1950_, v___x_1953_, v___x_1954_);
return v___x_1955_;
}
case 2:
{
lean_object* v___x_1956_; uint8_t v___x_1957_; uint8_t v___x_1958_; 
v___x_1956_ = ((lean_object*)(l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__9));
v___x_1957_ = 0;
v___x_1958_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(v_s_1948_, v_line_1950_, v___x_1956_, v___x_1957_);
return v___x_1958_;
}
case 3:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; uint8_t v___x_1961_; 
v___x_1959_ = ((lean_object*)(l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__10));
v___x_1960_ = 0;
v___x_1961_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(v_s_1948_, v_line_1950_, v___x_1959_, v___x_1960_);
return v___x_1961_;
}
case 4:
{
lean_object* v___x_1962_; uint8_t v___x_1963_; uint8_t v___x_1964_; 
v___x_1962_ = ((lean_object*)(l_Lean_Markdown_HtmlBlockKind_endConditionMet___closed__11));
v___x_1963_ = 0;
v___x_1964_ = l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_containsAscii(v_s_1948_, v_line_1950_, v___x_1962_, v___x_1963_);
return v___x_1964_;
}
default: 
{
uint8_t v___x_1965_; 
v___x_1965_ = 0;
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_HtmlBlockKind_endConditionMet___boxed(lean_object* v_s_1966_, lean_object* v_kind_1967_, lean_object* v_line_1968_){
_start:
{
uint8_t v_kind_boxed_1969_; uint8_t v_res_1970_; lean_object* v_r_1971_; 
v_kind_boxed_1969_ = lean_unbox(v_kind_1967_);
v_res_1970_ = l_Lean_Markdown_HtmlBlockKind_endConditionMet(v_s_1966_, v_kind_boxed_1969_, v_line_1968_);
lean_dec_ref(v_line_1968_);
lean_dec_ref(v_s_1966_);
v_r_1971_ = lean_box(v_res_1970_);
return v_r_1971_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Html(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__0___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__1___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__3___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_HtmlCloser_chars___closed__4___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__0___boxed__const__1);
l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1___boxed__const__1 = _init_l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_Data_Markdown_Parser_Html_0__Lean_Markdown_parseAttributeValue_x3f___closed__1___boxed__const__1);
l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1___boxed__const__1 = _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__1___boxed__const__1);
l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2___boxed__const__1 = _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__repeatM_erased___at___00Lean_Markdown_parseOpenTag_x3f_spec__2___redArg___closed__2___boxed__const__1);
l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2___boxed__const__1 = _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__2___boxed__const__1);
l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3___boxed__const__1 = _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__3___boxed__const__1);
l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4___boxed__const__1 = _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4___boxed__const__1();
lean_mark_persistent(l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__4___boxed__const__1);
l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6___boxed__const__1 = _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6___boxed__const__1();
lean_mark_persistent(l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__6___boxed__const__1);
l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7___boxed__const__1 = _init_l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7___boxed__const__1();
lean_mark_persistent(l_Lean_Markdown_parseMarkupDeclaration_x3f___closed__7___boxed__const__1);
l_Lean_Markdown_instInhabitedHtmlBlockKind_default = _init_l_Lean_Markdown_instInhabitedHtmlBlockKind_default();
l_Lean_Markdown_instInhabitedHtmlBlockKind = _init_l_Lean_Markdown_instInhabitedHtmlBlockKind();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_Html(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_Html(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Html(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_Html(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_Html(builtin);
}
#ifdef __cplusplus
}
#endif
