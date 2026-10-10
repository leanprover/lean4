// Lean compiler output
// Module: Lean.DocString.Formatter
// Imports: public import Lean.PrettyPrinter.Formatter public import Lean.DocString.Syntax import Init.Data.Range.Polymorphic.Iterators meta import Init.Data.Range.Polymorphic.GetElemTactic import Lean.DocString.View
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Doc_InlineView_of(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object*);
lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object*);
lean_object* l_Lean_TSyntax_getVersoRefName(lean_object*);
lean_object* l_String_Slice_lines_lineMap(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Doc_LinebreakView_of(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Doc_BlockView_of(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Doc_ArgValView_of(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Doc_ArgView_of(lean_object*);
lean_object* l_Lean_Doc_LinkTargetView_of(lean_object*);
lean_object* l_Lean_Doc_TextView_getVersoText(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object*);
lean_object* l_Lean_Doc_longestBacktickRun(lean_object*);
uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object*);
lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object*);
lean_object* l_Lean_Doc_ImageView_getAlt(lean_object*);
lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
lean_object* l_Lean_Doc_FootnoteView_getName(lean_object*);
lean_object* l_Lean_Doc_TextView_of(lean_object*);
lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object*);
lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object*);
lean_object* l_Lean_Doc_LinkRefView_getName(lean_object*);
lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object*);
lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object*);
lean_object* l_String_lines(lean_object*);
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_reprint(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Doc_RoleView_of(lean_object*);
lean_object* l_Lean_Doc_ParaView_of(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_visitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NON-ATOM "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "NON-IDENT "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "​"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "%%%"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ":::"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "+ "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "- "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\t"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12_value;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\\"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0;
static const lean_array_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "* "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ") "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "> "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "%%%\n"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_versoDocumentToString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoDocumentToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_document_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_document_formatter___lam__1___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_document_formatter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_document_formatter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "document"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(234, 113, 152, 229, 184, 253, 250, 127)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "formatter"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5_value;
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_2),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(234, 113, 152, 229, 184, 253, 250, 127)}};
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value_aux_3),((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(163, 42, 193, 184, 186, 47, 31, 255)}};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(lean_object* v_x_2_){
_start:
{
lean_object* v_stx_4_; 
switch(lean_obj_tag(v_x_2_))
{
case 1:
{
lean_object* v_args_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_args_13_ = lean_ctor_get(v_x_2_, 2);
v___x_14_ = lean_array_get_size(v_args_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_dec_eq(v___x_14_, v___x_15_);
if (v___x_16_ == 0)
{
v_stx_4_ = v_x_2_;
goto v___jp_3_;
}
else
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc_ref(v_args_13_);
lean_dec_ref_known(v_x_2_, 3);
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_array_fget(v_args_13_, v___x_17_);
lean_dec_ref(v_args_13_);
v_x_2_ = v___x_18_;
goto _start;
}
}
case 2:
{
lean_object* v_val_20_; 
v_val_20_ = lean_ctor_get(v_x_2_, 1);
lean_inc_ref(v_val_20_);
lean_dec_ref_known(v_x_2_, 2);
return v_val_20_;
}
default: 
{
v_stx_4_ = v_x_2_;
goto v___jp_3_;
}
}
v___jp_3_:
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_5_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString___closed__0));
v___x_6_ = lean_box(0);
v___x_7_ = 0;
v___x_8_ = l_Lean_Syntax_formatStx(v_stx_4_, v___x_6_, v___x_7_);
v___x_9_ = l_Std_Format_defWidth;
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = l_Std_Format_pretty(v___x_8_, v___x_9_, v___x_10_, v___x_10_);
v___x_12_ = lean_string_append(v___x_5_, v___x_11_);
lean_dec_ref(v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(lean_object* v_x_22_){
_start:
{
lean_object* v_stx_24_; 
switch(lean_obj_tag(v_x_22_))
{
case 1:
{
lean_object* v_args_33_; lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_args_33_ = lean_ctor_get(v_x_22_, 2);
v___x_34_ = lean_array_get_size(v_args_33_);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_dec_eq(v___x_34_, v___x_35_);
if (v___x_36_ == 0)
{
v_stx_24_ = v_x_22_;
goto v___jp_23_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_inc_ref(v_args_33_);
lean_dec_ref_known(v_x_22_, 3);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_array_fget(v_args_33_, v___x_37_);
lean_dec_ref(v_args_33_);
v_x_22_ = v___x_38_;
goto _start;
}
}
case 3:
{
lean_object* v_val_40_; lean_object* v___x_41_; uint8_t v___x_42_; lean_object* v___x_43_; 
v_val_40_ = lean_ctor_get(v_x_22_, 2);
lean_inc(v_val_40_);
lean_dec_ref_known(v_x_22_, 4);
v___x_41_ = l_Lean_Name_eraseMacroScopes(v_val_40_);
lean_dec(v_val_40_);
v___x_42_ = 1;
v___x_43_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_41_, v___x_42_);
return v___x_43_;
}
default: 
{
v_stx_24_ = v_x_22_;
goto v___jp_23_;
}
}
v___jp_23_:
{
lean_object* v___x_25_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_25_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString___closed__0));
v___x_26_ = lean_box(0);
v___x_27_ = 0;
v___x_28_ = l_Lean_Syntax_formatStx(v_stx_24_, v___x_26_, v___x_27_);
v___x_29_ = l_Std_Format_defWidth;
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l_Std_Format_pretty(v___x_28_, v___x_29_, v___x_30_, v___x_30_);
v___x_32_ = lean_string_append(v___x_25_, v___x_31_);
lean_dec_ref(v___x_31_);
return v___x_32_;
}
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl(uint8_t v_x_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_box(v_x_46_);
v___x_48_ = lean_obj_tag_nat(v___x_47_);
lean_dec(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_46_ = stack[0].m_num;
lean_object* v_res_49_;
v_res_49_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl(v_x_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl___boxed(lean_object* v_x_50_){
_start:
{
uint8_t v_x_4__boxed_51_; lean_object* v_res_52_; 
v_x_4__boxed_51_ = lean_unbox(v_x_50_);
v_res_52_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl(v_x_4__boxed_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(lean_object* v_k_53_){
_start:
{
lean_inc(v_k_53_);
return v_k_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg___boxed(lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(v_k_54_);
lean_dec(v_k_54_);
return v_res_55_;
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(lean_object* v_motive_56_, lean_object* v_ctorIdx_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_k_60_){
_start:
{
lean_inc(v_k_60_);
return v_k_60_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_57_ = stack[1].m_obj;
uint8_t v_t_58_ = stack[2].m_num;
lean_object* v_k_60_ = stack[4].m_obj;
lean_object* v_res_61_;
v_res_61_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(lean_box(0), v_ctorIdx_57_, v_t_58_, lean_box(0), v_k_60_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___boxed(lean_object* v_motive_62_, lean_object* v_ctorIdx_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_k_66_){
_start:
{
uint8_t v_t_boxed_67_; lean_object* v_res_68_; 
v_t_boxed_67_ = lean_unbox(v_t_64_);
v_res_68_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(v_motive_62_, v_ctorIdx_63_, v_t_boxed_67_, v_h_65_, v_k_66_);
lean_dec(v_k_66_);
lean_dec(v_ctorIdx_63_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(lean_object* v_ordered_69_){
_start:
{
lean_inc(v_ordered_69_);
return v_ordered_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg___boxed(lean_object* v_ordered_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(v_ordered_70_);
lean_dec(v_ordered_70_);
return v_res_71_;
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(lean_object* v_motive_72_, uint8_t v_t_73_, lean_object* v_h_74_, lean_object* v_ordered_75_){
_start:
{
lean_inc(v_ordered_75_);
return v_ordered_75_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_73_ = stack[1].m_num;
lean_object* v_ordered_75_ = stack[3].m_obj;
lean_object* v_res_76_;
v_res_76_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(lean_box(0), v_t_73_, lean_box(0), v_ordered_75_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___boxed(lean_object* v_motive_77_, lean_object* v_t_78_, lean_object* v_h_79_, lean_object* v_ordered_80_){
_start:
{
uint8_t v_t_boxed_81_; lean_object* v_res_82_; 
v_t_boxed_81_ = lean_unbox(v_t_78_);
v_res_82_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(v_motive_77_, v_t_boxed_81_, v_h_79_, v_ordered_80_);
lean_dec(v_ordered_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(lean_object* v_unordered_83_){
_start:
{
lean_inc(v_unordered_83_);
return v_unordered_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg___boxed(lean_object* v_unordered_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(v_unordered_84_);
lean_dec(v_unordered_84_);
return v_res_85_;
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(lean_object* v_motive_86_, uint8_t v_t_87_, lean_object* v_h_88_, lean_object* v_unordered_89_){
_start:
{
lean_inc(v_unordered_89_);
return v_unordered_89_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_87_ = stack[1].m_num;
lean_object* v_unordered_89_ = stack[3].m_obj;
lean_object* v_res_90_;
v_res_90_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(lean_box(0), v_t_87_, lean_box(0), v_unordered_89_);
stack->m_obj
 = v_res_90_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___boxed(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_unordered_94_){
_start:
{
uint8_t v_t_boxed_95_; lean_object* v_res_96_; 
v_t_boxed_95_ = lean_unbox(v_t_92_);
v_res_96_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(v_motive_91_, v_t_boxed_95_, v_h_93_, v_unordered_94_);
lean_dec(v_unordered_94_);
return v_res_96_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(uint8_t v_x_97_, uint8_t v_y_98_){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_99_ = lean_box(v_x_97_);
v___x_100_ = lean_obj_tag_nat(v___x_99_);
lean_dec(v___x_99_);
v___x_101_ = lean_box(v_y_98_);
v___x_102_ = lean_obj_tag_nat(v___x_101_);
lean_dec(v___x_101_);
v___x_103_ = lean_nat_dec_eq(v___x_100_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_97_ = stack[0].m_num;
uint8_t v_y_98_ = stack[1].m_num;
uint8_t v_res_104_;
v_res_104_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v_x_97_, v_y_98_);
stack->m_num = v_res_104_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed(lean_object* v_x_105_, lean_object* v_y_106_){
_start:
{
uint8_t v_x_24__boxed_107_; uint8_t v_y_25__boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_x_24__boxed_107_ = lean_unbox(v_x_105_);
v_y_25__boxed_108_ = lean_unbox(v_y_106_);
v_res_109_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v_x_24__boxed_107_, v_y_25__boxed_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(lean_object* v_stx_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Doc_BlockView_of(v_stx_119_);
if (lean_obj_tag(v___x_120_) == 1)
{
lean_object* v_val_121_; 
v_val_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v___x_120_, 1);
switch(lean_obj_tag(v_val_121_))
{
case 1:
{
lean_object* v___x_122_; 
lean_dec_ref_known(v_val_121_, 1);
v___x_122_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0));
return v___x_122_;
}
case 2:
{
lean_object* v___x_123_; 
lean_dec_ref_known(v_val_121_, 1);
v___x_123_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1));
return v___x_123_;
}
default: 
{
lean_object* v___x_124_; 
lean_dec(v_val_121_);
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
}
else
{
lean_object* v___x_125_; 
lean_dec(v___x_120_);
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(lean_object* v_prev_x3f_126_, lean_object* v_stx_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(v_stx_127_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v_val_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_148_; 
v_val_130_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_148_ == 0)
{
v___x_132_ = v___x_128_;
v_isShared_133_ = v_isSharedCheck_148_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_val_130_);
lean_dec(v___x_128_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_148_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint8_t v___y_135_; 
if (lean_obj_tag(v_prev_x3f_126_) == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 0;
v___y_135_ = v___x_141_;
goto v___jp_134_;
}
else
{
lean_object* v_val_142_; uint8_t v_kind_143_; uint8_t v_alternate_144_; uint8_t v___x_145_; uint8_t v___x_146_; 
v_val_142_ = lean_ctor_get(v_prev_x3f_126_, 0);
v_kind_143_ = lean_ctor_get_uint8(v_val_142_, 0);
v_alternate_144_ = lean_ctor_get_uint8(v_val_142_, 1);
v___x_145_ = lean_unbox(v_val_130_);
v___x_146_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v___x_145_, v_kind_143_);
if (v___x_146_ == 0)
{
v___y_135_ = v___x_146_;
goto v___jp_134_;
}
else
{
if (v_alternate_144_ == 0)
{
v___y_135_ = v___x_146_;
goto v___jp_134_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
v___y_135_ = v___x_147_;
goto v___jp_134_;
}
}
}
v___jp_134_:
{
lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_alloc_ctor(0, 0, 2);
v___x_137_ = lean_unbox(v_val_130_);
lean_dec(v_val_130_);
lean_ctor_set_uint8(v___x_136_, 0, v___x_137_);
lean_ctor_set_uint8(v___x_136_, 1, v___y_135_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v___x_136_);
v___x_139_ = v___x_132_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_136_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor___boxed(lean_object* v_prev_x3f_149_, lean_object* v_stx_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_prev_x3f_149_, v_stx_150_);
lean_dec(v_prev_x3f_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(lean_object* v_s_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = lean_string_append(v_a_153_, v_s_152_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg___boxed(lean_object* v_s_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_157_, v_a_158_);
lean_dec_ref(v_s_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(lean_object* v_s_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_160_, v_a_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___boxed(lean_object* v_s_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(v_s_164_, v_a_165_, v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_s_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
lean_object* v_zero_170_; uint8_t v_isZero_171_; 
v_zero_170_ = lean_unsigned_to_nat(0u);
v_isZero_171_ = lean_nat_dec_eq(v_x_168_, v_zero_170_);
if (v_isZero_171_ == 1)
{
lean_dec(v_x_168_);
return v_x_169_;
}
else
{
uint32_t v___x_172_; lean_object* v_one_173_; lean_object* v_n_174_; lean_object* v___x_175_; 
v___x_172_ = 32;
v_one_173_ = lean_unsigned_to_nat(1u);
v_n_174_ = lean_nat_sub(v_x_168_, v_one_173_);
lean_dec(v_x_168_);
v___x_175_ = lean_string_push(v_x_169_, v___x_172_);
v_x_168_ = v_n_174_;
v_x_169_ = v___x_175_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_184_ = lean_string_utf8_byte_size(v_a_180_);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_dec_le(v___x_185_, v___x_184_);
if (v___x_186_ == 0)
{
goto v___jp_181_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_187_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_nat_sub(v___x_184_, v___x_185_);
v___x_190_ = lean_string_memcmp(v_a_180_, v___x_187_, v___x_189_, v___x_188_, v___x_185_);
lean_dec(v___x_189_);
if (v___x_190_ == 0)
{
goto v___jp_181_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
lean_inc(v_a_179_);
v___x_192_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_179_, v___x_191_);
v___x_193_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_192_, v_a_180_);
lean_dec_ref(v___x_192_);
return v___x_193_;
}
}
v___jp_181_:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(0);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_a_180_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___boxed(lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_194_, v_a_195_);
lean_dec(v_a_194_);
return v_res_196_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(uint8_t v___x_197_, lean_object* v___x_198_, lean_object* v___x_199_, lean_object* v___x_200_, lean_object* v_a_201_, uint8_t v_b_202_){
_start:
{
lean_object* v___x_203_; uint8_t v_decide_204_; 
v___x_203_ = lean_nat_sub(v___x_198_, v___x_199_);
v_decide_204_ = lean_nat_dec_eq(v_a_201_, v___x_203_);
lean_dec(v___x_203_);
if (v_decide_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_nat_add(v___x_199_, v_a_201_);
lean_dec(v_a_201_);
v___x_206_ = lean_string_utf8_next_fast(v___x_200_, v___x_205_);
lean_dec(v___x_205_);
v___x_207_ = lean_nat_sub(v___x_206_, v___x_199_);
if (v_b_202_ == 0)
{
{
lean_object* _tmp_4 = v___x_207_;
uint8_t _tmp_5 = v___x_197_;
v_a_201_ = _tmp_4;
v_b_202_ = _tmp_5;
}
goto _start;
}
else
{
v_a_201_ = v___x_207_;
v_b_202_ = v_decide_204_;
goto _start;
}
}
else
{
lean_dec(v_a_201_);
return v_b_202_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_197_ = stack[0].m_num;
lean_object* v___x_198_ = stack[1].m_obj;
lean_object* v___x_199_ = stack[2].m_obj;
lean_object* v___x_200_ = stack[3].m_obj;
lean_object* v_a_201_ = stack[4].m_obj;
uint8_t v_b_202_ = stack[5].m_num;
uint8_t v_res_210_;
v_res_210_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_197_, v___x_198_, v___x_199_, v___x_200_, v_a_201_, v_b_202_);
stack->m_num = v_res_210_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg___boxed(lean_object* v___x_211_, lean_object* v___x_212_, lean_object* v___x_213_, lean_object* v___x_214_, lean_object* v_a_215_, lean_object* v_b_216_){
_start:
{
uint8_t v___x_1744__boxed_217_; uint8_t v_b_boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v___x_1744__boxed_217_ = lean_unbox(v___x_211_);
v_b_boxed_218_ = lean_unbox(v_b_216_);
v_res_219_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_1744__boxed_217_, v___x_212_, v___x_213_, v___x_214_, v_a_215_, v_b_boxed_218_);
lean_dec_ref(v___x_214_);
lean_dec(v___x_213_);
lean_dec(v___x_212_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(lean_object* v_s_221_, lean_object* v_pos_222_){
_start:
{
lean_object* v_str_223_; lean_object* v_startInclusive_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v_decide_228_; 
v_str_223_ = lean_ctor_get(v_s_221_, 0);
v_startInclusive_224_ = lean_ctor_get(v_s_221_, 1);
v___x_225_ = lean_nat_add(v_startInclusive_224_, v_pos_222_);
v___x_226_ = lean_nat_sub(v___x_225_, v_startInclusive_224_);
v___x_227_ = lean_unsigned_to_nat(0u);
v_decide_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
if (v_decide_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint32_t v___x_234_; uint32_t v___x_235_; uint8_t v___x_236_; 
lean_inc(v_startInclusive_224_);
lean_inc_ref(v_str_223_);
v___x_229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_229_, 0, v_str_223_);
lean_ctor_set(v___x_229_, 1, v_startInclusive_224_);
lean_ctor_set(v___x_229_, 2, v___x_225_);
v___x_230_ = lean_unsigned_to_nat(1u);
v___x_231_ = lean_nat_sub(v___x_226_, v___x_230_);
lean_dec(v___x_226_);
v___x_232_ = l_String_Slice_posLE(v___x_229_, v___x_231_);
lean_dec_ref_known(v___x_229_, 3);
v___x_233_ = lean_nat_add(v_startInclusive_224_, v___x_232_);
v___x_234_ = lean_string_utf8_get_fast(v_str_223_, v___x_233_);
lean_dec(v___x_233_);
v___x_235_ = 92;
v___x_236_ = lean_uint32_dec_eq(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v___x_232_);
return v_pos_222_;
}
else
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_nat_add(v___x_232_, v___x_230_);
v___x_238_ = lean_nat_dec_le(v___x_237_, v_pos_222_);
lean_dec(v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v___x_232_);
return v_pos_222_;
}
else
{
lean_dec(v_pos_222_);
v_pos_222_ = v___x_232_;
goto _start;
}
}
}
else
{
lean_dec(v___x_226_);
lean_dec(v___x_225_);
return v_pos_222_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0___boxed(lean_object* v_s_240_, lean_object* v_pos_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v_s_240_, v_pos_241_);
lean_dec_ref(v_s_240_);
return v_res_242_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(lean_object* v_s_243_){
_start:
{
lean_object* v_str_244_; lean_object* v_startInclusive_245_; lean_object* v_endExclusive_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_str_244_ = lean_ctor_get(v_s_243_, 0);
lean_inc_ref(v_str_244_);
v_startInclusive_245_ = lean_ctor_get(v_s_243_, 1);
lean_inc(v_startInclusive_245_);
v_endExclusive_246_ = lean_ctor_get(v_s_243_, 2);
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_sub(v_endExclusive_246_, v_startInclusive_245_);
v___x_249_ = lean_nat_dec_le(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_dec(v___x_248_);
lean_dec(v_startInclusive_245_);
lean_dec_ref(v_str_244_);
lean_dec_ref(v_s_243_);
return v___x_249_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_250_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_nat_sub(v___x_248_, v___x_247_);
v___x_253_ = lean_nat_add(v_startInclusive_245_, v___x_252_);
lean_dec(v___x_252_);
v___x_254_ = lean_string_memcmp(v_str_244_, v___x_250_, v___x_253_, v___x_251_, v___x_247_);
lean_dec(v___x_253_);
if (v___x_254_ == 0)
{
lean_dec(v___x_248_);
lean_dec(v_startInclusive_245_);
lean_dec_ref(v_str_244_);
lean_dec_ref(v_s_243_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_268_; 
v___x_255_ = l_String_Slice_Pos_prevn(v_s_243_, v___x_248_, v___x_247_);
v_isSharedCheck_268_ = !lean_is_exclusive(v_s_243_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; lean_object* v_unused_270_; lean_object* v_unused_271_; 
v_unused_269_ = lean_ctor_get(v_s_243_, 2);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_s_243_, 1);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_s_243_, 0);
lean_dec(v_unused_271_);
v___x_257_ = v_s_243_;
v_isShared_258_ = v_isSharedCheck_268_;
goto v_resetjp_256_;
}
else
{
lean_dec(v_s_243_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_268_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_259_ = lean_nat_add(v_startInclusive_245_, v___x_255_);
lean_dec(v___x_255_);
lean_inc(v___x_259_);
lean_inc(v_startInclusive_245_);
lean_inc_ref(v_str_244_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 2, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_str_244_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_startInclusive_245_);
lean_ctor_set(v_reuseFailAlloc_267_, 2, v___x_259_);
v___x_261_ = v_reuseFailAlloc_267_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; uint8_t v___x_266_; 
v___x_262_ = lean_nat_sub(v___x_259_, v_startInclusive_245_);
v___x_263_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v___x_261_, v___x_262_);
lean_dec_ref(v___x_261_);
v___x_264_ = lean_nat_add(v_startInclusive_245_, v___x_263_);
lean_dec(v___x_263_);
lean_dec(v_startInclusive_245_);
v___x_265_ = 0;
v___x_266_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_254_, v___x_259_, v___x_264_, v_str_244_, v___x_251_, v___x_265_);
lean_dec_ref(v_str_244_);
lean_dec(v___x_264_);
lean_dec(v___x_259_);
return v___x_266_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_243_ = stack[0].m_obj;
uint8_t v_res_272_;
v_res_272_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_243_);
stack->m_num = v_res_272_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline___boxed(lean_object* v_s_273_){
_start:
{
uint8_t v_res_274_; lean_object* v_r_275_; 
v_res_274_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_273_);
v_r_275_ = lean_box(v_res_274_);
return v_r_275_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(uint8_t v___x_276_, lean_object* v___x_277_, lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v___x_280_, lean_object* v_inst_281_, lean_object* v_R_282_, lean_object* v_a_283_, uint8_t v_b_284_, lean_object* v_c_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_276_, v___x_277_, v___x_278_, v___x_280_, v_a_283_, v_b_284_);
return v___x_286_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_276_ = stack[0].m_num;
lean_object* v___x_277_ = stack[1].m_obj;
lean_object* v___x_278_ = stack[2].m_obj;
lean_object* v___x_279_ = stack[3].m_obj;
lean_object* v___x_280_ = stack[4].m_obj;
lean_object* v_a_283_ = stack[7].m_obj;
uint8_t v_b_284_ = stack[8].m_num;
uint8_t v_res_287_;
v_res_287_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(v___x_276_, v___x_277_, v___x_278_, v___x_279_, v___x_280_, lean_box(0), lean_box(0), v_a_283_, v_b_284_, lean_box(0));
stack->m_num = v_res_287_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___boxed(lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v___x_290_, lean_object* v___x_291_, lean_object* v___x_292_, lean_object* v_inst_293_, lean_object* v_R_294_, lean_object* v_a_295_, lean_object* v_b_296_, lean_object* v_c_297_){
_start:
{
uint8_t v___x_1906__boxed_298_; uint8_t v_b_boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v___x_1906__boxed_298_ = lean_unbox(v___x_288_);
v_b_boxed_299_ = lean_unbox(v_b_296_);
v_res_300_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(v___x_1906__boxed_298_, v___x_289_, v___x_290_, v___x_291_, v___x_292_, v_inst_293_, v_R_294_, v_a_295_, v_b_boxed_299_, v_c_297_);
lean_dec_ref(v___x_292_);
lean_dec_ref(v___x_291_);
lean_dec(v___x_290_);
lean_dec(v___x_289_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(lean_object* v_s_302_){
_start:
{
lean_object* v_str_303_; lean_object* v_startInclusive_304_; lean_object* v_endExclusive_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_str_303_ = lean_ctor_get(v_s_302_, 0);
lean_inc_ref(v_str_303_);
v_startInclusive_304_ = lean_ctor_get(v_s_302_, 1);
lean_inc(v_startInclusive_304_);
v_endExclusive_305_ = lean_ctor_get(v_s_302_, 2);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_sub(v_endExclusive_305_, v_startInclusive_304_);
v___x_308_ = lean_nat_dec_le(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v___x_307_);
lean_dec(v_startInclusive_304_);
lean_dec_ref(v_str_303_);
lean_dec_ref(v_s_302_);
v___x_309_ = lean_unsigned_to_nat(0u);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_310_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_nat_sub(v___x_307_, v___x_306_);
v___x_313_ = lean_nat_add(v_startInclusive_304_, v___x_312_);
lean_dec(v___x_312_);
v___x_314_ = lean_string_memcmp(v_str_303_, v___x_310_, v___x_313_, v___x_311_, v___x_306_);
lean_dec(v___x_313_);
if (v___x_314_ == 0)
{
lean_dec(v___x_307_);
lean_dec(v_startInclusive_304_);
lean_dec_ref(v_str_303_);
lean_dec_ref(v_s_302_);
return v___x_311_;
}
else
{
uint8_t v___x_315_; 
lean_inc_ref(v_s_302_);
v___x_315_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_302_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_331_; 
v___x_316_ = l_String_Slice_Pos_prevn(v_s_302_, v___x_307_, v___x_306_);
v_isSharedCheck_331_ = !lean_is_exclusive(v_s_302_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_332_ = lean_ctor_get(v_s_302_, 2);
lean_dec(v_unused_332_);
v_unused_333_ = lean_ctor_get(v_s_302_, 1);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_s_302_, 0);
lean_dec(v_unused_334_);
v___x_318_ = v_s_302_;
v_isShared_319_ = v_isSharedCheck_331_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_s_302_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_331_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = lean_nat_add(v_startInclusive_304_, v___x_316_);
lean_dec(v___x_316_);
v___x_321_ = lean_nat_sub(v___x_320_, v_startInclusive_304_);
v___x_322_ = lean_nat_dec_le(v___x_306_, v___x_321_);
if (v___x_322_ == 0)
{
lean_dec(v___x_321_);
lean_dec(v___x_320_);
lean_del_object(v___x_318_);
lean_dec(v_startInclusive_304_);
lean_dec_ref(v_str_303_);
return v___x_306_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_323_ = lean_nat_sub(v___x_321_, v___x_306_);
lean_dec(v___x_321_);
v___x_324_ = lean_nat_add(v_startInclusive_304_, v___x_323_);
lean_dec(v___x_323_);
v___x_325_ = lean_string_memcmp(v_str_303_, v___x_310_, v___x_324_, v___x_311_, v___x_306_);
lean_dec(v___x_324_);
if (v___x_325_ == 0)
{
lean_dec(v___x_320_);
lean_del_object(v___x_318_);
lean_dec(v_startInclusive_304_);
lean_dec_ref(v_str_303_);
return v___x_306_;
}
else
{
if (v___x_315_ == 0)
{
lean_object* v_s_327_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 2, v___x_320_);
v_s_327_ = v___x_318_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_str_303_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_startInclusive_304_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v___x_320_);
v_s_327_ = v_reuseFailAlloc_330_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
uint8_t v___x_328_; 
v___x_328_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(2u);
return v___x_329_;
}
else
{
return v___x_306_;
}
}
}
else
{
lean_dec(v___x_320_);
lean_del_object(v___x_318_);
lean_dec(v_startInclusive_304_);
lean_dec_ref(v_str_303_);
return v___x_306_;
}
}
}
}
}
else
{
lean_dec(v___x_307_);
lean_dec(v_startInclusive_304_);
lean_dec_ref(v_str_303_);
lean_dec_ref(v_s_302_);
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v_zero_337_; uint8_t v_isZero_338_; 
v_zero_337_ = lean_unsigned_to_nat(0u);
v_isZero_338_ = lean_nat_dec_eq(v_x_335_, v_zero_337_);
if (v_isZero_338_ == 1)
{
lean_dec(v_x_335_);
return v_x_336_;
}
else
{
uint32_t v___x_339_; lean_object* v_one_340_; lean_object* v_n_341_; lean_object* v___x_342_; 
v___x_339_ = 10;
v_one_340_ = lean_unsigned_to_nat(1u);
v_n_341_ = lean_nat_sub(v_x_335_, v_one_340_);
lean_dec(v_x_335_);
v___x_342_ = lean_string_push(v_x_336_, v___x_339_);
v_x_335_ = v_n_341_;
v_x_336_ = v___x_342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_345_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_346_ = lean_unsigned_to_nat(2u);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_string_utf8_byte_size(v_a_344_);
lean_inc_ref(v_a_344_);
v___x_349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_349_, 0, v_a_344_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
lean_ctor_set(v___x_349_, 2, v___x_348_);
v___x_350_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(v___x_349_);
v___x_351_ = lean_nat_sub(v___x_346_, v___x_350_);
lean_dec(v___x_350_);
v___x_352_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_351_, v___x_345_);
v___x_353_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_352_, v_a_344_);
lean_dec_ref(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_a_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___boxed(lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(v_a_357_, v_a_358_);
lean_dec(v_a_357_);
return v_res_359_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(uint32_t v_a_360_){
_start:
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 92;
v___x_362_ = lean_uint32_dec_eq(v_a_360_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 42;
v___x_364_ = lean_uint32_dec_eq(v_a_360_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 95;
v___x_366_ = lean_uint32_dec_eq(v_a_360_, v___x_365_);
if (v___x_366_ == 0)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 91;
v___x_368_ = lean_uint32_dec_eq(v_a_360_, v___x_367_);
if (v___x_368_ == 0)
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 93;
v___x_370_ = lean_uint32_dec_eq(v_a_360_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 123;
v___x_372_ = lean_uint32_dec_eq(v_a_360_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 125;
v___x_374_ = lean_uint32_dec_eq(v_a_360_, v___x_373_);
if (v___x_374_ == 0)
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 96;
v___x_376_ = lean_uint32_dec_eq(v_a_360_, v___x_375_);
if (v___x_376_ == 0)
{
uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = 33;
v___x_378_ = lean_uint32_dec_eq(v_a_360_, v___x_377_);
if (v___x_378_ == 0)
{
uint32_t v___x_379_; uint8_t v___x_380_; 
v___x_379_ = 36;
v___x_380_ = lean_uint32_dec_eq(v_a_360_, v___x_379_);
if (v___x_380_ == 0)
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 10;
v___x_382_ = lean_uint32_dec_eq(v_a_360_, v___x_381_);
return v___x_382_;
}
else
{
return v___x_380_;
}
}
else
{
return v___x_378_;
}
}
else
{
return v___x_376_;
}
}
else
{
return v___x_374_;
}
}
else
{
return v___x_372_;
}
}
else
{
return v___x_370_;
}
}
else
{
return v___x_368_;
}
}
else
{
return v___x_366_;
}
}
else
{
return v___x_364_;
}
}
else
{
return v___x_362_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_360_ = stack[0].m_num;
uint8_t v_res_383_;
v_res_383_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v_a_360_);
stack->m_num = v_res_383_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial___boxed(lean_object* v_a_384_){
_start:
{
uint32_t v_a_242__boxed_385_; uint8_t v_res_386_; lean_object* v_r_387_; 
v_a_242__boxed_385_ = lean_unbox_uint32(v_a_384_);
lean_dec(v_a_384_);
v_res_386_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v_a_242__boxed_385_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(lean_object* v___x_388_, lean_object* v_value_389_, lean_object* v_a_390_, lean_object* v_b_391_){
_start:
{
uint8_t v_decide_392_; 
v_decide_392_ = lean_nat_dec_eq(v_a_390_, v___x_388_);
if (v_decide_392_ == 0)
{
uint32_t v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_string_utf8_get_fast(v_value_389_, v_a_390_);
v___x_394_ = lean_string_utf8_next_fast(v_value_389_, v_a_390_);
lean_dec(v_a_390_);
v___x_395_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v___x_393_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; 
v___x_396_ = lean_string_push(v_b_391_, v___x_393_);
v_a_390_ = v___x_394_;
v_b_391_ = v___x_396_;
goto _start;
}
else
{
uint32_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = 92;
v___x_399_ = lean_string_push(v_b_391_, v___x_398_);
v___x_400_ = lean_string_push(v___x_399_, v___x_393_);
v_a_390_ = v___x_394_;
v_b_391_ = v___x_400_;
goto _start;
}
}
else
{
lean_dec(v_a_390_);
return v_b_391_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg___boxed(lean_object* v___x_402_, lean_object* v_value_403_, lean_object* v_a_404_, lean_object* v_b_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_402_, v_value_403_, v_a_404_, v_b_405_);
lean_dec_ref(v_value_403_);
lean_dec(v___x_402_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(lean_object* v_value_407_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_408_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_409_ = lean_string_utf8_byte_size(v_value_407_);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_409_, v_value_407_, v___x_410_, v___x_408_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped___boxed(lean_object* v_value_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_412_);
lean_dec_ref(v_value_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_value_416_, lean_object* v_inst_417_, lean_object* v_R_418_, lean_object* v_a_419_, lean_object* v_b_420_, lean_object* v_c_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_415_, v_value_416_, v_a_419_, v_b_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___boxed(lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v_value_425_, lean_object* v_inst_426_, lean_object* v_R_427_, lean_object* v_a_428_, lean_object* v_b_429_, lean_object* v_c_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(v___x_423_, v___x_424_, v_value_425_, v_inst_426_, v_R_427_, v_a_428_, v_b_429_, v_c_430_);
lean_dec_ref(v_value_425_);
lean_dec(v___x_424_);
lean_dec_ref(v___x_423_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(lean_object* v_s_432_, lean_object* v_pos_433_){
_start:
{
lean_object* v_str_434_; lean_object* v_startInclusive_435_; lean_object* v_endExclusive_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v_decide_440_; 
v_str_434_ = lean_ctor_get(v_s_432_, 0);
v_startInclusive_435_ = lean_ctor_get(v_s_432_, 1);
v_endExclusive_436_ = lean_ctor_get(v_s_432_, 2);
v___x_437_ = lean_nat_add(v_startInclusive_435_, v_pos_433_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_nat_sub(v_endExclusive_436_, v___x_437_);
v_decide_440_ = lean_nat_dec_eq(v___x_438_, v___x_439_);
lean_dec(v___x_439_);
if (v_decide_440_ == 0)
{
uint32_t v___x_441_; uint32_t v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_string_utf8_get_fast(v_str_434_, v___x_437_);
v___x_442_ = 48;
v___x_443_ = lean_uint32_dec_le(v___x_442_, v___x_441_);
if (v___x_443_ == 0)
{
lean_dec(v___x_437_);
return v_pos_433_;
}
else
{
uint32_t v___x_444_; uint8_t v___x_445_; 
v___x_444_ = 57;
v___x_445_ = lean_uint32_dec_le(v___x_441_, v___x_444_);
if (v___x_445_ == 0)
{
lean_dec(v___x_437_);
return v_pos_433_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_446_ = lean_string_utf8_next_fast(v_str_434_, v___x_437_);
v___x_447_ = lean_nat_sub(v___x_446_, v___x_437_);
lean_dec(v___x_437_);
v___x_448_ = lean_nat_add(v_pos_433_, v___x_447_);
lean_dec(v___x_447_);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_pos_433_, v___x_449_);
v___x_451_ = lean_nat_dec_le(v___x_450_, v___x_448_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
lean_dec(v___x_448_);
return v_pos_433_;
}
else
{
lean_dec(v_pos_433_);
v_pos_433_ = v___x_448_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_437_);
return v_pos_433_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0___boxed(lean_object* v_s_453_, lean_object* v_pos_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v_s_453_, v_pos_454_);
lean_dec_ref(v_s_453_);
return v_res_455_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(lean_object* v_text_469_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_afterDigits_474_; uint8_t v___y_476_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_string_utf8_byte_size(v_text_469_);
lean_inc_ref_n(v_text_469_, 2);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v_text_469_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_471_);
v___x_473_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v___x_472_, v___x_470_);
lean_inc(v___x_473_);
v_afterDigits_474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_afterDigits_474_, 0, v_text_469_);
lean_ctor_set(v_afterDigits_474_, 1, v___x_473_);
lean_ctor_set(v_afterDigits_474_, 2, v___x_471_);
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_dec_le(v___x_551_, v___x_471_);
if (v___x_552_ == 0)
{
goto v___jp_546_;
}
else
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_554_ = lean_string_memcmp(v_text_469_, v___x_553_, v___x_470_, v___x_470_, v___x_551_);
if (v___x_554_ == 0)
{
goto v___jp_546_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_554_;
}
}
v___jp_475_:
{
if (v___y_476_ == 0)
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref(v_text_469_);
return v___y_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = l_String_Slice_Pos_nextn(v_afterDigits_474_, v___x_470_, v___x_477_);
lean_dec_ref_known(v_afterDigits_474_, 3);
v___x_479_ = lean_nat_add(v___x_473_, v___x_478_);
lean_dec(v___x_478_);
lean_dec(v___x_473_);
v___x_480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_480_, 0, v_text_469_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
lean_ctor_set(v___x_480_, 2, v___x_471_);
v___x_481_ = l_String_Slice_Pos_get_x3f(v___x_480_, v___x_470_);
lean_dec_ref_known(v___x_480_, 3);
if (lean_obj_tag(v___x_481_) == 0)
{
return v___y_476_;
}
else
{
lean_object* v_val_482_; uint32_t v___x_483_; uint32_t v___x_484_; uint8_t v___x_485_; 
v_val_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = 32;
v___x_484_ = lean_unbox_uint32(v_val_482_);
lean_dec(v_val_482_);
v___x_485_ = lean_uint32_dec_eq(v___x_484_, v___x_483_);
return v___x_485_;
}
}
}
v___jp_486_:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_sub(v___x_471_, v___x_473_);
v___x_489_ = lean_nat_dec_le(v___x_487_, v___x_488_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref(v_text_469_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_491_ = lean_string_memcmp(v_text_469_, v___x_490_, v___x_473_, v___x_470_, v___x_487_);
v___y_476_ = v___x_491_;
goto v___jp_475_;
}
}
v___jp_492_:
{
lean_object* v___x_493_; 
v___x_493_ = l_String_Slice_Pos_get_x3f(v___x_472_, v___x_470_);
lean_dec_ref_known(v___x_472_, 3);
if (lean_obj_tag(v___x_493_) == 0)
{
uint8_t v___x_494_; 
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref(v_text_469_);
v___x_494_ = 0;
return v___x_494_;
}
else
{
lean_object* v_val_495_; uint32_t v___x_496_; uint32_t v___x_497_; uint8_t v___x_498_; 
v_val_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_493_, 1);
v___x_496_ = 48;
v___x_497_ = lean_unbox_uint32(v_val_495_);
v___x_498_ = lean_uint32_dec_le(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_dec(v_val_495_);
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref(v_text_469_);
return v___x_498_;
}
else
{
uint32_t v___x_499_; uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = 57;
v___x_500_ = lean_unbox_uint32(v_val_495_);
lean_dec(v_val_495_);
v___x_501_ = lean_uint32_dec_le(v___x_500_, v___x_499_);
if (v___x_501_ == 0)
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref(v_text_469_);
return v___x_501_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_sub(v___x_471_, v___x_473_);
v___x_504_ = lean_nat_dec_le(v___x_502_, v___x_503_);
lean_dec(v___x_503_);
if (v___x_504_ == 0)
{
goto v___jp_486_;
}
else
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1));
v___x_506_ = lean_string_memcmp(v_text_469_, v___x_505_, v___x_473_, v___x_470_, v___x_502_);
if (v___x_506_ == 0)
{
goto v___jp_486_;
}
else
{
v___y_476_ = v___x_506_;
goto v___jp_475_;
}
}
}
}
}
}
v___jp_507_:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(3u);
v___x_509_ = lean_nat_dec_le(v___x_508_, v___x_471_);
if (v___x_509_ == 0)
{
goto v___jp_492_;
}
else
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_511_ = lean_string_memcmp(v_text_469_, v___x_510_, v___x_470_, v___x_470_, v___x_508_);
if (v___x_511_ == 0)
{
goto v___jp_492_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_511_;
}
}
}
v___jp_512_:
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(3u);
v___x_514_ = lean_nat_dec_le(v___x_513_, v___x_471_);
if (v___x_514_ == 0)
{
goto v___jp_507_;
}
else
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3));
v___x_516_ = lean_string_memcmp(v_text_469_, v___x_515_, v___x_470_, v___x_470_, v___x_513_);
if (v___x_516_ == 0)
{
goto v___jp_507_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_516_;
}
}
}
v___jp_517_:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(2u);
v___x_519_ = lean_nat_dec_le(v___x_518_, v___x_471_);
if (v___x_519_ == 0)
{
goto v___jp_512_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_521_ = lean_string_memcmp(v_text_469_, v___x_520_, v___x_470_, v___x_470_, v___x_518_);
if (v___x_521_ == 0)
{
goto v___jp_512_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_521_;
}
}
}
v___jp_522_:
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___x_524_ = lean_string_dec_eq(v_text_469_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_nat_dec_le(v___x_525_, v___x_471_);
if (v___x_526_ == 0)
{
goto v___jp_517_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_528_ = lean_string_memcmp(v_text_469_, v___x_527_, v___x_470_, v___x_470_, v___x_525_);
if (v___x_528_ == 0)
{
goto v___jp_517_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_528_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_524_;
}
}
v___jp_529_:
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___x_531_ = lean_string_dec_eq(v_text_469_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(2u);
v___x_533_ = lean_nat_dec_le(v___x_532_, v___x_471_);
if (v___x_533_ == 0)
{
goto v___jp_522_;
}
else
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_535_ = lean_string_memcmp(v_text_469_, v___x_534_, v___x_470_, v___x_470_, v___x_532_);
if (v___x_535_ == 0)
{
goto v___jp_522_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_535_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_531_;
}
}
v___jp_536_:
{
lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_dec_le(v___x_537_, v___x_471_);
if (v___x_538_ == 0)
{
goto v___jp_529_;
}
else
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___x_540_ = lean_string_memcmp(v_text_469_, v___x_539_, v___x_470_, v___x_470_, v___x_537_);
if (v___x_540_ == 0)
{
goto v___jp_529_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_540_;
}
}
}
v___jp_541_:
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_dec_le(v___x_542_, v___x_471_);
if (v___x_543_ == 0)
{
goto v___jp_536_;
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_545_ = lean_string_memcmp(v_text_469_, v___x_544_, v___x_470_, v___x_470_, v___x_542_);
if (v___x_545_ == 0)
{
goto v___jp_536_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_545_;
}
}
}
v___jp_546_:
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_dec_le(v___x_547_, v___x_471_);
if (v___x_548_ == 0)
{
goto v___jp_541_;
}
else
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_550_ = lean_string_memcmp(v_text_469_, v___x_549_, v___x_470_, v___x_470_, v___x_547_);
if (v___x_550_ == 0)
{
goto v___jp_541_;
}
else
{
lean_dec_ref_known(v_afterDigits_474_, 3);
lean_dec(v___x_473_);
lean_dec_ref_known(v___x_472_, 3);
lean_dec_ref(v_text_469_);
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_469_ = stack[0].m_obj;
uint8_t v_res_555_;
v_res_555_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_text_469_);
stack->m_num = v_res_555_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object* v_text_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_text_556_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t v_atLineStart_560_, lean_object* v_value_561_){
_start:
{
lean_object* v_text_562_; 
v_text_562_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_561_);
if (v_atLineStart_560_ == 0)
{
lean_dec_ref(v_value_561_);
return v_text_562_;
}
else
{
uint8_t v___x_563_; 
v___x_563_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_value_561_);
if (v___x_563_ == 0)
{
return v_text_562_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_565_ = lean_string_append(v___x_564_, v_text_562_);
lean_dec_ref(v_text_562_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_0interp(lean_interpreter_value* stack)
{
uint8_t v_atLineStart_560_ = stack[0].m_num;
lean_object* v_value_561_ = stack[1].m_obj;
lean_object* v_res_566_;
v_res_566_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_560_, v_value_561_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object* v_atLineStart_567_, lean_object* v_value_568_){
_start:
{
uint8_t v_atLineStart_boxed_569_; lean_object* v_res_570_; 
v_atLineStart_boxed_569_ = lean_unbox(v_atLineStart_567_);
v_res_570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_boxed_569_, v_value_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object* v_s_571_, lean_object* v_pos_572_){
_start:
{
lean_object* v_str_573_; lean_object* v_startInclusive_574_; lean_object* v_endExclusive_575_; lean_object* v___x_576_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v_decide_587_; 
v_str_573_ = lean_ctor_get(v_s_571_, 0);
v_startInclusive_574_ = lean_ctor_get(v_s_571_, 1);
v_endExclusive_575_ = lean_ctor_get(v_s_571_, 2);
v___x_576_ = lean_nat_add(v_startInclusive_574_, v_pos_572_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_nat_sub(v_endExclusive_575_, v___x_576_);
v_decide_587_ = lean_nat_dec_eq(v___x_585_, v___x_586_);
lean_dec(v___x_586_);
if (v_decide_587_ == 0)
{
uint32_t v___x_588_; uint32_t v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_string_utf8_get_fast(v_str_573_, v___x_576_);
v___x_589_ = 32;
v___x_590_ = lean_uint32_dec_eq(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
uint32_t v___x_591_; uint8_t v___x_592_; 
v___x_591_ = 9;
v___x_592_ = lean_uint32_dec_eq(v___x_588_, v___x_591_);
if (v___x_592_ == 0)
{
uint32_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = 13;
v___x_594_ = lean_uint32_dec_eq(v___x_588_, v___x_593_);
if (v___x_594_ == 0)
{
uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_595_ = 10;
v___x_596_ = lean_uint32_dec_eq(v___x_588_, v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v___x_576_);
return v_pos_572_;
}
else
{
goto v___jp_577_;
}
}
else
{
goto v___jp_577_;
}
}
else
{
goto v___jp_577_;
}
}
else
{
goto v___jp_577_;
}
}
else
{
lean_dec(v___x_576_);
return v_pos_572_;
}
v___jp_577_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_578_ = lean_string_utf8_next_fast(v_str_573_, v___x_576_);
v___x_579_ = lean_nat_sub(v___x_578_, v___x_576_);
lean_dec(v___x_576_);
v___x_580_ = lean_nat_add(v_pos_572_, v___x_579_);
lean_dec(v___x_579_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_add(v_pos_572_, v___x_581_);
v___x_583_ = lean_nat_dec_le(v___x_582_, v___x_580_);
lean_dec(v___x_582_);
if (v___x_583_ == 0)
{
lean_dec(v___x_580_);
return v_pos_572_;
}
else
{
lean_dec(v_pos_572_);
v_pos_572_ = v___x_580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object* v_s_597_, lean_object* v_pos_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_597_, v_pos_598_);
lean_dec_ref(v_s_597_);
return v_res_599_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object* v_s_600_){
_start:
{
lean_object* v_startInclusive_601_; lean_object* v_endExclusive_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v_decide_606_; 
v_startInclusive_601_ = lean_ctor_get(v_s_600_, 1);
v_endExclusive_602_ = lean_ctor_get(v_s_600_, 2);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_600_, v___x_603_);
v___x_605_ = lean_nat_sub(v_endExclusive_602_, v_startInclusive_601_);
v_decide_606_ = lean_nat_dec_eq(v___x_604_, v___x_605_);
lean_dec(v___x_605_);
lean_dec(v___x_604_);
return v_decide_606_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_600_ = stack[0].m_obj;
uint8_t v_res_607_;
v_res_607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v_s_600_);
stack->m_num = v_res_607_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object* v_s_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v_s_608_);
lean_dec_ref(v_s_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object* v_s_611_, lean_object* v_a_612_, lean_object* v_b_613_){
_start:
{
lean_object* v_str_614_; lean_object* v_startInclusive_615_; lean_object* v_endExclusive_616_; lean_object* v___x_617_; uint8_t v_decide_618_; 
v_str_614_ = lean_ctor_get(v_s_611_, 0);
v_startInclusive_615_ = lean_ctor_get(v_s_611_, 1);
v_endExclusive_616_ = lean_ctor_get(v_s_611_, 2);
v___x_617_ = lean_nat_sub(v_endExclusive_616_, v_startInclusive_615_);
v_decide_618_ = lean_nat_dec_eq(v_a_612_, v___x_617_);
lean_dec(v___x_617_);
if (v_decide_618_ == 0)
{
lean_object* v___x_619_; uint32_t v___x_620_; uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_nat_add(v_startInclusive_615_, v_a_612_);
lean_dec(v_a_612_);
v___x_620_ = lean_string_utf8_get_fast(v_str_614_, v___x_619_);
v___x_621_ = 32;
v___x_622_ = lean_uint32_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_dec(v___x_619_);
return v_b_613_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_623_ = lean_string_utf8_next_fast(v_str_614_, v___x_619_);
lean_dec(v___x_619_);
v___x_624_ = lean_nat_sub(v___x_623_, v_startInclusive_615_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_b_613_, v___x_625_);
lean_dec(v_b_613_);
v_a_612_ = v___x_624_;
v_b_613_ = v___x_626_;
goto _start;
}
}
else
{
lean_dec(v_a_612_);
return v_b_613_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object* v_s_628_, lean_object* v_a_629_, lean_object* v_b_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_628_, v_a_629_, v_b_630_);
lean_dec_ref(v_s_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object* v_s_632_){
_start:
{
lean_object* v_n_633_; lean_object* v___x_634_; 
v_n_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_632_, v_n_633_, v_n_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object* v_s_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v_s_635_);
lean_dec_ref(v_s_635_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object* v_s_637_, lean_object* v_inst_638_, lean_object* v_R_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v_c_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_637_, v_a_640_, v_b_641_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object* v_s_644_, lean_object* v_inst_645_, lean_object* v_R_646_, lean_object* v_a_647_, lean_object* v_b_648_, lean_object* v_c_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(v_s_644_, v_inst_645_, v_R_646_, v_a_647_, v_b_648_, v_c_649_);
lean_dec_ref(v_s_644_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_src_653_, lean_object* v___x_654_, lean_object* v_a_655_, lean_object* v_b_656_){
_start:
{
lean_object* v_it_658_; lean_object* v_out_659_; 
if (lean_obj_tag(v_a_655_) == 0)
{
lean_object* v_currPos_678_; lean_object* v_searcher_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_708_; 
v_currPos_678_ = lean_ctor_get(v_a_655_, 0);
v_searcher_679_ = lean_ctor_get(v_a_655_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_a_655_);
if (v_isSharedCheck_708_ == 0)
{
v___x_681_ = v_a_655_;
v_isShared_682_ = v_isSharedCheck_708_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_searcher_679_);
lean_inc(v_currPos_678_);
lean_dec(v_a_655_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_708_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_str_683_; lean_object* v_startInclusive_684_; lean_object* v_endExclusive_685_; lean_object* v___x_686_; uint8_t v_decide_687_; 
v_str_683_ = lean_ctor_get(v___x_651_, 0);
v_startInclusive_684_ = lean_ctor_get(v___x_651_, 1);
v_endExclusive_685_ = lean_ctor_get(v___x_651_, 2);
v___x_686_ = lean_nat_sub(v_endExclusive_685_, v_startInclusive_684_);
v_decide_687_ = lean_nat_dec_eq(v_searcher_679_, v___x_686_);
lean_dec(v___x_686_);
if (v_decide_687_ == 0)
{
uint32_t v___x_688_; lean_object* v___x_689_; uint32_t v___x_690_; uint8_t v___x_691_; 
v___x_688_ = 10;
v___x_689_ = lean_nat_add(v_startInclusive_684_, v_searcher_679_);
v___x_690_ = lean_string_utf8_get_fast(v_str_683_, v___x_689_);
v___x_691_ = lean_uint32_dec_eq(v___x_690_, v___x_688_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
lean_dec(v_searcher_679_);
v___x_692_ = lean_string_utf8_next_fast(v_str_683_, v___x_689_);
lean_dec(v___x_689_);
v___x_693_ = lean_nat_sub(v___x_692_, v_startInclusive_684_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_693_);
v___x_695_ = v___x_681_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_currPos_678_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
v_a_655_ = v___x_695_;
goto _start;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_slice_701_; lean_object* v_nextIt_703_; 
v___x_698_ = lean_string_utf8_next_fast(v_str_683_, v___x_689_);
v___x_699_ = lean_nat_sub(v___x_698_, v___x_689_);
lean_dec(v___x_689_);
v___x_700_ = lean_nat_add(v_searcher_679_, v___x_699_);
lean_dec(v___x_699_);
lean_dec(v_searcher_679_);
lean_inc_ref(v___x_651_);
v_slice_701_ = l_String_Slice_slice_x21(v___x_651_, v_currPos_678_, v___x_700_);
lean_dec(v_currPos_678_);
lean_inc(v___x_700_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_700_);
lean_ctor_set(v___x_681_, 0, v___x_700_);
v_nextIt_703_ = v___x_681_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_700_);
v_nextIt_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_it_658_ = v_nextIt_703_;
v_out_659_ = v_slice_701_;
goto v___jp_657_;
}
}
}
else
{
uint8_t v_decide_705_; 
lean_del_object(v___x_681_);
lean_dec(v_searcher_679_);
v_decide_705_ = lean_nat_dec_eq(v_currPos_678_, v___x_652_);
if (v_decide_705_ == 0)
{
lean_object* v_slice_706_; lean_object* v___x_707_; 
lean_inc(v___x_654_);
lean_inc_ref(v_src_653_);
v_slice_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_706_, 0, v_src_653_);
lean_ctor_set(v_slice_706_, 1, v_currPos_678_);
lean_ctor_set(v_slice_706_, 2, v___x_654_);
v___x_707_ = lean_box(1);
v_it_658_ = v___x_707_;
v_out_659_ = v_slice_706_;
goto v___jp_657_;
}
else
{
lean_dec(v_currPos_678_);
lean_dec(v___x_654_);
lean_dec_ref(v_src_653_);
lean_dec_ref(v___x_651_);
return v_b_656_;
}
}
}
}
else
{
lean_dec(v___x_654_);
lean_dec_ref(v_src_653_);
lean_dec_ref(v___x_651_);
return v_b_656_;
}
v___jp_657_:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = l_String_Slice_lines_lineMap(v_out_659_);
v___x_661_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_660_);
lean_dec_ref(v___x_660_);
if (lean_obj_tag(v_b_656_) == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
v_a_655_ = v_it_658_;
v_b_656_ = v___x_663_;
goto _start;
}
else
{
lean_object* v_val_665_; uint8_t v___x_666_; 
v_val_665_ = lean_ctor_get(v_b_656_, 0);
v___x_666_ = lean_nat_dec_le(v___x_662_, v_val_665_);
if (v___x_666_ == 0)
{
lean_dec(v___x_662_);
v_a_655_ = v_it_658_;
goto _start;
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_isSharedCheck_675_ = !lean_is_exclusive(v_b_656_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v_b_656_, 0);
lean_dec(v_unused_676_);
v___x_669_ = v_b_656_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_dec(v_b_656_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_662_);
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_662_);
v___x_672_ = v_reuseFailAlloc_674_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
v_a_655_ = v_it_658_;
v_b_656_ = v___x_672_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_660_);
v_a_655_ = v_it_658_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v_src_711_, lean_object* v___x_712_, lean_object* v_a_713_, lean_object* v_b_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_709_, v___x_710_, v_src_711_, v___x_712_, v_a_713_, v_b_714_);
lean_dec(v___x_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v_src_718_, lean_object* v___x_719_, lean_object* v_a_720_, lean_object* v_b_721_){
_start:
{
lean_object* v_it_723_; lean_object* v_out_724_; 
if (lean_obj_tag(v_a_720_) == 0)
{
lean_object* v_currPos_743_; lean_object* v_searcher_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_773_; 
v_currPos_743_ = lean_ctor_get(v_a_720_, 0);
v_searcher_744_ = lean_ctor_get(v_a_720_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_773_ == 0)
{
v___x_746_ = v_a_720_;
v_isShared_747_ = v_isSharedCheck_773_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_searcher_744_);
lean_inc(v_currPos_743_);
lean_dec(v_a_720_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_773_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_str_748_; lean_object* v_startInclusive_749_; lean_object* v_endExclusive_750_; lean_object* v___x_751_; uint8_t v_decide_752_; 
v_str_748_ = lean_ctor_get(v___x_716_, 0);
v_startInclusive_749_ = lean_ctor_get(v___x_716_, 1);
v_endExclusive_750_ = lean_ctor_get(v___x_716_, 2);
v___x_751_ = lean_nat_sub(v_endExclusive_750_, v_startInclusive_749_);
v_decide_752_ = lean_nat_dec_eq(v_searcher_744_, v___x_751_);
lean_dec(v___x_751_);
if (v_decide_752_ == 0)
{
lean_object* v___x_753_; uint32_t v___x_754_; uint32_t v___x_755_; uint8_t v___x_756_; 
v___x_753_ = lean_nat_add(v_startInclusive_749_, v_searcher_744_);
v___x_754_ = lean_string_utf8_get_fast(v_str_748_, v___x_753_);
v___x_755_ = 10;
v___x_756_ = lean_uint32_dec_eq(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_760_; 
lean_dec(v_searcher_744_);
v___x_757_ = lean_string_utf8_next_fast(v_str_748_, v___x_753_);
lean_dec(v___x_753_);
v___x_758_ = lean_nat_sub(v___x_757_, v_startInclusive_749_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_758_);
v___x_760_ = v___x_746_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_currPos_743_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v___x_758_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_716_, v___x_717_, v_src_718_, v___x_719_, v___x_760_, v_b_721_);
return v___x_761_;
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_slice_766_; lean_object* v_nextIt_768_; 
v___x_763_ = lean_string_utf8_next_fast(v_str_748_, v___x_753_);
v___x_764_ = lean_nat_sub(v___x_763_, v___x_753_);
lean_dec(v___x_753_);
v___x_765_ = lean_nat_add(v_searcher_744_, v___x_764_);
lean_dec(v___x_764_);
lean_dec(v_searcher_744_);
lean_inc_ref(v___x_716_);
v_slice_766_ = l_String_Slice_slice_x21(v___x_716_, v_currPos_743_, v___x_765_);
lean_dec(v_currPos_743_);
lean_inc(v___x_765_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_765_);
lean_ctor_set(v___x_746_, 0, v___x_765_);
v_nextIt_768_ = v___x_746_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_765_);
v_nextIt_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
v_it_723_ = v_nextIt_768_;
v_out_724_ = v_slice_766_;
goto v___jp_722_;
}
}
}
else
{
uint8_t v_decide_770_; 
lean_del_object(v___x_746_);
lean_dec(v_searcher_744_);
v_decide_770_ = lean_nat_dec_eq(v_currPos_743_, v___x_717_);
if (v_decide_770_ == 0)
{
lean_object* v_slice_771_; lean_object* v___x_772_; 
lean_inc(v___x_719_);
lean_inc_ref(v_src_718_);
v_slice_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_771_, 0, v_src_718_);
lean_ctor_set(v_slice_771_, 1, v_currPos_743_);
lean_ctor_set(v_slice_771_, 2, v___x_719_);
v___x_772_ = lean_box(1);
v_it_723_ = v___x_772_;
v_out_724_ = v_slice_771_;
goto v___jp_722_;
}
else
{
lean_dec(v_currPos_743_);
lean_dec(v___x_719_);
lean_dec_ref(v_src_718_);
lean_dec_ref(v___x_716_);
return v_b_721_;
}
}
}
}
else
{
lean_dec(v___x_719_);
lean_dec_ref(v_src_718_);
lean_dec_ref(v___x_716_);
return v_b_721_;
}
v___jp_722_:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = l_String_Slice_lines_lineMap(v_out_724_);
v___x_726_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; 
v___x_727_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_725_);
lean_dec_ref(v___x_725_);
if (lean_obj_tag(v_b_721_) == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___x_729_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_716_, v___x_717_, v_src_718_, v___x_719_, v_it_723_, v___x_728_);
return v___x_729_;
}
else
{
lean_object* v_val_730_; uint8_t v___x_731_; 
v_val_730_ = lean_ctor_get(v_b_721_, 0);
v___x_731_ = lean_nat_dec_le(v___x_727_, v_val_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
lean_dec(v___x_727_);
v___x_732_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_716_, v___x_717_, v_src_718_, v___x_719_, v_it_723_, v_b_721_);
return v___x_732_;
}
else
{
lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_740_; 
v_isSharedCheck_740_ = !lean_is_exclusive(v_b_721_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_b_721_, 0);
lean_dec(v_unused_741_);
v___x_734_ = v_b_721_;
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
else
{
lean_dec(v_b_721_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_740_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_727_);
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_727_);
v___x_737_ = v_reuseFailAlloc_739_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; 
v___x_738_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_716_, v___x_717_, v_src_718_, v___x_719_, v_it_723_, v___x_737_);
return v___x_738_;
}
}
}
}
}
else
{
lean_object* v___x_742_; 
lean_dec_ref(v___x_725_);
v___x_742_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_716_, v___x_717_, v_src_718_, v___x_719_, v_it_723_, v_b_721_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object* v___x_774_, lean_object* v___x_775_, lean_object* v_src_776_, lean_object* v___x_777_, lean_object* v_a_778_, lean_object* v_b_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_774_, v___x_775_, v_src_776_, v___x_777_, v_a_778_, v_b_779_);
lean_dec(v___x_775_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object* v___x_781_, lean_object* v_i_782_, lean_object* v_out_783_, lean_object* v_pending_784_, lean_object* v___y_785_, lean_object* v_____r_786_, lean_object* v_out_787_){
_start:
{
lean_object* v_str_788_; lean_object* v_startInclusive_789_; lean_object* v_endExclusive_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_str_788_ = lean_ctor_get(v___x_781_, 0);
v_startInclusive_789_ = lean_ctor_get(v___x_781_, 1);
v_endExclusive_790_ = lean_ctor_get(v___x_781_, 2);
v___x_791_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_i_782_, v_out_783_);
v___x_792_ = lean_string_append(v_out_787_, v___x_791_);
lean_dec_ref(v___x_791_);
lean_inc(v_pending_784_);
v___x_793_ = l_String_Slice_Pos_nextn(v___x_781_, v_pending_784_, v___y_785_);
v___x_794_ = lean_nat_add(v_startInclusive_789_, v___x_793_);
lean_dec(v___x_793_);
v___x_795_ = lean_string_utf8_extract_fast(v_str_788_, v___x_794_, v_endExclusive_790_);
lean_dec(v___x_794_);
v___x_796_ = lean_string_append(v___x_792_, v___x_795_);
lean_dec_ref(v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v_pending_784_);
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object* v___x_799_, lean_object* v_i_800_, lean_object* v_out_801_, lean_object* v_pending_802_, lean_object* v___y_803_, lean_object* v_____r_804_, lean_object* v_out_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_799_, v_i_800_, v_out_801_, v_pending_802_, v___y_803_, v_____r_804_, v_out_805_);
lean_dec_ref(v___x_799_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object* v_i_807_, lean_object* v___y_808_, lean_object* v___x_809_, lean_object* v___x_810_, lean_object* v_src_811_, lean_object* v___x_812_, lean_object* v_a_813_, lean_object* v_b_814_){
_start:
{
lean_object* v___y_816_; lean_object* v_val_817_; 
if (lean_obj_tag(v_a_813_) == 0)
{
lean_object* v_currPos_821_; lean_object* v_searcher_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_885_; 
v_currPos_821_ = lean_ctor_get(v_a_813_, 0);
v_searcher_822_ = lean_ctor_get(v_a_813_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_813_);
if (v_isSharedCheck_885_ == 0)
{
v___x_824_ = v_a_813_;
v_isShared_825_ = v_isSharedCheck_885_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_searcher_822_);
lean_inc(v_currPos_821_);
lean_dec(v_a_813_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_885_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_str_826_; lean_object* v_startInclusive_827_; lean_object* v_endExclusive_828_; lean_object* v_out_829_; lean_object* v_pending_830_; lean_object* v_it_832_; lean_object* v_out_833_; lean_object* v___x_863_; uint8_t v_decide_864_; 
v_str_826_ = lean_ctor_get(v___x_809_, 0);
v_startInclusive_827_ = lean_ctor_get(v___x_809_, 1);
v_endExclusive_828_ = lean_ctor_get(v___x_809_, 2);
v_out_829_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_830_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_nat_sub(v_endExclusive_828_, v_startInclusive_827_);
v_decide_864_ = lean_nat_dec_eq(v_searcher_822_, v___x_863_);
lean_dec(v___x_863_);
if (v_decide_864_ == 0)
{
uint32_t v___x_865_; lean_object* v___x_866_; uint32_t v___x_867_; uint8_t v___x_868_; 
v___x_865_ = 10;
v___x_866_ = lean_nat_add(v_startInclusive_827_, v_searcher_822_);
v___x_867_ = lean_string_utf8_get_fast(v_str_826_, v___x_866_);
v___x_868_ = lean_uint32_dec_eq(v___x_867_, v___x_865_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
lean_dec(v_searcher_822_);
v___x_869_ = lean_string_utf8_next_fast(v_str_826_, v___x_866_);
lean_dec(v___x_866_);
v___x_870_ = lean_nat_sub(v___x_869_, v_startInclusive_827_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_870_);
v___x_872_ = v___x_824_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_currPos_821_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_874_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
v_a_813_ = v___x_872_;
goto _start;
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_slice_878_; lean_object* v_nextIt_880_; 
v___x_875_ = lean_string_utf8_next_fast(v_str_826_, v___x_866_);
v___x_876_ = lean_nat_sub(v___x_875_, v___x_866_);
lean_dec(v___x_866_);
v___x_877_ = lean_nat_add(v_searcher_822_, v___x_876_);
lean_dec(v___x_876_);
lean_dec(v_searcher_822_);
lean_inc_ref(v___x_809_);
v_slice_878_ = l_String_Slice_slice_x21(v___x_809_, v_currPos_821_, v___x_877_);
lean_dec(v_currPos_821_);
lean_inc(v___x_877_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_877_);
lean_ctor_set(v___x_824_, 0, v___x_877_);
v_nextIt_880_ = v___x_824_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_877_);
v_nextIt_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
v_it_832_ = v_nextIt_880_;
v_out_833_ = v_slice_878_;
goto v___jp_831_;
}
}
}
else
{
uint8_t v_decide_882_; 
lean_del_object(v___x_824_);
lean_dec(v_searcher_822_);
v_decide_882_ = lean_nat_dec_eq(v_currPos_821_, v___x_810_);
if (v_decide_882_ == 0)
{
lean_object* v_slice_883_; lean_object* v___x_884_; 
lean_inc(v___x_812_);
lean_inc_ref(v_src_811_);
v_slice_883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_883_, 0, v_src_811_);
lean_ctor_set(v_slice_883_, 1, v_currPos_821_);
lean_ctor_set(v_slice_883_, 2, v___x_812_);
v___x_884_ = lean_box(1);
v_it_832_ = v___x_884_;
v_out_833_ = v_slice_883_;
goto v___jp_831_;
}
else
{
lean_dec(v_currPos_821_);
lean_dec(v___x_812_);
lean_dec_ref(v_src_811_);
lean_dec_ref(v___x_809_);
lean_dec(v___y_808_);
lean_dec(v_i_807_);
return v_b_814_;
}
}
v___jp_831_:
{
lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_862_; 
v_fst_834_ = lean_ctor_get(v_b_814_, 0);
v_snd_835_ = lean_ctor_get(v_b_814_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_b_814_);
if (v_isSharedCheck_862_ == 0)
{
v___x_837_ = v_b_814_;
v_isShared_838_ = v_isSharedCheck_862_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_snd_835_);
lean_inc(v_fst_834_);
lean_dec(v_b_814_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_862_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = l_String_Slice_lines_lineMap(v_out_833_);
v___x_840_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
lean_del_object(v___x_837_);
v___x_841_ = lean_string_utf8_byte_size(v_fst_834_);
v___x_842_ = lean_nat_dec_eq(v___x_841_, v_pending_830_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_nat_add(v_snd_835_, v___x_843_);
lean_dec(v_snd_835_);
v___x_845_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_844_, v_fst_834_);
v___x_846_ = lean_box(0);
lean_inc(v___y_808_);
lean_inc(v_i_807_);
v___x_847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_839_, v_i_807_, v_out_829_, v_pending_830_, v___y_808_, v___x_846_, v___x_845_);
lean_dec_ref(v___x_839_);
v___y_816_ = v_it_832_;
v_val_817_ = v___x_847_;
goto v___jp_815_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v_snd_835_);
v___x_848_ = lean_box(0);
lean_inc(v___y_808_);
lean_inc(v_i_807_);
v___x_849_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_839_, v_i_807_, v_out_829_, v_pending_830_, v___y_808_, v___x_848_, v_fst_834_);
lean_dec_ref(v___x_839_);
v___y_816_ = v_it_832_;
v_val_817_ = v___x_849_;
goto v___jp_815_;
}
}
else
{
lean_object* v___x_850_; uint8_t v___x_851_; 
lean_dec_ref(v___x_839_);
v___x_850_ = lean_string_utf8_byte_size(v_fst_834_);
v___x_851_ = lean_nat_dec_eq(v___x_850_, v_pending_830_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_852_ = lean_unsigned_to_nat(1u);
v___x_853_ = lean_nat_add(v_snd_835_, v___x_852_);
lean_dec(v_snd_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_853_);
v___x_855_ = v___x_837_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_853_);
v___x_855_ = v_reuseFailAlloc_857_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
v_a_813_ = v_it_832_;
v_b_814_ = v___x_855_;
goto _start;
}
}
else
{
lean_object* v___x_859_; 
if (v_isShared_838_ == 0)
{
v___x_859_ = v___x_837_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_fst_834_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_835_);
v___x_859_ = v_reuseFailAlloc_861_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
v_a_813_ = v_it_832_;
v_b_814_ = v___x_859_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_812_);
lean_dec_ref(v_src_811_);
lean_dec_ref(v___x_809_);
lean_dec(v___y_808_);
lean_dec(v_i_807_);
return v_b_814_;
}
v___jp_815_:
{
if (lean_obj_tag(v_val_817_) == 0)
{
lean_object* v_a_818_; 
lean_dec(v___y_816_);
lean_dec(v___x_812_);
lean_dec_ref(v_src_811_);
lean_dec_ref(v___x_809_);
lean_dec(v___y_808_);
lean_dec(v_i_807_);
v_a_818_ = lean_ctor_get(v_val_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v_val_817_, 1);
return v_a_818_;
}
else
{
lean_object* v_a_819_; 
v_a_819_ = lean_ctor_get(v_val_817_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v_val_817_, 1);
v_a_813_ = v___y_816_;
v_b_814_ = v_a_819_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object* v_i_886_, lean_object* v___y_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v_src_890_, lean_object* v___x_891_, lean_object* v_a_892_, lean_object* v_b_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_886_, v___y_887_, v___x_888_, v___x_889_, v_src_890_, v___x_891_, v_a_892_, v_b_893_);
lean_dec(v___x_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object* v_i_895_, lean_object* v___y_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_src_899_, lean_object* v___x_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v___y_904_; lean_object* v_val_905_; 
if (lean_obj_tag(v_a_901_) == 0)
{
lean_object* v_currPos_909_; lean_object* v_searcher_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_973_; 
v_currPos_909_ = lean_ctor_get(v_a_901_, 0);
v_searcher_910_ = lean_ctor_get(v_a_901_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_901_);
if (v_isSharedCheck_973_ == 0)
{
v___x_912_ = v_a_901_;
v_isShared_913_ = v_isSharedCheck_973_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_searcher_910_);
lean_inc(v_currPos_909_);
lean_dec(v_a_901_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_973_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_str_914_; lean_object* v_startInclusive_915_; lean_object* v_endExclusive_916_; lean_object* v_out_917_; lean_object* v_pending_918_; lean_object* v_it_920_; lean_object* v_out_921_; lean_object* v___x_951_; uint8_t v_decide_952_; 
v_str_914_ = lean_ctor_get(v___x_897_, 0);
v_startInclusive_915_ = lean_ctor_get(v___x_897_, 1);
v_endExclusive_916_ = lean_ctor_get(v___x_897_, 2);
v_out_917_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_918_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_nat_sub(v_endExclusive_916_, v_startInclusive_915_);
v_decide_952_ = lean_nat_dec_eq(v_searcher_910_, v___x_951_);
lean_dec(v___x_951_);
if (v_decide_952_ == 0)
{
lean_object* v___x_953_; uint32_t v___x_954_; uint32_t v___x_955_; uint8_t v___x_956_; 
v___x_953_ = lean_nat_add(v_startInclusive_915_, v_searcher_910_);
v___x_954_ = lean_string_utf8_get_fast(v_str_914_, v___x_953_);
v___x_955_ = 10;
v___x_956_ = lean_uint32_dec_eq(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec(v_searcher_910_);
v___x_957_ = lean_string_utf8_next_fast(v_str_914_, v___x_953_);
lean_dec(v___x_953_);
v___x_958_ = lean_nat_sub(v___x_957_, v_startInclusive_915_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_958_);
v___x_960_ = v___x_912_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_currPos_909_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_962_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; 
v___x_961_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_895_, v___y_896_, v___x_897_, v___x_898_, v_src_899_, v___x_900_, v___x_960_, v_b_902_);
return v___x_961_;
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_slice_966_; lean_object* v_nextIt_968_; 
v___x_963_ = lean_string_utf8_next_fast(v_str_914_, v___x_953_);
v___x_964_ = lean_nat_sub(v___x_963_, v___x_953_);
lean_dec(v___x_953_);
v___x_965_ = lean_nat_add(v_searcher_910_, v___x_964_);
lean_dec(v___x_964_);
lean_dec(v_searcher_910_);
lean_inc_ref(v___x_897_);
v_slice_966_ = l_String_Slice_slice_x21(v___x_897_, v_currPos_909_, v___x_965_);
lean_dec(v_currPos_909_);
lean_inc(v___x_965_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_965_);
lean_ctor_set(v___x_912_, 0, v___x_965_);
v_nextIt_968_ = v___x_912_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_965_);
v_nextIt_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
v_it_920_ = v_nextIt_968_;
v_out_921_ = v_slice_966_;
goto v___jp_919_;
}
}
}
else
{
uint8_t v_decide_970_; 
lean_del_object(v___x_912_);
lean_dec(v_searcher_910_);
v_decide_970_ = lean_nat_dec_eq(v_currPos_909_, v___x_898_);
if (v_decide_970_ == 0)
{
lean_object* v_slice_971_; lean_object* v___x_972_; 
lean_inc(v___x_900_);
lean_inc_ref(v_src_899_);
v_slice_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_971_, 0, v_src_899_);
lean_ctor_set(v_slice_971_, 1, v_currPos_909_);
lean_ctor_set(v_slice_971_, 2, v___x_900_);
v___x_972_ = lean_box(1);
v_it_920_ = v___x_972_;
v_out_921_ = v_slice_971_;
goto v___jp_919_;
}
else
{
lean_dec(v_currPos_909_);
lean_dec(v___x_900_);
lean_dec_ref(v_src_899_);
lean_dec_ref(v___x_897_);
lean_dec(v___y_896_);
lean_dec(v_i_895_);
return v_b_902_;
}
}
v___jp_919_:
{
lean_object* v_fst_922_; lean_object* v_snd_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_950_; 
v_fst_922_ = lean_ctor_get(v_b_902_, 0);
v_snd_923_ = lean_ctor_get(v_b_902_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_b_902_);
if (v_isSharedCheck_950_ == 0)
{
v___x_925_ = v_b_902_;
v_isShared_926_ = v_isSharedCheck_950_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_snd_923_);
lean_inc(v_fst_922_);
lean_dec(v_b_902_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_950_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = l_String_Slice_lines_lineMap(v_out_921_);
v___x_928_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; uint8_t v___x_930_; 
lean_del_object(v___x_925_);
v___x_929_ = lean_string_utf8_byte_size(v_fst_922_);
v___x_930_ = lean_nat_dec_eq(v___x_929_, v_pending_918_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = lean_nat_add(v_snd_923_, v___x_931_);
lean_dec(v_snd_923_);
v___x_933_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_932_, v_fst_922_);
v___x_934_ = lean_box(0);
lean_inc(v___y_896_);
lean_inc(v_i_895_);
v___x_935_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_927_, v_i_895_, v_out_917_, v_pending_918_, v___y_896_, v___x_934_, v___x_933_);
lean_dec_ref(v___x_927_);
v___y_904_ = v_it_920_;
v_val_905_ = v___x_935_;
goto v___jp_903_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v_snd_923_);
v___x_936_ = lean_box(0);
lean_inc(v___y_896_);
lean_inc(v_i_895_);
v___x_937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_927_, v_i_895_, v_out_917_, v_pending_918_, v___y_896_, v___x_936_, v_fst_922_);
lean_dec_ref(v___x_927_);
v___y_904_ = v_it_920_;
v_val_905_ = v___x_937_;
goto v___jp_903_;
}
}
else
{
lean_object* v___x_938_; uint8_t v___x_939_; 
lean_dec_ref(v___x_927_);
v___x_938_ = lean_string_utf8_byte_size(v_fst_922_);
v___x_939_ = lean_nat_dec_eq(v___x_938_, v_pending_918_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_add(v_snd_923_, v___x_940_);
lean_dec(v_snd_923_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 1, v___x_941_);
v___x_943_ = v___x_925_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_fst_922_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_941_);
v___x_943_ = v_reuseFailAlloc_945_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_895_, v___y_896_, v___x_897_, v___x_898_, v_src_899_, v___x_900_, v_it_920_, v___x_943_);
return v___x_944_;
}
}
else
{
lean_object* v___x_947_; 
if (v_isShared_926_ == 0)
{
v___x_947_ = v___x_925_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_fst_922_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_snd_923_);
v___x_947_ = v_reuseFailAlloc_949_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
v___x_948_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_895_, v___y_896_, v___x_897_, v___x_898_, v_src_899_, v___x_900_, v_it_920_, v___x_947_);
return v___x_948_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_900_);
lean_dec_ref(v_src_899_);
lean_dec_ref(v___x_897_);
lean_dec(v___y_896_);
lean_dec(v_i_895_);
return v_b_902_;
}
v___jp_903_:
{
if (lean_obj_tag(v_val_905_) == 0)
{
lean_object* v_a_906_; 
lean_dec(v___y_904_);
lean_dec(v___x_900_);
lean_dec_ref(v_src_899_);
lean_dec_ref(v___x_897_);
lean_dec(v___y_896_);
lean_dec(v_i_895_);
v_a_906_ = lean_ctor_get(v_val_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref_known(v_val_905_, 1);
return v_a_906_;
}
else
{
lean_object* v_a_907_; lean_object* v___x_908_; 
v_a_907_ = lean_ctor_get(v_val_905_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v_val_905_, 1);
v___x_908_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_895_, v___y_896_, v___x_897_, v___x_898_, v_src_899_, v___x_900_, v___y_904_, v_a_907_);
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object* v_i_974_, lean_object* v___y_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v_src_978_, lean_object* v___x_979_, lean_object* v_a_980_, lean_object* v_b_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_974_, v___y_975_, v___x_976_, v___x_977_, v_src_978_, v___x_979_, v_a_980_, v_b_981_);
lean_dec(v___x_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object* v_i_986_, lean_object* v_src_987_){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___y_994_; lean_object* v___x_998_; 
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = lean_string_utf8_byte_size(v_src_987_);
lean_inc_ref_n(v_src_987_, 3);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v_src_987_);
lean_ctor_set(v___x_990_, 1, v___x_988_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
v___x_991_ = lean_box(0);
v___x_992_ = l_String_lines(v_src_987_);
lean_inc(v___x_992_);
lean_inc_ref(v___x_990_);
v___x_998_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_990_, v___x_989_, v_src_987_, v___x_989_, v___x_992_, v___x_991_);
if (lean_obj_tag(v___x_998_) == 0)
{
v___y_994_ = v___x_988_;
goto v___jp_993_;
}
else
{
lean_object* v_val_999_; 
v_val_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v___x_998_, 1);
v___y_994_ = v_val_999_;
goto v___jp_993_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_fst_997_; 
v___x_995_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0));
v___x_996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_986_, v___y_994_, v___x_990_, v___x_989_, v_src_987_, v___x_989_, v___x_992_, v___x_995_);
v_fst_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_fst_997_);
lean_dec_ref(v___x_996_);
return v_fst_997_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object* v_i_1000_, lean_object* v___y_1001_, lean_object* v___x_1002_, lean_object* v___x_1003_, lean_object* v_src_1004_, lean_object* v___x_1005_, lean_object* v_inst_1006_, lean_object* v_R_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_, lean_object* v_c_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_1000_, v___y_1001_, v___x_1002_, v___x_1003_, v_src_1004_, v___x_1005_, v_a_1008_, v_b_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object* v_i_1012_, lean_object* v___y_1013_, lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v_src_1016_, lean_object* v___x_1017_, lean_object* v_inst_1018_, lean_object* v_R_1019_, lean_object* v_a_1020_, lean_object* v_b_1021_, lean_object* v_c_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(v_i_1012_, v___y_1013_, v___x_1014_, v___x_1015_, v_src_1016_, v___x_1017_, v_inst_1018_, v_R_1019_, v_a_1020_, v_b_1021_, v_c_1022_);
lean_dec(v___x_1015_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v_src_1026_, lean_object* v___x_1027_, lean_object* v_inst_1028_, lean_object* v_R_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_, lean_object* v_c_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1024_, v___x_1025_, v_src_1026_, v___x_1027_, v_a_1030_, v_b_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_src_1036_, lean_object* v___x_1037_, lean_object* v_inst_1038_, lean_object* v_R_1039_, lean_object* v_a_1040_, lean_object* v_b_1041_, lean_object* v_c_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(v___x_1034_, v___x_1035_, v_src_1036_, v___x_1037_, v_inst_1038_, v_R_1039_, v_a_1040_, v_b_1041_, v_c_1042_);
lean_dec(v___x_1035_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object* v_i_1044_, lean_object* v___y_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v_src_1048_, lean_object* v___x_1049_, lean_object* v_inst_1050_, lean_object* v_R_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v_c_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_1044_, v___y_1045_, v___x_1046_, v___x_1047_, v_src_1048_, v___x_1049_, v_a_1052_, v_b_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object* v_i_1056_, lean_object* v___y_1057_, lean_object* v___x_1058_, lean_object* v___x_1059_, lean_object* v_src_1060_, lean_object* v___x_1061_, lean_object* v_inst_1062_, lean_object* v_R_1063_, lean_object* v_a_1064_, lean_object* v_b_1065_, lean_object* v_c_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(v_i_1056_, v___y_1057_, v___x_1058_, v___x_1059_, v_src_1060_, v___x_1061_, v_inst_1062_, v_R_1063_, v_a_1064_, v_b_1065_, v_c_1066_);
lean_dec(v___x_1059_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object* v___x_1068_, lean_object* v___x_1069_, lean_object* v_src_1070_, lean_object* v___x_1071_, lean_object* v_inst_1072_, lean_object* v_R_1073_, lean_object* v_a_1074_, lean_object* v_b_1075_, lean_object* v_c_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_1068_, v___x_1069_, v_src_1070_, v___x_1071_, v_a_1074_, v_b_1075_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_src_1080_, lean_object* v___x_1081_, lean_object* v_inst_1082_, lean_object* v_R_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v_c_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(v___x_1078_, v___x_1079_, v_src_1080_, v___x_1081_, v_inst_1082_, v_R_1083_, v_a_1084_, v_b_1085_, v_c_1086_);
lean_dec(v___x_1079_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
lean_object* v_zero_1090_; uint8_t v_isZero_1091_; 
v_zero_1090_ = lean_unsigned_to_nat(0u);
v_isZero_1091_ = lean_nat_dec_eq(v_x_1088_, v_zero_1090_);
if (v_isZero_1091_ == 1)
{
lean_dec(v_x_1088_);
return v_x_1089_;
}
else
{
uint32_t v___x_1092_; lean_object* v_one_1093_; lean_object* v_n_1094_; lean_object* v___x_1095_; 
v___x_1092_ = 96;
v_one_1093_ = lean_unsigned_to_nat(1u);
v_n_1094_ = lean_nat_sub(v_x_1088_, v_one_1093_);
lean_dec(v_x_1088_);
v___x_1095_ = lean_string_push(v_x_1089_, v___x_1092_);
v_x_1088_ = v_n_1094_;
v_x_1089_ = v___x_1095_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object* v_value_1098_){
_start:
{
lean_object* v___y_1100_; lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1122_; 
v___x_1114_ = lean_string_utf8_byte_size(v_value_1098_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_nat_dec_eq(v___x_1114_, v___x_1115_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_nat_dec_le(v___x_1123_, v___x_1114_);
if (v___x_1124_ == 0)
{
goto v___jp_1116_;
}
else
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1126_ = lean_string_memcmp(v_value_1098_, v___x_1125_, v___x_1115_, v___x_1115_, v___x_1123_);
if (v___x_1126_ == 0)
{
goto v___jp_1116_;
}
else
{
goto v___jp_1108_;
}
}
}
else
{
lean_object* v___x_1127_; 
lean_dec_ref(v_value_1098_);
v___x_1127_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___y_1100_ = v___x_1127_;
goto v___jp_1099_;
}
v___jp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_delim_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1101_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_1102_ = l_Lean_Doc_longestBacktickRun(v___y_1100_);
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_add(v___x_1102_, v___x_1103_);
lean_dec(v___x_1102_);
v_delim_1105_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___x_1104_, v___x_1101_);
lean_inc_ref(v_delim_1105_);
v___x_1106_ = lean_string_append(v_delim_1105_, v___y_1100_);
lean_dec_ref(v___y_1100_);
v___x_1107_ = lean_string_append(v___x_1106_, v_delim_1105_);
lean_dec_ref(v_delim_1105_);
return v___x_1107_;
}
v___jp_1108_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1110_ = lean_string_append(v___x_1109_, v_value_1098_);
lean_dec_ref(v_value_1098_);
v___x_1111_ = lean_string_append(v___x_1110_, v___x_1109_);
v___y_1100_ = v___x_1111_;
goto v___jp_1099_;
}
v___jp_1112_:
{
uint8_t v___x_1113_; 
lean_inc_ref(v_value_1098_);
v___x_1113_ = l_Lean_Doc_versoCodeBoundarySpaces(v_value_1098_);
if (v___x_1113_ == 0)
{
v___y_1100_ = v_value_1098_;
goto v___jp_1099_;
}
else
{
goto v___jp_1108_;
}
}
v___jp_1116_:
{
lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_dec_le(v___x_1117_, v___x_1114_);
if (v___x_1118_ == 0)
{
goto v___jp_1112_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1119_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1120_ = lean_nat_sub(v___x_1114_, v___x_1117_);
v___x_1121_ = lean_string_memcmp(v_value_1098_, v___x_1119_, v___x_1120_, v___x_1115_, v___x_1117_);
lean_dec(v___x_1120_);
if (v___x_1121_ == 0)
{
goto v___jp_1112_;
}
else
{
goto v___jp_1108_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t v_char_1128_, lean_object* v_as_1129_, size_t v_i_1130_, size_t v_stop_1131_, lean_object* v_b_1132_){
_start:
{
lean_object* v___y_1134_; uint8_t v___x_1138_; 
v___x_1138_ = lean_usize_dec_eq(v_i_1130_, v_stop_1131_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_array_uget_borrowed(v_as_1129_, v_i_1130_);
lean_inc(v___x_1139_);
v___x_1140_ = l_Lean_Doc_InlineView_of(v___x_1139_);
if (lean_obj_tag(v___x_1140_) == 1)
{
lean_object* v_val_1141_; 
v_val_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_val_1141_);
lean_dec_ref_known(v___x_1140_, 1);
switch(lean_obj_tag(v_val_1141_))
{
case 1:
{
lean_object* v_view_1142_; lean_object* v___y_1144_; uint32_t v___x_1149_; uint8_t v___x_1150_; 
v_view_1142_ = lean_ctor_get(v_val_1141_, 0);
lean_inc_ref(v_view_1142_);
lean_dec_ref_known(v_val_1141_, 1);
v___x_1149_ = 95;
v___x_1150_ = lean_uint32_dec_eq(v_char_1128_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v___y_1144_ = v___x_1151_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_unsigned_to_nat(1u);
v___y_1144_ = v___x_1152_;
goto v___jp_1143_;
}
v___jp_1143_:
{
lean_object* v_content_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_content_1145_ = lean_ctor_get(v_view_1142_, 2);
lean_inc_ref(v_content_1145_);
lean_dec_ref(v_view_1142_);
v___x_1146_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1128_, v_content_1145_);
lean_dec_ref(v_content_1145_);
v___x_1147_ = lean_nat_add(v___y_1144_, v___x_1146_);
lean_dec(v___x_1146_);
v___x_1148_ = lean_nat_dec_le(v_b_1132_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec(v___x_1147_);
v___y_1134_ = v_b_1132_;
goto v___jp_1133_;
}
else
{
lean_dec(v_b_1132_);
v___y_1134_ = v___x_1147_;
goto v___jp_1133_;
}
}
}
case 2:
{
lean_object* v_view_1153_; lean_object* v___y_1155_; uint32_t v___x_1160_; uint8_t v___x_1161_; 
v_view_1153_ = lean_ctor_get(v_val_1141_, 0);
lean_inc_ref(v_view_1153_);
lean_dec_ref_known(v_val_1141_, 1);
v___x_1160_ = 42;
v___x_1161_ = lean_uint32_dec_eq(v_char_1128_, v___x_1160_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___y_1155_ = v___x_1162_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___y_1155_ = v___x_1163_;
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v_content_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_content_1156_ = lean_ctor_get(v_view_1153_, 2);
lean_inc_ref(v_content_1156_);
lean_dec_ref(v_view_1153_);
v___x_1157_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1128_, v_content_1156_);
lean_dec_ref(v_content_1156_);
v___x_1158_ = lean_nat_add(v___y_1155_, v___x_1157_);
lean_dec(v___x_1157_);
v___x_1159_ = lean_nat_dec_le(v_b_1132_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec(v___x_1158_);
v___y_1134_ = v_b_1132_;
goto v___jp_1133_;
}
else
{
lean_dec(v_b_1132_);
v___y_1134_ = v___x_1158_;
goto v___jp_1133_;
}
}
}
case 5:
{
lean_object* v_view_1164_; lean_object* v_content_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_view_1164_ = lean_ctor_get(v_val_1141_, 0);
lean_inc_ref(v_view_1164_);
lean_dec_ref_known(v_val_1141_, 1);
v_content_1165_ = lean_ctor_get(v_view_1164_, 2);
lean_inc_ref(v_content_1165_);
lean_dec_ref(v_view_1164_);
v___x_1166_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1128_, v_content_1165_);
lean_dec_ref(v_content_1165_);
v___x_1167_ = lean_nat_dec_le(v_b_1132_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec(v___x_1166_);
v___y_1134_ = v_b_1132_;
goto v___jp_1133_;
}
else
{
lean_dec(v_b_1132_);
v___y_1134_ = v___x_1166_;
goto v___jp_1133_;
}
}
case 9:
{
lean_object* v_view_1168_; lean_object* v_content_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_view_1168_ = lean_ctor_get(v_val_1141_, 0);
lean_inc_ref(v_view_1168_);
lean_dec_ref_known(v_val_1141_, 1);
v_content_1169_ = lean_ctor_get(v_view_1168_, 6);
lean_inc_ref(v_content_1169_);
lean_dec_ref(v_view_1168_);
v___x_1170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1128_, v_content_1169_);
lean_dec_ref(v_content_1169_);
v___x_1171_ = lean_nat_dec_le(v_b_1132_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_dec(v___x_1170_);
v___y_1134_ = v_b_1132_;
goto v___jp_1133_;
}
else
{
lean_dec(v_b_1132_);
v___y_1134_ = v___x_1170_;
goto v___jp_1133_;
}
}
default: 
{
lean_dec(v_val_1141_);
v___y_1134_ = v_b_1132_;
goto v___jp_1133_;
}
}
}
else
{
lean_dec(v___x_1140_);
v___y_1134_ = v_b_1132_;
goto v___jp_1133_;
}
}
else
{
return v_b_1132_;
}
v___jp_1133_:
{
size_t v___x_1135_; size_t v___x_1136_; 
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_add(v_i_1130_, v___x_1135_);
v_i_1130_ = v___x_1136_;
v_b_1132_ = v___y_1134_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_char_1128_ = stack[0].m_num;
lean_object* v_as_1129_ = stack[1].m_obj;
size_t v_i_1130_ = stack[2].m_num;
size_t v_stop_1131_ = stack[3].m_num;
lean_object* v_b_1132_ = stack[4].m_obj;
lean_object* v_res_1172_;
v_res_1172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1128_, v_as_1129_, v_i_1130_, v_stop_1131_, v_b_1132_);
stack->m_obj
 = v_res_1172_;
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t v_char_1173_, lean_object* v_inls_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_array_get_size(v_inls_1174_);
v___x_1177_ = lean_nat_dec_lt(v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
return v___x_1175_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_nat_dec_le(v___x_1176_, v___x_1176_);
if (v___x_1178_ == 0)
{
if (v___x_1177_ == 0)
{
return v___x_1175_;
}
else
{
size_t v___x_1179_; size_t v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = ((size_t)0ULL);
v___x_1180_ = lean_usize_of_nat(v___x_1176_);
v___x_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1173_, v_inls_1174_, v___x_1179_, v___x_1180_, v___x_1175_);
return v___x_1181_;
}
}
else
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = lean_usize_of_nat(v___x_1176_);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1173_, v_inls_1174_, v___x_1182_, v___x_1183_, v___x_1175_);
return v___x_1184_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_0interp(lean_interpreter_value* stack)
{
uint32_t v_char_1173_ = stack[0].m_num;
lean_object* v_inls_1174_ = stack[1].m_obj;
lean_object* v_res_1185_;
v_res_1185_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1173_, v_inls_1174_);
stack->m_obj
 = v_res_1185_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object* v_char_1186_, lean_object* v_inls_1187_){
_start:
{
uint32_t v_char_boxed_1188_; lean_object* v_res_1189_; 
v_char_boxed_1188_ = lean_unbox_uint32(v_char_1186_);
lean_dec(v_char_1186_);
v_res_1189_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_boxed_1188_, v_inls_1187_);
lean_dec_ref(v_inls_1187_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object* v_char_1190_, lean_object* v_as_1191_, lean_object* v_i_1192_, lean_object* v_stop_1193_, lean_object* v_b_1194_){
_start:
{
uint32_t v_char_boxed_1195_; size_t v_i_boxed_1196_; size_t v_stop_boxed_1197_; lean_object* v_res_1198_; 
v_char_boxed_1195_ = lean_unbox_uint32(v_char_1190_);
lean_dec(v_char_1190_);
v_i_boxed_1196_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_stop_boxed_1197_ = lean_unbox_usize(v_stop_1193_);
lean_dec(v_stop_1193_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_boxed_1195_, v_as_1191_, v_i_boxed_1196_, v_stop_boxed_1197_, v_b_1194_);
lean_dec_ref(v_as_1191_);
return v_res_1198_;
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t v_char_1199_, lean_object* v_inls_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1199_, v_inls_1200_);
v___x_1203_ = lean_nat_add(v___x_1201_, v___x_1202_);
lean_dec(v___x_1202_);
return v___x_1203_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_0interp(lean_interpreter_value* stack)
{
uint32_t v_char_1199_ = stack[0].m_num;
lean_object* v_inls_1200_ = stack[1].m_obj;
lean_object* v_res_1204_;
v_res_1204_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_1199_, v_inls_1200_);
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object* v_char_1205_, lean_object* v_inls_1206_){
_start:
{
uint32_t v_char_boxed_1207_; lean_object* v_res_1208_; 
v_char_boxed_1207_ = lean_unbox_uint32(v_char_1205_);
lean_dec(v_char_1205_);
v_res_1208_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_boxed_1207_, v_inls_1206_);
lean_dec_ref(v_inls_1206_);
return v_res_1208_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object* v_as_1209_, size_t v_i_1210_, size_t v_stop_1211_, lean_object* v_b_1212_){
_start:
{
lean_object* v___y_1214_; uint8_t v___x_1218_; 
v___x_1218_ = lean_usize_dec_eq(v_i_1210_, v_stop_1211_);
if (v___x_1218_ == 0)
{
lean_object* v___x_1219_; lean_object* v_contents_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1219_ = lean_array_uget_borrowed(v_as_1209_, v_i_1210_);
v_contents_1220_ = lean_ctor_get(v___x_1219_, 2);
v___x_1221_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1220_);
v___x_1222_ = lean_nat_dec_le(v_b_1212_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_dec(v___x_1221_);
v___y_1214_ = v_b_1212_;
goto v___jp_1213_;
}
else
{
lean_dec(v_b_1212_);
v___y_1214_ = v___x_1221_;
goto v___jp_1213_;
}
}
else
{
return v_b_1212_;
}
v___jp_1213_:
{
size_t v___x_1215_; size_t v___x_1216_; 
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1210_, v___x_1215_);
v_i_1210_ = v___x_1216_;
v_b_1212_ = v___y_1214_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1209_ = stack[0].m_obj;
size_t v_i_1210_ = stack[1].m_num;
size_t v_stop_1211_ = stack[2].m_num;
lean_object* v_b_1212_ = stack[3].m_obj;
lean_object* v_res_1223_;
v_res_1223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_as_1209_, v_i_1210_, v_stop_1211_, v_b_1212_);
stack->m_obj
 = v_res_1223_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object* v_as_1224_, size_t v_i_1225_, size_t v_stop_1226_, lean_object* v_b_1227_){
_start:
{
lean_object* v___y_1229_; uint8_t v___x_1233_; 
v___x_1233_ = lean_usize_dec_eq(v_i_1225_, v_stop_1226_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; lean_object* v_desc_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1234_ = lean_array_uget_borrowed(v_as_1224_, v_i_1225_);
v_desc_1235_ = lean_ctor_get(v___x_1234_, 3);
v___x_1236_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_desc_1235_);
v___x_1237_ = lean_nat_dec_le(v_b_1227_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec(v___x_1236_);
v___y_1229_ = v_b_1227_;
goto v___jp_1228_;
}
else
{
lean_dec(v_b_1227_);
v___y_1229_ = v___x_1236_;
goto v___jp_1228_;
}
}
else
{
return v_b_1227_;
}
v___jp_1228_:
{
size_t v___x_1230_; size_t v___x_1231_; 
v___x_1230_ = ((size_t)1ULL);
v___x_1231_ = lean_usize_add(v_i_1225_, v___x_1230_);
v_i_1225_ = v___x_1231_;
v_b_1227_ = v___y_1229_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1224_ = stack[0].m_obj;
size_t v_i_1225_ = stack[1].m_num;
size_t v_stop_1226_ = stack[2].m_num;
lean_object* v_b_1227_ = stack[3].m_obj;
lean_object* v_res_1238_;
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_as_1224_, v_i_1225_, v_stop_1226_, v_b_1227_);
stack->m_obj
 = v_res_1238_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object* v_as_1239_, size_t v_i_1240_, size_t v_stop_1241_, lean_object* v_b_1242_){
_start:
{
lean_object* v___y_1244_; lean_object* v___y_1249_; uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_eq(v_i_1240_, v_stop_1241_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_array_uget_borrowed(v_as_1239_, v_i_1240_);
lean_inc(v___x_1254_);
v___x_1255_ = l_Lean_Doc_BlockView_of(v___x_1254_);
if (lean_obj_tag(v___x_1255_) == 1)
{
lean_object* v_val_1256_; 
v_val_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_val_1256_);
lean_dec_ref_known(v___x_1255_, 1);
switch(lean_obj_tag(v_val_1256_))
{
case 6:
{
lean_object* v_view_1257_; lean_object* v_content_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_view_1257_ = lean_ctor_get(v_val_1256_, 0);
lean_inc_ref(v_view_1257_);
lean_dec_ref_known(v_val_1256_, 1);
v_content_1258_ = lean_ctor_get(v_view_1257_, 4);
lean_inc_ref(v_content_1258_);
lean_dec_ref(v_view_1257_);
v___x_1259_ = lean_unsigned_to_nat(3u);
v___x_1260_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1258_);
lean_dec_ref(v_content_1258_);
v___x_1261_ = lean_nat_dec_le(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_dec(v___x_1260_);
v___y_1249_ = v___x_1259_;
goto v___jp_1248_;
}
else
{
v___y_1249_ = v___x_1260_;
goto v___jp_1248_;
}
}
case 4:
{
lean_object* v_view_1262_; lean_object* v_content_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_view_1262_ = lean_ctor_get(v_val_1256_, 0);
lean_inc_ref(v_view_1262_);
lean_dec_ref_known(v_val_1256_, 1);
v_content_1263_ = lean_ctor_get(v_view_1262_, 2);
lean_inc_ref(v_content_1263_);
lean_dec_ref(v_view_1262_);
v___x_1264_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1263_);
lean_dec_ref(v_content_1263_);
v___x_1265_ = lean_nat_dec_le(v_b_1242_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec(v___x_1264_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
lean_dec(v_b_1242_);
v___y_1244_ = v___x_1264_;
goto v___jp_1243_;
}
}
case 1:
{
lean_object* v_view_1266_; lean_object* v_items_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_view_1266_ = lean_ctor_get(v_val_1256_, 0);
lean_inc_ref(v_view_1266_);
lean_dec_ref_known(v_val_1256_, 1);
v_items_1267_ = lean_ctor_get(v_view_1266_, 1);
lean_inc_ref(v_items_1267_);
lean_dec_ref(v_view_1266_);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_array_get_size(v_items_1267_);
v___x_1270_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec_ref(v_items_1267_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_nat_dec_le(v___x_1269_, v___x_1269_);
if (v___x_1271_ == 0)
{
if (v___x_1270_ == 0)
{
lean_dec_ref(v_items_1267_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = lean_usize_of_nat(v___x_1269_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1267_, v___x_1272_, v___x_1273_, v_b_1242_);
lean_dec_ref(v_items_1267_);
v___y_1244_ = v___x_1274_;
goto v___jp_1243_;
}
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = lean_usize_of_nat(v___x_1269_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1267_, v___x_1275_, v___x_1276_, v_b_1242_);
lean_dec_ref(v_items_1267_);
v___y_1244_ = v___x_1277_;
goto v___jp_1243_;
}
}
}
case 2:
{
lean_object* v_view_1278_; lean_object* v_items_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_view_1278_ = lean_ctor_get(v_val_1256_, 0);
lean_inc_ref(v_view_1278_);
lean_dec_ref_known(v_val_1256_, 1);
v_items_1279_ = lean_ctor_get(v_view_1278_, 2);
lean_inc_ref(v_items_1279_);
lean_dec_ref(v_view_1278_);
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_array_get_size(v_items_1279_);
v___x_1282_ = lean_nat_dec_lt(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec_ref(v_items_1279_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1283_; 
v___x_1283_ = lean_nat_dec_le(v___x_1281_, v___x_1281_);
if (v___x_1283_ == 0)
{
if (v___x_1282_ == 0)
{
lean_dec_ref(v_items_1279_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = lean_usize_of_nat(v___x_1281_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1279_, v___x_1284_, v___x_1285_, v_b_1242_);
lean_dec_ref(v_items_1279_);
v___y_1244_ = v___x_1286_;
goto v___jp_1243_;
}
}
else
{
size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = lean_usize_of_nat(v___x_1281_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1279_, v___x_1287_, v___x_1288_, v_b_1242_);
lean_dec_ref(v_items_1279_);
v___y_1244_ = v___x_1289_;
goto v___jp_1243_;
}
}
}
case 3:
{
lean_object* v_view_1290_; lean_object* v_items_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_view_1290_ = lean_ctor_get(v_val_1256_, 0);
lean_inc_ref(v_view_1290_);
lean_dec_ref_known(v_val_1256_, 1);
v_items_1291_ = lean_ctor_get(v_view_1290_, 1);
lean_inc_ref(v_items_1291_);
lean_dec_ref(v_view_1290_);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_array_get_size(v_items_1291_);
v___x_1294_ = lean_nat_dec_lt(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_dec_ref(v_items_1291_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_nat_dec_le(v___x_1293_, v___x_1293_);
if (v___x_1295_ == 0)
{
if (v___x_1294_ == 0)
{
lean_dec_ref(v_items_1291_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1293_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1291_, v___x_1296_, v___x_1297_, v_b_1242_);
lean_dec_ref(v_items_1291_);
v___y_1244_ = v___x_1298_;
goto v___jp_1243_;
}
}
else
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = lean_usize_of_nat(v___x_1293_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1291_, v___x_1299_, v___x_1300_, v_b_1242_);
lean_dec_ref(v_items_1291_);
v___y_1244_ = v___x_1301_;
goto v___jp_1243_;
}
}
}
default: 
{
lean_dec(v_val_1256_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
}
}
else
{
lean_dec(v___x_1255_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
}
else
{
return v_b_1242_;
}
v___jp_1243_:
{
size_t v___x_1245_; size_t v___x_1246_; 
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_i_1240_, v___x_1245_);
v_i_1240_ = v___x_1246_;
v_b_1242_ = v___y_1244_;
goto _start;
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = lean_unsigned_to_nat(1u);
v___x_1251_ = lean_nat_add(v___y_1249_, v___x_1250_);
lean_dec(v___y_1249_);
v___x_1252_ = lean_nat_dec_le(v_b_1242_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec(v___x_1251_);
v___y_1244_ = v_b_1242_;
goto v___jp_1243_;
}
else
{
lean_dec(v_b_1242_);
v___y_1244_ = v___x_1251_;
goto v___jp_1243_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1239_ = stack[0].m_obj;
size_t v_i_1240_ = stack[1].m_num;
size_t v_stop_1241_ = stack[2].m_num;
lean_object* v_b_1242_ = stack[3].m_obj;
lean_object* v_res_1302_;
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_as_1239_, v_i_1240_, v_stop_1241_, v_b_1242_);
stack->m_obj
 = v_res_1302_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object* v_blks_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_array_get_size(v_blks_1303_);
v___x_1306_ = lean_nat_dec_lt(v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
return v___x_1304_;
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_le(v___x_1305_, v___x_1305_);
if (v___x_1307_ == 0)
{
if (v___x_1306_ == 0)
{
return v___x_1304_;
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1305_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1303_, v___x_1308_, v___x_1309_, v___x_1304_);
return v___x_1310_;
}
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1305_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1303_, v___x_1311_, v___x_1312_, v___x_1304_);
return v___x_1313_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object* v_as_1314_, size_t v_i_1315_, size_t v_stop_1316_, lean_object* v_b_1317_){
_start:
{
lean_object* v___y_1319_; uint8_t v___x_1323_; 
v___x_1323_ = lean_usize_dec_eq(v_i_1315_, v_stop_1316_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v_contents_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1324_ = lean_array_uget_borrowed(v_as_1314_, v_i_1315_);
v_contents_1325_ = lean_ctor_get(v___x_1324_, 2);
v___x_1326_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1325_);
v___x_1327_ = lean_nat_dec_le(v_b_1317_, v___x_1326_);
if (v___x_1327_ == 0)
{
lean_dec(v___x_1326_);
v___y_1319_ = v_b_1317_;
goto v___jp_1318_;
}
else
{
lean_dec(v_b_1317_);
v___y_1319_ = v___x_1326_;
goto v___jp_1318_;
}
}
else
{
return v_b_1317_;
}
v___jp_1318_:
{
size_t v___x_1320_; size_t v___x_1321_; 
v___x_1320_ = ((size_t)1ULL);
v___x_1321_ = lean_usize_add(v_i_1315_, v___x_1320_);
v_i_1315_ = v___x_1321_;
v_b_1317_ = v___y_1319_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1314_ = stack[0].m_obj;
size_t v_i_1315_ = stack[1].m_num;
size_t v_stop_1316_ = stack[2].m_num;
lean_object* v_b_1317_ = stack[3].m_obj;
lean_object* v_res_1328_;
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_as_1314_, v_i_1315_, v_stop_1316_, v_b_1317_);
stack->m_obj
 = v_res_1328_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object* v_as_1329_, lean_object* v_i_1330_, lean_object* v_stop_1331_, lean_object* v_b_1332_){
_start:
{
size_t v_i_boxed_1333_; size_t v_stop_boxed_1334_; lean_object* v_res_1335_; 
v_i_boxed_1333_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_stop_boxed_1334_ = lean_unbox_usize(v_stop_1331_);
lean_dec(v_stop_1331_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_as_1329_, v_i_boxed_1333_, v_stop_boxed_1334_, v_b_1332_);
lean_dec_ref(v_as_1329_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object* v_as_1336_, lean_object* v_i_1337_, lean_object* v_stop_1338_, lean_object* v_b_1339_){
_start:
{
size_t v_i_boxed_1340_; size_t v_stop_boxed_1341_; lean_object* v_res_1342_; 
v_i_boxed_1340_ = lean_unbox_usize(v_i_1337_);
lean_dec(v_i_1337_);
v_stop_boxed_1341_ = lean_unbox_usize(v_stop_1338_);
lean_dec(v_stop_1338_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_as_1336_, v_i_boxed_1340_, v_stop_boxed_1341_, v_b_1339_);
lean_dec_ref(v_as_1336_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object* v_as_1343_, lean_object* v_i_1344_, lean_object* v_stop_1345_, lean_object* v_b_1346_){
_start:
{
size_t v_i_boxed_1347_; size_t v_stop_boxed_1348_; lean_object* v_res_1349_; 
v_i_boxed_1347_ = lean_unbox_usize(v_i_1344_);
lean_dec(v_i_1344_);
v_stop_boxed_1348_ = lean_unbox_usize(v_stop_1345_);
lean_dec(v_stop_1345_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_as_1343_, v_i_boxed_1347_, v_stop_boxed_1348_, v_b_1346_);
lean_dec_ref(v_as_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object* v_blks_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1350_);
lean_dec_ref(v_blks_1350_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object* v_as_1352_, lean_object* v_i_1353_, lean_object* v_stop_1354_, lean_object* v_b_1355_){
_start:
{
size_t v_i_boxed_1356_; size_t v_stop_boxed_1357_; lean_object* v_res_1358_; 
v_i_boxed_1356_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_stop_boxed_1357_ = lean_unbox_usize(v_stop_1354_);
lean_dec(v_stop_1354_);
v_res_1358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_as_1352_, v_i_boxed_1356_, v_stop_boxed_1357_, v_b_1355_);
lean_dec_ref(v_as_1352_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object* v_blks_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = lean_unsigned_to_nat(3u);
v___x_1361_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1359_);
v___x_1362_ = lean_nat_dec_le(v___x_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
lean_dec(v___x_1361_);
return v___x_1360_;
}
else
{
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object* v_blks_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_blks_1363_);
lean_dec_ref(v_blks_1363_);
return v_res_1364_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object* v_inl_1365_){
_start:
{
lean_object* v___x_1366_; 
lean_inc(v_inl_1365_);
v___x_1366_ = l_Lean_Doc_LinebreakView_of(v_inl_1365_);
if (lean_obj_tag(v___x_1366_) == 1)
{
uint8_t v___x_1367_; 
lean_dec_ref_known(v___x_1366_, 1);
lean_dec(v_inl_1365_);
v___x_1367_ = 1;
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; 
lean_dec(v___x_1366_);
v___x_1368_ = l_Lean_Doc_TextView_of(v_inl_1365_);
if (lean_obj_tag(v___x_1368_) == 1)
{
lean_object* v_val_1369_; uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v_decide_1377_; 
v_val_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = 1;
v___x_1371_ = l_Lean_Doc_TextView_getVersoText(v_val_1369_);
lean_dec(v_val_1369_);
v___x_1372_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v___x_1370_, v___x_1371_);
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_string_utf8_byte_size(v___x_1372_);
v___x_1375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1372_);
lean_ctor_set(v___x_1375_, 1, v___x_1373_);
lean_ctor_set(v___x_1375_, 2, v___x_1374_);
v___x_1376_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1375_, v___x_1373_);
lean_dec_ref_known(v___x_1375_, 3);
v_decide_1377_ = lean_nat_dec_eq(v___x_1376_, v___x_1374_);
lean_dec(v___x_1376_);
return v_decide_1377_;
}
else
{
uint8_t v___x_1378_; 
lean_dec(v___x_1368_);
v___x_1378_ = 0;
return v___x_1378_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank_0interp(lean_interpreter_value* stack)
{
lean_object* v_inl_1365_ = stack[0].m_obj;
uint8_t v_res_1379_;
v_res_1379_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v_inl_1365_);
stack->m_num = v_res_1379_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object* v_inl_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v_inl_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object* v_stx_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Doc_BlockView_of(v_stx_1383_);
if (lean_obj_tag(v___x_1384_) == 1)
{
lean_object* v_val_1385_; 
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1384_, 1);
switch(lean_obj_tag(v_val_1385_))
{
case 8:
{
uint8_t v___x_1386_; 
lean_dec_ref_known(v_val_1385_, 1);
v___x_1386_ = 1;
return v___x_1386_;
}
case 9:
{
uint8_t v___x_1387_; 
lean_dec_ref_known(v_val_1385_, 1);
v___x_1387_ = 1;
return v___x_1387_;
}
case 10:
{
uint8_t v___x_1388_; 
lean_dec_ref_known(v_val_1385_, 1);
v___x_1388_ = 1;
return v___x_1388_;
}
case 11:
{
uint8_t v___x_1389_; 
lean_dec_ref_known(v_val_1385_, 1);
v___x_1389_ = 1;
return v___x_1389_;
}
default: 
{
uint8_t v___x_1390_; 
lean_dec(v_val_1385_);
v___x_1390_ = 0;
return v___x_1390_;
}
}
}
else
{
uint8_t v___x_1391_; 
lean_dec(v___x_1384_);
v___x_1391_ = 0;
return v___x_1391_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1383_ = stack[0].m_obj;
uint8_t v_res_1392_;
v_res_1392_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v_stx_1383_);
stack->m_num = v_res_1392_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object* v_stx_1393_){
_start:
{
uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_res_1394_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v_stx_1393_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object* v_inl_1396_){
_start:
{
lean_object* v___x_1397_; 
lean_inc(v_inl_1396_);
v___x_1397_ = l_Lean_Doc_LinebreakView_of(v_inl_1396_);
if (lean_obj_tag(v___x_1397_) == 1)
{
uint8_t v___x_1398_; 
lean_dec_ref_known(v___x_1397_, 1);
lean_dec(v_inl_1396_);
v___x_1398_ = 1;
return v___x_1398_;
}
else
{
lean_object* v___x_1399_; 
lean_dec(v___x_1397_);
v___x_1399_ = l_Lean_Doc_TextView_of(v_inl_1396_);
if (lean_obj_tag(v___x_1399_) == 1)
{
lean_object* v_val_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v_decide_1406_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___x_1401_ = l_Lean_Doc_TextView_getVersoTextSource(v_val_1400_);
lean_dec(v_val_1400_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_string_utf8_byte_size(v___x_1401_);
v___x_1404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1401_);
lean_ctor_set(v___x_1404_, 1, v___x_1402_);
lean_ctor_set(v___x_1404_, 2, v___x_1403_);
v___x_1405_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1404_, v___x_1402_);
lean_dec_ref_known(v___x_1404_, 3);
v_decide_1406_ = lean_nat_dec_eq(v___x_1405_, v___x_1403_);
lean_dec(v___x_1405_);
return v_decide_1406_;
}
else
{
uint8_t v___x_1407_; 
lean_dec(v___x_1399_);
v___x_1407_ = 0;
return v___x_1407_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline_0interp(lean_interpreter_value* stack)
{
lean_object* v_inl_1396_ = stack[0].m_obj;
uint8_t v_res_1408_;
v_res_1408_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v_inl_1396_);
stack->m_num = v_res_1408_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object* v_inl_1409_){
_start:
{
uint8_t v_res_1410_; lean_object* v_r_1411_; 
v_res_1410_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v_inl_1409_);
v_r_1411_ = lean_box(v_res_1410_);
return v_r_1411_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object* v_as_1412_, size_t v_i_1413_, size_t v_stop_1414_){
_start:
{
uint8_t v___x_1415_; 
v___x_1415_ = lean_usize_dec_eq(v_i_1413_, v_stop_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; uint8_t v___x_1417_; 
v___x_1416_ = lean_array_uget_borrowed(v_as_1412_, v_i_1413_);
lean_inc(v___x_1416_);
v___x_1417_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1416_);
if (v___x_1417_ == 0)
{
uint8_t v___x_1418_; 
v___x_1418_ = 1;
return v___x_1418_;
}
else
{
size_t v___x_1419_; size_t v___x_1420_; 
v___x_1419_ = ((size_t)1ULL);
v___x_1420_ = lean_usize_add(v_i_1413_, v___x_1419_);
v_i_1413_ = v___x_1420_;
goto _start;
}
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = 0;
return v___x_1422_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1412_ = stack[0].m_obj;
size_t v_i_1413_ = stack[1].m_num;
size_t v_stop_1414_ = stack[2].m_num;
uint8_t v_res_1423_;
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_as_1412_, v_i_1413_, v_stop_1414_);
stack->m_num = v_res_1423_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object* v_as_1424_, lean_object* v_i_1425_, lean_object* v_stop_1426_){
_start:
{
size_t v_i_boxed_1427_; size_t v_stop_boxed_1428_; uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_i_boxed_1427_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_stop_boxed_1428_ = lean_unbox_usize(v_stop_1426_);
lean_dec(v_stop_1426_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_as_1424_, v_i_boxed_1427_, v_stop_boxed_1428_);
lean_dec_ref(v_as_1424_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object* v_stx_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Doc_ParaView_of(v_stx_1431_);
if (lean_obj_tag(v___x_1432_) == 1)
{
lean_object* v_val_1433_; lean_object* v_content_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v_content_1434_ = lean_ctor_get(v_val_1433_, 1);
lean_inc_ref(v_content_1434_);
lean_dec(v_val_1433_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_array_get_size(v_content_1434_);
v___x_1437_ = lean_nat_dec_lt(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; 
lean_dec_ref(v_content_1434_);
v___x_1438_ = 1;
return v___x_1438_;
}
else
{
if (v___x_1437_ == 0)
{
lean_dec_ref(v_content_1434_);
return v___x_1437_;
}
else
{
size_t v___x_1439_; size_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = lean_usize_of_nat(v___x_1436_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_content_1434_, v___x_1439_, v___x_1440_);
lean_dec_ref(v_content_1434_);
if (v___x_1441_ == 0)
{
return v___x_1437_;
}
else
{
uint8_t v___x_1442_; 
v___x_1442_ = 0;
return v___x_1442_;
}
}
}
}
else
{
uint8_t v___x_1443_; 
lean_dec(v___x_1432_);
v___x_1443_ = 0;
return v___x_1443_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1431_ = stack[0].m_obj;
uint8_t v_res_1444_;
v_res_1444_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_stx_1431_);
stack->m_num = v_res_1444_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object* v_stx_1445_){
_start:
{
uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_res_1446_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_stx_1445_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object* v_stx_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_Doc_LinebreakView_of(v_stx_1448_);
if (lean_obj_tag(v___x_1449_) == 1)
{
uint8_t v___x_1450_; 
lean_dec_ref_known(v___x_1449_, 1);
v___x_1450_ = 1;
return v___x_1450_;
}
else
{
uint8_t v___x_1451_; 
lean_dec(v___x_1449_);
v___x_1451_ = 0;
return v___x_1451_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_1448_ = stack[0].m_obj;
uint8_t v_res_1452_;
v_res_1452_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v_stx_1448_);
stack->m_num = v_res_1452_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object* v_stx_1453_){
_start:
{
uint8_t v_res_1454_; lean_object* v_r_1455_; 
v_res_1454_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v_stx_1453_);
v_r_1455_ = lean_box(v_res_1454_);
return v_r_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object* v_inls_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1457_ = lean_array_get_size(v_inls_1456_);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_dec_eq(v___x_1457_, v___x_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; lean_object* v_inl_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v_inl_1462_ = lean_array_fget_borrowed(v_inls_1456_, v___x_1461_);
lean_inc(v_inl_1462_);
v___x_1463_ = l_Lean_Doc_InlineView_of(v_inl_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_box(0);
return v___x_1464_;
}
else
{
lean_object* v_val_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1488_; 
v_val_1465_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1467_ = v___x_1463_;
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_val_1465_);
lean_dec(v___x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1488_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
switch(lean_obj_tag(v_val_1465_))
{
case 1:
{
lean_object* v___x_1470_; 
lean_dec_ref_known(v_val_1465_, 1);
lean_inc(v_inl_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_inl_1462_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_inl_1462_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
case 2:
{
lean_object* v___x_1473_; 
lean_dec_ref_known(v_val_1465_, 1);
lean_inc(v_inl_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_inl_1462_);
v___x_1473_ = v___x_1467_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_inl_1462_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
case 3:
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v_val_1465_, 1);
lean_inc(v_inl_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_inl_1462_);
v___x_1476_ = v___x_1467_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_inl_1462_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
case 4:
{
lean_object* v___x_1479_; 
lean_dec_ref_known(v_val_1465_, 1);
lean_inc(v_inl_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_inl_1462_);
v___x_1479_ = v___x_1467_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_inl_1462_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
case 6:
{
lean_object* v___x_1482_; 
lean_dec_ref_known(v_val_1465_, 1);
lean_inc(v_inl_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_inl_1462_);
v___x_1482_ = v___x_1467_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_inl_1462_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
case 9:
{
lean_object* v___x_1485_; 
lean_dec_ref_known(v_val_1465_, 1);
lean_inc(v_inl_1462_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_inl_1462_);
v___x_1485_ = v___x_1467_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_inl_1462_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
default: 
{
lean_object* v___x_1487_; 
lean_del_object(v___x_1467_);
lean_dec(v_val_1465_);
v___x_1487_ = lean_box(0);
return v___x_1487_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object* v_inls_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_inls_1489_);
lean_dec_ref(v_inls_1489_);
return v_res_1490_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = 41;
v___x_1492_ = lean_box_uint32(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = 93;
v___x_1496_ = lean_box_uint32(v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
v___x_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object* v_a_1499_){
_start:
{
if (lean_obj_tag(v_a_1499_) == 0)
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0);
return v___x_1500_;
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_a_1502_);
lean_dec_ref(v_a_1502_);
return v_res_1503_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = 95;
v___x_1505_ = lean_box_uint32(v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
v___x_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = 42;
v___x_1509_ = lean_box_uint32(v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
v___x_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = 96;
v___x_1513_ = lean_box_uint32(v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object* v_inl_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Doc_InlineView_of(v_inl_1516_);
if (lean_obj_tag(v___x_1517_) == 1)
{
lean_object* v_val_1518_; 
v_val_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v___x_1517_, 1);
switch(lean_obj_tag(v_val_1518_))
{
case 1:
{
lean_object* v___x_1519_; 
lean_dec_ref_known(v_val_1518_, 1);
v___x_1519_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1519_;
}
case 2:
{
lean_object* v___x_1520_; 
lean_dec_ref_known(v_val_1518_, 1);
v___x_1520_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1520_;
}
case 3:
{
lean_object* v___x_1521_; 
lean_dec_ref_known(v_val_1518_, 1);
v___x_1521_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1521_;
}
case 4:
{
lean_object* v___x_1522_; 
lean_dec_ref_known(v_val_1518_, 1);
v___x_1522_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1522_;
}
case 5:
{
lean_object* v_view_1523_; lean_object* v_target_1524_; lean_object* v___x_1525_; 
v_view_1523_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1523_);
lean_dec_ref_known(v_val_1518_, 1);
v_target_1524_ = lean_ctor_get(v_view_1523_, 4);
lean_inc_ref(v_target_1524_);
lean_dec_ref(v_view_1523_);
v___x_1525_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1524_);
lean_dec_ref(v_target_1524_);
return v___x_1525_;
}
case 6:
{
lean_object* v_view_1526_; lean_object* v_target_1527_; lean_object* v___x_1528_; 
v_view_1526_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1526_);
lean_dec_ref_known(v_val_1518_, 1);
v_target_1527_ = lean_ctor_get(v_view_1526_, 4);
lean_inc_ref(v_target_1527_);
lean_dec_ref(v_view_1526_);
v___x_1528_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1527_);
lean_dec_ref(v_target_1527_);
return v___x_1528_;
}
case 7:
{
lean_object* v___x_1529_; 
lean_dec_ref_known(v_val_1518_, 1);
v___x_1529_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1529_;
}
case 9:
{
lean_object* v_view_1530_; lean_object* v_content_1531_; lean_object* v___x_1532_; 
v_view_1530_ = lean_ctor_get(v_val_1518_, 0);
lean_inc_ref(v_view_1530_);
lean_dec_ref_known(v_val_1518_, 1);
v_content_1531_ = lean_ctor_get(v_view_1530_, 6);
lean_inc_ref(v_content_1531_);
lean_dec_ref(v_view_1530_);
v___x_1532_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_1531_);
lean_dec_ref(v_content_1531_);
if (lean_obj_tag(v___x_1532_) == 1)
{
lean_object* v_val_1533_; 
v_val_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v_inl_1516_ = v_val_1533_;
goto _start;
}
else
{
lean_object* v___x_1535_; 
lean_dec(v___x_1532_);
v___x_1535_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1535_;
}
}
default: 
{
lean_object* v___x_1536_; 
lean_dec(v_val_1518_);
v___x_1536_ = lean_box(0);
return v___x_1536_;
}
}
}
else
{
lean_object* v___x_1537_; 
lean_dec(v___x_1517_);
v___x_1537_ = lean_box(0);
return v___x_1537_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = 36;
v___x_1539_ = lean_box_uint32(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object* v_stx_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Doc_InlineView_of(v_stx_1542_);
if (lean_obj_tag(v___x_1543_) == 1)
{
lean_object* v_val_1544_; 
v_val_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_val_1544_);
lean_dec_ref_known(v___x_1543_, 1);
switch(lean_obj_tag(v_val_1544_))
{
case 1:
{
lean_object* v___x_1545_; 
lean_dec_ref_known(v_val_1544_, 1);
v___x_1545_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1545_;
}
case 2:
{
lean_object* v___x_1546_; 
lean_dec_ref_known(v_val_1544_, 1);
v___x_1546_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1546_;
}
case 3:
{
lean_object* v___x_1547_; 
lean_dec_ref_known(v_val_1544_, 1);
v___x_1547_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1547_;
}
case 4:
{
lean_object* v___x_1548_; 
lean_dec_ref_known(v_val_1544_, 1);
v___x_1548_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0);
return v___x_1548_;
}
default: 
{
lean_object* v___x_1549_; 
lean_dec(v_val_1544_);
v___x_1549_ = lean_box(0);
return v___x_1549_;
}
}
}
else
{
lean_object* v___x_1550_; 
lean_dec(v___x_1543_);
v___x_1550_ = lean_box(0);
return v___x_1550_;
}
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object* v_inl_1551_, lean_object* v_next_x3f_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1551_);
if (lean_obj_tag(v___x_1553_) == 1)
{
if (lean_obj_tag(v_next_x3f_1552_) == 0)
{
uint8_t v___x_1554_; 
lean_dec_ref_known(v___x_1553_, 1);
v___x_1554_ = 0;
return v___x_1554_;
}
else
{
lean_object* v_val_1555_; lean_object* v_val_1556_; lean_object* v___x_1557_; 
v_val_1555_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_val_1555_);
lean_dec_ref_known(v___x_1553_, 1);
v_val_1556_ = lean_ctor_get(v_next_x3f_1552_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v_next_x3f_1552_, 1);
v___x_1557_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1556_);
if (lean_obj_tag(v___x_1557_) == 1)
{
lean_object* v_val_1558_; uint32_t v___x_1559_; uint32_t v___x_1560_; uint8_t v___x_1561_; 
v_val_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v___x_1557_, 1);
v___x_1559_ = lean_unbox_uint32(v_val_1555_);
lean_dec(v_val_1555_);
v___x_1560_ = lean_unbox_uint32(v_val_1558_);
lean_dec(v_val_1558_);
v___x_1561_ = lean_uint32_dec_eq(v___x_1559_, v___x_1560_);
return v___x_1561_;
}
else
{
uint8_t v___x_1562_; 
lean_dec(v___x_1557_);
lean_dec(v_val_1555_);
v___x_1562_ = 0;
return v___x_1562_;
}
}
}
else
{
uint8_t v___x_1563_; 
lean_dec(v___x_1553_);
lean_dec(v_next_x3f_1552_);
v___x_1563_ = 0;
return v___x_1563_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto_0interp(lean_interpreter_value* stack)
{
lean_object* v_inl_1551_ = stack[0].m_obj;
lean_object* v_next_x3f_1552_ = stack[1].m_obj;
uint8_t v_res_1564_;
v_res_1564_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_inl_1551_, v_next_x3f_1552_);
stack->m_num = v_res_1564_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object* v_inl_1565_, lean_object* v_next_x3f_1566_){
_start:
{
uint8_t v_res_1567_; lean_object* v_r_1568_; 
v_res_1567_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_inl_1565_, v_next_x3f_1566_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object* v_inl_1569_, lean_object* v_next_x3f_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1569_);
if (lean_obj_tag(v___x_1571_) == 1)
{
lean_object* v_val_1572_; uint32_t v___x_1573_; uint32_t v___x_1574_; uint8_t v___x_1575_; 
v_val_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_val_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1573_ = 96;
v___x_1574_ = lean_unbox_uint32(v_val_1572_);
lean_dec(v_val_1572_);
v___x_1575_ = lean_uint32_dec_eq(v___x_1574_, v___x_1573_);
if (v___x_1575_ == 0)
{
lean_dec(v_next_x3f_1570_);
return v___x_1575_;
}
else
{
if (lean_obj_tag(v_next_x3f_1570_) == 0)
{
uint8_t v___x_1576_; 
v___x_1576_ = 0;
return v___x_1576_;
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1578_; 
v_val_1577_ = lean_ctor_get(v_next_x3f_1570_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v_next_x3f_1570_, 1);
v___x_1578_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1577_);
if (lean_obj_tag(v___x_1578_) == 1)
{
lean_object* v_val_1579_; uint32_t v___x_1580_; uint8_t v___x_1581_; 
v_val_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_val_1579_);
lean_dec_ref_known(v___x_1578_, 1);
v___x_1580_ = lean_unbox_uint32(v_val_1579_);
lean_dec(v_val_1579_);
v___x_1581_ = lean_uint32_dec_eq(v___x_1580_, v___x_1573_);
return v___x_1581_;
}
else
{
uint8_t v___x_1582_; 
lean_dec(v___x_1578_);
v___x_1582_ = 0;
return v___x_1582_;
}
}
}
}
else
{
uint8_t v___x_1583_; 
lean_dec(v___x_1571_);
lean_dec(v_next_x3f_1570_);
v___x_1583_ = 0;
return v___x_1583_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto_0interp(lean_interpreter_value* stack)
{
lean_object* v_inl_1569_ = stack[0].m_obj;
lean_object* v_next_x3f_1570_ = stack[1].m_obj;
uint8_t v_res_1584_;
v_res_1584_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v_inl_1569_, v_next_x3f_1570_);
stack->m_num = v_res_1584_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object* v_inl_1585_, lean_object* v_next_x3f_1586_){
_start:
{
uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_res_1587_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v_inl_1585_, v_next_x3f_1586_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object* v_inls_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = lean_array_get_size(v_inls_1589_);
v___x_1592_ = lean_nat_dec_lt(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
return v___x_1592_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_array_fget_borrowed(v_inls_1589_, v___x_1590_);
lean_inc(v___x_1593_);
v___x_1594_ = l_Lean_Doc_TextView_of(v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 1)
{
lean_object* v_val_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v_val_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1596_ = l_Lean_Doc_TextView_getVersoText(v_val_1595_);
lean_dec(v_val_1595_);
v___x_1597_ = lean_string_utf8_byte_size(v___x_1596_);
v___x_1598_ = lean_unsigned_to_nat(1u);
v___x_1599_ = lean_nat_dec_le(v___x_1598_, v___x_1597_);
if (v___x_1599_ == 0)
{
lean_dec_ref(v___x_1596_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1601_ = lean_string_memcmp(v___x_1596_, v___x_1600_, v___x_1590_, v___x_1590_, v___x_1598_);
lean_dec_ref(v___x_1596_);
return v___x_1601_;
}
}
else
{
uint8_t v___x_1602_; 
lean_dec(v___x_1594_);
v___x_1602_ = 0;
return v___x_1602_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace_0interp(lean_interpreter_value* stack)
{
lean_object* v_inls_1589_ = stack[0].m_obj;
uint8_t v_res_1603_;
v_res_1603_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_inls_1589_);
stack->m_num = v_res_1603_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object* v_inls_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_inls_1604_);
lean_dec_ref(v_inls_1604_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object* v_x_1610_, lean_object* v_a_1611_){
_start:
{
if (lean_obj_tag(v_x_1610_) == 0)
{
lean_object* v_url_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_snd_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_snd_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_url_1612_ = lean_ctor_get(v_x_1610_, 2);
v___x_1613_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_1614_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1613_, v_a_1611_);
v_snd_1615_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_snd_1615_);
lean_dec_ref(v___x_1614_);
v___x_1616_ = l_Lean_TSyntax_getVersoLinkUrl(v_url_1612_);
v___x_1617_ = l_Lean_Doc_escapeVersoLinkUrl(v___x_1616_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1617_, v_snd_1615_);
lean_dec_ref(v___x_1617_);
v_snd_1619_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_snd_1619_);
lean_dec_ref(v___x_1618_);
v___x_1620_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_1621_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1620_, v_snd_1619_);
return v___x_1621_;
}
else
{
lean_object* v_name_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_snd_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_snd_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v_name_1622_ = lean_ctor_get(v_x_1610_, 2);
v___x_1623_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_1624_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1623_, v_a_1611_);
v_snd_1625_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_snd_1625_);
lean_dec_ref(v___x_1624_);
v___x_1626_ = l_Lean_TSyntax_getVersoRefName(v_name_1622_);
v___x_1627_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1626_, v_snd_1625_);
lean_dec_ref(v___x_1626_);
v_snd_1628_ = lean_ctor_get(v___x_1627_, 1);
lean_inc(v_snd_1628_);
lean_dec_ref(v___x_1627_);
v___x_1629_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_1630_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1629_, v_snd_1628_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object* v_x_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1631_, v_a_1632_);
lean_dec_ref(v_x_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object* v_x_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1634_, v_a_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object* v_x_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(v_x_1638_, v_a_1639_, v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_x_1638_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object* v_s_1642_, lean_object* v_pos_1643_){
_start:
{
lean_object* v_str_1644_; lean_object* v_startInclusive_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v_decide_1649_; 
v_str_1644_ = lean_ctor_get(v_s_1642_, 0);
v_startInclusive_1645_ = lean_ctor_get(v_s_1642_, 1);
v___x_1646_ = lean_nat_add(v_startInclusive_1645_, v_pos_1643_);
v___x_1647_ = lean_nat_sub(v___x_1646_, v_startInclusive_1645_);
v___x_1648_ = lean_unsigned_to_nat(0u);
v_decide_1649_ = lean_nat_dec_eq(v___x_1647_, v___x_1648_);
if (v_decide_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint32_t v___x_1655_; uint32_t v___x_1656_; uint8_t v___x_1657_; 
lean_inc(v_startInclusive_1645_);
lean_inc_ref(v_str_1644_);
v___x_1650_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1650_, 0, v_str_1644_);
lean_ctor_set(v___x_1650_, 1, v_startInclusive_1645_);
lean_ctor_set(v___x_1650_, 2, v___x_1646_);
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_nat_sub(v___x_1647_, v___x_1651_);
lean_dec(v___x_1647_);
v___x_1653_ = l_String_Slice_posLE(v___x_1650_, v___x_1652_);
lean_dec_ref_known(v___x_1650_, 3);
v___x_1654_ = lean_nat_add(v_startInclusive_1645_, v___x_1653_);
v___x_1655_ = lean_string_utf8_get_fast(v_str_1644_, v___x_1654_);
lean_dec(v___x_1654_);
v___x_1656_ = 32;
v___x_1657_ = lean_uint32_dec_eq(v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_dec(v___x_1653_);
return v_pos_1643_;
}
else
{
lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = lean_nat_add(v___x_1653_, v___x_1651_);
v___x_1659_ = lean_nat_dec_le(v___x_1658_, v_pos_1643_);
lean_dec(v___x_1658_);
if (v___x_1659_ == 0)
{
lean_dec(v___x_1653_);
return v_pos_1643_;
}
else
{
lean_dec(v_pos_1643_);
v_pos_1643_ = v___x_1653_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1647_);
lean_dec(v___x_1646_);
return v_pos_1643_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object* v_s_1661_, lean_object* v_pos_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v_s_1661_, v_pos_1662_);
lean_dec_ref(v_s_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object* v_marker_1664_, lean_object* v_contents_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v_alone_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1667_ = lean_unsigned_to_nat(0u);
v___x_1668_ = lean_string_utf8_byte_size(v_marker_1664_);
lean_inc_ref(v_marker_1664_);
v___x_1669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1669_, 0, v_marker_1664_);
lean_ctor_set(v___x_1669_, 1, v___x_1667_);
lean_ctor_set(v___x_1669_, 2, v___x_1668_);
v___x_1670_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v___x_1669_, v___x_1668_);
lean_dec_ref_known(v___x_1669_, 3);
v_alone_1671_ = lean_string_utf8_extract_fast(v_marker_1664_, v___x_1667_, v___x_1670_);
lean_dec(v___x_1670_);
v___x_1672_ = lean_array_get_size(v_contents_1665_);
v___x_1673_ = lean_nat_dec_lt(v___x_1667_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref(v_marker_1664_);
v___x_1674_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_alone_1671_, v_a_1666_);
lean_dec_ref(v_alone_1671_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_array_fget_borrowed(v_contents_1665_, v___x_1667_);
lean_inc(v___x_1675_);
v___x_1676_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref(v_alone_1671_);
v___x_1677_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_marker_1664_, v_a_1666_);
lean_dec_ref(v_marker_1664_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec_ref(v_marker_1664_);
v___x_1678_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_1679_ = lean_string_append(v_alone_1671_, v___x_1678_);
v___x_1680_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1679_, v_a_1666_);
lean_dec_ref(v___x_1679_);
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object* v_marker_1681_, lean_object* v_contents_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1681_, v_contents_1682_, v_a_1683_);
lean_dec_ref(v_contents_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object* v_marker_1685_, lean_object* v_contents_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1685_, v_contents_1686_, v_a_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object* v_marker_1690_, lean_object* v_contents_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(v_marker_1690_, v_contents_1691_, v_a_1692_, v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_contents_1691_);
return v_res_1694_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object* v_as_1695_, size_t v_i_1696_, size_t v_stop_1697_, lean_object* v_b_1698_){
_start:
{
lean_object* v___y_1700_; uint8_t v___x_1704_; 
v___x_1704_ = lean_usize_dec_eq(v_i_1696_, v_stop_1697_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = lean_array_uget_borrowed(v_as_1695_, v_i_1696_);
lean_inc(v___x_1705_);
v___x_1706_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
lean_inc(v___x_1705_);
v___x_1707_ = lean_array_push(v_b_1698_, v___x_1705_);
v___y_1700_ = v___x_1707_;
goto v___jp_1699_;
}
else
{
v___y_1700_ = v_b_1698_;
goto v___jp_1699_;
}
}
else
{
return v_b_1698_;
}
v___jp_1699_:
{
size_t v___x_1701_; size_t v___x_1702_; 
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1696_, v___x_1701_);
v_i_1696_ = v___x_1702_;
v_b_1698_ = v___y_1700_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1695_ = stack[0].m_obj;
size_t v_i_1696_ = stack[1].m_num;
size_t v_stop_1697_ = stack[2].m_num;
lean_object* v_b_1698_ = stack[3].m_obj;
lean_object* v_res_1708_;
v_res_1708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_as_1695_, v_i_1696_, v_stop_1697_, v_b_1698_);
stack->m_obj
 = v_res_1708_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object* v_as_1709_, lean_object* v_i_1710_, lean_object* v_stop_1711_, lean_object* v_b_1712_){
_start:
{
size_t v_i_boxed_1713_; size_t v_stop_boxed_1714_; lean_object* v_res_1715_; 
v_i_boxed_1713_ = lean_unbox_usize(v_i_1710_);
lean_dec(v_i_1710_);
v_stop_boxed_1714_ = lean_unbox_usize(v_stop_1711_);
lean_dec(v_stop_1711_);
v_res_1715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_as_1709_, v_i_boxed_1713_, v_stop_boxed_1714_, v_b_1712_);
lean_dec_ref(v_as_1709_);
return v_res_1715_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t v_sz_1716_, size_t v_i_1717_, lean_object* v_bs_1718_){
_start:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1717_, v_sz_1716_);
if (v___x_1719_ == 0)
{
return v_bs_1718_;
}
else
{
lean_object* v_v_1720_; lean_object* v___x_1721_; lean_object* v_bs_x27_1722_; size_t v___x_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v_v_1720_ = lean_array_uget(v_bs_1718_, v_i_1717_);
v___x_1721_ = lean_unsigned_to_nat(0u);
v_bs_x27_1722_ = lean_array_uset(v_bs_1718_, v_i_1717_, v___x_1721_);
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = lean_usize_add(v_i_1717_, v___x_1723_);
v___x_1725_ = lean_array_uset(v_bs_x27_1722_, v_i_1717_, v_v_1720_);
v_i_1717_ = v___x_1724_;
v_bs_1718_ = v___x_1725_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1716_ = stack[0].m_num;
size_t v_i_1717_ = stack[1].m_num;
lean_object* v_bs_1718_ = stack[2].m_obj;
lean_object* v_res_1727_;
v_res_1727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_1716_, v_i_1717_, v_bs_1718_);
stack->m_obj
 = v_res_1727_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_sz_1728_, lean_object* v_i_1729_, lean_object* v_bs_1730_){
_start:
{
size_t v_sz_boxed_1731_; size_t v_i_boxed_1732_; lean_object* v_res_1733_; 
v_sz_boxed_1731_ = lean_unbox_usize(v_sz_1728_);
lean_dec(v_sz_1728_);
v_i_boxed_1732_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_res_1733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_boxed_1731_, v_i_boxed_1732_, v_bs_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
lean_object* v_zero_1736_; uint8_t v_isZero_1737_; 
v_zero_1736_ = lean_unsigned_to_nat(0u);
v_isZero_1737_ = lean_nat_dec_eq(v_x_1734_, v_zero_1736_);
if (v_isZero_1737_ == 1)
{
lean_dec(v_x_1734_);
return v_x_1735_;
}
else
{
uint32_t v___x_1738_; lean_object* v_one_1739_; lean_object* v_n_1740_; lean_object* v___x_1741_; 
v___x_1738_ = 35;
v_one_1739_ = lean_unsigned_to_nat(1u);
v_n_1740_ = lean_nat_sub(v_x_1734_, v_one_1739_);
lean_dec(v_x_1734_);
v___x_1741_ = lean_string_push(v_x_1735_, v___x_1738_);
v_x_1734_ = v_n_1740_;
v_x_1735_ = v___x_1741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
lean_object* v_zero_1745_; uint8_t v_isZero_1746_; 
v_zero_1745_ = lean_unsigned_to_nat(0u);
v_isZero_1746_ = lean_nat_dec_eq(v_x_1743_, v_zero_1745_);
if (v_isZero_1746_ == 1)
{
lean_dec(v_x_1743_);
return v_x_1744_;
}
else
{
uint32_t v___x_1747_; lean_object* v_one_1748_; lean_object* v_n_1749_; lean_object* v___x_1750_; 
v___x_1747_ = 58;
v_one_1748_ = lean_unsigned_to_nat(1u);
v_n_1749_ = lean_nat_sub(v_x_1743_, v_one_1748_);
lean_dec(v_x_1743_);
v___x_1750_ = lean_string_push(v_x_1744_, v___x_1747_);
v_x_1743_ = v_n_1749_;
v_x_1744_ = v___x_1750_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t v_char_1752_, lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v_zero_1755_; uint8_t v_isZero_1756_; 
v_zero_1755_ = lean_unsigned_to_nat(0u);
v_isZero_1756_ = lean_nat_dec_eq(v_x_1753_, v_zero_1755_);
if (v_isZero_1756_ == 1)
{
lean_dec(v_x_1753_);
return v_x_1754_;
}
else
{
lean_object* v_one_1757_; lean_object* v_n_1758_; lean_object* v___x_1759_; 
v_one_1757_ = lean_unsigned_to_nat(1u);
v_n_1758_ = lean_nat_sub(v_x_1753_, v_one_1757_);
lean_dec(v_x_1753_);
v___x_1759_ = lean_string_push(v_x_1754_, v_char_1752_);
v_x_1753_ = v_n_1758_;
v_x_1754_ = v___x_1759_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15_0interp(lean_interpreter_value* stack)
{
uint32_t v_char_1752_ = stack[0].m_num;
lean_object* v_x_1753_ = stack[1].m_obj;
lean_object* v_x_1754_ = stack[2].m_obj;
lean_object* v_res_1761_;
v_res_1761_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_1752_, v_x_1753_, v_x_1754_);
stack->m_obj
 = v_res_1761_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object* v_char_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint32_t v_char_boxed_1765_; lean_object* v_res_1766_; 
v_char_boxed_1765_ = lean_unbox_uint32(v_char_1762_);
lean_dec(v_char_1762_);
v_res_1766_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_boxed_1765_, v_x_1763_, v_x_1764_);
return v_res_1766_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
if (lean_obj_tag(v_x_1767_) == 0)
{
if (lean_obj_tag(v_x_1768_) == 0)
{
uint8_t v___x_1769_; 
v___x_1769_ = 1;
return v___x_1769_;
}
else
{
uint8_t v___x_1770_; 
v___x_1770_ = 0;
return v___x_1770_;
}
}
else
{
if (lean_obj_tag(v_x_1768_) == 0)
{
uint8_t v___x_1771_; 
v___x_1771_ = 0;
return v___x_1771_;
}
else
{
lean_object* v_val_1772_; lean_object* v_val_1773_; uint32_t v___x_1774_; uint32_t v___x_1775_; uint8_t v___x_1776_; 
v_val_1772_ = lean_ctor_get(v_x_1767_, 0);
v_val_1773_ = lean_ctor_get(v_x_1768_, 0);
v___x_1774_ = lean_unbox_uint32(v_val_1772_);
v___x_1775_ = lean_unbox_uint32(v_val_1773_);
v___x_1776_ = lean_uint32_dec_eq(v___x_1774_, v___x_1775_);
return v___x_1776_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1767_ = stack[0].m_obj;
lean_object* v_x_1768_ = stack[1].m_obj;
uint8_t v_res_1777_;
v_res_1777_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v_x_1767_, v_x_1768_);
stack->m_num = v_res_1777_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object* v_x_1778_, lean_object* v_x_1779_){
_start:
{
uint8_t v_res_1780_; lean_object* v_r_1781_; 
v_res_1780_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v_x_1778_, v_x_1779_);
lean_dec(v_x_1779_);
lean_dec(v_x_1778_);
v_r_1781_ = lean_box(v_res_1780_);
return v_r_1781_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg(){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0));
return v___x_1785_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1786_;
v_res_1786_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
stack->m_obj
 = v_res_1786_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___boxed(lean_object* v___dummy_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v_res_1788_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t v___x_1789_, lean_object* v_as_1790_, size_t v_i_1791_, size_t v_stop_1792_){
_start:
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_usize_dec_eq(v_i_1791_, v_stop_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1794_ = 1;
v___x_1795_ = lean_array_uget_borrowed(v_as_1790_, v_i_1791_);
lean_inc(v___x_1795_);
v___x_1796_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1795_);
if (v___x_1796_ == 0)
{
return v___x_1794_;
}
else
{
if (v___x_1789_ == 0)
{
size_t v___x_1797_; size_t v___x_1798_; 
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1791_, v___x_1797_);
v_i_1791_ = v___x_1798_;
goto _start;
}
else
{
return v___x_1794_;
}
}
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = 0;
return v___x_1800_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1789_ = stack[0].m_num;
lean_object* v_as_1790_ = stack[1].m_obj;
size_t v_i_1791_ = stack[2].m_num;
size_t v_stop_1792_ = stack[3].m_num;
uint8_t v_res_1801_;
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_1789_, v_as_1790_, v_i_1791_, v_stop_1792_);
stack->m_num = v_res_1801_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v___x_1802_, lean_object* v_as_1803_, lean_object* v_i_1804_, lean_object* v_stop_1805_){
_start:
{
uint8_t v___x_61923__boxed_1806_; size_t v_i_boxed_1807_; size_t v_stop_boxed_1808_; uint8_t v_res_1809_; lean_object* v_r_1810_; 
v___x_61923__boxed_1806_ = lean_unbox(v___x_1802_);
v_i_boxed_1807_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_stop_boxed_1808_ = lean_unbox_usize(v_stop_1805_);
lean_dec(v_stop_1805_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_61923__boxed_1806_, v_as_1803_, v_i_boxed_1807_, v_stop_boxed_1808_);
lean_dec_ref(v_as_1803_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t v___x_1811_, uint8_t v___x_1812_, lean_object* v_as_1813_, size_t v_i_1814_, size_t v_stop_1815_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_usize_dec_eq(v_i_1814_, v_stop_1815_);
if (v___x_1816_ == 0)
{
uint8_t v___x_1817_; uint8_t v___y_1819_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1817_ = 1;
v___x_1823_ = lean_array_uget_borrowed(v_as_1813_, v_i_1814_);
lean_inc(v___x_1823_);
v___x_1824_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v___x_1823_);
if (v___x_1824_ == 0)
{
v___y_1819_ = v___x_1811_;
goto v___jp_1818_;
}
else
{
v___y_1819_ = v___x_1812_;
goto v___jp_1818_;
}
v___jp_1818_:
{
if (v___y_1819_ == 0)
{
size_t v___x_1820_; size_t v___x_1821_; 
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1814_, v___x_1820_);
v_i_1814_ = v___x_1821_;
goto _start;
}
else
{
return v___x_1817_;
}
}
}
else
{
uint8_t v___x_1825_; 
v___x_1825_ = 0;
return v___x_1825_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1811_ = stack[0].m_num;
uint8_t v___x_1812_ = stack[1].m_num;
lean_object* v_as_1813_ = stack[2].m_obj;
size_t v_i_1814_ = stack[3].m_num;
size_t v_stop_1815_ = stack[4].m_num;
uint8_t v_res_1826_;
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_1811_, v___x_1812_, v_as_1813_, v_i_1814_, v_stop_1815_);
stack->m_num = v_res_1826_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v_as_1829_, lean_object* v_i_1830_, lean_object* v_stop_1831_){
_start:
{
uint8_t v___x_61952__boxed_1832_; uint8_t v___x_61953__boxed_1833_; size_t v_i_boxed_1834_; size_t v_stop_boxed_1835_; uint8_t v_res_1836_; lean_object* v_r_1837_; 
v___x_61952__boxed_1832_ = lean_unbox(v___x_1827_);
v___x_61953__boxed_1833_ = lean_unbox(v___x_1828_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1830_);
lean_dec(v_i_1830_);
v_stop_boxed_1835_ = lean_unbox_usize(v_stop_1831_);
lean_dec(v_stop_1831_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_61952__boxed_1832_, v___x_61953__boxed_1833_, v_as_1829_, v_i_boxed_1834_, v_stop_boxed_1835_);
lean_dec_ref(v_as_1829_);
v_r_1837_ = lean_box(v_res_1836_);
return v_r_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___x_1840_, lean_object* v___x_1841_, lean_object* v_a_1842_, lean_object* v_b_1843_){
_start:
{
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_object* v_currPos_1844_; lean_object* v_searcher_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1878_; 
v_currPos_1844_ = lean_ctor_get(v_a_1842_, 0);
v_searcher_1845_ = lean_ctor_get(v_a_1842_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1847_ = v_a_1842_;
v_isShared_1848_ = v_isSharedCheck_1878_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_searcher_1845_);
lean_inc(v_currPos_1844_);
lean_dec(v_a_1842_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1878_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v_it_1851_; lean_object* v_startInclusive_1852_; lean_object* v_endExclusive_1853_; uint8_t v_decide_1859_; 
v___x_1849_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_decide_1859_ = lean_nat_dec_eq(v_searcher_1845_, v___x_1841_);
if (v_decide_1859_ == 0)
{
uint32_t v___x_1860_; uint32_t v___x_1861_; uint8_t v___x_1862_; 
v___x_1860_ = 10;
v___x_1861_ = lean_string_utf8_get_fast(v___y_1839_, v_searcher_1845_);
v___x_1862_ = lean_uint32_dec_eq(v___x_1861_, v___x_1860_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1863_ = lean_string_utf8_next_fast(v___y_1839_, v_searcher_1845_);
lean_dec(v_searcher_1845_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1863_);
v___x_1865_ = v___x_1847_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_currPos_1844_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v_a_1842_ = v___x_1865_;
goto _start;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v_slice_1871_; lean_object* v_nextIt_1873_; 
v___x_1868_ = lean_string_utf8_next_fast(v___y_1839_, v_searcher_1845_);
v___x_1869_ = lean_nat_sub(v___x_1868_, v_searcher_1845_);
v___x_1870_ = lean_nat_add(v_searcher_1845_, v___x_1869_);
lean_dec(v___x_1869_);
v_slice_1871_ = l_String_Slice_subslice_x21(v___x_1840_, v_currPos_1844_, v_searcher_1845_);
lean_inc(v___x_1870_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1870_);
lean_ctor_set(v___x_1847_, 0, v___x_1870_);
v_nextIt_1873_ = v___x_1847_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1870_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1870_);
v_nextIt_1873_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v_startInclusive_1874_; lean_object* v_endExclusive_1875_; 
v_startInclusive_1874_ = lean_ctor_get(v_slice_1871_, 0);
lean_inc(v_startInclusive_1874_);
v_endExclusive_1875_ = lean_ctor_get(v_slice_1871_, 1);
lean_inc(v_endExclusive_1875_);
lean_dec_ref(v_slice_1871_);
v_it_1851_ = v_nextIt_1873_;
v_startInclusive_1852_ = v_startInclusive_1874_;
v_endExclusive_1853_ = v_endExclusive_1875_;
goto v___jp_1850_;
}
}
}
else
{
lean_object* v___x_1877_; 
lean_del_object(v___x_1847_);
lean_dec(v_searcher_1845_);
v___x_1877_ = lean_box(1);
lean_inc(v___x_1841_);
v_it_1851_ = v___x_1877_;
v_startInclusive_1852_ = v_currPos_1844_;
v_endExclusive_1853_ = v___x_1841_;
goto v___jp_1850_;
}
v___jp_1850_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_inc(v___y_1838_);
v___x_1854_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v___y_1838_, v___x_1849_);
v___x_1855_ = lean_string_utf8_extract_fast(v___y_1839_, v_startInclusive_1852_, v_endExclusive_1853_);
lean_dec(v_endExclusive_1853_);
lean_dec(v_startInclusive_1852_);
v___x_1856_ = lean_string_append(v___x_1854_, v___x_1855_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = lean_array_push(v_b_1843_, v___x_1856_);
v_a_1842_ = v_it_1851_;
v_b_1843_ = v___x_1857_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1841_);
return v_b_1843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___x_1881_, lean_object* v___x_1882_, lean_object* v_a_1883_, lean_object* v_b_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_1879_, v___y_1880_, v___x_1881_, v___x_1882_, v_a_1883_, v_b_1884_);
lean_dec_ref(v___x_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object* v___x_1886_, lean_object* v___x_1887_, lean_object* v_____r_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1891_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v___x_1886_);
v___x_1892_ = lean_box(v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1887_);
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___y_1890_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object* v___x_1896_, lean_object* v___x_1897_, lean_object* v_____r_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1896_, v___x_1897_, v_____r_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1899_);
return v_res_1901_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0(void){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object* v_upperBound_1909_, lean_object* v___y_1910_, lean_object* v_a_1911_, lean_object* v_b_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___y_1916_; uint8_t v___x_1933_; 
v___x_1933_ = lean_nat_dec_lt(v_a_1911_, v_upperBound_1909_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_dec(v_a_1911_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_b_1912_);
lean_ctor_set(v___x_1934_, 1, v___y_1914_);
return v___x_1934_;
}
else
{
lean_object* v_fst_1935_; lean_object* v_snd_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___y_1940_; lean_object* v___y_1944_; uint8_t v___y_1945_; lean_object* v___y_1960_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v_fst_1935_ = lean_ctor_get(v_b_1912_, 0);
lean_inc(v_fst_1935_);
v_snd_1936_ = lean_ctor_get(v_b_1912_, 1);
lean_inc(v_snd_1936_);
lean_dec_ref(v_b_1912_);
v___x_1937_ = lean_array_fget_borrowed(v___y_1910_, v_a_1911_);
lean_inc(v___x_1937_);
v___x_1938_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_snd_1936_, v___x_1937_);
lean_dec(v_snd_1936_);
v___x_1964_ = lean_unsigned_to_nat(1u);
v___x_1965_ = lean_nat_add(v_a_1911_, v___x_1964_);
v___x_1966_ = lean_array_get_size(v___y_1910_);
v___x_1967_ = lean_nat_dec_lt(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v___y_1960_ = v___x_1968_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_array_fget_borrowed(v___y_1910_, v___x_1965_);
lean_dec(v___x_1965_);
lean_inc(v___x_1969_);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
v___y_1960_ = v___x_1970_;
goto v___jp_1959_;
}
v___jp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = lean_box(0);
lean_inc(v___x_1937_);
v___x_1942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1937_, v___x_1938_, v___x_1941_, v___y_1913_, v___y_1940_);
v___y_1916_ = v___x_1942_;
goto v___jp_1915_;
}
v___jp_1943_:
{
uint8_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_unbox(v_fst_1935_);
lean_dec(v_fst_1935_);
lean_inc(v___y_1944_);
lean_inc(v___x_1937_);
v___x_1947_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1937_, v___y_1944_, v___x_1946_, v___y_1945_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___y_1944_) == 1)
{
lean_object* v_snd_1948_; lean_object* v___x_1949_; 
v_snd_1948_ = lean_ctor_get(v___x_1947_, 1);
lean_inc(v_snd_1948_);
lean_dec_ref(v___x_1947_);
lean_inc(v___x_1937_);
v___x_1949_ = l_Lean_Doc_RoleView_of(v___x_1937_);
if (lean_obj_tag(v___x_1949_) == 1)
{
lean_dec_ref_known(v___x_1949_, 1);
lean_dec_ref_known(v___y_1944_, 1);
v___y_1940_ = v_snd_1948_;
goto v___jp_1939_;
}
else
{
uint8_t v___x_1950_; 
lean_dec(v___x_1949_);
lean_inc(v___x_1937_);
v___x_1950_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v___x_1937_, v___y_1944_);
if (v___x_1950_ == 0)
{
v___y_1940_ = v_snd_1948_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_fst_1953_; lean_object* v_snd_1954_; lean_object* v___x_1955_; 
v___x_1951_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1952_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1951_, v_snd_1948_);
v_fst_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_fst_1953_);
v_snd_1954_ = lean_ctor_get(v___x_1952_, 1);
lean_inc(v_snd_1954_);
lean_dec_ref(v___x_1952_);
lean_inc(v___x_1937_);
v___x_1955_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1937_, v___x_1938_, v_fst_1953_, v___y_1913_, v_snd_1954_);
v___y_1916_ = v___x_1955_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v_snd_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec(v___y_1944_);
v_snd_1956_ = lean_ctor_get(v___x_1947_, 1);
lean_inc(v_snd_1956_);
lean_dec_ref(v___x_1947_);
v___x_1957_ = lean_box(0);
lean_inc(v___x_1937_);
v___x_1958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1937_, v___x_1938_, v___x_1957_, v___y_1913_, v_snd_1956_);
v___y_1916_ = v___x_1958_;
goto v___jp_1915_;
}
}
v___jp_1959_:
{
if (lean_obj_tag(v___x_1938_) == 0)
{
uint8_t v___x_1961_; 
v___x_1961_ = 0;
v___y_1944_ = v___y_1960_;
v___y_1945_ = v___x_1961_;
goto v___jp_1943_;
}
else
{
lean_object* v_val_1962_; uint8_t v_alternate_1963_; 
v_val_1962_ = lean_ctor_get(v___x_1938_, 0);
v_alternate_1963_ = lean_ctor_get_uint8(v_val_1962_, 1);
v___y_1944_ = v___y_1960_;
v___y_1945_ = v_alternate_1963_;
goto v___jp_1943_;
}
}
}
v___jp_1915_:
{
lean_object* v_fst_1917_; 
v_fst_1917_ = lean_ctor_get(v___y_1916_, 0);
lean_inc(v_fst_1917_);
if (lean_obj_tag(v_fst_1917_) == 0)
{
lean_object* v_snd_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_a_1911_);
v_snd_1918_ = lean_ctor_get(v___y_1916_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___y_1916_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___y_1916_, 0);
lean_dec(v_unused_1927_);
v___x_1920_ = v___y_1916_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_snd_1918_);
lean_dec(v___y_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_a_1922_; lean_object* v___x_1924_; 
v_a_1922_ = lean_ctor_get(v_fst_1917_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v_fst_1917_, 1);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_a_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1922_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_snd_1918_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
else
{
lean_object* v_snd_1928_; lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_snd_1928_ = lean_ctor_get(v___y_1916_, 1);
lean_inc(v_snd_1928_);
lean_dec_ref(v___y_1916_);
v_a_1929_ = lean_ctor_get(v_fst_1917_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v_fst_1917_, 1);
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_nat_add(v_a_1911_, v___x_1930_);
lean_dec(v_a_1911_);
v_a_1911_ = v___x_1931_;
v_b_1912_ = v_a_1929_;
v___y_1914_ = v_snd_1928_;
goto _start;
}
}
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object* v_stxs_1973_, uint8_t v_lineStart_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1977_; lean_object* v___y_1979_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_array_get_size(v_stxs_1973_);
v___x_1996_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0));
v___x_1997_ = lean_nat_dec_lt(v___x_1977_, v___x_1995_);
if (v___x_1997_ == 0)
{
v___y_1979_ = v___x_1996_;
goto v___jp_1978_;
}
else
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_nat_dec_le(v___x_1995_, v___x_1995_);
if (v___x_1998_ == 0)
{
if (v___x_1997_ == 0)
{
v___y_1979_ = v___x_1996_;
goto v___jp_1978_;
}
else
{
size_t v___x_1999_; size_t v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = lean_usize_of_nat(v___x_1995_);
v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1973_, v___x_1999_, v___x_2000_, v___x_1996_);
v___y_1979_ = v___x_2001_;
goto v___jp_1978_;
}
}
else
{
size_t v___x_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = lean_usize_of_nat(v___x_1995_);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1973_, v___x_2002_, v___x_2003_, v___x_1996_);
v___y_1979_ = v___x_2004_;
goto v___jp_1978_;
}
}
v___jp_1978_:
{
lean_object* v___x_1980_; lean_object* v_prev_x3f_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v_snd_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1993_; 
v___x_1980_ = lean_array_get_size(v___y_1979_);
v_prev_x3f_1981_ = lean_box(0);
v___x_1982_ = lean_box(v_lineStart_1974_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v_prev_x3f_1981_);
v___x_1984_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v___x_1980_, v___y_1979_, v___x_1977_, v___x_1983_, v_a_1975_, v_a_1976_);
lean_dec_ref(v___y_1979_);
v_snd_1985_ = lean_ctor_get(v___x_1984_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v___x_1984_, 0);
lean_dec(v_unused_1994_);
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_snd_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1993_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_box(0);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 0, v___x_1989_);
v___x_1991_ = v___x_1987_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_snd_1985_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_0interp(lean_interpreter_value* stack)
{
lean_object* v_stxs_1973_ = stack[0].m_obj;
uint8_t v_lineStart_1974_ = stack[1].m_num;
lean_object* v_a_1975_ = stack[2].m_obj;
lean_object* v_a_1976_ = stack[3].m_obj;
lean_object* v_res_2005_;
v_res_2005_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v_stxs_1973_, v_lineStart_1974_, v_a_1975_, v_a_1976_);
stack->m_obj
 = v_res_2005_;
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t v_char_2006_, lean_object* v_inls_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v_delim_2012_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___x_2023_; lean_object* v_snd_2024_; lean_object* v___y_2026_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2010_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2011_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_2006_, v_inls_2007_);
v_delim_2012_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_2006_, v___x_2011_, v___x_2010_);
v___x_2023_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_2012_, v_a_2009_);
v_snd_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2023_);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_array_get_size(v_inls_2007_);
v___x_2035_ = lean_nat_dec_lt(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_box(0);
v___y_2026_ = v___x_2036_;
goto v___jp_2025_;
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_array_fget_borrowed(v_inls_2007_, v___x_2033_);
lean_inc(v___x_2037_);
v___x_2038_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v___x_2037_);
v___y_2026_ = v___x_2038_;
goto v___jp_2025_;
}
v___jp_2013_:
{
size_t v_sz_2016_; size_t v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; lean_object* v_snd_2021_; lean_object* v___x_2022_; 
v_sz_2016_ = lean_array_size(v_inls_2007_);
v___x_2017_ = ((size_t)0ULL);
v___x_2018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2016_, v___x_2017_, v_inls_2007_);
v___x_2019_ = 0;
v___x_2020_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2018_, v___x_2019_, v___y_2014_, v___y_2015_);
lean_dec_ref(v___x_2018_);
v_snd_2021_ = lean_ctor_get(v___x_2020_, 1);
lean_inc(v_snd_2021_);
lean_dec_ref(v___x_2020_);
v___x_2022_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_2012_, v_snd_2021_);
lean_dec_ref(v_delim_2012_);
return v___x_2022_;
}
v___jp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2027_ = lean_box_uint32(v_char_2006_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
v___x_2029_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v___y_2026_, v___x_2028_);
lean_dec_ref_known(v___x_2028_, 1);
lean_dec(v___y_2026_);
if (v___x_2029_ == 0)
{
v___y_2014_ = v_a_2008_;
v___y_2015_ = v_snd_2024_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_snd_2032_; 
v___x_2030_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_2031_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2030_, v_snd_2024_);
v_snd_2032_ = lean_ctor_get(v___x_2031_, 1);
lean_inc(v_snd_2032_);
lean_dec_ref(v___x_2031_);
v___y_2014_ = v_a_2008_;
v___y_2015_ = v_snd_2032_;
goto v___jp_2013_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_0interp(lean_interpreter_value* stack)
{
uint32_t v_char_2006_ = stack[0].m_num;
lean_object* v_inls_2007_ = stack[1].m_obj;
lean_object* v_a_2008_ = stack[2].m_obj;
lean_object* v_a_2009_ = stack[3].m_obj;
lean_object* v_res_2039_;
v_res_2039_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v_char_2006_, v_inls_2007_, v_a_2008_, v_a_2009_);
stack->m_obj
 = v_res_2039_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v___y_2046_, uint8_t v___x_2047_, lean_object* v_as_2048_, size_t v_sz_2049_, size_t v_i_2050_, lean_object* v_b_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_usize_dec_lt(v_i_2050_, v_sz_2049_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec_ref(v___y_2046_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_b_2051_);
lean_ctor_set(v___x_2055_, 1, v___y_2053_);
return v___x_2055_;
}
else
{
lean_object* v___x_2056_; lean_object* v_snd_2057_; lean_object* v_a_2058_; lean_object* v_contents_2059_; lean_object* v___x_2060_; lean_object* v_snd_2061_; size_t v_sz_2062_; size_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_snd_2068_; lean_object* v___x_2069_; lean_object* v_snd_2070_; lean_object* v___x_2071_; size_t v___x_2072_; size_t v___x_2073_; 
v___x_2056_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2052_, v___y_2053_);
v_snd_2057_ = lean_ctor_get(v___x_2056_, 1);
lean_inc(v_snd_2057_);
lean_dec_ref(v___x_2056_);
v_a_2058_ = lean_array_uget_borrowed(v_as_2048_, v_i_2050_);
v_contents_2059_ = lean_ctor_get(v_a_2058_, 2);
lean_inc_ref(v___y_2046_);
v___x_2060_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2046_, v_contents_2059_, v_snd_2057_);
v_snd_2061_ = lean_ctor_get(v___x_2060_, 1);
lean_inc(v_snd_2061_);
lean_dec_ref(v___x_2060_);
v_sz_2062_ = lean_array_size(v_contents_2059_);
v___x_2063_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2059_);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2062_, v___x_2063_, v_contents_2059_);
v___x_2065_ = lean_string_length(v___y_2046_);
v___x_2066_ = lean_nat_add(v___y_2052_, v___x_2065_);
v___x_2067_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2064_, v___x_2047_, v___x_2066_, v_snd_2061_);
lean_dec(v___x_2066_);
lean_dec_ref(v___x_2064_);
v_snd_2068_ = lean_ctor_get(v___x_2067_, 1);
lean_inc(v_snd_2068_);
lean_dec_ref(v___x_2067_);
v___x_2069_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2068_);
v_snd_2070_ = lean_ctor_get(v___x_2069_, 1);
lean_inc(v_snd_2070_);
lean_dec_ref(v___x_2069_);
v___x_2071_ = lean_box(0);
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_add(v_i_2050_, v___x_2072_);
v_i_2050_ = v___x_2073_;
v_b_2051_ = v___x_2071_;
v___y_2053_ = v_snd_2070_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2046_ = stack[0].m_obj;
uint8_t v___x_2047_ = stack[1].m_num;
lean_object* v_as_2048_ = stack[2].m_obj;
size_t v_sz_2049_ = stack[3].m_num;
size_t v_i_2050_ = stack[4].m_num;
lean_object* v_b_2051_ = stack[5].m_obj;
lean_object* v___y_2052_ = stack[6].m_obj;
lean_object* v___y_2053_ = stack[7].m_obj;
lean_object* v_res_2075_;
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2046_, v___x_2047_, v_as_2048_, v_sz_2049_, v_i_2050_, v_b_2051_, v___y_2052_, v___y_2053_);
stack->m_obj
 = v_res_2075_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t v___x_2079_, uint8_t v_alternate_2080_, lean_object* v_as_2081_, size_t v_sz_2082_, size_t v_i_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_lt(v_i_2083_, v_sz_2082_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_b_2084_);
lean_ctor_set(v___x_2088_, 1, v___y_2086_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; lean_object* v_snd_2090_; lean_object* v_a_2091_; lean_object* v___y_2093_; 
v___x_2089_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2085_, v___y_2086_);
v_snd_2090_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_snd_2090_);
lean_dec_ref(v___x_2089_);
v_a_2091_ = lean_array_uget_borrowed(v_as_2081_, v_i_2083_);
if (v_alternate_2080_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_inc(v_b_2084_);
v___x_2111_ = l_Nat_reprFast(v_b_2084_);
v___x_2112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0));
v___x_2113_ = lean_string_append(v___x_2111_, v___x_2112_);
v___y_2093_ = v___x_2113_;
goto v___jp_2092_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_inc(v_b_2084_);
v___x_2114_ = l_Nat_reprFast(v_b_2084_);
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1));
v___x_2116_ = lean_string_append(v___x_2114_, v___x_2115_);
v___y_2093_ = v___x_2116_;
goto v___jp_2092_;
}
v___jp_2092_:
{
lean_object* v_contents_2094_; lean_object* v___x_2095_; lean_object* v_snd_2096_; size_t v_sz_2097_; size_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v_snd_2103_; lean_object* v___x_2104_; lean_object* v_snd_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; 
v_contents_2094_ = lean_ctor_get(v_a_2091_, 2);
lean_inc_ref(v___y_2093_);
v___x_2095_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2093_, v_contents_2094_, v_snd_2090_);
v_snd_2096_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_snd_2096_);
lean_dec_ref(v___x_2095_);
v_sz_2097_ = lean_array_size(v_contents_2094_);
v___x_2098_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2094_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2097_, v___x_2098_, v_contents_2094_);
v___x_2100_ = lean_string_length(v___y_2093_);
lean_dec_ref(v___y_2093_);
v___x_2101_ = lean_nat_add(v___y_2085_, v___x_2100_);
v___x_2102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2099_, v___x_2079_, v___x_2101_, v_snd_2096_);
lean_dec(v___x_2101_);
lean_dec_ref(v___x_2099_);
v_snd_2103_ = lean_ctor_get(v___x_2102_, 1);
lean_inc(v_snd_2103_);
lean_dec_ref(v___x_2102_);
v___x_2104_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2103_);
v_snd_2105_ = lean_ctor_get(v___x_2104_, 1);
lean_inc(v_snd_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = lean_nat_add(v_b_2084_, v___x_2106_);
lean_dec(v_b_2084_);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_add(v_i_2083_, v___x_2108_);
v_i_2083_ = v___x_2109_;
v_b_2084_ = v___x_2107_;
v___y_2086_ = v_snd_2105_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2079_ = stack[0].m_num;
uint8_t v_alternate_2080_ = stack[1].m_num;
lean_object* v_as_2081_ = stack[2].m_obj;
size_t v_sz_2082_ = stack[3].m_num;
size_t v_i_2083_ = stack[4].m_num;
lean_object* v_b_2084_ = stack[5].m_obj;
lean_object* v___y_2085_ = stack[6].m_obj;
lean_object* v___y_2086_ = stack[7].m_obj;
lean_object* v_res_2117_;
v_res_2117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_2079_, v_alternate_2080_, v_as_2081_, v_sz_2082_, v_i_2083_, v_b_2084_, v___y_2085_, v___y_2086_);
stack->m_obj
 = v_res_2117_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t v___x_2118_, lean_object* v_as_2119_, size_t v_sz_2120_, size_t v_i_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v___x_2125_; 
v___x_2125_ = lean_usize_dec_lt(v_i_2121_, v_sz_2120_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_b_2122_);
lean_ctor_set(v___x_2126_, 1, v___y_2124_);
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; lean_object* v_snd_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v_snd_2131_; lean_object* v_a_2132_; lean_object* v_term_2133_; lean_object* v___x_2134_; lean_object* v___y_2136_; lean_object* v___y_2137_; uint8_t v___x_2158_; 
v___x_2127_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2123_, v___y_2124_);
v_snd_2128_ = lean_ctor_get(v___x_2127_, 1);
lean_inc(v_snd_2128_);
lean_dec_ref(v___x_2127_);
v___x_2129_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_2130_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2129_, v_snd_2128_);
v_snd_2131_ = lean_ctor_get(v___x_2130_, 1);
lean_inc(v_snd_2131_);
lean_dec_ref(v___x_2130_);
v_a_2132_ = lean_array_uget_borrowed(v_as_2119_, v_i_2121_);
v_term_2133_ = lean_ctor_get(v_a_2132_, 2);
v___x_2134_ = lean_box(0);
v___x_2158_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_term_2133_);
if (v___x_2158_ == 0)
{
v___y_2136_ = v___y_2123_;
v___y_2137_ = v_snd_2131_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_snd_2161_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2159_, v_snd_2131_);
v_snd_2161_ = lean_ctor_get(v___x_2160_, 1);
lean_inc(v_snd_2161_);
lean_dec_ref(v___x_2160_);
v___y_2136_ = v___y_2123_;
v___y_2137_ = v_snd_2161_;
goto v___jp_2135_;
}
v___jp_2135_:
{
lean_object* v_term_2138_; lean_object* v_desc_2139_; size_t v_sz_2140_; size_t v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v_snd_2144_; lean_object* v___x_2145_; lean_object* v_snd_2146_; size_t v_sz_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_snd_2152_; lean_object* v___x_2153_; lean_object* v_snd_2154_; size_t v___x_2155_; size_t v___x_2156_; 
v_term_2138_ = lean_ctor_get(v_a_2132_, 2);
v_desc_2139_ = lean_ctor_get(v_a_2132_, 3);
v_sz_2140_ = lean_array_size(v_term_2138_);
v___x_2141_ = ((size_t)0ULL);
lean_inc_ref(v_term_2138_);
v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2140_, v___x_2141_, v_term_2138_);
v___x_2143_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2142_, v___x_2118_, v___y_2136_, v___y_2137_);
lean_dec_ref(v___x_2142_);
v_snd_2144_ = lean_ctor_get(v___x_2143_, 1);
lean_inc(v_snd_2144_);
lean_dec_ref(v___x_2143_);
v___x_2145_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2144_);
v_snd_2146_ = lean_ctor_get(v___x_2145_, 1);
lean_inc(v_snd_2146_);
lean_dec_ref(v___x_2145_);
v_sz_2147_ = lean_array_size(v_desc_2139_);
lean_inc_ref(v_desc_2139_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2147_, v___x_2141_, v_desc_2139_);
v___x_2149_ = lean_unsigned_to_nat(2u);
v___x_2150_ = lean_nat_add(v___y_2136_, v___x_2149_);
v___x_2151_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2148_, v___x_2118_, v___x_2150_, v_snd_2146_);
lean_dec(v___x_2150_);
lean_dec_ref(v___x_2148_);
v_snd_2152_ = lean_ctor_get(v___x_2151_, 1);
lean_inc(v_snd_2152_);
lean_dec_ref(v___x_2151_);
v___x_2153_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2152_);
v_snd_2154_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_snd_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = ((size_t)1ULL);
v___x_2156_ = lean_usize_add(v_i_2121_, v___x_2155_);
v_i_2121_ = v___x_2156_;
v_b_2122_ = v___x_2134_;
v___y_2124_ = v_snd_2154_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2118_ = stack[0].m_num;
lean_object* v_as_2119_ = stack[1].m_obj;
size_t v_sz_2120_ = stack[2].m_num;
size_t v_i_2121_ = stack[3].m_num;
lean_object* v_b_2122_ = stack[4].m_obj;
lean_object* v___y_2123_ = stack[5].m_obj;
lean_object* v___y_2124_ = stack[6].m_obj;
lean_object* v_res_2162_;
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_2118_, v_as_2119_, v_sz_2120_, v_i_2121_, v_b_2122_, v___y_2123_, v___y_2124_);
stack->m_obj
 = v_res_2162_;
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_2166_, lean_object* v_next_x3f_2167_, uint8_t v_atLineStart_2168_, uint8_t v_alternate_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___y_2173_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
lean_inc(v_stx_2166_);
v___x_2203_ = l_Lean_Syntax_getKind(v_stx_2166_);
v___x_2204_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3));
v___x_2205_ = lean_name_eq(v___x_2203_, v___x_2204_);
lean_dec(v___x_2203_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; 
lean_inc(v_stx_2166_);
v___x_2206_ = l_Lean_Doc_ArgValView_of(v_stx_2166_);
if (lean_obj_tag(v___x_2206_) == 1)
{
lean_object* v_val_2207_; 
lean_dec(v_next_x3f_2167_);
lean_dec(v_stx_2166_);
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2206_, 1);
if (lean_obj_tag(v_val_2207_) == 1)
{
lean_object* v_x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_x_2208_ = lean_ctor_get(v_val_2207_, 0);
lean_inc(v_x_2208_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2209_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_x_2208_);
v___x_2210_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2209_, v_a_2171_);
lean_dec_ref(v___x_2209_);
return v___x_2210_;
}
else
{
lean_object* v_lit_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_lit_2211_ = lean_ctor_get(v_val_2207_, 0);
lean_inc(v_lit_2211_);
lean_dec(v_val_2207_);
v___x_2212_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_lit_2211_);
v___x_2213_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2212_, v_a_2171_);
lean_dec_ref(v___x_2212_);
return v___x_2213_;
}
}
else
{
lean_object* v___x_2214_; 
lean_dec(v___x_2206_);
lean_inc(v_stx_2166_);
v___x_2214_ = l_Lean_Doc_ArgView_of(v_stx_2166_);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_object* v_val_2215_; 
lean_dec(v_next_x3f_2167_);
lean_dec(v_stx_2166_);
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v___x_2214_, 1);
switch(lean_obj_tag(v_val_2215_))
{
case 0:
{
lean_object* v_val_2216_; lean_object* v___x_2217_; 
v_val_2216_ = lean_ctor_get(v_val_2215_, 1);
lean_inc(v_val_2216_);
lean_dec_ref_known(v_val_2215_, 2);
v___x_2217_ = lean_box(0);
v_stx_2166_ = v_val_2216_;
v_next_x3f_2167_ = v___x_2217_;
v_atLineStart_2168_ = v___x_2205_;
v_alternate_2169_ = v___x_2205_;
goto _start;
}
case 1:
{
lean_object* v_name_2219_; lean_object* v_val_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_snd_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v_snd_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_snd_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_name_2219_ = lean_ctor_get(v_val_2215_, 2);
lean_inc(v_name_2219_);
v_val_2220_ = lean_ctor_get(v_val_2215_, 4);
lean_inc(v_val_2220_);
lean_dec_ref_known(v_val_2215_, 5);
v___x_2221_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_2222_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2221_, v_a_2171_);
v_snd_2223_ = lean_ctor_get(v___x_2222_, 1);
lean_inc(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2219_);
v___x_2225_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2224_, v_snd_2223_);
lean_dec_ref(v___x_2224_);
v_snd_2226_ = lean_ctor_get(v___x_2225_, 1);
lean_inc(v_snd_2226_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
v___x_2228_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2227_, v_snd_2226_);
v_snd_2229_ = lean_ctor_get(v___x_2228_, 1);
lean_inc(v_snd_2229_);
lean_dec_ref(v___x_2228_);
v___x_2230_ = lean_box(0);
v___x_2231_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_val_2220_, v___x_2230_, v___x_2205_, v___x_2205_, v_a_2170_, v_snd_2229_);
v_snd_2232_ = lean_ctor_get(v___x_2231_, 1);
lean_inc(v_snd_2232_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_2234_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2233_, v_snd_2232_);
return v___x_2234_;
}
default: 
{
lean_object* v_name_2235_; uint8_t v_isOn_2236_; lean_object* v___y_2238_; 
v_name_2235_ = lean_ctor_get(v_val_2215_, 2);
lean_inc(v_name_2235_);
v_isOn_2236_ = lean_ctor_get_uint8(v_val_2215_, sizeof(void*)*3);
lean_dec_ref_known(v_val_2215_, 3);
if (v_isOn_2236_ == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___y_2238_ = v___x_2243_;
goto v___jp_2237_;
}
else
{
lean_object* v___x_2244_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___y_2238_ = v___x_2244_;
goto v___jp_2237_;
}
v___jp_2237_:
{
lean_object* v___x_2239_; lean_object* v_snd_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2239_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2238_, v_a_2171_);
v_snd_2240_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_snd_2240_);
lean_dec_ref(v___x_2239_);
v___x_2241_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2235_);
v___x_2242_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2241_, v_snd_2240_);
lean_dec_ref(v___x_2241_);
return v___x_2242_;
}
}
}
}
else
{
lean_object* v___x_2245_; 
lean_dec(v___x_2214_);
lean_inc(v_stx_2166_);
v___x_2245_ = l_Lean_Doc_LinkTargetView_of(v_stx_2166_);
if (lean_obj_tag(v___x_2245_) == 1)
{
lean_object* v_val_2246_; lean_object* v___x_2247_; 
lean_dec(v_next_x3f_2167_);
lean_dec(v_stx_2166_);
v_val_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v___x_2247_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_val_2246_, v_a_2171_);
lean_dec(v_val_2246_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; 
lean_dec(v___x_2245_);
lean_inc(v_stx_2166_);
v___x_2248_ = l_Lean_Doc_InlineView_of(v_stx_2166_);
if (lean_obj_tag(v___x_2248_) == 1)
{
lean_object* v_val_2249_; 
lean_dec(v_stx_2166_);
v_val_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2248_, 1);
switch(lean_obj_tag(v_val_2249_))
{
case 0:
{
lean_object* v_view_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v_next_x3f_2167_);
v_view_2250_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2250_);
lean_dec_ref_known(v_val_2249_, 1);
v___x_2251_ = l_Lean_Doc_TextView_getVersoText(v_view_2250_);
lean_dec_ref(v_view_2250_);
v___x_2252_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_2168_, v___x_2251_);
v___x_2253_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2252_, v_a_2171_);
lean_dec_ref(v___x_2252_);
return v___x_2253_;
}
case 1:
{
lean_object* v_view_2254_; lean_object* v_content_2255_; uint32_t v___x_2256_; lean_object* v___x_2257_; 
lean_dec(v_next_x3f_2167_);
v_view_2254_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2254_);
lean_dec_ref_known(v_val_2249_, 1);
v_content_2255_ = lean_ctor_get(v_view_2254_, 2);
lean_inc_ref(v_content_2255_);
lean_dec_ref(v_view_2254_);
v___x_2256_ = 95;
v___x_2257_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2256_, v_content_2255_, v_a_2170_, v_a_2171_);
return v___x_2257_;
}
case 2:
{
lean_object* v_view_2258_; lean_object* v_content_2259_; uint32_t v___x_2260_; lean_object* v___x_2261_; 
lean_dec(v_next_x3f_2167_);
v_view_2258_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2258_);
lean_dec_ref_known(v_val_2249_, 1);
v_content_2259_ = lean_ctor_get(v_view_2258_, 2);
lean_inc_ref(v_content_2259_);
lean_dec_ref(v_view_2258_);
v___x_2260_ = 42;
v___x_2261_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2260_, v_content_2259_, v_a_2170_, v_a_2171_);
return v___x_2261_;
}
case 3:
{
lean_object* v_view_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
lean_dec(v_next_x3f_2167_);
v_view_2262_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2262_);
lean_dec_ref_known(v_val_2249_, 1);
v___x_2263_ = l_Lean_Doc_CodeView_getVersoCode(v_view_2262_);
lean_dec_ref(v_view_2262_);
v___x_2264_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2263_);
v___x_2265_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2264_, v_a_2171_);
lean_dec_ref(v___x_2264_);
return v___x_2265_;
}
case 4:
{
lean_object* v_view_2266_; lean_object* v___y_2268_; uint8_t v_mode_2274_; 
lean_dec(v_next_x3f_2167_);
v_view_2266_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2266_);
lean_dec_ref_known(v_val_2249_, 1);
v_mode_2274_ = lean_ctor_get_uint8(v_view_2266_, sizeof(void*)*3);
if (v_mode_2274_ == 0)
{
lean_object* v___x_2275_; 
v___x_2275_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5));
v___y_2268_ = v___x_2275_;
goto v___jp_2267_;
}
else
{
lean_object* v___x_2276_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
v___y_2268_ = v___x_2276_;
goto v___jp_2267_;
}
v___jp_2267_:
{
lean_object* v___x_2269_; lean_object* v_snd_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2269_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2268_, v_a_2171_);
v_snd_2270_ = lean_ctor_get(v___x_2269_, 1);
lean_inc(v_snd_2270_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = l_Lean_Doc_MathView_getVersoCode(v_view_2266_);
lean_dec_ref(v_view_2266_);
v___x_2272_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2271_);
v___x_2273_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2272_, v_snd_2270_);
lean_dec_ref(v___x_2272_);
return v___x_2273_;
}
}
case 5:
{
lean_object* v_view_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v_snd_2280_; lean_object* v_content_2281_; lean_object* v_target_2282_; size_t v_sz_2283_; size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v_snd_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_snd_2290_; lean_object* v___x_2291_; 
lean_dec(v_next_x3f_2167_);
v_view_2277_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2277_);
lean_dec_ref_known(v_val_2249_, 1);
v___x_2278_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2279_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2278_, v_a_2171_);
v_snd_2280_ = lean_ctor_get(v___x_2279_, 1);
lean_inc(v_snd_2280_);
lean_dec_ref(v___x_2279_);
v_content_2281_ = lean_ctor_get(v_view_2277_, 2);
lean_inc_ref(v_content_2281_);
v_target_2282_ = lean_ctor_get(v_view_2277_, 4);
lean_inc_ref(v_target_2282_);
lean_dec_ref(v_view_2277_);
v_sz_2283_ = lean_array_size(v_content_2281_);
v___x_2284_ = ((size_t)0ULL);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2283_, v___x_2284_, v_content_2281_);
v___x_2286_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2285_, v___x_2205_, v_a_2170_, v_snd_2280_);
lean_dec_ref(v___x_2285_);
v_snd_2287_ = lean_ctor_get(v___x_2286_, 1);
lean_inc(v_snd_2287_);
lean_dec_ref(v___x_2286_);
v___x_2288_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2289_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2288_, v_snd_2287_);
v_snd_2290_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_snd_2290_);
lean_dec_ref(v___x_2289_);
v___x_2291_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2282_, v_snd_2290_);
lean_dec_ref(v_target_2282_);
return v___x_2291_;
}
case 6:
{
lean_object* v_view_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_snd_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_snd_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v_snd_2302_; lean_object* v_target_2303_; lean_object* v___x_2304_; 
lean_dec(v_next_x3f_2167_);
v_view_2292_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2292_);
lean_dec_ref_known(v_val_2249_, 1);
v___x_2293_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7));
v___x_2294_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2293_, v_a_2171_);
v_snd_2295_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_snd_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = l_Lean_Doc_ImageView_getAlt(v_view_2292_);
v___x_2297_ = l_Lean_Doc_escapeVersoImageAlt(v___x_2296_);
lean_dec_ref(v___x_2296_);
v___x_2298_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2297_, v_snd_2295_);
lean_dec_ref(v___x_2297_);
v_snd_2299_ = lean_ctor_get(v___x_2298_, 1);
lean_inc(v_snd_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2301_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2300_, v_snd_2299_);
v_snd_2302_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_snd_2302_);
lean_dec_ref(v___x_2301_);
v_target_2303_ = lean_ctor_get(v_view_2292_, 4);
lean_inc_ref(v_target_2303_);
lean_dec_ref(v_view_2292_);
v___x_2304_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2303_, v_snd_2302_);
lean_dec_ref(v_target_2303_);
return v___x_2304_;
}
case 7:
{
lean_object* v_view_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_snd_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_snd_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec(v_next_x3f_2167_);
v_view_2305_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2305_);
lean_dec_ref_known(v_val_2249_, 1);
v___x_2306_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2307_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2306_, v_a_2171_);
v_snd_2308_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_snd_2308_);
lean_dec_ref(v___x_2307_);
v___x_2309_ = l_Lean_Doc_FootnoteView_getName(v_view_2305_);
lean_dec_ref(v_view_2305_);
v___x_2310_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2309_, v_snd_2308_);
lean_dec_ref(v___x_2309_);
v_snd_2311_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2313_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2312_, v_snd_2311_);
return v___x_2313_;
}
case 8:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec_ref_known(v_val_2249_, 1);
lean_dec(v_next_x3f_2167_);
v___x_2314_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2315_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2314_, v_a_2171_);
return v___x_2315_;
}
default: 
{
lean_object* v_view_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v_snd_2319_; lean_object* v_name_2320_; lean_object* v_args_2321_; lean_object* v_content_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_snd_2325_; lean_object* v___x_2326_; size_t v_sz_2327_; size_t v___x_2328_; lean_object* v___x_2329_; lean_object* v_snd_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_snd_2333_; lean_object* v___x_2344_; 
v_view_2316_ = lean_ctor_get(v_val_2249_, 0);
lean_inc_ref(v_view_2316_);
lean_dec_ref_known(v_val_2249_, 1);
v___x_2317_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2318_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2317_, v_a_2171_);
v_snd_2319_ = lean_ctor_get(v___x_2318_, 1);
lean_inc(v_snd_2319_);
lean_dec_ref(v___x_2318_);
v_name_2320_ = lean_ctor_get(v_view_2316_, 2);
lean_inc(v_name_2320_);
v_args_2321_ = lean_ctor_get(v_view_2316_, 3);
lean_inc_ref(v_args_2321_);
v_content_2322_ = lean_ctor_get(v_view_2316_, 6);
lean_inc_ref(v_content_2322_);
lean_dec_ref(v_view_2316_);
v___x_2323_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2320_);
v___x_2324_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2323_, v_snd_2319_);
lean_dec_ref(v___x_2323_);
v_snd_2325_ = lean_ctor_get(v___x_2324_, 1);
lean_inc(v_snd_2325_);
lean_dec_ref(v___x_2324_);
v___x_2326_ = lean_box(0);
v_sz_2327_ = lean_array_size(v_args_2321_);
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2205_, v_args_2321_, v_sz_2327_, v___x_2328_, v___x_2326_, v_a_2170_, v_snd_2325_);
lean_dec_ref(v_args_2321_);
v_snd_2330_ = lean_ctor_get(v___x_2329_, 1);
lean_inc(v_snd_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2332_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2331_, v_snd_2330_);
v_snd_2333_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_snd_2333_);
lean_dec_ref(v___x_2332_);
v___x_2344_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_2322_);
if (lean_obj_tag(v___x_2344_) == 1)
{
lean_object* v_val_2345_; uint8_t v___x_2346_; 
v_val_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_val_2345_, v_next_x3f_2167_);
if (v___x_2346_ == 0)
{
size_t v_sz_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_sz_2347_ = lean_array_size(v_content_2322_);
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2347_, v___x_2328_, v_content_2322_);
v___x_2349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2348_, v___x_2346_, v_a_2170_, v_snd_2333_);
lean_dec_ref(v___x_2348_);
return v___x_2349_;
}
else
{
goto v___jp_2334_;
}
}
else
{
lean_dec(v___x_2344_);
lean_dec(v_next_x3f_2167_);
goto v___jp_2334_;
}
v___jp_2334_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v_snd_2337_; size_t v_sz_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v_snd_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2336_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2335_, v_snd_2333_);
v_snd_2337_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_snd_2337_);
lean_dec_ref(v___x_2336_);
v_sz_2338_ = lean_array_size(v_content_2322_);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2338_, v___x_2328_, v_content_2322_);
v___x_2340_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2339_, v___x_2205_, v_a_2170_, v_snd_2337_);
lean_dec_ref(v___x_2339_);
v_snd_2341_ = lean_ctor_get(v___x_2340_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v___x_2340_);
v___x_2342_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2343_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2342_, v_snd_2341_);
return v___x_2343_;
}
}
}
}
else
{
lean_object* v___x_2350_; 
lean_dec(v___x_2248_);
lean_dec(v_next_x3f_2167_);
lean_inc(v_stx_2166_);
v___x_2350_ = l_Lean_Doc_BlockView_of(v_stx_2166_);
if (lean_obj_tag(v___x_2350_) == 1)
{
lean_object* v_val_2351_; 
v_val_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_val_2351_);
lean_dec_ref_known(v___x_2350_, 1);
switch(lean_obj_tag(v_val_2351_))
{
case 0:
{
lean_object* v_view_2352_; lean_object* v_content_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
lean_dec(v_stx_2166_);
v_view_2352_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2352_);
lean_dec_ref_known(v_val_2351_, 1);
v_content_2353_ = lean_ctor_get(v_view_2352_, 1);
lean_inc_ref(v_content_2353_);
lean_dec_ref(v_view_2352_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_array_get_size(v_content_2353_);
v___x_2356_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_dec_ref(v_content_2353_);
goto v___jp_2200_;
}
else
{
if (v___x_2356_ == 0)
{
lean_dec_ref(v_content_2353_);
goto v___jp_2200_;
}
else
{
size_t v___x_2357_; size_t v___x_2358_; uint8_t v___x_2359_; lean_object* v___y_2361_; lean_object* v___y_2362_; 
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = lean_usize_of_nat(v___x_2355_);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_2205_, v_content_2353_, v___x_2357_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_dec_ref(v_content_2353_);
goto v___jp_2200_;
}
else
{
if (v___x_2205_ == 0)
{
lean_object* v___x_2368_; lean_object* v_snd_2369_; 
v___x_2368_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2369_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_snd_2369_);
lean_dec_ref(v___x_2368_);
if (v___x_2356_ == 0)
{
goto v___jp_2370_;
}
else
{
if (v___x_2356_ == 0)
{
goto v___jp_2370_;
}
else
{
uint8_t v___x_2374_; 
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_2359_, v___x_2205_, v_content_2353_, v___x_2357_, v___x_2358_);
if (v___x_2374_ == 0)
{
goto v___jp_2370_;
}
else
{
v___y_2361_ = v_a_2170_;
v___y_2362_ = v_snd_2369_;
goto v___jp_2360_;
}
}
}
v___jp_2370_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v_snd_2373_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2372_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2371_, v_snd_2369_);
v_snd_2373_ = lean_ctor_get(v___x_2372_, 1);
lean_inc(v_snd_2373_);
lean_dec_ref(v___x_2372_);
v___y_2361_ = v_a_2170_;
v___y_2362_ = v_snd_2373_;
goto v___jp_2360_;
}
}
else
{
lean_dec_ref(v_content_2353_);
goto v___jp_2200_;
}
}
v___jp_2360_:
{
size_t v_sz_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_snd_2366_; lean_object* v___x_2367_; 
v_sz_2363_ = lean_array_size(v_content_2353_);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2363_, v___x_2357_, v_content_2353_);
v___x_2365_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2364_, v___x_2359_, v___y_2361_, v___y_2362_);
lean_dec_ref(v___x_2364_);
v_snd_2366_ = lean_ctor_get(v___x_2365_, 1);
lean_inc(v_snd_2366_);
lean_dec_ref(v___x_2365_);
v___x_2367_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2366_);
return v___x_2367_;
}
}
}
}
case 1:
{
lean_object* v_view_2375_; lean_object* v___y_2377_; 
lean_dec(v_stx_2166_);
v_view_2375_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2375_);
lean_dec_ref_known(v_val_2351_, 1);
if (v_alternate_2169_ == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11));
v___y_2377_ = v___x_2385_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___y_2377_ = v___x_2386_;
goto v___jp_2376_;
}
v___jp_2376_:
{
lean_object* v_items_2378_; lean_object* v___x_2379_; size_t v_sz_2380_; size_t v___x_2381_; lean_object* v___x_2382_; lean_object* v_snd_2383_; lean_object* v___x_2384_; 
v_items_2378_ = lean_ctor_get(v_view_2375_, 1);
lean_inc_ref(v_items_2378_);
lean_dec_ref(v_view_2375_);
v___x_2379_ = lean_box(0);
v_sz_2380_ = lean_array_size(v_items_2378_);
v___x_2381_ = ((size_t)0ULL);
lean_inc_ref(v___y_2377_);
v___x_2382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2377_, v___x_2205_, v_items_2378_, v_sz_2380_, v___x_2381_, v___x_2379_, v_a_2170_, v_a_2171_);
lean_dec_ref(v_items_2378_);
v_snd_2383_ = lean_ctor_get(v___x_2382_, 1);
lean_inc(v_snd_2383_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2383_);
return v___x_2384_;
}
}
case 2:
{
lean_object* v_view_2387_; lean_object* v_start_2388_; lean_object* v_items_2389_; size_t v_sz_2390_; size_t v___x_2391_; lean_object* v___x_2392_; lean_object* v_snd_2393_; lean_object* v___x_2394_; 
lean_dec(v_stx_2166_);
v_view_2387_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2387_);
lean_dec_ref_known(v_val_2351_, 1);
v_start_2388_ = lean_ctor_get(v_view_2387_, 1);
lean_inc(v_start_2388_);
v_items_2389_ = lean_ctor_get(v_view_2387_, 2);
lean_inc_ref(v_items_2389_);
lean_dec_ref(v_view_2387_);
v_sz_2390_ = lean_array_size(v_items_2389_);
v___x_2391_ = ((size_t)0ULL);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_2205_, v_alternate_2169_, v_items_2389_, v_sz_2390_, v___x_2391_, v_start_2388_, v_a_2170_, v_a_2171_);
lean_dec_ref(v_items_2389_);
v_snd_2393_ = lean_ctor_get(v___x_2392_, 1);
lean_inc(v_snd_2393_);
lean_dec_ref(v___x_2392_);
v___x_2394_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2393_);
return v___x_2394_;
}
case 3:
{
lean_object* v_view_2395_; lean_object* v_items_2396_; lean_object* v___x_2397_; size_t v_sz_2398_; size_t v___x_2399_; lean_object* v___x_2400_; lean_object* v_snd_2401_; lean_object* v___x_2402_; 
lean_dec(v_stx_2166_);
v_view_2395_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2395_);
lean_dec_ref_known(v_val_2351_, 1);
v_items_2396_ = lean_ctor_get(v_view_2395_, 1);
lean_inc_ref(v_items_2396_);
lean_dec_ref(v_view_2395_);
v___x_2397_ = lean_box(0);
v_sz_2398_ = lean_array_size(v_items_2396_);
v___x_2399_ = ((size_t)0ULL);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_2205_, v_items_2396_, v_sz_2398_, v___x_2399_, v___x_2397_, v_a_2170_, v_a_2171_);
lean_dec_ref(v_items_2396_);
v_snd_2401_ = lean_ctor_get(v___x_2400_, 1);
lean_inc(v_snd_2401_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2401_);
return v___x_2402_;
}
case 4:
{
lean_object* v_view_2403_; lean_object* v___x_2404_; lean_object* v_snd_2405_; lean_object* v_content_2406_; lean_object* v___y_2408_; lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
lean_dec(v_stx_2166_);
v_view_2403_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2403_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2404_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2405_ = lean_ctor_get(v___x_2404_, 1);
lean_inc(v_snd_2405_);
lean_dec_ref(v___x_2404_);
v_content_2406_ = lean_ctor_get(v_view_2403_, 2);
lean_inc_ref(v_content_2406_);
lean_dec_ref(v_view_2403_);
v___x_2419_ = lean_array_get_size(v_content_2406_);
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_nat_dec_eq(v___x_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
v___y_2408_ = v___x_2422_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2423_; 
v___x_2423_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___y_2408_ = v___x_2423_;
goto v___jp_2407_;
}
v___jp_2407_:
{
lean_object* v___x_2409_; lean_object* v_snd_2410_; size_t v_sz_2411_; size_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_snd_2417_; lean_object* v___x_2418_; 
v___x_2409_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2408_, v_snd_2405_);
v_snd_2410_ = lean_ctor_get(v___x_2409_, 1);
lean_inc(v_snd_2410_);
lean_dec_ref(v___x_2409_);
v_sz_2411_ = lean_array_size(v_content_2406_);
v___x_2412_ = ((size_t)0ULL);
v___x_2413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2411_, v___x_2412_, v_content_2406_);
v___x_2414_ = lean_unsigned_to_nat(2u);
v___x_2415_ = lean_nat_add(v_a_2170_, v___x_2414_);
v___x_2416_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2413_, v___x_2205_, v___x_2415_, v_snd_2410_);
lean_dec(v___x_2415_);
lean_dec_ref(v___x_2413_);
v_snd_2417_ = lean_ctor_get(v___x_2416_, 1);
lean_inc(v_snd_2417_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2417_);
return v___x_2418_;
}
}
case 5:
{
lean_object* v_view_2424_; lean_object* v___x_2425_; lean_object* v_snd_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2451_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
lean_dec(v_stx_2166_);
v_view_2424_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2424_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2425_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2426_ = lean_ctor_get(v___x_2425_, 1);
lean_inc(v_snd_2426_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2428_ = lean_unsigned_to_nat(3u);
v___x_2429_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_view_2424_);
v___x_2467_ = l_Lean_Doc_longestBacktickRun(v___x_2429_);
v___x_2468_ = lean_unsigned_to_nat(1u);
v___x_2469_ = lean_nat_add(v___x_2467_, v___x_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_nat_dec_le(v___x_2428_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec(v___x_2469_);
v___y_2451_ = v___x_2428_;
goto v___jp_2450_;
}
else
{
v___y_2451_ = v___x_2469_;
goto v___jp_2450_;
}
v___jp_2430_:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_string_append(v___x_2429_, v___y_2433_);
v___y_2182_ = v___y_2431_;
v___y_2183_ = v___y_2432_;
v___y_2184_ = v___y_2433_;
v___y_2185_ = v___y_2434_;
v___y_2186_ = v___x_2435_;
goto v___jp_2181_;
}
v___jp_2436_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v_snd_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2441_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2440_, v___y_2439_);
v_snd_2442_ = lean_ctor_get(v___x_2441_, 1);
lean_inc(v_snd_2442_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = lean_string_utf8_byte_size(v___x_2429_);
v___x_2444_ = lean_unsigned_to_nat(0u);
v___x_2445_ = lean_nat_dec_eq(v___x_2443_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; uint8_t v___x_2447_; 
v___x_2446_ = lean_unsigned_to_nat(1u);
v___x_2447_ = lean_nat_dec_le(v___x_2446_, v___x_2443_);
if (v___x_2447_ == 0)
{
v___y_2431_ = v___y_2437_;
v___y_2432_ = v_snd_2442_;
v___y_2433_ = v___x_2440_;
v___y_2434_ = v___y_2438_;
goto v___jp_2430_;
}
else
{
lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = lean_nat_sub(v___x_2443_, v___x_2446_);
v___x_2449_ = lean_string_memcmp(v___x_2429_, v___x_2440_, v___x_2448_, v___x_2444_, v___x_2446_);
lean_dec(v___x_2448_);
if (v___x_2449_ == 0)
{
v___y_2431_ = v___y_2437_;
v___y_2432_ = v_snd_2442_;
v___y_2433_ = v___x_2440_;
v___y_2434_ = v___y_2438_;
goto v___jp_2430_;
}
else
{
v___y_2182_ = v___y_2437_;
v___y_2183_ = v_snd_2442_;
v___y_2184_ = v___x_2440_;
v___y_2185_ = v___y_2438_;
v___y_2186_ = v___x_2429_;
goto v___jp_2181_;
}
}
}
else
{
v___y_2182_ = v___y_2437_;
v___y_2183_ = v_snd_2442_;
v___y_2184_ = v___x_2440_;
v___y_2185_ = v___y_2438_;
v___y_2186_ = v___x_2429_;
goto v___jp_2181_;
}
}
v___jp_2450_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_name_x3f_2454_; 
v___x_2452_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___y_2451_, v___x_2427_);
v___x_2453_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2452_, v_snd_2426_);
v_name_x3f_2454_ = lean_ctor_get(v_view_2424_, 2);
lean_inc(v_name_x3f_2454_);
if (lean_obj_tag(v_name_x3f_2454_) == 1)
{
lean_object* v_snd_2455_; lean_object* v_args_2456_; lean_object* v_val_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_snd_2460_; lean_object* v___x_2461_; size_t v_sz_2462_; size_t v___x_2463_; lean_object* v___x_2464_; lean_object* v_snd_2465_; 
v_snd_2455_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_snd_2455_);
lean_dec_ref(v___x_2453_);
v_args_2456_ = lean_ctor_get(v_view_2424_, 3);
lean_inc_ref(v_args_2456_);
lean_dec_ref(v_view_2424_);
v_val_2457_ = lean_ctor_get(v_name_x3f_2454_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v_name_x3f_2454_, 1);
v___x_2458_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_val_2457_);
v___x_2459_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2458_, v_snd_2455_);
lean_dec_ref(v___x_2458_);
v_snd_2460_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_snd_2460_);
lean_dec_ref(v___x_2459_);
v___x_2461_ = lean_box(0);
v_sz_2462_ = lean_array_size(v_args_2456_);
v___x_2463_ = ((size_t)0ULL);
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2205_, v_args_2456_, v_sz_2462_, v___x_2463_, v___x_2461_, v_a_2170_, v_snd_2460_);
lean_dec_ref(v_args_2456_);
v_snd_2465_ = lean_ctor_get(v___x_2464_, 1);
lean_inc(v_snd_2465_);
lean_dec_ref(v___x_2464_);
v___y_2437_ = v___x_2452_;
v___y_2438_ = v_a_2170_;
v___y_2439_ = v_snd_2465_;
goto v___jp_2436_;
}
else
{
lean_object* v_snd_2466_; 
lean_dec(v_name_x3f_2454_);
lean_dec_ref(v_view_2424_);
v_snd_2466_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_snd_2466_);
lean_dec_ref(v___x_2453_);
v___y_2437_ = v___x_2452_;
v___y_2438_ = v_a_2170_;
v___y_2439_ = v_snd_2466_;
goto v___jp_2436_;
}
}
}
case 6:
{
lean_object* v_view_2471_; lean_object* v___x_2472_; lean_object* v_snd_2473_; lean_object* v_name_2474_; lean_object* v_args_2475_; lean_object* v_content_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v_snd_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_snd_2484_; lean_object* v___x_2485_; size_t v_sz_2486_; size_t v___x_2487_; lean_object* v___x_2488_; lean_object* v_snd_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v_snd_2492_; size_t v_sz_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v_snd_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v_snd_2499_; lean_object* v___x_2500_; lean_object* v_snd_2501_; lean_object* v___x_2502_; 
lean_dec(v_stx_2166_);
v_view_2471_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2471_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2472_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2473_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_snd_2473_);
lean_dec_ref(v___x_2472_);
v_name_2474_ = lean_ctor_get(v_view_2471_, 2);
lean_inc(v_name_2474_);
v_args_2475_ = lean_ctor_get(v_view_2471_, 3);
lean_inc_ref(v_args_2475_);
v_content_2476_ = lean_ctor_get(v_view_2471_, 4);
lean_inc_ref(v_content_2476_);
lean_dec_ref(v_view_2471_);
v___x_2477_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2478_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_content_2476_);
v___x_2479_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(v___x_2478_, v___x_2477_);
v___x_2480_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2479_, v_snd_2473_);
v_snd_2481_ = lean_ctor_get(v___x_2480_, 1);
lean_inc(v_snd_2481_);
lean_dec_ref(v___x_2480_);
v___x_2482_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2474_);
v___x_2483_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2482_, v_snd_2481_);
lean_dec_ref(v___x_2482_);
v_snd_2484_ = lean_ctor_get(v___x_2483_, 1);
lean_inc(v_snd_2484_);
lean_dec_ref(v___x_2483_);
v___x_2485_ = lean_box(0);
v_sz_2486_ = lean_array_size(v_args_2475_);
v___x_2487_ = ((size_t)0ULL);
v___x_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2205_, v_args_2475_, v_sz_2486_, v___x_2487_, v___x_2485_, v_a_2170_, v_snd_2484_);
lean_dec_ref(v_args_2475_);
v_snd_2489_ = lean_ctor_get(v___x_2488_, 1);
lean_inc(v_snd_2489_);
lean_dec_ref(v___x_2488_);
v___x_2490_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2491_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2490_, v_snd_2489_);
v_snd_2492_ = lean_ctor_get(v___x_2491_, 1);
lean_inc(v_snd_2492_);
lean_dec_ref(v___x_2491_);
v_sz_2493_ = lean_array_size(v_content_2476_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2493_, v___x_2487_, v_content_2476_);
v___x_2495_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2494_, v___x_2205_, v_a_2170_, v_snd_2492_);
lean_dec_ref(v___x_2494_);
v_snd_2496_ = lean_ctor_get(v___x_2495_, 1);
lean_inc(v_snd_2496_);
lean_dec_ref(v___x_2495_);
lean_inc(v_a_2170_);
v___x_2497_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2170_, v___x_2477_);
v___x_2498_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2497_, v_snd_2496_);
lean_dec_ref(v___x_2497_);
v_snd_2499_ = lean_ctor_get(v___x_2498_, 1);
lean_inc(v_snd_2499_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2479_, v_snd_2499_);
lean_dec_ref(v___x_2479_);
v_snd_2501_ = lean_ctor_get(v___x_2500_, 1);
lean_inc(v_snd_2501_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2501_);
return v___x_2502_;
}
case 7:
{
lean_object* v_view_2503_; lean_object* v___x_2504_; lean_object* v_snd_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v_snd_2508_; lean_object* v_name_2509_; lean_object* v_args_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_snd_2513_; lean_object* v___x_2514_; size_t v_sz_2515_; size_t v___x_2516_; lean_object* v___x_2517_; lean_object* v_snd_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_snd_2521_; lean_object* v___x_2522_; 
lean_dec(v_stx_2166_);
v_view_2503_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2503_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2504_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2505_ = lean_ctor_get(v___x_2504_, 1);
lean_inc(v_snd_2505_);
lean_dec_ref(v___x_2504_);
v___x_2506_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2507_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2506_, v_snd_2505_);
v_snd_2508_ = lean_ctor_get(v___x_2507_, 1);
lean_inc(v_snd_2508_);
lean_dec_ref(v___x_2507_);
v_name_2509_ = lean_ctor_get(v_view_2503_, 2);
lean_inc(v_name_2509_);
v_args_2510_ = lean_ctor_get(v_view_2503_, 3);
lean_inc_ref(v_args_2510_);
lean_dec_ref(v_view_2503_);
v___x_2511_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2509_);
v___x_2512_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2511_, v_snd_2508_);
lean_dec_ref(v___x_2511_);
v_snd_2513_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_snd_2513_);
lean_dec_ref(v___x_2512_);
v___x_2514_ = lean_box(0);
v_sz_2515_ = lean_array_size(v_args_2510_);
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2205_, v_args_2510_, v_sz_2515_, v___x_2516_, v___x_2514_, v_a_2170_, v_snd_2513_);
lean_dec_ref(v_args_2510_);
v_snd_2518_ = lean_ctor_get(v___x_2517_, 1);
lean_inc(v_snd_2518_);
lean_dec_ref(v___x_2517_);
v___x_2519_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2520_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2519_, v_snd_2518_);
v_snd_2521_ = lean_ctor_get(v___x_2520_, 1);
lean_inc(v_snd_2521_);
lean_dec_ref(v___x_2520_);
v___x_2522_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2521_);
return v___x_2522_;
}
case 8:
{
lean_object* v_view_2523_; lean_object* v___x_2524_; lean_object* v_snd_2525_; lean_object* v_level_2526_; lean_object* v_content_2527_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_snd_2542_; uint8_t v___x_2543_; 
lean_dec(v_stx_2166_);
v_view_2523_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2523_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2524_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2525_ = lean_ctor_get(v___x_2524_, 1);
lean_inc(v_snd_2525_);
lean_dec_ref(v___x_2524_);
v_level_2526_ = lean_ctor_get(v_view_2523_, 2);
lean_inc(v_level_2526_);
v_content_2527_ = lean_ctor_get(v_view_2523_, 3);
lean_inc_ref(v_content_2527_);
lean_dec_ref(v_view_2523_);
v___x_2537_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_2538_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(v_level_2526_, v___x_2537_);
v___x_2539_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2540_ = lean_string_append(v___x_2538_, v___x_2539_);
v___x_2541_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2540_, v_snd_2525_);
lean_dec_ref(v___x_2540_);
v_snd_2542_ = lean_ctor_get(v___x_2541_, 1);
lean_inc(v_snd_2542_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2527_);
if (v___x_2543_ == 0)
{
v___y_2529_ = v_a_2170_;
v___y_2530_ = v_snd_2542_;
goto v___jp_2528_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_snd_2546_; 
v___x_2544_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2545_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2544_, v_snd_2542_);
v_snd_2546_ = lean_ctor_get(v___x_2545_, 1);
lean_inc(v_snd_2546_);
lean_dec_ref(v___x_2545_);
v___y_2529_ = v_a_2170_;
v___y_2530_ = v_snd_2546_;
goto v___jp_2528_;
}
v___jp_2528_:
{
size_t v_sz_2531_; size_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_snd_2535_; lean_object* v___x_2536_; 
v_sz_2531_ = lean_array_size(v_content_2527_);
v___x_2532_ = ((size_t)0ULL);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2531_, v___x_2532_, v_content_2527_);
v___x_2534_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2533_, v___x_2205_, v___y_2529_, v___y_2530_);
lean_dec_ref(v___x_2533_);
v_snd_2535_ = lean_ctor_get(v___x_2534_, 1);
lean_inc(v_snd_2535_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2535_);
return v___x_2536_;
}
}
case 9:
{
lean_object* v_view_2547_; lean_object* v___x_2548_; lean_object* v_snd_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_snd_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_snd_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v_snd_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v_snd_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_snd_2564_; lean_object* v___x_2565_; 
lean_dec(v_stx_2166_);
v_view_2547_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2547_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2548_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2549_ = lean_ctor_get(v___x_2548_, 1);
lean_inc(v_snd_2549_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2551_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2550_, v_snd_2549_);
v_snd_2552_ = lean_ctor_get(v___x_2551_, 1);
lean_inc(v_snd_2552_);
lean_dec_ref(v___x_2551_);
v___x_2553_ = l_Lean_Doc_LinkRefView_getName(v_view_2547_);
v___x_2554_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2553_, v_snd_2552_);
lean_dec_ref(v___x_2553_);
v_snd_2555_ = lean_ctor_get(v___x_2554_, 1);
lean_inc(v_snd_2555_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2557_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2556_, v_snd_2555_);
v_snd_2558_ = lean_ctor_get(v___x_2557_, 1);
lean_inc(v_snd_2558_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2560_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2559_, v_snd_2558_);
v_snd_2561_ = lean_ctor_get(v___x_2560_, 1);
lean_inc(v_snd_2561_);
lean_dec_ref(v___x_2560_);
v___x_2562_ = l_Lean_Doc_LinkRefView_getUrl(v_view_2547_);
lean_dec_ref(v_view_2547_);
v___x_2563_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2562_, v_snd_2561_);
lean_dec_ref(v___x_2562_);
v_snd_2564_ = lean_ctor_get(v___x_2563_, 1);
lean_inc(v_snd_2564_);
lean_dec_ref(v___x_2563_);
v___x_2565_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2564_);
return v___x_2565_;
}
case 10:
{
lean_object* v_view_2566_; lean_object* v___x_2567_; lean_object* v_snd_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_snd_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_snd_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v_snd_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_snd_2580_; lean_object* v_content_2581_; lean_object* v___y_2583_; lean_object* v___y_2584_; uint8_t v___x_2591_; 
lean_dec(v_stx_2166_);
v_view_2566_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2566_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2567_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2568_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_snd_2568_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2569_, v_snd_2568_);
v_snd_2571_ = lean_ctor_get(v___x_2570_, 1);
lean_inc(v_snd_2571_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = l_Lean_Doc_FootnoteRefView_getName(v_view_2566_);
v___x_2573_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2572_, v_snd_2571_);
lean_dec_ref(v___x_2572_);
v_snd_2574_ = lean_ctor_get(v___x_2573_, 1);
lean_inc(v_snd_2574_);
lean_dec_ref(v___x_2573_);
v___x_2575_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2576_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2575_, v_snd_2574_);
v_snd_2577_ = lean_ctor_get(v___x_2576_, 1);
lean_inc(v_snd_2577_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2579_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2578_, v_snd_2577_);
v_snd_2580_ = lean_ctor_get(v___x_2579_, 1);
lean_inc(v_snd_2580_);
lean_dec_ref(v___x_2579_);
v_content_2581_ = lean_ctor_get(v_view_2566_, 4);
lean_inc_ref(v_content_2581_);
lean_dec_ref(v_view_2566_);
v___x_2591_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2581_);
if (v___x_2591_ == 0)
{
v___y_2583_ = v_a_2170_;
v___y_2584_ = v_snd_2580_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_snd_2594_; 
v___x_2592_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2593_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2592_, v_snd_2580_);
v_snd_2594_ = lean_ctor_get(v___x_2593_, 1);
lean_inc(v_snd_2594_);
lean_dec_ref(v___x_2593_);
v___y_2583_ = v_a_2170_;
v___y_2584_ = v_snd_2594_;
goto v___jp_2582_;
}
v___jp_2582_:
{
size_t v_sz_2585_; size_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v_snd_2589_; lean_object* v___x_2590_; 
v_sz_2585_ = lean_array_size(v_content_2581_);
v___x_2586_ = ((size_t)0ULL);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2585_, v___x_2586_, v_content_2581_);
v___x_2588_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2587_, v___x_2205_, v___y_2583_, v___y_2584_);
lean_dec_ref(v___x_2587_);
v_snd_2589_ = lean_ctor_get(v___x_2588_, 1);
lean_inc(v_snd_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2589_);
return v___x_2590_;
}
}
default: 
{
lean_object* v_view_2595_; lean_object* v___x_2596_; lean_object* v_snd_2597_; lean_object* v___y_2599_; lean_object* v___x_2612_; 
v_view_2595_ = lean_ctor_get(v_val_2351_, 0);
lean_inc_ref(v_view_2595_);
lean_dec_ref_known(v_val_2351_, 1);
v___x_2596_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2170_, v_a_2171_);
v_snd_2597_ = lean_ctor_get(v___x_2596_, 1);
lean_inc(v_snd_2597_);
lean_dec_ref(v___x_2596_);
v___x_2612_ = l_Lean_Syntax_getSubstring_x3f(v_stx_2166_, v___x_2205_, v___x_2205_);
lean_dec(v_stx_2166_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_contents_2613_; lean_object* v___x_2614_; 
v_contents_2613_ = lean_ctor_get(v_view_2595_, 2);
lean_inc(v_contents_2613_);
lean_dec_ref(v_view_2595_);
v___x_2614_ = l_Lean_Syntax_reprint(v_contents_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v___x_2615_; 
v___x_2615_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___y_2599_ = v___x_2615_;
goto v___jp_2598_;
}
else
{
lean_object* v_val_2616_; 
v_val_2616_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_val_2616_);
lean_dec_ref_known(v___x_2614_, 1);
v___y_2599_ = v_val_2616_;
goto v___jp_2598_;
}
}
else
{
lean_object* v_val_2617_; lean_object* v_str_2618_; lean_object* v_startPos_2619_; lean_object* v_stopPos_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v_snd_2624_; lean_object* v___x_2625_; 
lean_dec_ref(v_view_2595_);
v_val_2617_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v___x_2612_, 1);
v_str_2618_ = lean_ctor_get(v_val_2617_, 0);
lean_inc_ref(v_str_2618_);
v_startPos_2619_ = lean_ctor_get(v_val_2617_, 1);
lean_inc(v_startPos_2619_);
v_stopPos_2620_ = lean_ctor_get(v_val_2617_, 2);
lean_inc(v_stopPos_2620_);
lean_dec(v_val_2617_);
v___x_2621_ = lean_string_utf8_extract(v_str_2618_, v_startPos_2619_, v_stopPos_2620_);
lean_dec(v_stopPos_2620_);
lean_dec(v_startPos_2619_);
lean_dec_ref(v_str_2618_);
lean_inc(v_a_2170_);
v___x_2622_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2170_, v___x_2621_);
v___x_2623_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2622_, v_snd_2597_);
lean_dec_ref(v___x_2622_);
v_snd_2624_ = lean_ctor_get(v___x_2623_, 1);
lean_inc(v_snd_2624_);
lean_dec_ref(v___x_2623_);
v___x_2625_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2624_);
return v___x_2625_;
}
v___jp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_snd_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2600_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
v___x_2601_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2600_, v_snd_2597_);
v_snd_2602_ = lean_ctor_get(v___x_2601_, 1);
lean_inc(v_snd_2602_);
lean_dec_ref(v___x_2601_);
lean_inc(v_a_2170_);
v___x_2603_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2170_, v___y_2599_);
v___x_2604_ = lean_string_utf8_byte_size(v___x_2603_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_nat_dec_eq(v___x_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v_snd_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v_snd_2611_; 
v___x_2607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2603_, v_snd_2602_);
lean_dec_ref(v___x_2603_);
v_snd_2608_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_snd_2608_);
lean_dec_ref(v___x_2607_);
v___x_2609_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2610_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2609_, v_snd_2608_);
v_snd_2611_ = lean_ctor_get(v___x_2610_, 1);
lean_inc(v_snd_2611_);
lean_dec_ref(v___x_2610_);
v___y_2173_ = v_snd_2611_;
goto v___jp_2172_;
}
else
{
lean_dec_ref(v___x_2603_);
v___y_2173_ = v_snd_2602_;
goto v___jp_2172_;
}
}
}
}
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec(v___x_2350_);
v___x_2626_ = lean_box(0);
v___x_2627_ = l_Lean_Syntax_formatStx(v_stx_2166_, v___x_2626_, v___x_2205_);
v___x_2628_ = l_Std_Format_defWidth;
v___x_2629_ = lean_unsigned_to_nat(0u);
v___x_2630_ = l_Std_Format_pretty(v___x_2627_, v___x_2628_, v___x_2629_, v___x_2629_);
v___x_2631_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2630_, v_a_2171_);
lean_dec_ref(v___x_2630_);
return v___x_2631_;
}
}
}
}
}
}
else
{
lean_object* v___x_2632_; uint8_t v___x_2633_; lean_object* v___x_2634_; 
lean_dec(v_next_x3f_2167_);
v___x_2632_ = l_Lean_Syntax_getArgs(v_stx_2166_);
lean_dec(v_stx_2166_);
v___x_2633_ = 0;
v___x_2634_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2632_, v___x_2633_, v_a_2170_, v_a_2171_);
lean_dec_ref(v___x_2632_);
return v___x_2634_;
}
v___jp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_snd_2179_; lean_object* v___x_2180_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
lean_inc(v_a_2170_);
v___x_2175_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2170_, v___x_2174_);
v___x_2176_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_2177_ = lean_string_append(v___x_2175_, v___x_2176_);
v___x_2178_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2177_, v___y_2173_);
lean_dec_ref(v___x_2177_);
v_snd_2179_ = lean_ctor_get(v___x_2178_, 1);
lean_inc(v_snd_2179_);
lean_dec_ref(v___x_2178_);
v___x_2180_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2179_);
return v___x_2180_;
}
v___jp_2181_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v_snd_2196_; lean_object* v___x_2197_; lean_object* v_snd_2198_; lean_object* v___x_2199_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_string_utf8_byte_size(v___y_2186_);
lean_inc_ref(v___y_2186_);
v___x_2189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2189_, 0, v___y_2186_);
lean_ctor_set(v___x_2189_, 1, v___x_2187_);
lean_ctor_set(v___x_2189_, 2, v___x_2188_);
v___x_2190_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
v___x_2191_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2192_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2185_, v___y_2186_, v___x_2189_, v___x_2188_, v___x_2190_, v___x_2191_);
lean_dec_ref_known(v___x_2189_, 3);
lean_dec_ref(v___y_2186_);
v___x_2193_ = lean_array_to_list(v___x_2192_);
v___x_2194_ = l_String_intercalate(v___y_2184_, v___x_2193_);
v___x_2195_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2194_, v___y_2183_);
lean_dec_ref(v___x_2194_);
v_snd_2196_ = lean_ctor_get(v___x_2195_, 1);
lean_inc(v_snd_2196_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2182_, v_snd_2196_);
lean_dec_ref(v___y_2182_);
v_snd_2198_ = lean_ctor_get(v___x_2197_, 1);
lean_inc(v_snd_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2198_);
return v___x_2199_;
}
v___jp_2200_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v_a_2171_);
return v___x_2202_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2166_ = stack[0].m_obj;
lean_object* v_next_x3f_2167_ = stack[1].m_obj;
uint8_t v_atLineStart_2168_ = stack[2].m_num;
uint8_t v_alternate_2169_ = stack[3].m_num;
lean_object* v_a_2170_ = stack[4].m_obj;
lean_object* v_a_2171_ = stack[5].m_obj;
lean_object* v_res_2635_;
v_res_2635_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2166_, v_next_x3f_2167_, v_atLineStart_2168_, v_alternate_2169_, v_a_2170_, v_a_2171_);
stack->m_obj
 = v_res_2635_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t v___x_2636_, lean_object* v_as_2637_, size_t v_sz_2638_, size_t v_i_2639_, lean_object* v_b_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_usize_dec_lt(v_i_2639_, v_sz_2638_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_b_2640_);
lean_ctor_set(v___x_2644_, 1, v___y_2642_);
return v___x_2644_;
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v_snd_2647_; lean_object* v_a_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v_snd_2651_; lean_object* v___x_2652_; size_t v___x_2653_; size_t v___x_2654_; 
v___x_2645_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2646_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2645_, v___y_2642_);
v_snd_2647_ = lean_ctor_get(v___x_2646_, 1);
lean_inc(v_snd_2647_);
lean_dec_ref(v___x_2646_);
v_a_2648_ = lean_array_uget_borrowed(v_as_2637_, v_i_2639_);
v___x_2649_ = lean_box(0);
lean_inc(v_a_2648_);
v___x_2650_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2648_, v___x_2649_, v___x_2636_, v___x_2636_, v___y_2641_, v_snd_2647_);
v_snd_2651_ = lean_ctor_get(v___x_2650_, 1);
lean_inc(v_snd_2651_);
lean_dec_ref(v___x_2650_);
v___x_2652_ = lean_box(0);
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_add(v_i_2639_, v___x_2653_);
v_i_2639_ = v___x_2654_;
v_b_2640_ = v___x_2652_;
v___y_2642_ = v_snd_2651_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2636_ = stack[0].m_num;
lean_object* v_as_2637_ = stack[1].m_obj;
size_t v_sz_2638_ = stack[2].m_num;
size_t v_i_2639_ = stack[3].m_num;
lean_object* v_b_2640_ = stack[4].m_obj;
lean_object* v___y_2641_ = stack[5].m_obj;
lean_object* v___y_2642_ = stack[6].m_obj;
lean_object* v_res_2656_;
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2636_, v_as_2637_, v_sz_2638_, v_i_2639_, v_b_2640_, v___y_2641_, v___y_2642_);
stack->m_obj
 = v_res_2656_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v___x_2657_, lean_object* v_as_2658_, lean_object* v_sz_2659_, lean_object* v_i_2660_, lean_object* v_b_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v___x_62200__boxed_2664_; size_t v_sz_boxed_2665_; size_t v_i_boxed_2666_; lean_object* v_res_2667_; 
v___x_62200__boxed_2664_ = lean_unbox(v___x_2657_);
v_sz_boxed_2665_ = lean_unbox_usize(v_sz_2659_);
lean_dec(v_sz_2659_);
v_i_boxed_2666_ = lean_unbox_usize(v_i_2660_);
lean_dec(v_i_2660_);
v_res_2667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_62200__boxed_2664_, v_as_2658_, v_sz_boxed_2665_, v_i_boxed_2666_, v_b_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v_as_2658_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object* v___y_2668_, lean_object* v___x_2669_, lean_object* v_as_2670_, lean_object* v_sz_2671_, lean_object* v_i_2672_, lean_object* v_b_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
uint8_t v___x_62218__boxed_2676_; size_t v_sz_boxed_2677_; size_t v_i_boxed_2678_; lean_object* v_res_2679_; 
v___x_62218__boxed_2676_ = lean_unbox(v___x_2669_);
v_sz_boxed_2677_ = lean_unbox_usize(v_sz_2671_);
lean_dec(v_sz_2671_);
v_i_boxed_2678_ = lean_unbox_usize(v_i_2672_);
lean_dec(v_i_2672_);
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2668_, v___x_62218__boxed_2676_, v_as_2670_, v_sz_boxed_2677_, v_i_boxed_2678_, v_b_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v_as_2670_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object* v_stxs_2680_, lean_object* v_lineStart_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_lineStart_boxed_2684_; lean_object* v_res_2685_; 
v_lineStart_boxed_2684_ = lean_unbox(v_lineStart_2681_);
v_res_2685_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v_stxs_2680_, v_lineStart_boxed_2684_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_stxs_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object* v_char_2686_, lean_object* v_inls_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
uint32_t v_char_boxed_2690_; lean_object* v_res_2691_; 
v_char_boxed_2690_ = lean_unbox_uint32(v_char_2686_);
lean_dec(v_char_2686_);
v_res_2691_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v_char_boxed_2690_, v_inls_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2688_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object* v___x_2692_, lean_object* v_alternate_2693_, lean_object* v_as_2694_, lean_object* v_sz_2695_, lean_object* v_i_2696_, lean_object* v_b_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
uint8_t v___x_62298__boxed_2700_; uint8_t v_alternate_boxed_2701_; size_t v_sz_boxed_2702_; size_t v_i_boxed_2703_; lean_object* v_res_2704_; 
v___x_62298__boxed_2700_ = lean_unbox(v___x_2692_);
v_alternate_boxed_2701_ = lean_unbox(v_alternate_2693_);
v_sz_boxed_2702_ = lean_unbox_usize(v_sz_2695_);
lean_dec(v_sz_2695_);
v_i_boxed_2703_ = lean_unbox_usize(v_i_2696_);
lean_dec(v_i_2696_);
v_res_2704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_62298__boxed_2700_, v_alternate_boxed_2701_, v_as_2694_, v_sz_boxed_2702_, v_i_boxed_2703_, v_b_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v_as_2694_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object* v___x_2705_, lean_object* v_as_2706_, lean_object* v_sz_2707_, lean_object* v_i_2708_, lean_object* v_b_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
uint8_t v___x_62332__boxed_2712_; size_t v_sz_boxed_2713_; size_t v_i_boxed_2714_; lean_object* v_res_2715_; 
v___x_62332__boxed_2712_ = lean_unbox(v___x_2705_);
v_sz_boxed_2713_ = lean_unbox_usize(v_sz_2707_);
lean_dec(v_sz_2707_);
v_i_boxed_2714_ = lean_unbox_usize(v_i_2708_);
lean_dec(v_i_2708_);
v_res_2715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_62332__boxed_2712_, v_as_2706_, v_sz_boxed_2713_, v_i_boxed_2714_, v_b_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v_as_2706_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object* v_upperBound_2716_, lean_object* v___y_2717_, lean_object* v_a_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2716_, v___y_2717_, v_a_2718_, v_b_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2717_);
lean_dec(v_upperBound_2716_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object* v_stx_2723_, lean_object* v_next_x3f_2724_, lean_object* v_atLineStart_2725_, lean_object* v_alternate_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
uint8_t v_atLineStart_boxed_2729_; uint8_t v_alternate_boxed_2730_; lean_object* v_res_2731_; 
v_atLineStart_boxed_2729_ = lean_unbox(v_atLineStart_2725_);
v_alternate_boxed_2730_ = lean_unbox(v_alternate_2726_);
v_res_2731_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2723_, v_next_x3f_2724_, v_atLineStart_boxed_2729_, v_alternate_boxed_2730_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2727_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object* v_s_2732_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object* v_s_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(v_s_2734_);
lean_dec_ref(v_s_2734_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object* v_upperBound_2736_, lean_object* v___y_2737_, lean_object* v_inst_2738_, lean_object* v_R_2739_, lean_object* v_a_2740_, lean_object* v_b_2741_, lean_object* v_c_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2736_, v___y_2737_, v_a_2740_, v_b_2741_, v___y_2743_, v___y_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object* v_upperBound_2746_, lean_object* v___y_2747_, lean_object* v_inst_2748_, lean_object* v_R_2749_, lean_object* v_a_2750_, lean_object* v_b_2751_, lean_object* v_c_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(v_upperBound_2746_, v___y_2747_, v_inst_2748_, v_R_2749_, v_a_2750_, v_b_2751_, v_c_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2747_);
lean_dec(v_upperBound_2746_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___x_2758_, lean_object* v___x_2759_, lean_object* v_inst_2760_, lean_object* v_R_2761_, lean_object* v_a_2762_, lean_object* v_b_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2756_, v___y_2757_, v___x_2758_, v___x_2759_, v_a_2762_, v_b_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v_inst_2769_, lean_object* v_R_2770_, lean_object* v_a_2771_, lean_object* v_b_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(v___y_2765_, v___y_2766_, v___x_2767_, v___x_2768_, v_inst_2769_, v_R_2770_, v_a_2771_, v_b_2772_);
lean_dec_ref(v___x_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object* v_s_2774_, lean_object* v_pos_2775_){
_start:
{
lean_object* v_str_2776_; lean_object* v_startInclusive_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; uint8_t v_decide_2781_; 
v_str_2776_ = lean_ctor_get(v_s_2774_, 0);
v_startInclusive_2777_ = lean_ctor_get(v_s_2774_, 1);
v___x_2778_ = lean_nat_add(v_startInclusive_2777_, v_pos_2775_);
v___x_2779_ = lean_nat_sub(v___x_2778_, v_startInclusive_2777_);
v___x_2780_ = lean_unsigned_to_nat(0u);
v_decide_2781_ = lean_nat_dec_eq(v___x_2779_, v___x_2780_);
if (v_decide_2781_ == 0)
{
uint32_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint32_t v___x_2788_; uint8_t v___x_2789_; 
v___x_2782_ = 10;
lean_inc(v_startInclusive_2777_);
lean_inc_ref(v_str_2776_);
v___x_2783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2783_, 0, v_str_2776_);
lean_ctor_set(v___x_2783_, 1, v_startInclusive_2777_);
lean_ctor_set(v___x_2783_, 2, v___x_2778_);
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = lean_nat_sub(v___x_2779_, v___x_2784_);
lean_dec(v___x_2779_);
v___x_2786_ = l_String_Slice_posLE(v___x_2783_, v___x_2785_);
lean_dec_ref_known(v___x_2783_, 3);
v___x_2787_ = lean_nat_add(v_startInclusive_2777_, v___x_2786_);
v___x_2788_ = lean_string_utf8_get_fast(v_str_2776_, v___x_2787_);
lean_dec(v___x_2787_);
v___x_2789_ = lean_uint32_dec_eq(v___x_2788_, v___x_2782_);
if (v___x_2789_ == 0)
{
lean_dec(v___x_2786_);
return v_pos_2775_;
}
else
{
lean_object* v___x_2790_; uint8_t v___x_2791_; 
v___x_2790_ = lean_nat_add(v___x_2786_, v___x_2784_);
v___x_2791_ = lean_nat_dec_le(v___x_2790_, v_pos_2775_);
lean_dec(v___x_2790_);
if (v___x_2791_ == 0)
{
lean_dec(v___x_2786_);
return v_pos_2775_;
}
else
{
lean_dec(v_pos_2775_);
v_pos_2775_ = v___x_2786_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2779_);
lean_dec(v___x_2778_);
return v_pos_2775_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object* v_s_2793_, lean_object* v_pos_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v_s_2793_, v_pos_2794_);
lean_dec_ref(v_s_2793_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object* v_s_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v___x_2797_ = lean_string_utf8_byte_size(v_s_2796_);
v___x_2798_ = lean_unsigned_to_nat(1u);
v___x_2799_ = lean_nat_dec_le(v___x_2798_, v___x_2797_);
if (v___x_2799_ == 0)
{
return v_s_2796_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2800_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = lean_nat_sub(v___x_2797_, v___x_2798_);
v___x_2803_ = lean_string_memcmp(v_s_2796_, v___x_2800_, v___x_2802_, v___x_2801_, v___x_2798_);
lean_dec(v___x_2802_);
if (v___x_2803_ == 0)
{
return v_s_2796_;
}
else
{
uint32_t v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2804_ = 10;
lean_inc_ref(v_s_2796_);
v___x_2805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2805_, 0, v_s_2796_);
lean_ctor_set(v___x_2805_, 1, v___x_2801_);
lean_ctor_set(v___x_2805_, 2, v___x_2797_);
v___x_2806_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v___x_2805_, v___x_2797_);
lean_dec_ref_known(v___x_2805_, 3);
v___x_2807_ = lean_string_utf8_extract_fast(v_s_2796_, v___x_2801_, v___x_2806_);
lean_dec(v___x_2806_);
lean_dec_ref(v_s_2796_);
v___x_2808_ = lean_string_push(v___x_2807_, v___x_2804_);
return v___x_2808_;
}
}
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object* v_stx_2809_, uint8_t v_alternate_2810_){
_start:
{
lean_object* v___x_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v_snd_2816_; 
v___x_2811_ = lean_box(0);
v___x_2812_ = 0;
v___x_2813_ = lean_unsigned_to_nat(0u);
v___x_2814_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2815_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2809_, v___x_2811_, v___x_2812_, v_alternate_2810_, v___x_2813_, v___x_2814_);
v_snd_2816_ = lean_ctor_get(v___x_2815_, 1);
lean_inc(v_snd_2816_);
lean_dec_ref(v___x_2815_);
return v_snd_2816_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2809_ = stack[0].m_obj;
uint8_t v_alternate_2810_ = stack[1].m_num;
lean_object* v_res_2817_;
v_res_2817_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2809_, v_alternate_2810_);
stack->m_obj
 = v_res_2817_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object* v_stx_2818_, lean_object* v_alternate_2819_){
_start:
{
uint8_t v_alternate_boxed_2820_; lean_object* v_res_2821_; 
v_alternate_boxed_2820_ = lean_unbox(v_alternate_2819_);
v_res_2821_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2818_, v_alternate_boxed_2820_);
return v_res_2821_;
}
}
lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_2822_, uint8_t v_alternate_2823_){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2822_, v_alternate_2823_);
v___x_2825_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT void l_Lean_Doc_Parser_versoSyntaxToString_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_2822_ = stack[0].m_obj;
uint8_t v_alternate_2823_ = stack[1].m_num;
lean_object* v_res_2826_;
v_res_2826_ = l_Lean_Doc_Parser_versoSyntaxToString(v_stx_2822_, v_alternate_2823_);
stack->m_obj
 = v_res_2826_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object* v_stx_2827_, lean_object* v_alternate_2828_){
_start:
{
uint8_t v_alternate_boxed_2829_; lean_object* v_res_2830_; 
v_alternate_boxed_2829_ = lean_unbox(v_alternate_2828_);
v_res_2830_ = l_Lean_Doc_Parser_versoSyntaxToString(v_stx_2827_, v_alternate_boxed_2829_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object* v_b_2831_, lean_object* v___y_2832_){
_start:
{
uint8_t v___x_2833_; 
lean_inc(v_b_2831_);
v___x_2833_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_b_2831_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; uint8_t v___y_2836_; 
lean_inc(v_b_2831_);
v___x_2834_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v___y_2832_, v_b_2831_);
lean_dec(v___y_2832_);
if (lean_obj_tag(v___x_2834_) == 0)
{
v___y_2836_ = v___x_2833_;
goto v___jp_2835_;
}
else
{
lean_object* v_val_2839_; uint8_t v_alternate_2840_; 
v_val_2839_ = lean_ctor_get(v___x_2834_, 0);
v_alternate_2840_ = lean_ctor_get_uint8(v_val_2839_, 1);
v___y_2836_ = v_alternate_2840_;
goto v___jp_2835_;
}
v___jp_2835_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_b_2831_, v___y_2836_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v___x_2834_);
return v___x_2838_;
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_dec(v_b_2831_);
v___x_2841_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___y_2832_);
return v___x_2842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object* v_n_2843_, lean_object* v_f_2844_, lean_object* v_xs_2845_, lean_object* v_k_2846_, lean_object* v_acc_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_nat_dec_lt(v_k_2846_, v_n_2843_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; 
lean_dec(v_k_2846_);
lean_dec_ref(v_f_2844_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_acc_2847_);
lean_ctor_set(v___x_2850_, 1, v___y_2848_);
return v___x_2850_;
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v_fst_2853_; lean_object* v_snd_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2851_ = lean_array_fget_borrowed(v_xs_2845_, v_k_2846_);
lean_inc_ref(v_f_2844_);
lean_inc(v___x_2851_);
v___x_2852_ = lean_apply_2(v_f_2844_, v___x_2851_, v___y_2848_);
v_fst_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_fst_2853_);
v_snd_2854_ = lean_ctor_get(v___x_2852_, 1);
lean_inc(v_snd_2854_);
lean_dec_ref(v___x_2852_);
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_2856_ = lean_nat_add(v_k_2846_, v___x_2855_);
lean_dec(v_k_2846_);
v___x_2857_ = lean_array_push(v_acc_2847_, v_fst_2853_);
v_k_2846_ = v___x_2856_;
v_acc_2847_ = v___x_2857_;
v___y_2848_ = v_snd_2854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object* v_n_2859_, lean_object* v_f_2860_, lean_object* v_xs_2861_, lean_object* v_k_2862_, lean_object* v_acc_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2859_, v_f_2860_, v_xs_2861_, v_k_2862_, v_acc_2863_, v___y_2864_);
lean_dec_ref(v_xs_2861_);
lean_dec(v_n_2859_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object* v_blocks_2867_){
_start:
{
lean_object* v___f_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v_fst_2874_; 
v___f_2868_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0));
v___x_2869_ = lean_array_get_size(v_blocks_2867_);
v___x_2870_ = lean_unsigned_to_nat(0u);
v___x_2871_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2872_ = lean_box(0);
v___x_2873_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v___x_2869_, v___f_2868_, v_blocks_2867_, v___x_2870_, v___x_2871_, v___x_2872_);
v_fst_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_fst_2874_);
lean_dec_ref(v___x_2873_);
return v_fst_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object* v_blocks_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2875_);
lean_dec_ref(v_blocks_2875_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object* v_00_u03b1_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_n_2879_, lean_object* v_f_2880_, lean_object* v_xs_2881_, lean_object* v_k_2882_, lean_object* v_h_2883_, lean_object* v_acc_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2879_, v_f_2880_, v_xs_2881_, v_k_2882_, v_acc_2884_, v___y_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object* v_00_u03b1_2887_, lean_object* v_00_u03b2_2888_, lean_object* v_n_2889_, lean_object* v_f_2890_, lean_object* v_xs_2891_, lean_object* v_k_2892_, lean_object* v_h_2893_, lean_object* v_acc_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(v_00_u03b1_2887_, v_00_u03b2_2888_, v_n_2889_, v_f_2890_, v_xs_2891_, v_k_2892_, v_h_2893_, v_acc_2894_, v___y_2895_);
lean_dec_ref(v_xs_2891_);
lean_dec(v_n_2889_);
return v_res_2896_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object* v_as_2897_, size_t v_i_2898_, size_t v_stop_2899_, lean_object* v_b_2900_){
_start:
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_usize_dec_eq(v_i_2898_, v_stop_2899_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; lean_object* v___x_2903_; size_t v___x_2904_; size_t v___x_2905_; 
v___x_2902_ = lean_array_uget_borrowed(v_as_2897_, v_i_2898_);
v___x_2903_ = lean_string_append(v_b_2900_, v___x_2902_);
v___x_2904_ = ((size_t)1ULL);
v___x_2905_ = lean_usize_add(v_i_2898_, v___x_2904_);
v_i_2898_ = v___x_2905_;
v_b_2900_ = v___x_2903_;
goto _start;
}
else
{
return v_b_2900_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2897_ = stack[0].m_obj;
size_t v_i_2898_ = stack[1].m_num;
size_t v_stop_2899_ = stack[2].m_num;
lean_object* v_b_2900_ = stack[3].m_obj;
lean_object* v_res_2907_;
v_res_2907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v_as_2897_, v_i_2898_, v_stop_2899_, v_b_2900_);
stack->m_obj
 = v_res_2907_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object* v_as_2908_, lean_object* v_i_2909_, lean_object* v_stop_2910_, lean_object* v_b_2911_){
_start:
{
size_t v_i_boxed_2912_; size_t v_stop_boxed_2913_; lean_object* v_res_2914_; 
v_i_boxed_2912_ = lean_unbox_usize(v_i_2909_);
lean_dec(v_i_2909_);
v_stop_boxed_2913_ = lean_unbox_usize(v_stop_2910_);
lean_dec(v_stop_2910_);
v_res_2914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v_as_2908_, v_i_boxed_2912_, v_stop_boxed_2913_, v_b_2911_);
lean_dec_ref(v_as_2908_);
return v_res_2914_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0(void){
_start:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; 
v___x_2915_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2916_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object* v_blocks_2917_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v___x_2918_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2919_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2917_);
v___x_2920_ = lean_unsigned_to_nat(0u);
v___x_2921_ = lean_array_get_size(v___x_2919_);
v___x_2922_ = lean_nat_dec_lt(v___x_2920_, v___x_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2923_; 
lean_dec_ref(v___x_2919_);
v___x_2923_ = lean_obj_once(&l_Lean_Doc_Parser_versoDocumentToString___closed__0, &l_Lean_Doc_Parser_versoDocumentToString___closed__0_once, _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0);
return v___x_2923_;
}
else
{
size_t v___x_2924_; size_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = lean_usize_of_nat(v___x_2921_);
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v___x_2919_, v___x_2924_, v___x_2925_, v___x_2918_);
lean_dec_ref(v___x_2919_);
v___x_2927_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2926_);
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object* v_blocks_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Doc_Parser_versoDocumentToString(v_blocks_2928_);
lean_dec_ref(v_blocks_2928_);
return v_res_2929_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; lean_object* v_stxTrav_2933_; lean_object* v_cur_2934_; lean_object* v___x_2935_; 
v___x_2932_ = lean_st_ref_get(v___y_2930_);
v_stxTrav_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc_ref(v_stxTrav_2933_);
lean_dec(v___x_2932_);
v_cur_2934_ = lean_ctor_get(v_stxTrav_2933_, 0);
lean_inc(v_cur_2934_);
lean_dec_ref(v_stxTrav_2933_);
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_cur_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2930_ = stack[0].m_obj;
lean_object* v_res_2936_;
v_res_2936_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2930_);
stack->m_obj
 = v_res_2936_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2937_);
lean_dec(v___y_2937_);
return v_res_2939_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2941_);
return v___x_2945_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2940_ = stack[0].m_obj;
lean_object* v___y_2941_ = stack[1].m_obj;
lean_object* v___y_2942_ = stack[2].m_obj;
lean_object* v___y_2943_ = stack[3].m_obj;
lean_object* v_res_2946_;
v_res_2946_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
stack->m_obj
 = v_res_2946_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
return v_res_2952_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; lean_object* v_stxTrav_2956_; lean_object* v_leadWord_2957_; uint8_t v_leadWordIdent_2958_; uint8_t v_isUngrouped_2959_; uint8_t v_mustBeGrouped_2960_; lean_object* v_stack_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2972_; 
v___x_2955_ = lean_st_ref_take(v___y_2953_);
v_stxTrav_2956_ = lean_ctor_get(v___x_2955_, 0);
v_leadWord_2957_ = lean_ctor_get(v___x_2955_, 1);
v_leadWordIdent_2958_ = lean_ctor_get_uint8(v___x_2955_, sizeof(void*)*3);
v_isUngrouped_2959_ = lean_ctor_get_uint8(v___x_2955_, sizeof(void*)*3 + 1);
v_mustBeGrouped_2960_ = lean_ctor_get_uint8(v___x_2955_, sizeof(void*)*3 + 2);
v_stack_2961_ = lean_ctor_get(v___x_2955_, 2);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2963_ = v___x_2955_;
v_isShared_2964_ = v_isSharedCheck_2972_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_stack_2961_);
lean_inc(v_leadWord_2957_);
lean_inc(v_stxTrav_2956_);
lean_dec(v___x_2955_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2972_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2965_ = lean_box(0);
v___x_2966_ = l_Lean_Syntax_Traverser_left(v_stxTrav_2956_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2966_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2971_, 1, v_leadWord_2957_);
lean_ctor_set(v_reuseFailAlloc_2971_, 2, v_stack_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2971_, sizeof(void*)*3, v_leadWordIdent_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_2971_, sizeof(void*)*3 + 1, v_isUngrouped_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_2971_, sizeof(void*)*3 + 2, v_mustBeGrouped_2960_);
v___x_2968_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_st_ref_put(v___y_2953_, v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2965_);
return v___x_2970_;
}
}
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2953_ = stack[0].m_obj;
lean_object* v_res_2973_;
v_res_2973_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2953_);
stack->m_obj
 = v_res_2973_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2974_);
lean_dec(v___y_2974_);
return v_res_2976_;
}
}
lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2978_);
return v___x_2982_;
}
}
LEAN_EXPORT void l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2977_ = stack[0].m_obj;
lean_object* v___y_2978_ = stack[1].m_obj;
lean_object* v___y_2979_ = stack[2].m_obj;
lean_object* v___y_2980_ = stack[3].m_obj;
lean_object* v_res_2983_;
v_res_2983_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
stack->m_obj
 = v_res_2983_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
return v_res_2989_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object* v_upperBound_2990_, lean_object* v___x_2991_, lean_object* v_rendered_2992_, lean_object* v_a_2993_, lean_object* v_b_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_nat_dec_lt(v_a_2993_, v_upperBound_2990_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_a_2993_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_b_2994_);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v___y_3004_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3002_ = lean_box(0);
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = lean_unsigned_to_nat(1u);
v___x_3012_ = lean_nat_sub(v___x_2991_, v___x_3011_);
v___x_3013_ = lean_nat_sub(v___x_3012_, v_a_2993_);
lean_dec(v___x_3012_);
v___x_3014_ = lean_array_fget_borrowed(v_rendered_2992_, v___x_3013_);
lean_dec(v___x_3013_);
v___x_3015_ = lean_nat_dec_eq(v_a_2993_, v___x_3010_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
lean_inc(v___x_3014_);
v___x_3016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
v___y_3004_ = v___x_3016_;
goto v___jp_3003_;
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_inc(v___x_3014_);
v___x_3017_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_3014_);
v___x_3018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
v___y_3004_ = v___x_3018_;
goto v___jp_3003_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___y_3004_, v___y_2996_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3006_; 
lean_dec_ref_known(v___x_3005_, 1);
v___x_3006_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2996_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
lean_dec_ref_known(v___x_3006_, 1);
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_nat_add(v_a_2993_, v___x_3007_);
lean_dec(v_a_2993_);
v_a_2993_ = v___x_3008_;
v_b_2994_ = v___x_3002_;
goto _start;
}
else
{
lean_dec(v_a_2993_);
return v___x_3006_;
}
}
else
{
lean_dec(v_a_2993_);
return v___x_3005_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2990_ = stack[0].m_obj;
lean_object* v___x_2991_ = stack[1].m_obj;
lean_object* v_rendered_2992_ = stack[2].m_obj;
lean_object* v_a_2993_ = stack[3].m_obj;
lean_object* v_b_2994_ = stack[4].m_obj;
lean_object* v___y_2995_ = stack[5].m_obj;
lean_object* v___y_2996_ = stack[6].m_obj;
lean_object* v___y_2997_ = stack[7].m_obj;
lean_object* v___y_2998_ = stack[8].m_obj;
lean_object* v_res_3019_;
v_res_3019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_2990_, v___x_2991_, v_rendered_2992_, v_a_2993_, v_b_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
stack->m_obj
 = v_res_3019_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object* v_upperBound_3020_, lean_object* v___x_3021_, lean_object* v_rendered_3022_, lean_object* v_a_3023_, lean_object* v_b_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_3020_, v___x_3021_, v_rendered_3022_, v_a_3023_, v_b_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v_rendered_3022_);
lean_dec(v___x_3021_);
lean_dec(v_upperBound_3020_);
return v_res_3030_;
}
}
lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_3031_, lean_object* v_rendered_3032_, lean_object* v___x_3033_, lean_object* v___x_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v___x_3031_, v___x_3031_, v_rendered_3032_, v___x_3033_, v___x_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3040_, 0);
lean_dec(v_unused_3048_);
v___x_3042_ = v___x_3040_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v___x_3040_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3034_);
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3034_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
return v___x_3040_;
}
}
}
LEAN_EXPORT void l_Lean_Doc_Parser_document_formatter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3031_ = stack[0].m_obj;
lean_object* v_rendered_3032_ = stack[1].m_obj;
lean_object* v___x_3033_ = stack[2].m_obj;
lean_object* v___x_3034_ = stack[3].m_obj;
lean_object* v___y_3035_ = stack[4].m_obj;
lean_object* v___y_3036_ = stack[5].m_obj;
lean_object* v___y_3037_ = stack[6].m_obj;
lean_object* v___y_3038_ = stack[7].m_obj;
lean_object* v_res_3049_;
v_res_3049_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_3031_, v_rendered_3032_, v___x_3033_, v___x_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
stack->m_obj
 = v_res_3049_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_3050_, lean_object* v_rendered_3051_, lean_object* v___x_3052_, lean_object* v___x_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_3050_, v_rendered_3051_, v___x_3052_, v___x_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v_rendered_3051_);
lean_dec(v___x_3050_);
return v_res_3059_;
}
}
lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; lean_object* v_a_3066_; lean_object* v_blocks_3067_; lean_object* v_rendered_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___f_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3065_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_3061_);
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref(v___x_3065_);
v_blocks_3067_ = l_Lean_TSyntax_getVersoBlocks(v_a_3066_);
lean_dec(v_a_3066_);
v_rendered_3068_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_3067_);
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_array_get_size(v_blocks_3067_);
lean_dec_ref(v_blocks_3067_);
v___x_3071_ = lean_box(0);
v___f_3072_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3072_, 0, v___x_3070_);
lean_closure_set(v___f_3072_, 1, v_rendered_3068_);
lean_closure_set(v___f_3072_, 2, v___x_3069_);
lean_closure_set(v___f_3072_, 3, v___x_3071_);
v___x_3073_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs___boxed), 6, 1);
lean_closure_set(v___x_3073_, 0, v___f_3072_);
v___x_3074_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3073_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
return v___x_3074_;
}
}
LEAN_EXPORT void l_Lean_Doc_Parser_document_formatter___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3060_ = stack[0].m_obj;
lean_object* v___y_3061_ = stack[1].m_obj;
lean_object* v___y_3062_ = stack[2].m_obj;
lean_object* v___y_3063_ = stack[3].m_obj;
lean_object* v_res_3075_;
v_res_3075_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
stack->m_obj
 = v_res_3075_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3081_;
}
}
lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v___f_3088_; lean_object* v___x_3089_; 
v___f_3088_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_3089_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_3088_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_);
return v___x_3089_;
}
}
LEAN_EXPORT void l_Lean_Doc_Parser_document_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3083_ = stack[0].m_obj;
lean_object* v_a_3084_ = stack[1].m_obj;
lean_object* v_a_3085_ = stack[2].m_obj;
lean_object* v_a_3086_ = stack[3].m_obj;
lean_object* v_res_3090_;
v_res_3090_ = l_Lean_Doc_Parser_document_formatter(v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_);
stack->m_obj
 = v_res_3090_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_Doc_Parser_document_formatter(v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
return v_res_3096_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object* v_upperBound_3097_, lean_object* v___x_3098_, lean_object* v_rendered_3099_, lean_object* v_inst_3100_, lean_object* v_R_3101_, lean_object* v_a_3102_, lean_object* v_b_3103_, lean_object* v_c_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_3097_, v___x_3098_, v_rendered_3099_, v_a_3102_, v_b_3103_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3097_ = stack[0].m_obj;
lean_object* v___x_3098_ = stack[1].m_obj;
lean_object* v_rendered_3099_ = stack[2].m_obj;
lean_object* v_a_3102_ = stack[5].m_obj;
lean_object* v_b_3103_ = stack[6].m_obj;
lean_object* v___y_3105_ = stack[8].m_obj;
lean_object* v___y_3106_ = stack[9].m_obj;
lean_object* v___y_3107_ = stack[10].m_obj;
lean_object* v___y_3108_ = stack[11].m_obj;
lean_object* v_res_3111_;
v_res_3111_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(v_upperBound_3097_, v___x_3098_, v_rendered_3099_, lean_box(0), lean_box(0), v_a_3102_, v_b_3103_, lean_box(0), v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
stack->m_obj
 = v_res_3111_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object* v_upperBound_3112_, lean_object* v___x_3113_, lean_object* v_rendered_3114_, lean_object* v_inst_3115_, lean_object* v_R_3116_, lean_object* v_a_3117_, lean_object* v_b_3118_, lean_object* v_c_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(v_upperBound_3112_, v___x_3113_, v_rendered_3114_, v_inst_3115_, v_R_3116_, v_a_3117_, v_b_3118_, v_c_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v_rendered_3114_);
lean_dec(v___x_3113_);
lean_dec(v_upperBound_3112_);
return v_res_3125_;
}
}
lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1(){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3143_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3144_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4));
v___x_3145_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6));
v___x_3146_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___boxed), 5, 0);
v___x_3147_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3143_, v___x_3144_, v___x_3145_, v___x_3146_);
return v___x_3147_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3148_;
v_res_3148_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
stack->m_obj
 = v_res_3148_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
return v_res_3150_;
}
}
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_View(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1);
l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1 = _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1);
res = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin);
lean_object* initialize_Lean_DocString_View(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Formatter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Formatter(builtin);
}
#ifdef __cplusplus
}
#endif
