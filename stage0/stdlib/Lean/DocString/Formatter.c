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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl(uint8_t v_x_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_box(v_x_46_);
v___x_48_ = lean_obj_tag_nat(v___x_47_);
lean_dec(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl___boxed(lean_object* v_x_49_){
_start:
{
uint8_t v_x_4__boxed_50_; lean_object* v_res_51_; 
v_x_4__boxed_50_ = lean_unbox(v_x_49_);
v_res_51_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___impl(v_x_4__boxed_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(lean_object* v_k_52_){
_start:
{
lean_inc(v_k_52_);
return v_k_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg___boxed(lean_object* v_k_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___redArg(v_k_53_);
lean_dec(v_k_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(lean_object* v_motive_55_, lean_object* v_ctorIdx_56_, uint8_t v_t_57_, lean_object* v_h_58_, lean_object* v_k_59_){
_start:
{
lean_inc(v_k_59_);
return v_k_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim___boxed(lean_object* v_motive_60_, lean_object* v_ctorIdx_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_k_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorElim(v_motive_60_, v_ctorIdx_61_, v_t_boxed_65_, v_h_63_, v_k_64_);
lean_dec(v_k_64_);
lean_dec(v_ctorIdx_61_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(lean_object* v_ordered_67_){
_start:
{
lean_inc(v_ordered_67_);
return v_ordered_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg___boxed(lean_object* v_ordered_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___redArg(v_ordered_68_);
lean_dec(v_ordered_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(lean_object* v_motive_70_, uint8_t v_t_71_, lean_object* v_h_72_, lean_object* v_ordered_73_){
_start:
{
lean_inc(v_ordered_73_);
return v_ordered_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim___boxed(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_ordered_77_){
_start:
{
uint8_t v_t_boxed_78_; lean_object* v_res_79_; 
v_t_boxed_78_ = lean_unbox(v_t_75_);
v_res_79_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ordered_elim(v_motive_74_, v_t_boxed_78_, v_h_76_, v_ordered_77_);
lean_dec(v_ordered_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(lean_object* v_unordered_80_){
_start:
{
lean_inc(v_unordered_80_);
return v_unordered_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg___boxed(lean_object* v_unordered_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___redArg(v_unordered_81_);
lean_dec(v_unordered_81_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(lean_object* v_motive_83_, uint8_t v_t_84_, lean_object* v_h_85_, lean_object* v_unordered_86_){
_start:
{
lean_inc(v_unordered_86_);
return v_unordered_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim___boxed(lean_object* v_motive_87_, lean_object* v_t_88_, lean_object* v_h_89_, lean_object* v_unordered_90_){
_start:
{
uint8_t v_t_boxed_91_; lean_object* v_res_92_; 
v_t_boxed_91_ = lean_unbox(v_t_88_);
v_res_92_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_unordered_elim(v_motive_87_, v_t_boxed_91_, v_h_89_, v_unordered_90_);
lean_dec(v_unordered_90_);
return v_res_92_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(uint8_t v_x_93_, uint8_t v_y_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_95_ = lean_box(v_x_93_);
v___x_96_ = lean_obj_tag_nat(v___x_95_);
lean_dec(v___x_95_);
v___x_97_ = lean_box(v_y_94_);
v___x_98_ = lean_obj_tag_nat(v___x_97_);
lean_dec(v___x_97_);
v___x_99_ = lean_nat_dec_eq(v___x_96_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed(lean_object* v_x_100_, lean_object* v_y_101_){
_start:
{
uint8_t v_x_24__boxed_102_; uint8_t v_y_25__boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v_x_24__boxed_102_ = lean_unbox(v_x_100_);
v_y_25__boxed_103_ = lean_unbox(v_y_101_);
v_res_104_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v_x_24__boxed_102_, v_y_25__boxed_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(lean_object* v_stx_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Doc_BlockView_of(v_stx_114_);
if (lean_obj_tag(v___x_115_) == 1)
{
lean_object* v_val_116_; 
v_val_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v___x_115_, 1);
switch(lean_obj_tag(v_val_116_))
{
case 1:
{
lean_object* v___x_117_; 
lean_dec_ref_known(v_val_116_, 1);
v___x_117_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0));
return v___x_117_;
}
case 2:
{
lean_object* v___x_118_; 
lean_dec_ref_known(v_val_116_, 1);
v___x_118_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1));
return v___x_118_;
}
default: 
{
lean_object* v___x_119_; 
lean_dec(v_val_116_);
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
}
else
{
lean_object* v___x_120_; 
lean_dec(v___x_115_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(lean_object* v_prev_x3f_121_, lean_object* v_stx_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(v_stx_122_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
else
{
lean_object* v_val_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_143_; 
v_val_125_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_143_ == 0)
{
v___x_127_ = v___x_123_;
v_isShared_128_ = v_isSharedCheck_143_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_val_125_);
lean_dec(v___x_123_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_143_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
uint8_t v___y_130_; 
if (lean_obj_tag(v_prev_x3f_121_) == 0)
{
uint8_t v___x_136_; 
v___x_136_ = 0;
v___y_130_ = v___x_136_;
goto v___jp_129_;
}
else
{
lean_object* v_val_137_; uint8_t v_kind_138_; uint8_t v_alternate_139_; uint8_t v___x_140_; uint8_t v___x_141_; 
v_val_137_ = lean_ctor_get(v_prev_x3f_121_, 0);
v_kind_138_ = lean_ctor_get_uint8(v_val_137_, 0);
v_alternate_139_ = lean_ctor_get_uint8(v_val_137_, 1);
v___x_140_ = lean_unbox(v_val_125_);
v___x_141_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v___x_140_, v_kind_138_);
if (v___x_141_ == 0)
{
v___y_130_ = v___x_141_;
goto v___jp_129_;
}
else
{
if (v_alternate_139_ == 0)
{
v___y_130_ = v___x_141_;
goto v___jp_129_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = 0;
v___y_130_ = v___x_142_;
goto v___jp_129_;
}
}
}
v___jp_129_:
{
lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_134_; 
v___x_131_ = lean_alloc_ctor(0, 0, 2);
v___x_132_ = lean_unbox(v_val_125_);
lean_dec(v_val_125_);
lean_ctor_set_uint8(v___x_131_, 0, v___x_132_);
lean_ctor_set_uint8(v___x_131_, 1, v___y_130_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_131_);
v___x_134_ = v___x_127_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_131_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor___boxed(lean_object* v_prev_x3f_144_, lean_object* v_stx_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_prev_x3f_144_, v_stx_145_);
lean_dec(v_prev_x3f_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(lean_object* v_s_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_box(0);
v___x_150_ = lean_string_append(v_a_148_, v_s_147_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg___boxed(lean_object* v_s_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_152_, v_a_153_);
lean_dec_ref(v_s_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(lean_object* v_s_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_155_, v_a_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___boxed(lean_object* v_s_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(v_s_159_, v_a_160_, v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_s_159_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_zero_165_; uint8_t v_isZero_166_; 
v_zero_165_ = lean_unsigned_to_nat(0u);
v_isZero_166_ = lean_nat_dec_eq(v_x_163_, v_zero_165_);
if (v_isZero_166_ == 1)
{
lean_dec(v_x_163_);
return v_x_164_;
}
else
{
uint32_t v___x_167_; lean_object* v_one_168_; lean_object* v_n_169_; lean_object* v___x_170_; 
v___x_167_ = 32;
v_one_168_ = lean_unsigned_to_nat(1u);
v_n_169_ = lean_nat_sub(v_x_163_, v_one_168_);
lean_dec(v_x_163_);
v___x_170_ = lean_string_push(v_x_164_, v___x_167_);
v_x_163_ = v_n_169_;
v_x_164_ = v___x_170_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_string_utf8_byte_size(v_a_175_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v___x_179_);
if (v___x_181_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_182_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_nat_sub(v___x_179_, v___x_180_);
v___x_185_ = lean_string_memcmp(v_a_175_, v___x_182_, v___x_184_, v___x_183_, v___x_180_);
lean_dec(v___x_184_);
if (v___x_185_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
lean_inc(v_a_174_);
v___x_187_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_174_, v___x_186_);
v___x_188_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_187_, v_a_175_);
lean_dec_ref(v___x_187_);
return v___x_188_;
}
}
v___jp_176_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_box(0);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v_a_175_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___boxed(lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_189_, v_a_190_);
lean_dec(v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(uint8_t v___x_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v___x_195_, lean_object* v_a_196_, uint8_t v_b_197_){
_start:
{
lean_object* v___x_198_; uint8_t v_decide_199_; 
v___x_198_ = lean_nat_sub(v___x_193_, v___x_194_);
v_decide_199_ = lean_nat_dec_eq(v_a_196_, v___x_198_);
lean_dec(v___x_198_);
if (v_decide_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_nat_add(v___x_194_, v_a_196_);
lean_dec(v_a_196_);
v___x_201_ = lean_string_utf8_next_fast(v___x_195_, v___x_200_);
lean_dec(v___x_200_);
v___x_202_ = lean_nat_sub(v___x_201_, v___x_194_);
if (v_b_197_ == 0)
{
{
lean_object* _tmp_4 = v___x_202_;
uint8_t _tmp_5 = v___x_192_;
v_a_196_ = _tmp_4;
v_b_197_ = _tmp_5;
}
goto _start;
}
else
{
v_a_196_ = v___x_202_;
v_b_197_ = v_decide_199_;
goto _start;
}
}
else
{
lean_dec(v_a_196_);
return v_b_197_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg___boxed(lean_object* v___x_205_, lean_object* v___x_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
uint8_t v___x_1744__boxed_211_; uint8_t v_b_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v___x_1744__boxed_211_ = lean_unbox(v___x_205_);
v_b_boxed_212_ = lean_unbox(v_b_210_);
v_res_213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_1744__boxed_211_, v___x_206_, v___x_207_, v___x_208_, v_a_209_, v_b_boxed_212_);
lean_dec_ref(v___x_208_);
lean_dec(v___x_207_);
lean_dec(v___x_206_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(lean_object* v_s_215_, lean_object* v_pos_216_){
_start:
{
lean_object* v_str_217_; lean_object* v_startInclusive_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v_decide_222_; 
v_str_217_ = lean_ctor_get(v_s_215_, 0);
v_startInclusive_218_ = lean_ctor_get(v_s_215_, 1);
v___x_219_ = lean_nat_add(v_startInclusive_218_, v_pos_216_);
v___x_220_ = lean_nat_sub(v___x_219_, v_startInclusive_218_);
v___x_221_ = lean_unsigned_to_nat(0u);
v_decide_222_ = lean_nat_dec_eq(v___x_220_, v___x_221_);
if (v_decide_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint32_t v___x_228_; uint32_t v___x_229_; uint8_t v___x_230_; 
lean_inc(v_startInclusive_218_);
lean_inc_ref(v_str_217_);
v___x_223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_223_, 0, v_str_217_);
lean_ctor_set(v___x_223_, 1, v_startInclusive_218_);
lean_ctor_set(v___x_223_, 2, v___x_219_);
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_sub(v___x_220_, v___x_224_);
lean_dec(v___x_220_);
v___x_226_ = l_String_Slice_posLE(v___x_223_, v___x_225_);
lean_dec_ref_known(v___x_223_, 3);
v___x_227_ = lean_nat_add(v_startInclusive_218_, v___x_226_);
v___x_228_ = lean_string_utf8_get_fast(v_str_217_, v___x_227_);
lean_dec(v___x_227_);
v___x_229_ = 92;
v___x_230_ = lean_uint32_dec_eq(v___x_228_, v___x_229_);
if (v___x_230_ == 0)
{
lean_dec(v___x_226_);
return v_pos_216_;
}
else
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_nat_add(v___x_226_, v___x_224_);
v___x_232_ = lean_nat_dec_le(v___x_231_, v_pos_216_);
lean_dec(v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v___x_226_);
return v_pos_216_;
}
else
{
lean_dec(v_pos_216_);
v_pos_216_ = v___x_226_;
goto _start;
}
}
}
else
{
lean_dec(v___x_220_);
lean_dec(v___x_219_);
return v_pos_216_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0___boxed(lean_object* v_s_234_, lean_object* v_pos_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v_s_234_, v_pos_235_);
lean_dec_ref(v_s_234_);
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(lean_object* v_s_237_){
_start:
{
lean_object* v_str_238_; lean_object* v_startInclusive_239_; lean_object* v_endExclusive_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_str_238_ = lean_ctor_get(v_s_237_, 0);
lean_inc_ref(v_str_238_);
v_startInclusive_239_ = lean_ctor_get(v_s_237_, 1);
lean_inc(v_startInclusive_239_);
v_endExclusive_240_ = lean_ctor_get(v_s_237_, 2);
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_sub(v_endExclusive_240_, v_startInclusive_239_);
v___x_243_ = lean_nat_dec_le(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v___x_242_);
lean_dec(v_startInclusive_239_);
lean_dec_ref(v_str_238_);
lean_dec_ref(v_s_237_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_244_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_sub(v___x_242_, v___x_241_);
v___x_247_ = lean_nat_add(v_startInclusive_239_, v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = lean_string_memcmp(v_str_238_, v___x_244_, v___x_247_, v___x_245_, v___x_241_);
lean_dec(v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v___x_242_);
lean_dec(v_startInclusive_239_);
lean_dec_ref(v_str_238_);
lean_dec_ref(v_s_237_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_262_; 
v___x_249_ = l_String_Slice_Pos_prevn(v_s_237_, v___x_242_, v___x_241_);
v_isSharedCheck_262_ = !lean_is_exclusive(v_s_237_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; lean_object* v_unused_264_; lean_object* v_unused_265_; 
v_unused_263_ = lean_ctor_get(v_s_237_, 2);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_s_237_, 1);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_s_237_, 0);
lean_dec(v_unused_265_);
v___x_251_ = v_s_237_;
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
else
{
lean_dec(v_s_237_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_262_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_nat_add(v_startInclusive_239_, v___x_249_);
lean_dec(v___x_249_);
lean_inc(v___x_253_);
lean_inc(v_startInclusive_239_);
lean_inc_ref(v_str_238_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 2, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_str_238_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_startInclusive_239_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v___x_253_);
v___x_255_ = v_reuseFailAlloc_261_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; uint8_t v___x_260_; 
v___x_256_ = lean_nat_sub(v___x_253_, v_startInclusive_239_);
v___x_257_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v___x_255_, v___x_256_);
lean_dec_ref(v___x_255_);
v___x_258_ = lean_nat_add(v_startInclusive_239_, v___x_257_);
lean_dec(v___x_257_);
lean_dec(v_startInclusive_239_);
v___x_259_ = 0;
v___x_260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_248_, v___x_253_, v___x_258_, v_str_238_, v___x_245_, v___x_259_);
lean_dec_ref(v_str_238_);
lean_dec(v___x_258_);
lean_dec(v___x_253_);
return v___x_260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline___boxed(lean_object* v_s_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_266_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(uint8_t v___x_269_, lean_object* v___x_270_, lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v___x_273_, lean_object* v_inst_274_, lean_object* v_R_275_, lean_object* v_a_276_, uint8_t v_b_277_, lean_object* v_c_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_269_, v___x_270_, v___x_271_, v___x_273_, v_a_276_, v_b_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___boxed(lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v___x_282_, lean_object* v___x_283_, lean_object* v___x_284_, lean_object* v_inst_285_, lean_object* v_R_286_, lean_object* v_a_287_, lean_object* v_b_288_, lean_object* v_c_289_){
_start:
{
uint8_t v___x_1851__boxed_290_; uint8_t v_b_boxed_291_; uint8_t v_res_292_; lean_object* v_r_293_; 
v___x_1851__boxed_290_ = lean_unbox(v___x_280_);
v_b_boxed_291_ = lean_unbox(v_b_288_);
v_res_292_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(v___x_1851__boxed_290_, v___x_281_, v___x_282_, v___x_283_, v___x_284_, v_inst_285_, v_R_286_, v_a_287_, v_b_boxed_291_, v_c_289_);
lean_dec_ref(v___x_284_);
lean_dec_ref(v___x_283_);
lean_dec(v___x_282_);
lean_dec(v___x_281_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(lean_object* v_s_294_){
_start:
{
lean_object* v_str_295_; lean_object* v_startInclusive_296_; lean_object* v_endExclusive_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v_str_295_ = lean_ctor_get(v_s_294_, 0);
lean_inc_ref(v_str_295_);
v_startInclusive_296_ = lean_ctor_get(v_s_294_, 1);
lean_inc(v_startInclusive_296_);
v_endExclusive_297_ = lean_ctor_get(v_s_294_, 2);
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_nat_sub(v_endExclusive_297_, v_startInclusive_296_);
v___x_300_ = lean_nat_dec_le(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec(v___x_299_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
lean_dec_ref(v_s_294_);
v___x_301_ = lean_unsigned_to_nat(0u);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_302_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_nat_sub(v___x_299_, v___x_298_);
v___x_305_ = lean_nat_add(v_startInclusive_296_, v___x_304_);
lean_dec(v___x_304_);
v___x_306_ = lean_string_memcmp(v_str_295_, v___x_302_, v___x_305_, v___x_303_, v___x_298_);
lean_dec(v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v___x_299_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
lean_dec_ref(v_s_294_);
return v___x_303_;
}
else
{
uint8_t v___x_307_; 
lean_inc_ref(v_s_294_);
v___x_307_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_294_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_323_; 
v___x_308_ = l_String_Slice_Pos_prevn(v_s_294_, v___x_299_, v___x_298_);
v_isSharedCheck_323_ = !lean_is_exclusive(v_s_294_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; lean_object* v_unused_325_; lean_object* v_unused_326_; 
v_unused_324_ = lean_ctor_get(v_s_294_, 2);
lean_dec(v_unused_324_);
v_unused_325_ = lean_ctor_get(v_s_294_, 1);
lean_dec(v_unused_325_);
v_unused_326_ = lean_ctor_get(v_s_294_, 0);
lean_dec(v_unused_326_);
v___x_310_ = v_s_294_;
v_isShared_311_ = v_isSharedCheck_323_;
goto v_resetjp_309_;
}
else
{
lean_dec(v_s_294_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_323_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_312_ = lean_nat_add(v_startInclusive_296_, v___x_308_);
lean_dec(v___x_308_);
v___x_313_ = lean_nat_sub(v___x_312_, v_startInclusive_296_);
v___x_314_ = lean_nat_dec_le(v___x_298_, v___x_313_);
if (v___x_314_ == 0)
{
lean_dec(v___x_313_);
lean_dec(v___x_312_);
lean_del_object(v___x_310_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
return v___x_298_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_nat_sub(v___x_313_, v___x_298_);
lean_dec(v___x_313_);
v___x_316_ = lean_nat_add(v_startInclusive_296_, v___x_315_);
lean_dec(v___x_315_);
v___x_317_ = lean_string_memcmp(v_str_295_, v___x_302_, v___x_316_, v___x_303_, v___x_298_);
lean_dec(v___x_316_);
if (v___x_317_ == 0)
{
lean_dec(v___x_312_);
lean_del_object(v___x_310_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
return v___x_298_;
}
else
{
if (v___x_307_ == 0)
{
lean_object* v_s_319_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 2, v___x_312_);
v_s_319_ = v___x_310_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_str_295_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_startInclusive_296_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v___x_312_);
v_s_319_ = v_reuseFailAlloc_322_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
uint8_t v___x_320_; 
v___x_320_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_unsigned_to_nat(2u);
return v___x_321_;
}
else
{
return v___x_298_;
}
}
}
else
{
lean_dec(v___x_312_);
lean_del_object(v___x_310_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
return v___x_298_;
}
}
}
}
}
else
{
lean_dec(v___x_299_);
lean_dec(v_startInclusive_296_);
lean_dec_ref(v_str_295_);
lean_dec_ref(v_s_294_);
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_zero_329_; uint8_t v_isZero_330_; 
v_zero_329_ = lean_unsigned_to_nat(0u);
v_isZero_330_ = lean_nat_dec_eq(v_x_327_, v_zero_329_);
if (v_isZero_330_ == 1)
{
lean_dec(v_x_327_);
return v_x_328_;
}
else
{
uint32_t v___x_331_; lean_object* v_one_332_; lean_object* v_n_333_; lean_object* v___x_334_; 
v___x_331_ = 10;
v_one_332_ = lean_unsigned_to_nat(1u);
v_n_333_ = lean_nat_sub(v_x_327_, v_one_332_);
lean_dec(v_x_327_);
v___x_334_ = lean_string_push(v_x_328_, v___x_331_);
v_x_327_ = v_n_333_;
v_x_328_ = v___x_334_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_337_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_string_utf8_byte_size(v_a_336_);
lean_inc_ref(v_a_336_);
v___x_341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_341_, 0, v_a_336_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_ctor_set(v___x_341_, 2, v___x_340_);
v___x_342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(v___x_341_);
v___x_343_ = lean_nat_sub(v___x_338_, v___x_342_);
lean_dec(v___x_342_);
v___x_344_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_343_, v___x_337_);
v___x_345_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_344_, v_a_336_);
lean_dec_ref(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_a_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___boxed(lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(v_a_349_, v_a_350_);
lean_dec(v_a_349_);
return v_res_351_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(uint32_t v_a_352_){
_start:
{
uint32_t v___x_353_; uint8_t v___x_354_; 
v___x_353_ = 92;
v___x_354_ = lean_uint32_dec_eq(v_a_352_, v___x_353_);
if (v___x_354_ == 0)
{
uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 42;
v___x_356_ = lean_uint32_dec_eq(v_a_352_, v___x_355_);
if (v___x_356_ == 0)
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 95;
v___x_358_ = lean_uint32_dec_eq(v_a_352_, v___x_357_);
if (v___x_358_ == 0)
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 91;
v___x_360_ = lean_uint32_dec_eq(v_a_352_, v___x_359_);
if (v___x_360_ == 0)
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 93;
v___x_362_ = lean_uint32_dec_eq(v_a_352_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 123;
v___x_364_ = lean_uint32_dec_eq(v_a_352_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 125;
v___x_366_ = lean_uint32_dec_eq(v_a_352_, v___x_365_);
if (v___x_366_ == 0)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 96;
v___x_368_ = lean_uint32_dec_eq(v_a_352_, v___x_367_);
if (v___x_368_ == 0)
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 33;
v___x_370_ = lean_uint32_dec_eq(v_a_352_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 36;
v___x_372_ = lean_uint32_dec_eq(v_a_352_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 10;
v___x_374_ = lean_uint32_dec_eq(v_a_352_, v___x_373_);
return v___x_374_;
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
else
{
return v___x_360_;
}
}
else
{
return v___x_358_;
}
}
else
{
return v___x_356_;
}
}
else
{
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial___boxed(lean_object* v_a_375_){
_start:
{
uint32_t v_a_242__boxed_376_; uint8_t v_res_377_; lean_object* v_r_378_; 
v_a_242__boxed_376_ = lean_unbox_uint32(v_a_375_);
lean_dec(v_a_375_);
v_res_377_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v_a_242__boxed_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(lean_object* v___x_379_, lean_object* v_value_380_, lean_object* v_a_381_, lean_object* v_b_382_){
_start:
{
uint8_t v_decide_383_; 
v_decide_383_ = lean_nat_dec_eq(v_a_381_, v___x_379_);
if (v_decide_383_ == 0)
{
uint32_t v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_384_ = lean_string_utf8_get_fast(v_value_380_, v_a_381_);
v___x_385_ = lean_string_utf8_next_fast(v_value_380_, v_a_381_);
lean_dec(v_a_381_);
v___x_386_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v___x_384_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_string_push(v_b_382_, v___x_384_);
v_a_381_ = v___x_385_;
v_b_382_ = v___x_387_;
goto _start;
}
else
{
uint32_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = 92;
v___x_390_ = lean_string_push(v_b_382_, v___x_389_);
v___x_391_ = lean_string_push(v___x_390_, v___x_384_);
v_a_381_ = v___x_385_;
v_b_382_ = v___x_391_;
goto _start;
}
}
else
{
lean_dec(v_a_381_);
return v_b_382_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg___boxed(lean_object* v___x_393_, lean_object* v_value_394_, lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_393_, v_value_394_, v_a_395_, v_b_396_);
lean_dec_ref(v_value_394_);
lean_dec(v___x_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(lean_object* v_value_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_399_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_400_ = lean_string_utf8_byte_size(v_value_398_);
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_400_, v_value_398_, v___x_401_, v___x_399_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped___boxed(lean_object* v_value_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_403_);
lean_dec_ref(v_value_403_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(lean_object* v___x_405_, lean_object* v___x_406_, lean_object* v_value_407_, lean_object* v_inst_408_, lean_object* v_R_409_, lean_object* v_a_410_, lean_object* v_b_411_, lean_object* v_c_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_406_, v_value_407_, v_a_410_, v_b_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___boxed(lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_value_416_, lean_object* v_inst_417_, lean_object* v_R_418_, lean_object* v_a_419_, lean_object* v_b_420_, lean_object* v_c_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(v___x_414_, v___x_415_, v_value_416_, v_inst_417_, v_R_418_, v_a_419_, v_b_420_, v_c_421_);
lean_dec_ref(v_value_416_);
lean_dec(v___x_415_);
lean_dec_ref(v___x_414_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(lean_object* v_s_423_, lean_object* v_pos_424_){
_start:
{
lean_object* v_str_425_; lean_object* v_startInclusive_426_; lean_object* v_endExclusive_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v_decide_431_; 
v_str_425_ = lean_ctor_get(v_s_423_, 0);
v_startInclusive_426_ = lean_ctor_get(v_s_423_, 1);
v_endExclusive_427_ = lean_ctor_get(v_s_423_, 2);
v___x_428_ = lean_nat_add(v_startInclusive_426_, v_pos_424_);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_nat_sub(v_endExclusive_427_, v___x_428_);
v_decide_431_ = lean_nat_dec_eq(v___x_429_, v___x_430_);
lean_dec(v___x_430_);
if (v_decide_431_ == 0)
{
uint32_t v___x_432_; uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_432_ = lean_string_utf8_get_fast(v_str_425_, v___x_428_);
v___x_433_ = 48;
v___x_434_ = lean_uint32_dec_le(v___x_433_, v___x_432_);
if (v___x_434_ == 0)
{
lean_dec(v___x_428_);
return v_pos_424_;
}
else
{
uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_435_ = 57;
v___x_436_ = lean_uint32_dec_le(v___x_432_, v___x_435_);
if (v___x_436_ == 0)
{
lean_dec(v___x_428_);
return v_pos_424_;
}
else
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_437_ = lean_string_utf8_next_fast(v_str_425_, v___x_428_);
v___x_438_ = lean_nat_sub(v___x_437_, v___x_428_);
lean_dec(v___x_428_);
v___x_439_ = lean_nat_add(v_pos_424_, v___x_438_);
lean_dec(v___x_438_);
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_pos_424_, v___x_440_);
v___x_442_ = lean_nat_dec_le(v___x_441_, v___x_439_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
lean_dec(v___x_439_);
return v_pos_424_;
}
else
{
lean_dec(v_pos_424_);
v_pos_424_ = v___x_439_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_428_);
return v_pos_424_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0___boxed(lean_object* v_s_444_, lean_object* v_pos_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v_s_444_, v_pos_445_);
lean_dec_ref(v_s_444_);
return v_res_446_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(lean_object* v_text_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_afterDigits_465_; uint8_t v___y_467_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_string_utf8_byte_size(v_text_460_);
lean_inc_ref_n(v_text_460_, 2);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v_text_460_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
v___x_464_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v___x_463_, v___x_461_);
lean_inc(v___x_464_);
v_afterDigits_465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_afterDigits_465_, 0, v_text_460_);
lean_ctor_set(v_afterDigits_465_, 1, v___x_464_);
lean_ctor_set(v_afterDigits_465_, 2, v___x_462_);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_dec_le(v___x_542_, v___x_462_);
if (v___x_543_ == 0)
{
goto v___jp_537_;
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_545_ = lean_string_memcmp(v_text_460_, v___x_544_, v___x_461_, v___x_461_, v___x_542_);
if (v___x_545_ == 0)
{
goto v___jp_537_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_545_;
}
}
v___jp_466_:
{
if (v___y_467_ == 0)
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___y_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_String_Slice_Pos_nextn(v_afterDigits_465_, v___x_461_, v___x_468_);
lean_dec_ref_known(v_afterDigits_465_, 3);
v___x_470_ = lean_nat_add(v___x_464_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_464_);
v___x_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_471_, 0, v_text_460_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
lean_ctor_set(v___x_471_, 2, v___x_462_);
v___x_472_ = l_String_Slice_Pos_get_x3f(v___x_471_, v___x_461_);
lean_dec_ref_known(v___x_471_, 3);
if (lean_obj_tag(v___x_472_) == 0)
{
return v___y_467_;
}
else
{
lean_object* v_val_473_; uint32_t v___x_474_; uint32_t v___x_475_; uint8_t v___x_476_; 
v_val_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v___x_472_, 1);
v___x_474_ = 32;
v___x_475_ = lean_unbox_uint32(v_val_473_);
lean_dec(v_val_473_);
v___x_476_ = lean_uint32_dec_eq(v___x_475_, v___x_474_);
return v___x_476_;
}
}
}
v___jp_477_:
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_sub(v___x_462_, v___x_464_);
v___x_480_ = lean_nat_dec_le(v___x_478_, v___x_479_);
lean_dec(v___x_479_);
if (v___x_480_ == 0)
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_482_ = lean_string_memcmp(v_text_460_, v___x_481_, v___x_464_, v___x_461_, v___x_478_);
v___y_467_ = v___x_482_;
goto v___jp_466_;
}
}
v___jp_483_:
{
lean_object* v___x_484_; 
v___x_484_ = l_String_Slice_Pos_get_x3f(v___x_463_, v___x_461_);
lean_dec_ref_known(v___x_463_, 3);
if (lean_obj_tag(v___x_484_) == 0)
{
uint8_t v___x_485_; 
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
v___x_485_ = 0;
return v___x_485_;
}
else
{
lean_object* v_val_486_; uint32_t v___x_487_; uint32_t v___x_488_; uint8_t v___x_489_; 
v_val_486_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v___x_484_, 1);
v___x_487_ = 48;
v___x_488_ = lean_unbox_uint32(v_val_486_);
v___x_489_ = lean_uint32_dec_le(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v_val_486_);
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___x_489_;
}
else
{
uint32_t v___x_490_; uint32_t v___x_491_; uint8_t v___x_492_; 
v___x_490_ = 57;
v___x_491_ = lean_unbox_uint32(v_val_486_);
lean_dec(v_val_486_);
v___x_492_ = lean_uint32_dec_le(v___x_491_, v___x_490_);
if (v___x_492_ == 0)
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_sub(v___x_462_, v___x_464_);
v___x_495_ = lean_nat_dec_le(v___x_493_, v___x_494_);
lean_dec(v___x_494_);
if (v___x_495_ == 0)
{
goto v___jp_477_;
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1));
v___x_497_ = lean_string_memcmp(v_text_460_, v___x_496_, v___x_464_, v___x_461_, v___x_493_);
if (v___x_497_ == 0)
{
goto v___jp_477_;
}
else
{
v___y_467_ = v___x_497_;
goto v___jp_466_;
}
}
}
}
}
}
v___jp_498_:
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_dec_le(v___x_499_, v___x_462_);
if (v___x_500_ == 0)
{
goto v___jp_483_;
}
else
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_502_ = lean_string_memcmp(v_text_460_, v___x_501_, v___x_461_, v___x_461_, v___x_499_);
if (v___x_502_ == 0)
{
goto v___jp_483_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_502_;
}
}
}
v___jp_503_:
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(3u);
v___x_505_ = lean_nat_dec_le(v___x_504_, v___x_462_);
if (v___x_505_ == 0)
{
goto v___jp_498_;
}
else
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3));
v___x_507_ = lean_string_memcmp(v_text_460_, v___x_506_, v___x_461_, v___x_461_, v___x_504_);
if (v___x_507_ == 0)
{
goto v___jp_498_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_507_;
}
}
}
v___jp_508_:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(2u);
v___x_510_ = lean_nat_dec_le(v___x_509_, v___x_462_);
if (v___x_510_ == 0)
{
goto v___jp_503_;
}
else
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_512_ = lean_string_memcmp(v_text_460_, v___x_511_, v___x_461_, v___x_461_, v___x_509_);
if (v___x_512_ == 0)
{
goto v___jp_503_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_512_;
}
}
}
v___jp_513_:
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___x_515_ = lean_string_dec_eq(v_text_460_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(2u);
v___x_517_ = lean_nat_dec_le(v___x_516_, v___x_462_);
if (v___x_517_ == 0)
{
goto v___jp_508_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_519_ = lean_string_memcmp(v_text_460_, v___x_518_, v___x_461_, v___x_461_, v___x_516_);
if (v___x_519_ == 0)
{
goto v___jp_508_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_519_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_515_;
}
}
v___jp_520_:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___x_522_ = lean_string_dec_eq(v_text_460_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_nat_dec_le(v___x_523_, v___x_462_);
if (v___x_524_ == 0)
{
goto v___jp_513_;
}
else
{
lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_525_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_526_ = lean_string_memcmp(v_text_460_, v___x_525_, v___x_461_, v___x_461_, v___x_523_);
if (v___x_526_ == 0)
{
goto v___jp_513_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_526_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_522_;
}
}
v___jp_527_:
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_dec_le(v___x_528_, v___x_462_);
if (v___x_529_ == 0)
{
goto v___jp_520_;
}
else
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___x_531_ = lean_string_memcmp(v_text_460_, v___x_530_, v___x_461_, v___x_461_, v___x_528_);
if (v___x_531_ == 0)
{
goto v___jp_520_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_531_;
}
}
}
v___jp_532_:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_dec_le(v___x_533_, v___x_462_);
if (v___x_534_ == 0)
{
goto v___jp_527_;
}
else
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_536_ = lean_string_memcmp(v_text_460_, v___x_535_, v___x_461_, v___x_461_, v___x_533_);
if (v___x_536_ == 0)
{
goto v___jp_527_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_536_;
}
}
}
v___jp_537_:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_dec_le(v___x_538_, v___x_462_);
if (v___x_539_ == 0)
{
goto v___jp_532_;
}
else
{
lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_541_ = lean_string_memcmp(v_text_460_, v___x_540_, v___x_461_, v___x_461_, v___x_538_);
if (v___x_541_ == 0)
{
goto v___jp_532_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object* v_text_546_){
_start:
{
uint8_t v_res_547_; lean_object* v_r_548_; 
v_res_547_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_text_546_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t v_atLineStart_550_, lean_object* v_value_551_){
_start:
{
lean_object* v_text_552_; 
v_text_552_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_551_);
if (v_atLineStart_550_ == 0)
{
lean_dec_ref(v_value_551_);
return v_text_552_;
}
else
{
uint8_t v___x_553_; 
v___x_553_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_value_551_);
if (v___x_553_ == 0)
{
return v_text_552_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_555_ = lean_string_append(v___x_554_, v_text_552_);
lean_dec_ref(v_text_552_);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object* v_atLineStart_556_, lean_object* v_value_557_){
_start:
{
uint8_t v_atLineStart_boxed_558_; lean_object* v_res_559_; 
v_atLineStart_boxed_558_ = lean_unbox(v_atLineStart_556_);
v_res_559_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_boxed_558_, v_value_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object* v_s_560_, lean_object* v_pos_561_){
_start:
{
lean_object* v_str_562_; lean_object* v_startInclusive_563_; lean_object* v_endExclusive_564_; lean_object* v___x_565_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v_decide_576_; 
v_str_562_ = lean_ctor_get(v_s_560_, 0);
v_startInclusive_563_ = lean_ctor_get(v_s_560_, 1);
v_endExclusive_564_ = lean_ctor_get(v_s_560_, 2);
v___x_565_ = lean_nat_add(v_startInclusive_563_, v_pos_561_);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_sub(v_endExclusive_564_, v___x_565_);
v_decide_576_ = lean_nat_dec_eq(v___x_574_, v___x_575_);
lean_dec(v___x_575_);
if (v_decide_576_ == 0)
{
uint32_t v___x_577_; uint32_t v___x_578_; uint8_t v___x_579_; 
v___x_577_ = lean_string_utf8_get_fast(v_str_562_, v___x_565_);
v___x_578_ = 32;
v___x_579_ = lean_uint32_dec_eq(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
uint32_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 9;
v___x_581_ = lean_uint32_dec_eq(v___x_577_, v___x_580_);
if (v___x_581_ == 0)
{
uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 13;
v___x_583_ = lean_uint32_dec_eq(v___x_577_, v___x_582_);
if (v___x_583_ == 0)
{
uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_584_ = 10;
v___x_585_ = lean_uint32_dec_eq(v___x_577_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v___x_565_);
return v_pos_561_;
}
else
{
goto v___jp_566_;
}
}
else
{
goto v___jp_566_;
}
}
else
{
goto v___jp_566_;
}
}
else
{
goto v___jp_566_;
}
}
else
{
lean_dec(v___x_565_);
return v_pos_561_;
}
v___jp_566_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_567_ = lean_string_utf8_next_fast(v_str_562_, v___x_565_);
v___x_568_ = lean_nat_sub(v___x_567_, v___x_565_);
lean_dec(v___x_565_);
v___x_569_ = lean_nat_add(v_pos_561_, v___x_568_);
lean_dec(v___x_568_);
v___x_570_ = lean_unsigned_to_nat(1u);
v___x_571_ = lean_nat_add(v_pos_561_, v___x_570_);
v___x_572_ = lean_nat_dec_le(v___x_571_, v___x_569_);
lean_dec(v___x_571_);
if (v___x_572_ == 0)
{
lean_dec(v___x_569_);
return v_pos_561_;
}
else
{
lean_dec(v_pos_561_);
v_pos_561_ = v___x_569_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object* v_s_586_, lean_object* v_pos_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_586_, v_pos_587_);
lean_dec_ref(v_s_586_);
return v_res_588_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object* v_s_589_){
_start:
{
lean_object* v_startInclusive_590_; lean_object* v_endExclusive_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v_decide_595_; 
v_startInclusive_590_ = lean_ctor_get(v_s_589_, 1);
v_endExclusive_591_ = lean_ctor_get(v_s_589_, 2);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_589_, v___x_592_);
v___x_594_ = lean_nat_sub(v_endExclusive_591_, v_startInclusive_590_);
v_decide_595_ = lean_nat_dec_eq(v___x_593_, v___x_594_);
lean_dec(v___x_594_);
lean_dec(v___x_593_);
return v_decide_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object* v_s_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v_s_596_);
lean_dec_ref(v_s_596_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object* v_s_599_, lean_object* v_a_600_, lean_object* v_b_601_){
_start:
{
lean_object* v_str_602_; lean_object* v_startInclusive_603_; lean_object* v_endExclusive_604_; lean_object* v___x_605_; uint8_t v_decide_606_; 
v_str_602_ = lean_ctor_get(v_s_599_, 0);
v_startInclusive_603_ = lean_ctor_get(v_s_599_, 1);
v_endExclusive_604_ = lean_ctor_get(v_s_599_, 2);
v___x_605_ = lean_nat_sub(v_endExclusive_604_, v_startInclusive_603_);
v_decide_606_ = lean_nat_dec_eq(v_a_600_, v___x_605_);
lean_dec(v___x_605_);
if (v_decide_606_ == 0)
{
lean_object* v___x_607_; uint32_t v___x_608_; uint32_t v___x_609_; uint8_t v___x_610_; 
v___x_607_ = lean_nat_add(v_startInclusive_603_, v_a_600_);
lean_dec(v_a_600_);
v___x_608_ = lean_string_utf8_get_fast(v_str_602_, v___x_607_);
v___x_609_ = 32;
v___x_610_ = lean_uint32_dec_eq(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_dec(v___x_607_);
return v_b_601_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_string_utf8_next_fast(v_str_602_, v___x_607_);
lean_dec(v___x_607_);
v___x_612_ = lean_nat_sub(v___x_611_, v_startInclusive_603_);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_b_601_, v___x_613_);
lean_dec(v_b_601_);
v_a_600_ = v___x_612_;
v_b_601_ = v___x_614_;
goto _start;
}
}
else
{
lean_dec(v_a_600_);
return v_b_601_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object* v_s_616_, lean_object* v_a_617_, lean_object* v_b_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_616_, v_a_617_, v_b_618_);
lean_dec_ref(v_s_616_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object* v_s_620_){
_start:
{
lean_object* v_n_621_; lean_object* v___x_622_; 
v_n_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_620_, v_n_621_, v_n_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object* v_s_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v_s_623_);
lean_dec_ref(v_s_623_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object* v_s_625_, lean_object* v_inst_626_, lean_object* v_R_627_, lean_object* v_a_628_, lean_object* v_b_629_, lean_object* v_c_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_625_, v_a_628_, v_b_629_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object* v_s_632_, lean_object* v_inst_633_, lean_object* v_R_634_, lean_object* v_a_635_, lean_object* v_b_636_, lean_object* v_c_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(v_s_632_, v_inst_633_, v_R_634_, v_a_635_, v_b_636_, v_c_637_);
lean_dec_ref(v_s_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object* v___x_639_, lean_object* v___x_640_, lean_object* v_src_641_, lean_object* v___x_642_, lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
lean_object* v_it_646_; lean_object* v_out_647_; 
if (lean_obj_tag(v_a_643_) == 0)
{
lean_object* v_currPos_666_; lean_object* v_searcher_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_696_; 
v_currPos_666_ = lean_ctor_get(v_a_643_, 0);
v_searcher_667_ = lean_ctor_get(v_a_643_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_a_643_);
if (v_isSharedCheck_696_ == 0)
{
v___x_669_ = v_a_643_;
v_isShared_670_ = v_isSharedCheck_696_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_searcher_667_);
lean_inc(v_currPos_666_);
lean_dec(v_a_643_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_696_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_str_671_; lean_object* v_startInclusive_672_; lean_object* v_endExclusive_673_; lean_object* v___x_674_; uint8_t v_decide_675_; 
v_str_671_ = lean_ctor_get(v___x_639_, 0);
v_startInclusive_672_ = lean_ctor_get(v___x_639_, 1);
v_endExclusive_673_ = lean_ctor_get(v___x_639_, 2);
v___x_674_ = lean_nat_sub(v_endExclusive_673_, v_startInclusive_672_);
v_decide_675_ = lean_nat_dec_eq(v_searcher_667_, v___x_674_);
lean_dec(v___x_674_);
if (v_decide_675_ == 0)
{
uint32_t v___x_676_; lean_object* v___x_677_; uint32_t v___x_678_; uint8_t v___x_679_; 
v___x_676_ = 10;
v___x_677_ = lean_nat_add(v_startInclusive_672_, v_searcher_667_);
v___x_678_ = lean_string_utf8_get_fast(v_str_671_, v___x_677_);
v___x_679_ = lean_uint32_dec_eq(v___x_678_, v___x_676_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
lean_dec(v_searcher_667_);
v___x_680_ = lean_string_utf8_next_fast(v_str_671_, v___x_677_);
lean_dec(v___x_677_);
v___x_681_ = lean_nat_sub(v___x_680_, v_startInclusive_672_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_681_);
v___x_683_ = v___x_669_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_currPos_666_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_681_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
v_a_643_ = v___x_683_;
goto _start;
}
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_slice_689_; lean_object* v_nextIt_691_; 
v___x_686_ = lean_string_utf8_next_fast(v_str_671_, v___x_677_);
v___x_687_ = lean_nat_sub(v___x_686_, v___x_677_);
lean_dec(v___x_677_);
v___x_688_ = lean_nat_add(v_searcher_667_, v___x_687_);
lean_dec(v___x_687_);
lean_dec(v_searcher_667_);
lean_inc_ref(v___x_639_);
v_slice_689_ = l_String_Slice_slice_x21(v___x_639_, v_currPos_666_, v___x_688_);
lean_dec(v_currPos_666_);
lean_inc(v___x_688_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 1, v___x_688_);
lean_ctor_set(v___x_669_, 0, v___x_688_);
v_nextIt_691_ = v___x_669_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_688_);
v_nextIt_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
v_it_646_ = v_nextIt_691_;
v_out_647_ = v_slice_689_;
goto v___jp_645_;
}
}
}
else
{
uint8_t v_decide_693_; 
lean_del_object(v___x_669_);
lean_dec(v_searcher_667_);
v_decide_693_ = lean_nat_dec_eq(v_currPos_666_, v___x_640_);
if (v_decide_693_ == 0)
{
lean_object* v_slice_694_; lean_object* v___x_695_; 
lean_inc(v___x_642_);
lean_inc_ref(v_src_641_);
v_slice_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_694_, 0, v_src_641_);
lean_ctor_set(v_slice_694_, 1, v_currPos_666_);
lean_ctor_set(v_slice_694_, 2, v___x_642_);
v___x_695_ = lean_box(1);
v_it_646_ = v___x_695_;
v_out_647_ = v_slice_694_;
goto v___jp_645_;
}
else
{
lean_dec(v_currPos_666_);
lean_dec(v___x_642_);
lean_dec_ref(v_src_641_);
lean_dec_ref(v___x_639_);
return v_b_644_;
}
}
}
}
else
{
lean_dec(v___x_642_);
lean_dec_ref(v_src_641_);
lean_dec_ref(v___x_639_);
return v_b_644_;
}
v___jp_645_:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = l_String_Slice_lines_lineMap(v_out_647_);
v___x_649_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_648_);
lean_dec_ref(v___x_648_);
if (lean_obj_tag(v_b_644_) == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v_a_643_ = v_it_646_;
v_b_644_ = v___x_651_;
goto _start;
}
else
{
lean_object* v_val_653_; uint8_t v___x_654_; 
v_val_653_ = lean_ctor_get(v_b_644_, 0);
v___x_654_ = lean_nat_dec_le(v___x_650_, v_val_653_);
if (v___x_654_ == 0)
{
lean_dec(v___x_650_);
v_a_643_ = v_it_646_;
goto _start;
}
else
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_isSharedCheck_663_ = !lean_is_exclusive(v_b_644_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_b_644_, 0);
lean_dec(v_unused_664_);
v___x_657_ = v_b_644_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_b_644_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_650_);
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_650_);
v___x_660_ = v_reuseFailAlloc_662_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
v_a_643_ = v_it_646_;
v_b_644_ = v___x_660_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_648_);
v_a_643_ = v_it_646_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object* v___x_697_, lean_object* v___x_698_, lean_object* v_src_699_, lean_object* v___x_700_, lean_object* v_a_701_, lean_object* v_b_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_697_, v___x_698_, v_src_699_, v___x_700_, v_a_701_, v_b_702_);
lean_dec(v___x_698_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v_src_706_, lean_object* v___x_707_, lean_object* v_a_708_, lean_object* v_b_709_){
_start:
{
lean_object* v_it_711_; lean_object* v_out_712_; 
if (lean_obj_tag(v_a_708_) == 0)
{
lean_object* v_currPos_731_; lean_object* v_searcher_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_761_; 
v_currPos_731_ = lean_ctor_get(v_a_708_, 0);
v_searcher_732_ = lean_ctor_get(v_a_708_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_761_ == 0)
{
v___x_734_ = v_a_708_;
v_isShared_735_ = v_isSharedCheck_761_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_searcher_732_);
lean_inc(v_currPos_731_);
lean_dec(v_a_708_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_761_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_str_736_; lean_object* v_startInclusive_737_; lean_object* v_endExclusive_738_; lean_object* v___x_739_; uint8_t v_decide_740_; 
v_str_736_ = lean_ctor_get(v___x_704_, 0);
v_startInclusive_737_ = lean_ctor_get(v___x_704_, 1);
v_endExclusive_738_ = lean_ctor_get(v___x_704_, 2);
v___x_739_ = lean_nat_sub(v_endExclusive_738_, v_startInclusive_737_);
v_decide_740_ = lean_nat_dec_eq(v_searcher_732_, v___x_739_);
lean_dec(v___x_739_);
if (v_decide_740_ == 0)
{
lean_object* v___x_741_; uint32_t v___x_742_; uint32_t v___x_743_; uint8_t v___x_744_; 
v___x_741_ = lean_nat_add(v_startInclusive_737_, v_searcher_732_);
v___x_742_ = lean_string_utf8_get_fast(v_str_736_, v___x_741_);
v___x_743_ = 10;
v___x_744_ = lean_uint32_dec_eq(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec(v_searcher_732_);
v___x_745_ = lean_string_utf8_next_fast(v_str_736_, v___x_741_);
lean_dec(v___x_741_);
v___x_746_ = lean_nat_sub(v___x_745_, v_startInclusive_737_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_746_);
v___x_748_ = v___x_734_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_currPos_731_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_750_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; 
v___x_749_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_704_, v___x_705_, v_src_706_, v___x_707_, v___x_748_, v_b_709_);
return v___x_749_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_slice_754_; lean_object* v_nextIt_756_; 
v___x_751_ = lean_string_utf8_next_fast(v_str_736_, v___x_741_);
v___x_752_ = lean_nat_sub(v___x_751_, v___x_741_);
lean_dec(v___x_741_);
v___x_753_ = lean_nat_add(v_searcher_732_, v___x_752_);
lean_dec(v___x_752_);
lean_dec(v_searcher_732_);
lean_inc_ref(v___x_704_);
v_slice_754_ = l_String_Slice_slice_x21(v___x_704_, v_currPos_731_, v___x_753_);
lean_dec(v_currPos_731_);
lean_inc(v___x_753_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v___x_753_);
lean_ctor_set(v___x_734_, 0, v___x_753_);
v_nextIt_756_ = v___x_734_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_753_);
v_nextIt_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v_it_711_ = v_nextIt_756_;
v_out_712_ = v_slice_754_;
goto v___jp_710_;
}
}
}
else
{
uint8_t v_decide_758_; 
lean_del_object(v___x_734_);
lean_dec(v_searcher_732_);
v_decide_758_ = lean_nat_dec_eq(v_currPos_731_, v___x_705_);
if (v_decide_758_ == 0)
{
lean_object* v_slice_759_; lean_object* v___x_760_; 
lean_inc(v___x_707_);
lean_inc_ref(v_src_706_);
v_slice_759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_759_, 0, v_src_706_);
lean_ctor_set(v_slice_759_, 1, v_currPos_731_);
lean_ctor_set(v_slice_759_, 2, v___x_707_);
v___x_760_ = lean_box(1);
v_it_711_ = v___x_760_;
v_out_712_ = v_slice_759_;
goto v___jp_710_;
}
else
{
lean_dec(v_currPos_731_);
lean_dec(v___x_707_);
lean_dec_ref(v_src_706_);
lean_dec_ref(v___x_704_);
return v_b_709_;
}
}
}
}
else
{
lean_dec(v___x_707_);
lean_dec_ref(v_src_706_);
lean_dec_ref(v___x_704_);
return v_b_709_;
}
v___jp_710_:
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = l_String_Slice_lines_lineMap(v_out_712_);
v___x_714_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_713_);
lean_dec_ref(v___x_713_);
if (lean_obj_tag(v_b_709_) == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___x_717_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_704_, v___x_705_, v_src_706_, v___x_707_, v_it_711_, v___x_716_);
return v___x_717_;
}
else
{
lean_object* v_val_718_; uint8_t v___x_719_; 
v_val_718_ = lean_ctor_get(v_b_709_, 0);
v___x_719_ = lean_nat_dec_le(v___x_715_, v_val_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v___x_715_);
v___x_720_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_704_, v___x_705_, v_src_706_, v___x_707_, v_it_711_, v_b_709_);
return v___x_720_;
}
else
{
lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
v_isSharedCheck_728_ = !lean_is_exclusive(v_b_709_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v_b_709_, 0);
lean_dec(v_unused_729_);
v___x_722_ = v_b_709_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_dec(v_b_709_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_715_);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_715_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_704_, v___x_705_, v_src_706_, v___x_707_, v_it_711_, v___x_725_);
return v___x_726_;
}
}
}
}
}
else
{
lean_object* v___x_730_; 
lean_dec_ref(v___x_713_);
v___x_730_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_704_, v___x_705_, v_src_706_, v___x_707_, v_it_711_, v_b_709_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object* v___x_762_, lean_object* v___x_763_, lean_object* v_src_764_, lean_object* v___x_765_, lean_object* v_a_766_, lean_object* v_b_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_762_, v___x_763_, v_src_764_, v___x_765_, v_a_766_, v_b_767_);
lean_dec(v___x_763_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object* v___x_769_, lean_object* v_i_770_, lean_object* v_out_771_, lean_object* v_pending_772_, lean_object* v___y_773_, lean_object* v_____r_774_, lean_object* v_out_775_){
_start:
{
lean_object* v_str_776_; lean_object* v_startInclusive_777_; lean_object* v_endExclusive_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_str_776_ = lean_ctor_get(v___x_769_, 0);
v_startInclusive_777_ = lean_ctor_get(v___x_769_, 1);
v_endExclusive_778_ = lean_ctor_get(v___x_769_, 2);
v___x_779_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_i_770_, v_out_771_);
v___x_780_ = lean_string_append(v_out_775_, v___x_779_);
lean_dec_ref(v___x_779_);
lean_inc(v_pending_772_);
v___x_781_ = l_String_Slice_Pos_nextn(v___x_769_, v_pending_772_, v___y_773_);
v___x_782_ = lean_nat_add(v_startInclusive_777_, v___x_781_);
lean_dec(v___x_781_);
v___x_783_ = lean_string_utf8_extract_fast(v_str_776_, v___x_782_, v_endExclusive_778_);
lean_dec(v___x_782_);
v___x_784_ = lean_string_append(v___x_780_, v___x_783_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_pending_772_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object* v___x_787_, lean_object* v_i_788_, lean_object* v_out_789_, lean_object* v_pending_790_, lean_object* v___y_791_, lean_object* v_____r_792_, lean_object* v_out_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_787_, v_i_788_, v_out_789_, v_pending_790_, v___y_791_, v_____r_792_, v_out_793_);
lean_dec_ref(v___x_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object* v_i_795_, lean_object* v___y_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_src_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v___y_804_; lean_object* v_val_805_; 
if (lean_obj_tag(v_a_801_) == 0)
{
lean_object* v_currPos_809_; lean_object* v_searcher_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_873_; 
v_currPos_809_ = lean_ctor_get(v_a_801_, 0);
v_searcher_810_ = lean_ctor_get(v_a_801_, 1);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_873_ == 0)
{
v___x_812_ = v_a_801_;
v_isShared_813_ = v_isSharedCheck_873_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_searcher_810_);
lean_inc(v_currPos_809_);
lean_dec(v_a_801_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_873_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_str_814_; lean_object* v_startInclusive_815_; lean_object* v_endExclusive_816_; lean_object* v_out_817_; lean_object* v_pending_818_; lean_object* v_it_820_; lean_object* v_out_821_; lean_object* v___x_851_; uint8_t v_decide_852_; 
v_str_814_ = lean_ctor_get(v___x_797_, 0);
v_startInclusive_815_ = lean_ctor_get(v___x_797_, 1);
v_endExclusive_816_ = lean_ctor_get(v___x_797_, 2);
v_out_817_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_818_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_nat_sub(v_endExclusive_816_, v_startInclusive_815_);
v_decide_852_ = lean_nat_dec_eq(v_searcher_810_, v___x_851_);
lean_dec(v___x_851_);
if (v_decide_852_ == 0)
{
uint32_t v___x_853_; lean_object* v___x_854_; uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_853_ = 10;
v___x_854_ = lean_nat_add(v_startInclusive_815_, v_searcher_810_);
v___x_855_ = lean_string_utf8_get_fast(v_str_814_, v___x_854_);
v___x_856_ = lean_uint32_dec_eq(v___x_855_, v___x_853_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
lean_dec(v_searcher_810_);
v___x_857_ = lean_string_utf8_next_fast(v_str_814_, v___x_854_);
lean_dec(v___x_854_);
v___x_858_ = lean_nat_sub(v___x_857_, v_startInclusive_815_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_858_);
v___x_860_ = v___x_812_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_currPos_809_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_862_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
v_a_801_ = v___x_860_;
goto _start;
}
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_slice_866_; lean_object* v_nextIt_868_; 
v___x_863_ = lean_string_utf8_next_fast(v_str_814_, v___x_854_);
v___x_864_ = lean_nat_sub(v___x_863_, v___x_854_);
lean_dec(v___x_854_);
v___x_865_ = lean_nat_add(v_searcher_810_, v___x_864_);
lean_dec(v___x_864_);
lean_dec(v_searcher_810_);
lean_inc_ref(v___x_797_);
v_slice_866_ = l_String_Slice_slice_x21(v___x_797_, v_currPos_809_, v___x_865_);
lean_dec(v_currPos_809_);
lean_inc(v___x_865_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_865_);
lean_ctor_set(v___x_812_, 0, v___x_865_);
v_nextIt_868_ = v___x_812_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_865_);
v_nextIt_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
v_it_820_ = v_nextIt_868_;
v_out_821_ = v_slice_866_;
goto v___jp_819_;
}
}
}
else
{
uint8_t v_decide_870_; 
lean_del_object(v___x_812_);
lean_dec(v_searcher_810_);
v_decide_870_ = lean_nat_dec_eq(v_currPos_809_, v___x_798_);
if (v_decide_870_ == 0)
{
lean_object* v_slice_871_; lean_object* v___x_872_; 
lean_inc(v___x_800_);
lean_inc_ref(v_src_799_);
v_slice_871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_871_, 0, v_src_799_);
lean_ctor_set(v_slice_871_, 1, v_currPos_809_);
lean_ctor_set(v_slice_871_, 2, v___x_800_);
v___x_872_ = lean_box(1);
v_it_820_ = v___x_872_;
v_out_821_ = v_slice_871_;
goto v___jp_819_;
}
else
{
lean_dec(v_currPos_809_);
lean_dec(v___x_800_);
lean_dec_ref(v_src_799_);
lean_dec_ref(v___x_797_);
lean_dec(v___y_796_);
lean_dec(v_i_795_);
return v_b_802_;
}
}
v___jp_819_:
{
lean_object* v_fst_822_; lean_object* v_snd_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_850_; 
v_fst_822_ = lean_ctor_get(v_b_802_, 0);
v_snd_823_ = lean_ctor_get(v_b_802_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_b_802_);
if (v_isSharedCheck_850_ == 0)
{
v___x_825_ = v_b_802_;
v_isShared_826_ = v_isSharedCheck_850_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_snd_823_);
lean_inc(v_fst_822_);
lean_dec(v_b_802_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_850_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_827_ = l_String_Slice_lines_lineMap(v_out_821_);
v___x_828_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; uint8_t v___x_830_; 
lean_del_object(v___x_825_);
v___x_829_ = lean_string_utf8_byte_size(v_fst_822_);
v___x_830_ = lean_nat_dec_eq(v___x_829_, v_pending_818_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_add(v_snd_823_, v___x_831_);
lean_dec(v_snd_823_);
v___x_833_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_832_, v_fst_822_);
v___x_834_ = lean_box(0);
lean_inc(v___y_796_);
lean_inc(v_i_795_);
v___x_835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_827_, v_i_795_, v_out_817_, v_pending_818_, v___y_796_, v___x_834_, v___x_833_);
lean_dec_ref(v___x_827_);
v___y_804_ = v_it_820_;
v_val_805_ = v___x_835_;
goto v___jp_803_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v_snd_823_);
v___x_836_ = lean_box(0);
lean_inc(v___y_796_);
lean_inc(v_i_795_);
v___x_837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_827_, v_i_795_, v_out_817_, v_pending_818_, v___y_796_, v___x_836_, v_fst_822_);
lean_dec_ref(v___x_827_);
v___y_804_ = v_it_820_;
v_val_805_ = v___x_837_;
goto v___jp_803_;
}
}
else
{
lean_object* v___x_838_; uint8_t v___x_839_; 
lean_dec_ref(v___x_827_);
v___x_838_ = lean_string_utf8_byte_size(v_fst_822_);
v___x_839_ = lean_nat_dec_eq(v___x_838_, v_pending_818_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_snd_823_, v___x_840_);
lean_dec(v_snd_823_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___x_841_);
v___x_843_ = v___x_825_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_fst_822_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_841_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
v_a_801_ = v_it_820_;
v_b_802_ = v___x_843_;
goto _start;
}
}
else
{
lean_object* v___x_847_; 
if (v_isShared_826_ == 0)
{
v___x_847_ = v___x_825_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_fst_822_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_snd_823_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v_a_801_ = v_it_820_;
v_b_802_ = v___x_847_;
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
lean_dec(v___x_800_);
lean_dec_ref(v_src_799_);
lean_dec_ref(v___x_797_);
lean_dec(v___y_796_);
lean_dec(v_i_795_);
return v_b_802_;
}
v___jp_803_:
{
if (lean_obj_tag(v_val_805_) == 0)
{
lean_object* v_a_806_; 
lean_dec(v___y_804_);
lean_dec(v___x_800_);
lean_dec_ref(v_src_799_);
lean_dec_ref(v___x_797_);
lean_dec(v___y_796_);
lean_dec(v_i_795_);
v_a_806_ = lean_ctor_get(v_val_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v_val_805_, 1);
return v_a_806_;
}
else
{
lean_object* v_a_807_; 
v_a_807_ = lean_ctor_get(v_val_805_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v_val_805_, 1);
v_a_801_ = v___y_804_;
v_b_802_ = v_a_807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object* v_i_874_, lean_object* v___y_875_, lean_object* v___x_876_, lean_object* v___x_877_, lean_object* v_src_878_, lean_object* v___x_879_, lean_object* v_a_880_, lean_object* v_b_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_874_, v___y_875_, v___x_876_, v___x_877_, v_src_878_, v___x_879_, v_a_880_, v_b_881_);
lean_dec(v___x_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object* v_i_883_, lean_object* v___y_884_, lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v_src_887_, lean_object* v___x_888_, lean_object* v_a_889_, lean_object* v_b_890_){
_start:
{
lean_object* v___y_892_; lean_object* v_val_893_; 
if (lean_obj_tag(v_a_889_) == 0)
{
lean_object* v_currPos_897_; lean_object* v_searcher_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_961_; 
v_currPos_897_ = lean_ctor_get(v_a_889_, 0);
v_searcher_898_ = lean_ctor_get(v_a_889_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_a_889_);
if (v_isSharedCheck_961_ == 0)
{
v___x_900_ = v_a_889_;
v_isShared_901_ = v_isSharedCheck_961_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_searcher_898_);
lean_inc(v_currPos_897_);
lean_dec(v_a_889_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_961_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_str_902_; lean_object* v_startInclusive_903_; lean_object* v_endExclusive_904_; lean_object* v_out_905_; lean_object* v_pending_906_; lean_object* v_it_908_; lean_object* v_out_909_; lean_object* v___x_939_; uint8_t v_decide_940_; 
v_str_902_ = lean_ctor_get(v___x_885_, 0);
v_startInclusive_903_ = lean_ctor_get(v___x_885_, 1);
v_endExclusive_904_ = lean_ctor_get(v___x_885_, 2);
v_out_905_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_906_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_nat_sub(v_endExclusive_904_, v_startInclusive_903_);
v_decide_940_ = lean_nat_dec_eq(v_searcher_898_, v___x_939_);
lean_dec(v___x_939_);
if (v_decide_940_ == 0)
{
lean_object* v___x_941_; uint32_t v___x_942_; uint32_t v___x_943_; uint8_t v___x_944_; 
v___x_941_ = lean_nat_add(v_startInclusive_903_, v_searcher_898_);
v___x_942_ = lean_string_utf8_get_fast(v_str_902_, v___x_941_);
v___x_943_ = 10;
v___x_944_ = lean_uint32_dec_eq(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_dec(v_searcher_898_);
v___x_945_ = lean_string_utf8_next_fast(v_str_902_, v___x_941_);
lean_dec(v___x_941_);
v___x_946_ = lean_nat_sub(v___x_945_, v_startInclusive_903_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v___x_946_);
v___x_948_ = v___x_900_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_currPos_897_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_950_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
v___x_949_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_883_, v___y_884_, v___x_885_, v___x_886_, v_src_887_, v___x_888_, v___x_948_, v_b_890_);
return v___x_949_;
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_slice_954_; lean_object* v_nextIt_956_; 
v___x_951_ = lean_string_utf8_next_fast(v_str_902_, v___x_941_);
v___x_952_ = lean_nat_sub(v___x_951_, v___x_941_);
lean_dec(v___x_941_);
v___x_953_ = lean_nat_add(v_searcher_898_, v___x_952_);
lean_dec(v___x_952_);
lean_dec(v_searcher_898_);
lean_inc_ref(v___x_885_);
v_slice_954_ = l_String_Slice_slice_x21(v___x_885_, v_currPos_897_, v___x_953_);
lean_dec(v_currPos_897_);
lean_inc(v___x_953_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v___x_953_);
lean_ctor_set(v___x_900_, 0, v___x_953_);
v_nextIt_956_ = v___x_900_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_953_);
v_nextIt_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
v_it_908_ = v_nextIt_956_;
v_out_909_ = v_slice_954_;
goto v___jp_907_;
}
}
}
else
{
uint8_t v_decide_958_; 
lean_del_object(v___x_900_);
lean_dec(v_searcher_898_);
v_decide_958_ = lean_nat_dec_eq(v_currPos_897_, v___x_886_);
if (v_decide_958_ == 0)
{
lean_object* v_slice_959_; lean_object* v___x_960_; 
lean_inc(v___x_888_);
lean_inc_ref(v_src_887_);
v_slice_959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_959_, 0, v_src_887_);
lean_ctor_set(v_slice_959_, 1, v_currPos_897_);
lean_ctor_set(v_slice_959_, 2, v___x_888_);
v___x_960_ = lean_box(1);
v_it_908_ = v___x_960_;
v_out_909_ = v_slice_959_;
goto v___jp_907_;
}
else
{
lean_dec(v_currPos_897_);
lean_dec(v___x_888_);
lean_dec_ref(v_src_887_);
lean_dec_ref(v___x_885_);
lean_dec(v___y_884_);
lean_dec(v_i_883_);
return v_b_890_;
}
}
v___jp_907_:
{
lean_object* v_fst_910_; lean_object* v_snd_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_938_; 
v_fst_910_ = lean_ctor_get(v_b_890_, 0);
v_snd_911_ = lean_ctor_get(v_b_890_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_b_890_);
if (v_isSharedCheck_938_ == 0)
{
v___x_913_ = v_b_890_;
v_isShared_914_ = v_isSharedCheck_938_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_snd_911_);
lean_inc(v_fst_910_);
lean_dec(v_b_890_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_938_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = l_String_Slice_lines_lineMap(v_out_909_);
v___x_916_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; uint8_t v___x_918_; 
lean_del_object(v___x_913_);
v___x_917_ = lean_string_utf8_byte_size(v_fst_910_);
v___x_918_ = lean_nat_dec_eq(v___x_917_, v_pending_906_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_add(v_snd_911_, v___x_919_);
lean_dec(v_snd_911_);
v___x_921_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_920_, v_fst_910_);
v___x_922_ = lean_box(0);
lean_inc(v___y_884_);
lean_inc(v_i_883_);
v___x_923_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_915_, v_i_883_, v_out_905_, v_pending_906_, v___y_884_, v___x_922_, v___x_921_);
lean_dec_ref(v___x_915_);
v___y_892_ = v_it_908_;
v_val_893_ = v___x_923_;
goto v___jp_891_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_snd_911_);
v___x_924_ = lean_box(0);
lean_inc(v___y_884_);
lean_inc(v_i_883_);
v___x_925_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_915_, v_i_883_, v_out_905_, v_pending_906_, v___y_884_, v___x_924_, v_fst_910_);
lean_dec_ref(v___x_915_);
v___y_892_ = v_it_908_;
v_val_893_ = v___x_925_;
goto v___jp_891_;
}
}
else
{
lean_object* v___x_926_; uint8_t v___x_927_; 
lean_dec_ref(v___x_915_);
v___x_926_ = lean_string_utf8_byte_size(v_fst_910_);
v___x_927_ = lean_nat_dec_eq(v___x_926_, v_pending_906_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_nat_add(v_snd_911_, v___x_928_);
lean_dec(v_snd_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v___x_929_);
v___x_931_ = v___x_913_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_929_);
v___x_931_ = v_reuseFailAlloc_933_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; 
v___x_932_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_883_, v___y_884_, v___x_885_, v___x_886_, v_src_887_, v___x_888_, v_it_908_, v___x_931_);
return v___x_932_;
}
}
else
{
lean_object* v___x_935_; 
if (v_isShared_914_ == 0)
{
v___x_935_ = v___x_913_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_fst_910_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_snd_911_);
v___x_935_ = v_reuseFailAlloc_937_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; 
v___x_936_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_883_, v___y_884_, v___x_885_, v___x_886_, v_src_887_, v___x_888_, v_it_908_, v___x_935_);
return v___x_936_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_888_);
lean_dec_ref(v_src_887_);
lean_dec_ref(v___x_885_);
lean_dec(v___y_884_);
lean_dec(v_i_883_);
return v_b_890_;
}
v___jp_891_:
{
if (lean_obj_tag(v_val_893_) == 0)
{
lean_object* v_a_894_; 
lean_dec(v___y_892_);
lean_dec(v___x_888_);
lean_dec_ref(v_src_887_);
lean_dec_ref(v___x_885_);
lean_dec(v___y_884_);
lean_dec(v_i_883_);
v_a_894_ = lean_ctor_get(v_val_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v_val_893_, 1);
return v_a_894_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v_val_893_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v_val_893_, 1);
v___x_896_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_883_, v___y_884_, v___x_885_, v___x_886_, v_src_887_, v___x_888_, v___y_892_, v_a_895_);
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object* v_i_962_, lean_object* v___y_963_, lean_object* v___x_964_, lean_object* v___x_965_, lean_object* v_src_966_, lean_object* v___x_967_, lean_object* v_a_968_, lean_object* v_b_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_962_, v___y_963_, v___x_964_, v___x_965_, v_src_966_, v___x_967_, v_a_968_, v_b_969_);
lean_dec(v___x_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object* v_i_974_, lean_object* v_src_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___y_982_; lean_object* v___x_986_; 
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = lean_string_utf8_byte_size(v_src_975_);
lean_inc_ref_n(v_src_975_, 3);
v___x_978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_978_, 0, v_src_975_);
lean_ctor_set(v___x_978_, 1, v___x_976_);
lean_ctor_set(v___x_978_, 2, v___x_977_);
v___x_979_ = lean_box(0);
v___x_980_ = l_String_lines(v_src_975_);
lean_inc(v___x_980_);
lean_inc_ref(v___x_978_);
v___x_986_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_978_, v___x_977_, v_src_975_, v___x_977_, v___x_980_, v___x_979_);
if (lean_obj_tag(v___x_986_) == 0)
{
v___y_982_ = v___x_976_;
goto v___jp_981_;
}
else
{
lean_object* v_val_987_; 
v_val_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v___x_986_, 1);
v___y_982_ = v_val_987_;
goto v___jp_981_;
}
v___jp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_fst_985_; 
v___x_983_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0));
v___x_984_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_974_, v___y_982_, v___x_978_, v___x_977_, v_src_975_, v___x_977_, v___x_980_, v___x_983_);
v_fst_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_fst_985_);
lean_dec_ref(v___x_984_);
return v_fst_985_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object* v_i_988_, lean_object* v___y_989_, lean_object* v___x_990_, lean_object* v___x_991_, lean_object* v_src_992_, lean_object* v___x_993_, lean_object* v_inst_994_, lean_object* v_R_995_, lean_object* v_a_996_, lean_object* v_b_997_, lean_object* v_c_998_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_988_, v___y_989_, v___x_990_, v___x_991_, v_src_992_, v___x_993_, v_a_996_, v_b_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object* v_i_1000_, lean_object* v___y_1001_, lean_object* v___x_1002_, lean_object* v___x_1003_, lean_object* v_src_1004_, lean_object* v___x_1005_, lean_object* v_inst_1006_, lean_object* v_R_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_, lean_object* v_c_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(v_i_1000_, v___y_1001_, v___x_1002_, v___x_1003_, v_src_1004_, v___x_1005_, v_inst_1006_, v_R_1007_, v_a_1008_, v_b_1009_, v_c_1010_);
lean_dec(v___x_1003_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v_src_1014_, lean_object* v___x_1015_, lean_object* v_inst_1016_, lean_object* v_R_1017_, lean_object* v_a_1018_, lean_object* v_b_1019_, lean_object* v_c_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1012_, v___x_1013_, v_src_1014_, v___x_1015_, v_a_1018_, v_b_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object* v___x_1022_, lean_object* v___x_1023_, lean_object* v_src_1024_, lean_object* v___x_1025_, lean_object* v_inst_1026_, lean_object* v_R_1027_, lean_object* v_a_1028_, lean_object* v_b_1029_, lean_object* v_c_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(v___x_1022_, v___x_1023_, v_src_1024_, v___x_1025_, v_inst_1026_, v_R_1027_, v_a_1028_, v_b_1029_, v_c_1030_);
lean_dec(v___x_1023_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object* v_i_1032_, lean_object* v___y_1033_, lean_object* v___x_1034_, lean_object* v___x_1035_, lean_object* v_src_1036_, lean_object* v___x_1037_, lean_object* v_inst_1038_, lean_object* v_R_1039_, lean_object* v_a_1040_, lean_object* v_b_1041_, lean_object* v_c_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_1032_, v___y_1033_, v___x_1034_, v___x_1035_, v_src_1036_, v___x_1037_, v_a_1040_, v_b_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object* v_i_1044_, lean_object* v___y_1045_, lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v_src_1048_, lean_object* v___x_1049_, lean_object* v_inst_1050_, lean_object* v_R_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v_c_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(v_i_1044_, v___y_1045_, v___x_1046_, v___x_1047_, v_src_1048_, v___x_1049_, v_inst_1050_, v_R_1051_, v_a_1052_, v_b_1053_, v_c_1054_);
lean_dec(v___x_1047_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object* v___x_1056_, lean_object* v___x_1057_, lean_object* v_src_1058_, lean_object* v___x_1059_, lean_object* v_inst_1060_, lean_object* v_R_1061_, lean_object* v_a_1062_, lean_object* v_b_1063_, lean_object* v_c_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_1056_, v___x_1057_, v_src_1058_, v___x_1059_, v_a_1062_, v_b_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object* v___x_1066_, lean_object* v___x_1067_, lean_object* v_src_1068_, lean_object* v___x_1069_, lean_object* v_inst_1070_, lean_object* v_R_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_, lean_object* v_c_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(v___x_1066_, v___x_1067_, v_src_1068_, v___x_1069_, v_inst_1070_, v_R_1071_, v_a_1072_, v_b_1073_, v_c_1074_);
lean_dec(v___x_1067_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v_zero_1078_; uint8_t v_isZero_1079_; 
v_zero_1078_ = lean_unsigned_to_nat(0u);
v_isZero_1079_ = lean_nat_dec_eq(v_x_1076_, v_zero_1078_);
if (v_isZero_1079_ == 1)
{
lean_dec(v_x_1076_);
return v_x_1077_;
}
else
{
uint32_t v___x_1080_; lean_object* v_one_1081_; lean_object* v_n_1082_; lean_object* v___x_1083_; 
v___x_1080_ = 96;
v_one_1081_ = lean_unsigned_to_nat(1u);
v_n_1082_ = lean_nat_sub(v_x_1076_, v_one_1081_);
lean_dec(v_x_1076_);
v___x_1083_ = lean_string_push(v_x_1077_, v___x_1080_);
v_x_1076_ = v_n_1082_;
v_x_1077_ = v___x_1083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object* v_value_1086_){
_start:
{
lean_object* v___y_1088_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1110_; 
v___x_1102_ = lean_string_utf8_byte_size(v_value_1086_);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_nat_dec_eq(v___x_1102_, v___x_1103_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_dec_le(v___x_1111_, v___x_1102_);
if (v___x_1112_ == 0)
{
goto v___jp_1104_;
}
else
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1114_ = lean_string_memcmp(v_value_1086_, v___x_1113_, v___x_1103_, v___x_1103_, v___x_1111_);
if (v___x_1114_ == 0)
{
goto v___jp_1104_;
}
else
{
goto v___jp_1096_;
}
}
}
else
{
lean_object* v___x_1115_; 
lean_dec_ref(v_value_1086_);
v___x_1115_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___y_1088_ = v___x_1115_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_delim_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1089_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_1090_ = l_Lean_Doc_longestBacktickRun(v___y_1088_);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_add(v___x_1090_, v___x_1091_);
lean_dec(v___x_1090_);
v_delim_1093_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___x_1092_, v___x_1089_);
lean_inc_ref(v_delim_1093_);
v___x_1094_ = lean_string_append(v_delim_1093_, v___y_1088_);
lean_dec_ref(v___y_1088_);
v___x_1095_ = lean_string_append(v___x_1094_, v_delim_1093_);
lean_dec_ref(v_delim_1093_);
return v___x_1095_;
}
v___jp_1096_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1098_ = lean_string_append(v___x_1097_, v_value_1086_);
lean_dec_ref(v_value_1086_);
v___x_1099_ = lean_string_append(v___x_1098_, v___x_1097_);
v___y_1088_ = v___x_1099_;
goto v___jp_1087_;
}
v___jp_1100_:
{
uint8_t v___x_1101_; 
lean_inc_ref(v_value_1086_);
v___x_1101_ = l_Lean_Doc_versoCodeBoundarySpaces(v_value_1086_);
if (v___x_1101_ == 0)
{
v___y_1088_ = v_value_1086_;
goto v___jp_1087_;
}
else
{
goto v___jp_1096_;
}
}
v___jp_1104_:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_unsigned_to_nat(1u);
v___x_1106_ = lean_nat_dec_le(v___x_1105_, v___x_1102_);
if (v___x_1106_ == 0)
{
goto v___jp_1100_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1108_ = lean_nat_sub(v___x_1102_, v___x_1105_);
v___x_1109_ = lean_string_memcmp(v_value_1086_, v___x_1107_, v___x_1108_, v___x_1103_, v___x_1105_);
lean_dec(v___x_1108_);
if (v___x_1109_ == 0)
{
goto v___jp_1100_;
}
else
{
goto v___jp_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t v_char_1116_, lean_object* v_as_1117_, size_t v_i_1118_, size_t v_stop_1119_, lean_object* v_b_1120_){
_start:
{
lean_object* v___y_1122_; uint8_t v___x_1126_; 
v___x_1126_ = lean_usize_dec_eq(v_i_1118_, v_stop_1119_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_array_uget_borrowed(v_as_1117_, v_i_1118_);
lean_inc(v___x_1127_);
v___x_1128_ = l_Lean_Doc_InlineView_of(v___x_1127_);
if (lean_obj_tag(v___x_1128_) == 1)
{
lean_object* v_val_1129_; 
v_val_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_val_1129_);
lean_dec_ref_known(v___x_1128_, 1);
switch(lean_obj_tag(v_val_1129_))
{
case 1:
{
lean_object* v_view_1130_; lean_object* v___y_1132_; uint32_t v___x_1137_; uint8_t v___x_1138_; 
v_view_1130_ = lean_ctor_get(v_val_1129_, 0);
lean_inc_ref(v_view_1130_);
lean_dec_ref_known(v_val_1129_, 1);
v___x_1137_ = 95;
v___x_1138_ = lean_uint32_dec_eq(v_char_1116_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_unsigned_to_nat(0u);
v___y_1132_ = v___x_1139_;
goto v___jp_1131_;
}
else
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_unsigned_to_nat(1u);
v___y_1132_ = v___x_1140_;
goto v___jp_1131_;
}
v___jp_1131_:
{
lean_object* v_content_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_content_1133_ = lean_ctor_get(v_view_1130_, 2);
lean_inc_ref(v_content_1133_);
lean_dec_ref(v_view_1130_);
v___x_1134_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1116_, v_content_1133_);
lean_dec_ref(v_content_1133_);
v___x_1135_ = lean_nat_add(v___y_1132_, v___x_1134_);
lean_dec(v___x_1134_);
v___x_1136_ = lean_nat_dec_le(v_b_1120_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec(v___x_1135_);
v___y_1122_ = v_b_1120_;
goto v___jp_1121_;
}
else
{
lean_dec(v_b_1120_);
v___y_1122_ = v___x_1135_;
goto v___jp_1121_;
}
}
}
case 2:
{
lean_object* v_view_1141_; lean_object* v___y_1143_; uint32_t v___x_1148_; uint8_t v___x_1149_; 
v_view_1141_ = lean_ctor_get(v_val_1129_, 0);
lean_inc_ref(v_view_1141_);
lean_dec_ref_known(v_val_1129_, 1);
v___x_1148_ = 42;
v___x_1149_ = lean_uint32_dec_eq(v_char_1116_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___y_1143_ = v___x_1150_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___y_1143_ = v___x_1151_;
goto v___jp_1142_;
}
v___jp_1142_:
{
lean_object* v_content_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v_content_1144_ = lean_ctor_get(v_view_1141_, 2);
lean_inc_ref(v_content_1144_);
lean_dec_ref(v_view_1141_);
v___x_1145_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1116_, v_content_1144_);
lean_dec_ref(v_content_1144_);
v___x_1146_ = lean_nat_add(v___y_1143_, v___x_1145_);
lean_dec(v___x_1145_);
v___x_1147_ = lean_nat_dec_le(v_b_1120_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_dec(v___x_1146_);
v___y_1122_ = v_b_1120_;
goto v___jp_1121_;
}
else
{
lean_dec(v_b_1120_);
v___y_1122_ = v___x_1146_;
goto v___jp_1121_;
}
}
}
case 5:
{
lean_object* v_view_1152_; lean_object* v_content_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
v_view_1152_ = lean_ctor_get(v_val_1129_, 0);
lean_inc_ref(v_view_1152_);
lean_dec_ref_known(v_val_1129_, 1);
v_content_1153_ = lean_ctor_get(v_view_1152_, 2);
lean_inc_ref(v_content_1153_);
lean_dec_ref(v_view_1152_);
v___x_1154_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1116_, v_content_1153_);
lean_dec_ref(v_content_1153_);
v___x_1155_ = lean_nat_dec_le(v_b_1120_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_dec(v___x_1154_);
v___y_1122_ = v_b_1120_;
goto v___jp_1121_;
}
else
{
lean_dec(v_b_1120_);
v___y_1122_ = v___x_1154_;
goto v___jp_1121_;
}
}
case 9:
{
lean_object* v_view_1156_; lean_object* v_content_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_view_1156_ = lean_ctor_get(v_val_1129_, 0);
lean_inc_ref(v_view_1156_);
lean_dec_ref_known(v_val_1129_, 1);
v_content_1157_ = lean_ctor_get(v_view_1156_, 6);
lean_inc_ref(v_content_1157_);
lean_dec_ref(v_view_1156_);
v___x_1158_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1116_, v_content_1157_);
lean_dec_ref(v_content_1157_);
v___x_1159_ = lean_nat_dec_le(v_b_1120_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec(v___x_1158_);
v___y_1122_ = v_b_1120_;
goto v___jp_1121_;
}
else
{
lean_dec(v_b_1120_);
v___y_1122_ = v___x_1158_;
goto v___jp_1121_;
}
}
default: 
{
lean_dec(v_val_1129_);
v___y_1122_ = v_b_1120_;
goto v___jp_1121_;
}
}
}
else
{
lean_dec(v___x_1128_);
v___y_1122_ = v_b_1120_;
goto v___jp_1121_;
}
}
else
{
return v_b_1120_;
}
v___jp_1121_:
{
size_t v___x_1123_; size_t v___x_1124_; 
v___x_1123_ = ((size_t)1ULL);
v___x_1124_ = lean_usize_add(v_i_1118_, v___x_1123_);
v_i_1118_ = v___x_1124_;
v_b_1120_ = v___y_1122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t v_char_1160_, lean_object* v_inls_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_array_get_size(v_inls_1161_);
v___x_1164_ = lean_nat_dec_lt(v___x_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
return v___x_1162_;
}
else
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_nat_dec_le(v___x_1163_, v___x_1163_);
if (v___x_1165_ == 0)
{
if (v___x_1164_ == 0)
{
return v___x_1162_;
}
else
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = lean_usize_of_nat(v___x_1163_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1160_, v_inls_1161_, v___x_1166_, v___x_1167_, v___x_1162_);
return v___x_1168_;
}
}
else
{
size_t v___x_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = ((size_t)0ULL);
v___x_1170_ = lean_usize_of_nat(v___x_1163_);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1160_, v_inls_1161_, v___x_1169_, v___x_1170_, v___x_1162_);
return v___x_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object* v_char_1172_, lean_object* v_inls_1173_){
_start:
{
uint32_t v_char_boxed_1174_; lean_object* v_res_1175_; 
v_char_boxed_1174_ = lean_unbox_uint32(v_char_1172_);
lean_dec(v_char_1172_);
v_res_1175_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_boxed_1174_, v_inls_1173_);
lean_dec_ref(v_inls_1173_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object* v_char_1176_, lean_object* v_as_1177_, lean_object* v_i_1178_, lean_object* v_stop_1179_, lean_object* v_b_1180_){
_start:
{
uint32_t v_char_boxed_1181_; size_t v_i_boxed_1182_; size_t v_stop_boxed_1183_; lean_object* v_res_1184_; 
v_char_boxed_1181_ = lean_unbox_uint32(v_char_1176_);
lean_dec(v_char_1176_);
v_i_boxed_1182_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_stop_boxed_1183_ = lean_unbox_usize(v_stop_1179_);
lean_dec(v_stop_1179_);
v_res_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_boxed_1181_, v_as_1177_, v_i_boxed_1182_, v_stop_boxed_1183_, v_b_1180_);
lean_dec_ref(v_as_1177_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t v_char_1185_, lean_object* v_inls_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1185_, v_inls_1186_);
v___x_1189_ = lean_nat_add(v___x_1187_, v___x_1188_);
lean_dec(v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object* v_char_1190_, lean_object* v_inls_1191_){
_start:
{
uint32_t v_char_boxed_1192_; lean_object* v_res_1193_; 
v_char_boxed_1192_ = lean_unbox_uint32(v_char_1190_);
lean_dec(v_char_1190_);
v_res_1193_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_boxed_1192_, v_inls_1191_);
lean_dec_ref(v_inls_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object* v_as_1194_, size_t v_i_1195_, size_t v_stop_1196_, lean_object* v_b_1197_){
_start:
{
lean_object* v___y_1199_; uint8_t v___x_1203_; 
v___x_1203_ = lean_usize_dec_eq(v_i_1195_, v_stop_1196_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v_contents_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1204_ = lean_array_uget_borrowed(v_as_1194_, v_i_1195_);
v_contents_1205_ = lean_ctor_get(v___x_1204_, 2);
v___x_1206_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1205_);
v___x_1207_ = lean_nat_dec_le(v_b_1197_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_dec(v___x_1206_);
v___y_1199_ = v_b_1197_;
goto v___jp_1198_;
}
else
{
lean_dec(v_b_1197_);
v___y_1199_ = v___x_1206_;
goto v___jp_1198_;
}
}
else
{
return v_b_1197_;
}
v___jp_1198_:
{
size_t v___x_1200_; size_t v___x_1201_; 
v___x_1200_ = ((size_t)1ULL);
v___x_1201_ = lean_usize_add(v_i_1195_, v___x_1200_);
v_i_1195_ = v___x_1201_;
v_b_1197_ = v___y_1199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object* v_as_1208_, size_t v_i_1209_, size_t v_stop_1210_, lean_object* v_b_1211_){
_start:
{
lean_object* v___y_1213_; uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_eq(v_i_1209_, v_stop_1210_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v_desc_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1218_ = lean_array_uget_borrowed(v_as_1208_, v_i_1209_);
v_desc_1219_ = lean_ctor_get(v___x_1218_, 3);
v___x_1220_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_desc_1219_);
v___x_1221_ = lean_nat_dec_le(v_b_1211_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_dec(v___x_1220_);
v___y_1213_ = v_b_1211_;
goto v___jp_1212_;
}
else
{
lean_dec(v_b_1211_);
v___y_1213_ = v___x_1220_;
goto v___jp_1212_;
}
}
else
{
return v_b_1211_;
}
v___jp_1212_:
{
size_t v___x_1214_; size_t v___x_1215_; 
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_add(v_i_1209_, v___x_1214_);
v_i_1209_ = v___x_1215_;
v_b_1211_ = v___y_1213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object* v_as_1222_, size_t v_i_1223_, size_t v_stop_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v___y_1227_; lean_object* v___y_1232_; uint8_t v___x_1236_; 
v___x_1236_ = lean_usize_dec_eq(v_i_1223_, v_stop_1224_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_array_uget_borrowed(v_as_1222_, v_i_1223_);
lean_inc(v___x_1237_);
v___x_1238_ = l_Lean_Doc_BlockView_of(v___x_1237_);
if (lean_obj_tag(v___x_1238_) == 1)
{
lean_object* v_val_1239_; 
v_val_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_val_1239_);
lean_dec_ref_known(v___x_1238_, 1);
switch(lean_obj_tag(v_val_1239_))
{
case 6:
{
lean_object* v_view_1240_; lean_object* v_content_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_view_1240_ = lean_ctor_get(v_val_1239_, 0);
lean_inc_ref(v_view_1240_);
lean_dec_ref_known(v_val_1239_, 1);
v_content_1241_ = lean_ctor_get(v_view_1240_, 4);
lean_inc_ref(v_content_1241_);
lean_dec_ref(v_view_1240_);
v___x_1242_ = lean_unsigned_to_nat(3u);
v___x_1243_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1241_);
lean_dec_ref(v_content_1241_);
v___x_1244_ = lean_nat_dec_le(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec(v___x_1243_);
v___y_1232_ = v___x_1242_;
goto v___jp_1231_;
}
else
{
v___y_1232_ = v___x_1243_;
goto v___jp_1231_;
}
}
case 4:
{
lean_object* v_view_1245_; lean_object* v_content_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_view_1245_ = lean_ctor_get(v_val_1239_, 0);
lean_inc_ref(v_view_1245_);
lean_dec_ref_known(v_val_1239_, 1);
v_content_1246_ = lean_ctor_get(v_view_1245_, 2);
lean_inc_ref(v_content_1246_);
lean_dec_ref(v_view_1245_);
v___x_1247_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1246_);
lean_dec_ref(v_content_1246_);
v___x_1248_ = lean_nat_dec_le(v_b_1225_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec(v___x_1247_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
lean_dec(v_b_1225_);
v___y_1227_ = v___x_1247_;
goto v___jp_1226_;
}
}
case 1:
{
lean_object* v_view_1249_; lean_object* v_items_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_view_1249_ = lean_ctor_get(v_val_1239_, 0);
lean_inc_ref(v_view_1249_);
lean_dec_ref_known(v_val_1239_, 1);
v_items_1250_ = lean_ctor_get(v_view_1249_, 1);
lean_inc_ref(v_items_1250_);
lean_dec_ref(v_view_1249_);
v___x_1251_ = lean_unsigned_to_nat(0u);
v___x_1252_ = lean_array_get_size(v_items_1250_);
v___x_1253_ = lean_nat_dec_lt(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec_ref(v_items_1250_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_nat_dec_le(v___x_1252_, v___x_1252_);
if (v___x_1254_ == 0)
{
if (v___x_1253_ == 0)
{
lean_dec_ref(v_items_1250_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = lean_usize_of_nat(v___x_1252_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1250_, v___x_1255_, v___x_1256_, v_b_1225_);
lean_dec_ref(v_items_1250_);
v___y_1227_ = v___x_1257_;
goto v___jp_1226_;
}
}
else
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = lean_usize_of_nat(v___x_1252_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1250_, v___x_1258_, v___x_1259_, v_b_1225_);
lean_dec_ref(v_items_1250_);
v___y_1227_ = v___x_1260_;
goto v___jp_1226_;
}
}
}
case 2:
{
lean_object* v_view_1261_; lean_object* v_items_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_view_1261_ = lean_ctor_get(v_val_1239_, 0);
lean_inc_ref(v_view_1261_);
lean_dec_ref_known(v_val_1239_, 1);
v_items_1262_ = lean_ctor_get(v_view_1261_, 2);
lean_inc_ref(v_items_1262_);
lean_dec_ref(v_view_1261_);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_array_get_size(v_items_1262_);
v___x_1265_ = lean_nat_dec_lt(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec_ref(v_items_1262_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_nat_dec_le(v___x_1264_, v___x_1264_);
if (v___x_1266_ == 0)
{
if (v___x_1265_ == 0)
{
lean_dec_ref(v_items_1262_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = ((size_t)0ULL);
v___x_1268_ = lean_usize_of_nat(v___x_1264_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1262_, v___x_1267_, v___x_1268_, v_b_1225_);
lean_dec_ref(v_items_1262_);
v___y_1227_ = v___x_1269_;
goto v___jp_1226_;
}
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = ((size_t)0ULL);
v___x_1271_ = lean_usize_of_nat(v___x_1264_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1262_, v___x_1270_, v___x_1271_, v_b_1225_);
lean_dec_ref(v_items_1262_);
v___y_1227_ = v___x_1272_;
goto v___jp_1226_;
}
}
}
case 3:
{
lean_object* v_view_1273_; lean_object* v_items_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_view_1273_ = lean_ctor_get(v_val_1239_, 0);
lean_inc_ref(v_view_1273_);
lean_dec_ref_known(v_val_1239_, 1);
v_items_1274_ = lean_ctor_get(v_view_1273_, 1);
lean_inc_ref(v_items_1274_);
lean_dec_ref(v_view_1273_);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_array_get_size(v_items_1274_);
v___x_1277_ = lean_nat_dec_lt(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
lean_dec_ref(v_items_1274_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
uint8_t v___x_1278_; 
v___x_1278_ = lean_nat_dec_le(v___x_1276_, v___x_1276_);
if (v___x_1278_ == 0)
{
if (v___x_1277_ == 0)
{
lean_dec_ref(v_items_1274_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = lean_usize_of_nat(v___x_1276_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1274_, v___x_1279_, v___x_1280_, v_b_1225_);
lean_dec_ref(v_items_1274_);
v___y_1227_ = v___x_1281_;
goto v___jp_1226_;
}
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1276_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1274_, v___x_1282_, v___x_1283_, v_b_1225_);
lean_dec_ref(v_items_1274_);
v___y_1227_ = v___x_1284_;
goto v___jp_1226_;
}
}
}
default: 
{
lean_dec(v_val_1239_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
}
}
else
{
lean_dec(v___x_1238_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
}
else
{
return v_b_1225_;
}
v___jp_1226_:
{
size_t v___x_1228_; size_t v___x_1229_; 
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1223_, v___x_1228_);
v_i_1223_ = v___x_1229_;
v_b_1225_ = v___y_1227_;
goto _start;
}
v___jp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_add(v___y_1232_, v___x_1233_);
lean_dec(v___y_1232_);
v___x_1235_ = lean_nat_dec_le(v_b_1225_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_dec(v___x_1234_);
v___y_1227_ = v_b_1225_;
goto v___jp_1226_;
}
else
{
lean_dec(v_b_1225_);
v___y_1227_ = v___x_1234_;
goto v___jp_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object* v_blks_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_array_get_size(v_blks_1285_);
v___x_1288_ = lean_nat_dec_lt(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
return v___x_1286_;
}
else
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_nat_dec_le(v___x_1287_, v___x_1287_);
if (v___x_1289_ == 0)
{
if (v___x_1288_ == 0)
{
return v___x_1286_;
}
else
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = lean_usize_of_nat(v___x_1287_);
v___x_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1285_, v___x_1290_, v___x_1291_, v___x_1286_);
return v___x_1292_;
}
}
else
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_usize_of_nat(v___x_1287_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1285_, v___x_1293_, v___x_1294_, v___x_1286_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object* v_as_1296_, size_t v_i_1297_, size_t v_stop_1298_, lean_object* v_b_1299_){
_start:
{
lean_object* v___y_1301_; uint8_t v___x_1305_; 
v___x_1305_ = lean_usize_dec_eq(v_i_1297_, v_stop_1298_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v_contents_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1306_ = lean_array_uget_borrowed(v_as_1296_, v_i_1297_);
v_contents_1307_ = lean_ctor_get(v___x_1306_, 2);
v___x_1308_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1307_);
v___x_1309_ = lean_nat_dec_le(v_b_1299_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_dec(v___x_1308_);
v___y_1301_ = v_b_1299_;
goto v___jp_1300_;
}
else
{
lean_dec(v_b_1299_);
v___y_1301_ = v___x_1308_;
goto v___jp_1300_;
}
}
else
{
return v_b_1299_;
}
v___jp_1300_:
{
size_t v___x_1302_; size_t v___x_1303_; 
v___x_1302_ = ((size_t)1ULL);
v___x_1303_ = lean_usize_add(v_i_1297_, v___x_1302_);
v_i_1297_ = v___x_1303_;
v_b_1299_ = v___y_1301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object* v_as_1310_, lean_object* v_i_1311_, lean_object* v_stop_1312_, lean_object* v_b_1313_){
_start:
{
size_t v_i_boxed_1314_; size_t v_stop_boxed_1315_; lean_object* v_res_1316_; 
v_i_boxed_1314_ = lean_unbox_usize(v_i_1311_);
lean_dec(v_i_1311_);
v_stop_boxed_1315_ = lean_unbox_usize(v_stop_1312_);
lean_dec(v_stop_1312_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_as_1310_, v_i_boxed_1314_, v_stop_boxed_1315_, v_b_1313_);
lean_dec_ref(v_as_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object* v_as_1317_, lean_object* v_i_1318_, lean_object* v_stop_1319_, lean_object* v_b_1320_){
_start:
{
size_t v_i_boxed_1321_; size_t v_stop_boxed_1322_; lean_object* v_res_1323_; 
v_i_boxed_1321_ = lean_unbox_usize(v_i_1318_);
lean_dec(v_i_1318_);
v_stop_boxed_1322_ = lean_unbox_usize(v_stop_1319_);
lean_dec(v_stop_1319_);
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_as_1317_, v_i_boxed_1321_, v_stop_boxed_1322_, v_b_1320_);
lean_dec_ref(v_as_1317_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object* v_as_1324_, lean_object* v_i_1325_, lean_object* v_stop_1326_, lean_object* v_b_1327_){
_start:
{
size_t v_i_boxed_1328_; size_t v_stop_boxed_1329_; lean_object* v_res_1330_; 
v_i_boxed_1328_ = lean_unbox_usize(v_i_1325_);
lean_dec(v_i_1325_);
v_stop_boxed_1329_ = lean_unbox_usize(v_stop_1326_);
lean_dec(v_stop_1326_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_as_1324_, v_i_boxed_1328_, v_stop_boxed_1329_, v_b_1327_);
lean_dec_ref(v_as_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object* v_blks_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1331_);
lean_dec_ref(v_blks_1331_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object* v_as_1333_, lean_object* v_i_1334_, lean_object* v_stop_1335_, lean_object* v_b_1336_){
_start:
{
size_t v_i_boxed_1337_; size_t v_stop_boxed_1338_; lean_object* v_res_1339_; 
v_i_boxed_1337_ = lean_unbox_usize(v_i_1334_);
lean_dec(v_i_1334_);
v_stop_boxed_1338_ = lean_unbox_usize(v_stop_1335_);
lean_dec(v_stop_1335_);
v_res_1339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_as_1333_, v_i_boxed_1337_, v_stop_boxed_1338_, v_b_1336_);
lean_dec_ref(v_as_1333_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object* v_blks_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1341_ = lean_unsigned_to_nat(3u);
v___x_1342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1340_);
v___x_1343_ = lean_nat_dec_le(v___x_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_dec(v___x_1342_);
return v___x_1341_;
}
else
{
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object* v_blks_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_blks_1344_);
lean_dec_ref(v_blks_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object* v_inl_1346_){
_start:
{
lean_object* v___x_1347_; 
lean_inc(v_inl_1346_);
v___x_1347_ = l_Lean_Doc_LinebreakView_of(v_inl_1346_);
if (lean_obj_tag(v___x_1347_) == 1)
{
uint8_t v___x_1348_; 
lean_dec_ref_known(v___x_1347_, 1);
lean_dec(v_inl_1346_);
v___x_1348_ = 1;
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; 
lean_dec(v___x_1347_);
v___x_1349_ = l_Lean_Doc_TextView_of(v_inl_1346_);
if (lean_obj_tag(v___x_1349_) == 1)
{
lean_object* v_val_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v_decide_1358_; 
v_val_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = 1;
v___x_1352_ = l_Lean_Doc_TextView_getVersoText(v_val_1350_);
lean_dec(v_val_1350_);
v___x_1353_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = lean_string_utf8_byte_size(v___x_1353_);
v___x_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1354_);
lean_ctor_set(v___x_1356_, 2, v___x_1355_);
v___x_1357_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1356_, v___x_1354_);
lean_dec_ref_known(v___x_1356_, 3);
v_decide_1358_ = lean_nat_dec_eq(v___x_1357_, v___x_1355_);
lean_dec(v___x_1357_);
return v_decide_1358_;
}
else
{
uint8_t v___x_1359_; 
lean_dec(v___x_1349_);
v___x_1359_ = 0;
return v___x_1359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object* v_inl_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v_inl_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object* v_stx_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Doc_BlockView_of(v_stx_1363_);
if (lean_obj_tag(v___x_1364_) == 1)
{
lean_object* v_val_1365_; 
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v___x_1364_, 1);
switch(lean_obj_tag(v_val_1365_))
{
case 8:
{
uint8_t v___x_1366_; 
lean_dec_ref_known(v_val_1365_, 1);
v___x_1366_ = 1;
return v___x_1366_;
}
case 9:
{
uint8_t v___x_1367_; 
lean_dec_ref_known(v_val_1365_, 1);
v___x_1367_ = 1;
return v___x_1367_;
}
case 10:
{
uint8_t v___x_1368_; 
lean_dec_ref_known(v_val_1365_, 1);
v___x_1368_ = 1;
return v___x_1368_;
}
case 11:
{
uint8_t v___x_1369_; 
lean_dec_ref_known(v_val_1365_, 1);
v___x_1369_ = 1;
return v___x_1369_;
}
default: 
{
uint8_t v___x_1370_; 
lean_dec(v_val_1365_);
v___x_1370_ = 0;
return v___x_1370_;
}
}
}
else
{
uint8_t v___x_1371_; 
lean_dec(v___x_1364_);
v___x_1371_ = 0;
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object* v_stx_1372_){
_start:
{
uint8_t v_res_1373_; lean_object* v_r_1374_; 
v_res_1373_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v_stx_1372_);
v_r_1374_ = lean_box(v_res_1373_);
return v_r_1374_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object* v_inl_1375_){
_start:
{
lean_object* v___x_1376_; 
lean_inc(v_inl_1375_);
v___x_1376_ = l_Lean_Doc_LinebreakView_of(v_inl_1375_);
if (lean_obj_tag(v___x_1376_) == 1)
{
uint8_t v___x_1377_; 
lean_dec_ref_known(v___x_1376_, 1);
lean_dec(v_inl_1375_);
v___x_1377_ = 1;
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; 
lean_dec(v___x_1376_);
v___x_1378_ = l_Lean_Doc_TextView_of(v_inl_1375_);
if (lean_obj_tag(v___x_1378_) == 1)
{
lean_object* v_val_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v_decide_1385_; 
v_val_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = l_Lean_Doc_TextView_getVersoTextSource(v_val_1379_);
lean_dec(v_val_1379_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_string_utf8_byte_size(v___x_1380_);
v___x_1383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1380_);
lean_ctor_set(v___x_1383_, 1, v___x_1381_);
lean_ctor_set(v___x_1383_, 2, v___x_1382_);
v___x_1384_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1383_, v___x_1381_);
lean_dec_ref_known(v___x_1383_, 3);
v_decide_1385_ = lean_nat_dec_eq(v___x_1384_, v___x_1382_);
lean_dec(v___x_1384_);
return v_decide_1385_;
}
else
{
uint8_t v___x_1386_; 
lean_dec(v___x_1378_);
v___x_1386_ = 0;
return v___x_1386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object* v_inl_1387_){
_start:
{
uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_res_1388_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v_inl_1387_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object* v_as_1390_, size_t v_i_1391_, size_t v_stop_1392_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_usize_dec_eq(v_i_1391_, v_stop_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_array_uget_borrowed(v_as_1390_, v_i_1391_);
lean_inc(v___x_1394_);
v___x_1395_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1394_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
v___x_1396_ = 1;
return v___x_1396_;
}
else
{
size_t v___x_1397_; size_t v___x_1398_; 
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_i_1391_, v___x_1397_);
v_i_1391_ = v___x_1398_;
goto _start;
}
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = 0;
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object* v_as_1401_, lean_object* v_i_1402_, lean_object* v_stop_1403_){
_start:
{
size_t v_i_boxed_1404_; size_t v_stop_boxed_1405_; uint8_t v_res_1406_; lean_object* v_r_1407_; 
v_i_boxed_1404_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_stop_boxed_1405_ = lean_unbox_usize(v_stop_1403_);
lean_dec(v_stop_1403_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_as_1401_, v_i_boxed_1404_, v_stop_boxed_1405_);
lean_dec_ref(v_as_1401_);
v_r_1407_ = lean_box(v_res_1406_);
return v_r_1407_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object* v_stx_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Doc_ParaView_of(v_stx_1408_);
if (lean_obj_tag(v___x_1409_) == 1)
{
lean_object* v_val_1410_; lean_object* v_content_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_val_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_val_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v_content_1411_ = lean_ctor_get(v_val_1410_, 1);
lean_inc_ref(v_content_1411_);
lean_dec(v_val_1410_);
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_content_1411_);
v___x_1414_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; 
lean_dec_ref(v_content_1411_);
v___x_1415_ = 1;
return v___x_1415_;
}
else
{
if (v___x_1414_ == 0)
{
lean_dec_ref(v_content_1411_);
return v___x_1414_;
}
else
{
size_t v___x_1416_; size_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1413_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_content_1411_, v___x_1416_, v___x_1417_);
lean_dec_ref(v_content_1411_);
if (v___x_1418_ == 0)
{
return v___x_1414_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = 0;
return v___x_1419_;
}
}
}
}
else
{
uint8_t v___x_1420_; 
lean_dec(v___x_1409_);
v___x_1420_ = 0;
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object* v_stx_1421_){
_start:
{
uint8_t v_res_1422_; lean_object* v_r_1423_; 
v_res_1422_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_stx_1421_);
v_r_1423_ = lean_box(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object* v_stx_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_Doc_LinebreakView_of(v_stx_1424_);
if (lean_obj_tag(v___x_1425_) == 1)
{
uint8_t v___x_1426_; 
lean_dec_ref_known(v___x_1425_, 1);
v___x_1426_ = 1;
return v___x_1426_;
}
else
{
uint8_t v___x_1427_; 
lean_dec(v___x_1425_);
v___x_1427_ = 0;
return v___x_1427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object* v_stx_1428_){
_start:
{
uint8_t v_res_1429_; lean_object* v_r_1430_; 
v_res_1429_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v_stx_1428_);
v_r_1430_ = lean_box(v_res_1429_);
return v_r_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object* v_inls_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_array_get_size(v_inls_1431_);
v___x_1433_ = lean_unsigned_to_nat(1u);
v___x_1434_ = lean_nat_dec_eq(v___x_1432_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_box(0);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; lean_object* v_inl_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v_inl_1437_ = lean_array_fget_borrowed(v_inls_1431_, v___x_1436_);
lean_inc(v_inl_1437_);
v___x_1438_ = l_Lean_Doc_InlineView_of(v_inl_1437_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_box(0);
return v___x_1439_;
}
else
{
lean_object* v_val_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1463_; 
v_val_1440_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1463_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_val_1440_);
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1463_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
switch(lean_obj_tag(v_val_1440_))
{
case 1:
{
lean_object* v___x_1445_; 
lean_dec_ref_known(v_val_1440_, 1);
lean_inc(v_inl_1437_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v_inl_1437_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_inl_1437_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
case 2:
{
lean_object* v___x_1448_; 
lean_dec_ref_known(v_val_1440_, 1);
lean_inc(v_inl_1437_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v_inl_1437_);
v___x_1448_ = v___x_1442_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_inl_1437_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
case 3:
{
lean_object* v___x_1451_; 
lean_dec_ref_known(v_val_1440_, 1);
lean_inc(v_inl_1437_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v_inl_1437_);
v___x_1451_ = v___x_1442_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_inl_1437_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
case 4:
{
lean_object* v___x_1454_; 
lean_dec_ref_known(v_val_1440_, 1);
lean_inc(v_inl_1437_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v_inl_1437_);
v___x_1454_ = v___x_1442_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_inl_1437_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
case 6:
{
lean_object* v___x_1457_; 
lean_dec_ref_known(v_val_1440_, 1);
lean_inc(v_inl_1437_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v_inl_1437_);
v___x_1457_ = v___x_1442_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_inl_1437_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
case 9:
{
lean_object* v___x_1460_; 
lean_dec_ref_known(v_val_1440_, 1);
lean_inc(v_inl_1437_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v_inl_1437_);
v___x_1460_ = v___x_1442_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_inl_1437_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
default: 
{
lean_object* v___x_1462_; 
lean_del_object(v___x_1442_);
lean_dec(v_val_1440_);
v___x_1462_ = lean_box(0);
return v___x_1462_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object* v_inls_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_inls_1464_);
lean_dec_ref(v_inls_1464_);
return v_res_1465_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = 41;
v___x_1467_ = lean_box_uint32(v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = 93;
v___x_1471_ = lean_box_uint32(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object* v_a_1474_){
_start:
{
if (lean_obj_tag(v_a_1474_) == 0)
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_a_1477_);
lean_dec_ref(v_a_1477_);
return v_res_1478_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = 95;
v___x_1480_ = lean_box_uint32(v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = 42;
v___x_1484_ = lean_box_uint32(v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = 96;
v___x_1488_ = lean_box_uint32(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
v___x_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object* v_inl_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Doc_InlineView_of(v_inl_1491_);
if (lean_obj_tag(v___x_1492_) == 1)
{
lean_object* v_val_1493_; 
v_val_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_val_1493_);
lean_dec_ref_known(v___x_1492_, 1);
switch(lean_obj_tag(v_val_1493_))
{
case 1:
{
lean_object* v___x_1494_; 
lean_dec_ref_known(v_val_1493_, 1);
v___x_1494_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1494_;
}
case 2:
{
lean_object* v___x_1495_; 
lean_dec_ref_known(v_val_1493_, 1);
v___x_1495_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1495_;
}
case 3:
{
lean_object* v___x_1496_; 
lean_dec_ref_known(v_val_1493_, 1);
v___x_1496_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1496_;
}
case 4:
{
lean_object* v___x_1497_; 
lean_dec_ref_known(v_val_1493_, 1);
v___x_1497_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1497_;
}
case 5:
{
lean_object* v_view_1498_; lean_object* v_target_1499_; lean_object* v___x_1500_; 
v_view_1498_ = lean_ctor_get(v_val_1493_, 0);
lean_inc_ref(v_view_1498_);
lean_dec_ref_known(v_val_1493_, 1);
v_target_1499_ = lean_ctor_get(v_view_1498_, 4);
lean_inc_ref(v_target_1499_);
lean_dec_ref(v_view_1498_);
v___x_1500_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1499_);
lean_dec_ref(v_target_1499_);
return v___x_1500_;
}
case 6:
{
lean_object* v_view_1501_; lean_object* v_target_1502_; lean_object* v___x_1503_; 
v_view_1501_ = lean_ctor_get(v_val_1493_, 0);
lean_inc_ref(v_view_1501_);
lean_dec_ref_known(v_val_1493_, 1);
v_target_1502_ = lean_ctor_get(v_view_1501_, 4);
lean_inc_ref(v_target_1502_);
lean_dec_ref(v_view_1501_);
v___x_1503_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1502_);
lean_dec_ref(v_target_1502_);
return v___x_1503_;
}
case 7:
{
lean_object* v___x_1504_; 
lean_dec_ref_known(v_val_1493_, 1);
v___x_1504_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1504_;
}
case 9:
{
lean_object* v_view_1505_; lean_object* v_content_1506_; lean_object* v___x_1507_; 
v_view_1505_ = lean_ctor_get(v_val_1493_, 0);
lean_inc_ref(v_view_1505_);
lean_dec_ref_known(v_val_1493_, 1);
v_content_1506_ = lean_ctor_get(v_view_1505_, 6);
lean_inc_ref(v_content_1506_);
lean_dec_ref(v_view_1505_);
v___x_1507_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_1506_);
lean_dec_ref(v_content_1506_);
if (lean_obj_tag(v___x_1507_) == 1)
{
lean_object* v_val_1508_; 
v_val_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1508_);
lean_dec_ref_known(v___x_1507_, 1);
v_inl_1491_ = v_val_1508_;
goto _start;
}
else
{
lean_object* v___x_1510_; 
lean_dec(v___x_1507_);
v___x_1510_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1510_;
}
}
default: 
{
lean_object* v___x_1511_; 
lean_dec(v_val_1493_);
v___x_1511_ = lean_box(0);
return v___x_1511_;
}
}
}
else
{
lean_object* v___x_1512_; 
lean_dec(v___x_1492_);
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = 36;
v___x_1514_ = lean_box_uint32(v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object* v_stx_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Doc_InlineView_of(v_stx_1517_);
if (lean_obj_tag(v___x_1518_) == 1)
{
lean_object* v_val_1519_; 
v_val_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v___x_1518_, 1);
switch(lean_obj_tag(v_val_1519_))
{
case 1:
{
lean_object* v___x_1520_; 
lean_dec_ref_known(v_val_1519_, 1);
v___x_1520_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1520_;
}
case 2:
{
lean_object* v___x_1521_; 
lean_dec_ref_known(v_val_1519_, 1);
v___x_1521_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1521_;
}
case 3:
{
lean_object* v___x_1522_; 
lean_dec_ref_known(v_val_1519_, 1);
v___x_1522_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1522_;
}
case 4:
{
lean_object* v___x_1523_; 
lean_dec_ref_known(v_val_1519_, 1);
v___x_1523_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0);
return v___x_1523_;
}
default: 
{
lean_object* v___x_1524_; 
lean_dec(v_val_1519_);
v___x_1524_ = lean_box(0);
return v___x_1524_;
}
}
}
else
{
lean_object* v___x_1525_; 
lean_dec(v___x_1518_);
v___x_1525_ = lean_box(0);
return v___x_1525_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object* v_inl_1526_, lean_object* v_next_x3f_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1526_);
if (lean_obj_tag(v___x_1528_) == 1)
{
if (lean_obj_tag(v_next_x3f_1527_) == 0)
{
uint8_t v___x_1529_; 
lean_dec_ref_known(v___x_1528_, 1);
v___x_1529_ = 0;
return v___x_1529_;
}
else
{
lean_object* v_val_1530_; lean_object* v_val_1531_; lean_object* v___x_1532_; 
v_val_1530_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_val_1530_);
lean_dec_ref_known(v___x_1528_, 1);
v_val_1531_ = lean_ctor_get(v_next_x3f_1527_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v_next_x3f_1527_, 1);
v___x_1532_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1531_);
if (lean_obj_tag(v___x_1532_) == 1)
{
lean_object* v_val_1533_; uint32_t v___x_1534_; uint32_t v___x_1535_; uint8_t v___x_1536_; 
v_val_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = lean_unbox_uint32(v_val_1530_);
lean_dec(v_val_1530_);
v___x_1535_ = lean_unbox_uint32(v_val_1533_);
lean_dec(v_val_1533_);
v___x_1536_ = lean_uint32_dec_eq(v___x_1534_, v___x_1535_);
return v___x_1536_;
}
else
{
uint8_t v___x_1537_; 
lean_dec(v___x_1532_);
lean_dec(v_val_1530_);
v___x_1537_ = 0;
return v___x_1537_;
}
}
}
else
{
uint8_t v___x_1538_; 
lean_dec(v___x_1528_);
lean_dec(v_next_x3f_1527_);
v___x_1538_ = 0;
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object* v_inl_1539_, lean_object* v_next_x3f_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_inl_1539_, v_next_x3f_1540_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object* v_inl_1543_, lean_object* v_next_x3f_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1543_);
if (lean_obj_tag(v___x_1545_) == 1)
{
lean_object* v_val_1546_; uint32_t v___x_1547_; uint32_t v___x_1548_; uint8_t v___x_1549_; 
v_val_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = 96;
v___x_1548_ = lean_unbox_uint32(v_val_1546_);
lean_dec(v_val_1546_);
v___x_1549_ = lean_uint32_dec_eq(v___x_1548_, v___x_1547_);
if (v___x_1549_ == 0)
{
lean_dec(v_next_x3f_1544_);
return v___x_1549_;
}
else
{
if (lean_obj_tag(v_next_x3f_1544_) == 0)
{
uint8_t v___x_1550_; 
v___x_1550_ = 0;
return v___x_1550_;
}
else
{
lean_object* v_val_1551_; lean_object* v___x_1552_; 
v_val_1551_ = lean_ctor_get(v_next_x3f_1544_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v_next_x3f_1544_, 1);
v___x_1552_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1551_);
if (lean_obj_tag(v___x_1552_) == 1)
{
lean_object* v_val_1553_; uint32_t v___x_1554_; uint8_t v___x_1555_; 
v_val_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = lean_unbox_uint32(v_val_1553_);
lean_dec(v_val_1553_);
v___x_1555_ = lean_uint32_dec_eq(v___x_1554_, v___x_1547_);
return v___x_1555_;
}
else
{
uint8_t v___x_1556_; 
lean_dec(v___x_1552_);
v___x_1556_ = 0;
return v___x_1556_;
}
}
}
}
else
{
uint8_t v___x_1557_; 
lean_dec(v___x_1545_);
lean_dec(v_next_x3f_1544_);
v___x_1557_ = 0;
return v___x_1557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object* v_inl_1558_, lean_object* v_next_x3f_1559_){
_start:
{
uint8_t v_res_1560_; lean_object* v_r_1561_; 
v_res_1560_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v_inl_1558_, v_next_x3f_1559_);
v_r_1561_ = lean_box(v_res_1560_);
return v_r_1561_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object* v_inls_1562_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_array_get_size(v_inls_1562_);
v___x_1565_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = lean_array_fget_borrowed(v_inls_1562_, v___x_1563_);
lean_inc(v___x_1566_);
v___x_1567_ = l_Lean_Doc_TextView_of(v___x_1566_);
if (lean_obj_tag(v___x_1567_) == 1)
{
lean_object* v_val_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_val_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = l_Lean_Doc_TextView_getVersoText(v_val_1568_);
lean_dec(v_val_1568_);
v___x_1570_ = lean_string_utf8_byte_size(v___x_1569_);
v___x_1571_ = lean_unsigned_to_nat(1u);
v___x_1572_ = lean_nat_dec_le(v___x_1571_, v___x_1570_);
if (v___x_1572_ == 0)
{
lean_dec_ref(v___x_1569_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1574_ = lean_string_memcmp(v___x_1569_, v___x_1573_, v___x_1563_, v___x_1563_, v___x_1571_);
lean_dec_ref(v___x_1569_);
return v___x_1574_;
}
}
else
{
uint8_t v___x_1575_; 
lean_dec(v___x_1567_);
v___x_1575_ = 0;
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object* v_inls_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_inls_1576_);
lean_dec_ref(v_inls_1576_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object* v_x_1582_, lean_object* v_a_1583_){
_start:
{
if (lean_obj_tag(v_x_1582_) == 0)
{
lean_object* v_url_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v_snd_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_snd_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_url_1584_ = lean_ctor_get(v_x_1582_, 2);
v___x_1585_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_1586_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1585_, v_a_1583_);
v_snd_1587_ = lean_ctor_get(v___x_1586_, 1);
lean_inc(v_snd_1587_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = l_Lean_TSyntax_getVersoLinkUrl(v_url_1584_);
v___x_1589_ = l_Lean_Doc_escapeVersoLinkUrl(v___x_1588_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1589_, v_snd_1587_);
lean_dec_ref(v___x_1589_);
v_snd_1591_ = lean_ctor_get(v___x_1590_, 1);
lean_inc(v_snd_1591_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_1593_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1592_, v_snd_1591_);
return v___x_1593_;
}
else
{
lean_object* v_name_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_snd_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v_snd_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_name_1594_ = lean_ctor_get(v_x_1582_, 2);
v___x_1595_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_1596_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1595_, v_a_1583_);
v_snd_1597_ = lean_ctor_get(v___x_1596_, 1);
lean_inc(v_snd_1597_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = l_Lean_TSyntax_getVersoRefName(v_name_1594_);
v___x_1599_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1598_, v_snd_1597_);
lean_dec_ref(v___x_1598_);
v_snd_1600_ = lean_ctor_get(v___x_1599_, 1);
lean_inc(v_snd_1600_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_1602_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1601_, v_snd_1600_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object* v_x_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1603_, v_a_1604_);
lean_dec_ref(v_x_1603_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object* v_x_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1606_, v_a_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object* v_x_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(v_x_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1611_);
lean_dec_ref(v_x_1610_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object* v_s_1614_, lean_object* v_pos_1615_){
_start:
{
lean_object* v_str_1616_; lean_object* v_startInclusive_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v_decide_1621_; 
v_str_1616_ = lean_ctor_get(v_s_1614_, 0);
v_startInclusive_1617_ = lean_ctor_get(v_s_1614_, 1);
v___x_1618_ = lean_nat_add(v_startInclusive_1617_, v_pos_1615_);
v___x_1619_ = lean_nat_sub(v___x_1618_, v_startInclusive_1617_);
v___x_1620_ = lean_unsigned_to_nat(0u);
v_decide_1621_ = lean_nat_dec_eq(v___x_1619_, v___x_1620_);
if (v_decide_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; uint32_t v___x_1627_; uint32_t v___x_1628_; uint8_t v___x_1629_; 
lean_inc(v_startInclusive_1617_);
lean_inc_ref(v_str_1616_);
v___x_1622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1622_, 0, v_str_1616_);
lean_ctor_set(v___x_1622_, 1, v_startInclusive_1617_);
lean_ctor_set(v___x_1622_, 2, v___x_1618_);
v___x_1623_ = lean_unsigned_to_nat(1u);
v___x_1624_ = lean_nat_sub(v___x_1619_, v___x_1623_);
lean_dec(v___x_1619_);
v___x_1625_ = l_String_Slice_posLE(v___x_1622_, v___x_1624_);
lean_dec_ref_known(v___x_1622_, 3);
v___x_1626_ = lean_nat_add(v_startInclusive_1617_, v___x_1625_);
v___x_1627_ = lean_string_utf8_get_fast(v_str_1616_, v___x_1626_);
lean_dec(v___x_1626_);
v___x_1628_ = 32;
v___x_1629_ = lean_uint32_dec_eq(v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_dec(v___x_1625_);
return v_pos_1615_;
}
else
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = lean_nat_add(v___x_1625_, v___x_1623_);
v___x_1631_ = lean_nat_dec_le(v___x_1630_, v_pos_1615_);
lean_dec(v___x_1630_);
if (v___x_1631_ == 0)
{
lean_dec(v___x_1625_);
return v_pos_1615_;
}
else
{
lean_dec(v_pos_1615_);
v_pos_1615_ = v___x_1625_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1619_);
lean_dec(v___x_1618_);
return v_pos_1615_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object* v_s_1633_, lean_object* v_pos_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v_s_1633_, v_pos_1634_);
lean_dec_ref(v_s_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object* v_marker_1636_, lean_object* v_contents_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_alone_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_string_utf8_byte_size(v_marker_1636_);
lean_inc_ref(v_marker_1636_);
v___x_1641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1641_, 0, v_marker_1636_);
lean_ctor_set(v___x_1641_, 1, v___x_1639_);
lean_ctor_set(v___x_1641_, 2, v___x_1640_);
v___x_1642_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v___x_1641_, v___x_1640_);
lean_dec_ref_known(v___x_1641_, 3);
v_alone_1643_ = lean_string_utf8_extract_fast(v_marker_1636_, v___x_1639_, v___x_1642_);
lean_dec(v___x_1642_);
v___x_1644_ = lean_array_get_size(v_contents_1637_);
v___x_1645_ = lean_nat_dec_lt(v___x_1639_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v_marker_1636_);
v___x_1646_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_alone_1643_, v_a_1638_);
lean_dec_ref(v_alone_1643_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; uint8_t v___x_1648_; 
v___x_1647_ = lean_array_fget_borrowed(v_contents_1637_, v___x_1639_);
lean_inc(v___x_1647_);
v___x_1648_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_dec_ref(v_alone_1643_);
v___x_1649_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_marker_1636_, v_a_1638_);
lean_dec_ref(v_marker_1636_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_marker_1636_);
v___x_1650_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_1651_ = lean_string_append(v_alone_1643_, v___x_1650_);
v___x_1652_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1651_, v_a_1638_);
lean_dec_ref(v___x_1651_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object* v_marker_1653_, lean_object* v_contents_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1653_, v_contents_1654_, v_a_1655_);
lean_dec_ref(v_contents_1654_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object* v_marker_1657_, lean_object* v_contents_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1657_, v_contents_1658_, v_a_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object* v_marker_1662_, lean_object* v_contents_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(v_marker_1662_, v_contents_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_contents_1663_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object* v_as_1667_, size_t v_i_1668_, size_t v_stop_1669_, lean_object* v_b_1670_){
_start:
{
lean_object* v___y_1672_; uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_eq(v_i_1668_, v_stop_1669_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = lean_array_uget_borrowed(v_as_1667_, v_i_1668_);
lean_inc(v___x_1677_);
v___x_1678_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_inc(v___x_1677_);
v___x_1679_ = lean_array_push(v_b_1670_, v___x_1677_);
v___y_1672_ = v___x_1679_;
goto v___jp_1671_;
}
else
{
v___y_1672_ = v_b_1670_;
goto v___jp_1671_;
}
}
else
{
return v_b_1670_;
}
v___jp_1671_:
{
size_t v___x_1673_; size_t v___x_1674_; 
v___x_1673_ = ((size_t)1ULL);
v___x_1674_ = lean_usize_add(v_i_1668_, v___x_1673_);
v_i_1668_ = v___x_1674_;
v_b_1670_ = v___y_1672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object* v_as_1680_, lean_object* v_i_1681_, lean_object* v_stop_1682_, lean_object* v_b_1683_){
_start:
{
size_t v_i_boxed_1684_; size_t v_stop_boxed_1685_; lean_object* v_res_1686_; 
v_i_boxed_1684_ = lean_unbox_usize(v_i_1681_);
lean_dec(v_i_1681_);
v_stop_boxed_1685_ = lean_unbox_usize(v_stop_1682_);
lean_dec(v_stop_1682_);
v_res_1686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_as_1680_, v_i_boxed_1684_, v_stop_boxed_1685_, v_b_1683_);
lean_dec_ref(v_as_1680_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t v_sz_1687_, size_t v_i_1688_, lean_object* v_bs_1689_){
_start:
{
uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_lt(v_i_1688_, v_sz_1687_);
if (v___x_1690_ == 0)
{
return v_bs_1689_;
}
else
{
lean_object* v_v_1691_; lean_object* v___x_1692_; lean_object* v_bs_x27_1693_; size_t v___x_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
v_v_1691_ = lean_array_uget(v_bs_1689_, v_i_1688_);
v___x_1692_ = lean_unsigned_to_nat(0u);
v_bs_x27_1693_ = lean_array_uset(v_bs_1689_, v_i_1688_, v___x_1692_);
v___x_1694_ = ((size_t)1ULL);
v___x_1695_ = lean_usize_add(v_i_1688_, v___x_1694_);
v___x_1696_ = lean_array_uset(v_bs_x27_1693_, v_i_1688_, v_v_1691_);
v_i_1688_ = v___x_1695_;
v_bs_1689_ = v___x_1696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_sz_1698_, lean_object* v_i_1699_, lean_object* v_bs_1700_){
_start:
{
size_t v_sz_boxed_1701_; size_t v_i_boxed_1702_; lean_object* v_res_1703_; 
v_sz_boxed_1701_ = lean_unbox_usize(v_sz_1698_);
lean_dec(v_sz_1698_);
v_i_boxed_1702_ = lean_unbox_usize(v_i_1699_);
lean_dec(v_i_1699_);
v_res_1703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_boxed_1701_, v_i_boxed_1702_, v_bs_1700_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
lean_object* v_zero_1706_; uint8_t v_isZero_1707_; 
v_zero_1706_ = lean_unsigned_to_nat(0u);
v_isZero_1707_ = lean_nat_dec_eq(v_x_1704_, v_zero_1706_);
if (v_isZero_1707_ == 1)
{
lean_dec(v_x_1704_);
return v_x_1705_;
}
else
{
uint32_t v___x_1708_; lean_object* v_one_1709_; lean_object* v_n_1710_; lean_object* v___x_1711_; 
v___x_1708_ = 35;
v_one_1709_ = lean_unsigned_to_nat(1u);
v_n_1710_ = lean_nat_sub(v_x_1704_, v_one_1709_);
lean_dec(v_x_1704_);
v___x_1711_ = lean_string_push(v_x_1705_, v___x_1708_);
v_x_1704_ = v_n_1710_;
v_x_1705_ = v___x_1711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v_zero_1715_; uint8_t v_isZero_1716_; 
v_zero_1715_ = lean_unsigned_to_nat(0u);
v_isZero_1716_ = lean_nat_dec_eq(v_x_1713_, v_zero_1715_);
if (v_isZero_1716_ == 1)
{
lean_dec(v_x_1713_);
return v_x_1714_;
}
else
{
uint32_t v___x_1717_; lean_object* v_one_1718_; lean_object* v_n_1719_; lean_object* v___x_1720_; 
v___x_1717_ = 58;
v_one_1718_ = lean_unsigned_to_nat(1u);
v_n_1719_ = lean_nat_sub(v_x_1713_, v_one_1718_);
lean_dec(v_x_1713_);
v___x_1720_ = lean_string_push(v_x_1714_, v___x_1717_);
v_x_1713_ = v_n_1719_;
v_x_1714_ = v___x_1720_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t v_char_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v_zero_1725_; uint8_t v_isZero_1726_; 
v_zero_1725_ = lean_unsigned_to_nat(0u);
v_isZero_1726_ = lean_nat_dec_eq(v_x_1723_, v_zero_1725_);
if (v_isZero_1726_ == 1)
{
lean_dec(v_x_1723_);
return v_x_1724_;
}
else
{
lean_object* v_one_1727_; lean_object* v_n_1728_; lean_object* v___x_1729_; 
v_one_1727_ = lean_unsigned_to_nat(1u);
v_n_1728_ = lean_nat_sub(v_x_1723_, v_one_1727_);
lean_dec(v_x_1723_);
v___x_1729_ = lean_string_push(v_x_1724_, v_char_1722_);
v_x_1723_ = v_n_1728_;
v_x_1724_ = v___x_1729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object* v_char_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
uint32_t v_char_boxed_1734_; lean_object* v_res_1735_; 
v_char_boxed_1734_ = lean_unbox_uint32(v_char_1731_);
lean_dec(v_char_1731_);
v_res_1735_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_boxed_1734_, v_x_1732_, v_x_1733_);
return v_res_1735_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
if (lean_obj_tag(v_x_1737_) == 0)
{
uint8_t v___x_1738_; 
v___x_1738_ = 1;
return v___x_1738_;
}
else
{
uint8_t v___x_1739_; 
v___x_1739_ = 0;
return v___x_1739_;
}
}
else
{
if (lean_obj_tag(v_x_1737_) == 0)
{
uint8_t v___x_1740_; 
v___x_1740_ = 0;
return v___x_1740_;
}
else
{
lean_object* v_val_1741_; lean_object* v_val_1742_; uint32_t v___x_1743_; uint32_t v___x_1744_; uint8_t v___x_1745_; 
v_val_1741_ = lean_ctor_get(v_x_1736_, 0);
v_val_1742_ = lean_ctor_get(v_x_1737_, 0);
v___x_1743_ = lean_unbox_uint32(v_val_1741_);
v___x_1744_ = lean_unbox_uint32(v_val_1742_);
v___x_1745_ = lean_uint32_dec_eq(v___x_1743_, v___x_1744_);
return v___x_1745_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
uint8_t v_res_1748_; lean_object* v_r_1749_; 
v_res_1748_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v_x_1746_, v_x_1747_);
lean_dec(v_x_1747_);
lean_dec(v_x_1746_);
v_r_1749_ = lean_box(v_res_1748_);
return v_r_1749_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg(){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0));
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___boxed(lean_object* v___dummy_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v_res_1755_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t v___x_1756_, lean_object* v_as_1757_, size_t v_i_1758_, size_t v_stop_1759_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_eq(v_i_1758_, v_stop_1759_);
if (v___x_1760_ == 0)
{
uint8_t v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1761_ = 1;
v___x_1762_ = lean_array_uget_borrowed(v_as_1757_, v_i_1758_);
lean_inc(v___x_1762_);
v___x_1763_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1762_);
if (v___x_1763_ == 0)
{
return v___x_1761_;
}
else
{
if (v___x_1756_ == 0)
{
size_t v___x_1764_; size_t v___x_1765_; 
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1758_, v___x_1764_);
v_i_1758_ = v___x_1765_;
goto _start;
}
else
{
return v___x_1761_;
}
}
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v___x_1768_, lean_object* v_as_1769_, lean_object* v_i_1770_, lean_object* v_stop_1771_){
_start:
{
uint8_t v___x_61874__boxed_1772_; size_t v_i_boxed_1773_; size_t v_stop_boxed_1774_; uint8_t v_res_1775_; lean_object* v_r_1776_; 
v___x_61874__boxed_1772_ = lean_unbox(v___x_1768_);
v_i_boxed_1773_ = lean_unbox_usize(v_i_1770_);
lean_dec(v_i_1770_);
v_stop_boxed_1774_ = lean_unbox_usize(v_stop_1771_);
lean_dec(v_stop_1771_);
v_res_1775_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_61874__boxed_1772_, v_as_1769_, v_i_boxed_1773_, v_stop_boxed_1774_);
lean_dec_ref(v_as_1769_);
v_r_1776_ = lean_box(v_res_1775_);
return v_r_1776_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t v___x_1777_, uint8_t v___x_1778_, lean_object* v_as_1779_, size_t v_i_1780_, size_t v_stop_1781_){
_start:
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_usize_dec_eq(v_i_1780_, v_stop_1781_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; uint8_t v___y_1785_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1783_ = 1;
v___x_1789_ = lean_array_uget_borrowed(v_as_1779_, v_i_1780_);
lean_inc(v___x_1789_);
v___x_1790_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v___x_1789_);
if (v___x_1790_ == 0)
{
v___y_1785_ = v___x_1777_;
goto v___jp_1784_;
}
else
{
v___y_1785_ = v___x_1778_;
goto v___jp_1784_;
}
v___jp_1784_:
{
if (v___y_1785_ == 0)
{
size_t v___x_1786_; size_t v___x_1787_; 
v___x_1786_ = ((size_t)1ULL);
v___x_1787_ = lean_usize_add(v_i_1780_, v___x_1786_);
v_i_1780_ = v___x_1787_;
goto _start;
}
else
{
return v___x_1783_;
}
}
}
else
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v___x_1792_, lean_object* v___x_1793_, lean_object* v_as_1794_, lean_object* v_i_1795_, lean_object* v_stop_1796_){
_start:
{
uint8_t v___x_61893__boxed_1797_; uint8_t v___x_61894__boxed_1798_; size_t v_i_boxed_1799_; size_t v_stop_boxed_1800_; uint8_t v_res_1801_; lean_object* v_r_1802_; 
v___x_61893__boxed_1797_ = lean_unbox(v___x_1792_);
v___x_61894__boxed_1798_ = lean_unbox(v___x_1793_);
v_i_boxed_1799_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_stop_boxed_1800_ = lean_unbox_usize(v_stop_1796_);
lean_dec(v_stop_1796_);
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_61893__boxed_1797_, v___x_61894__boxed_1798_, v_as_1794_, v_i_boxed_1799_, v_stop_boxed_1800_);
lean_dec_ref(v_as_1794_);
v_r_1802_ = lean_box(v_res_1801_);
return v_r_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___x_1805_, lean_object* v___x_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_){
_start:
{
if (lean_obj_tag(v_a_1807_) == 0)
{
lean_object* v_currPos_1809_; lean_object* v_searcher_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1843_; 
v_currPos_1809_ = lean_ctor_get(v_a_1807_, 0);
v_searcher_1810_ = lean_ctor_get(v_a_1807_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_a_1807_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1812_ = v_a_1807_;
v_isShared_1813_ = v_isSharedCheck_1843_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_searcher_1810_);
lean_inc(v_currPos_1809_);
lean_dec(v_a_1807_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1843_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v_it_1816_; lean_object* v_startInclusive_1817_; lean_object* v_endExclusive_1818_; uint8_t v_decide_1824_; 
v___x_1814_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_decide_1824_ = lean_nat_dec_eq(v_searcher_1810_, v___x_1806_);
if (v_decide_1824_ == 0)
{
uint32_t v___x_1825_; uint32_t v___x_1826_; uint8_t v___x_1827_; 
v___x_1825_ = 10;
v___x_1826_ = lean_string_utf8_get_fast(v___y_1804_, v_searcher_1810_);
v___x_1827_ = lean_uint32_dec_eq(v___x_1826_, v___x_1825_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_string_utf8_next_fast(v___y_1804_, v_searcher_1810_);
lean_dec(v_searcher_1810_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 1, v___x_1828_);
v___x_1830_ = v___x_1812_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_currPos_1809_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
v_a_1807_ = v___x_1830_;
goto _start;
}
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v_slice_1836_; lean_object* v_nextIt_1838_; 
v___x_1833_ = lean_string_utf8_next_fast(v___y_1804_, v_searcher_1810_);
v___x_1834_ = lean_nat_sub(v___x_1833_, v_searcher_1810_);
v___x_1835_ = lean_nat_add(v_searcher_1810_, v___x_1834_);
lean_dec(v___x_1834_);
v_slice_1836_ = l_String_Slice_subslice_x21(v___x_1805_, v_currPos_1809_, v_searcher_1810_);
lean_inc(v___x_1835_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 1, v___x_1835_);
lean_ctor_set(v___x_1812_, 0, v___x_1835_);
v_nextIt_1838_ = v___x_1812_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1835_);
v_nextIt_1838_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v_startInclusive_1839_; lean_object* v_endExclusive_1840_; 
v_startInclusive_1839_ = lean_ctor_get(v_slice_1836_, 0);
lean_inc(v_startInclusive_1839_);
v_endExclusive_1840_ = lean_ctor_get(v_slice_1836_, 1);
lean_inc(v_endExclusive_1840_);
lean_dec_ref(v_slice_1836_);
v_it_1816_ = v_nextIt_1838_;
v_startInclusive_1817_ = v_startInclusive_1839_;
v_endExclusive_1818_ = v_endExclusive_1840_;
goto v___jp_1815_;
}
}
}
else
{
lean_object* v___x_1842_; 
lean_del_object(v___x_1812_);
lean_dec(v_searcher_1810_);
v___x_1842_ = lean_box(1);
lean_inc(v___x_1806_);
v_it_1816_ = v___x_1842_;
v_startInclusive_1817_ = v_currPos_1809_;
v_endExclusive_1818_ = v___x_1806_;
goto v___jp_1815_;
}
v___jp_1815_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_inc(v___y_1803_);
v___x_1819_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v___y_1803_, v___x_1814_);
v___x_1820_ = lean_string_utf8_extract_fast(v___y_1804_, v_startInclusive_1817_, v_endExclusive_1818_);
lean_dec(v_endExclusive_1818_);
lean_dec(v_startInclusive_1817_);
v___x_1821_ = lean_string_append(v___x_1819_, v___x_1820_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = lean_array_push(v_b_1808_, v___x_1821_);
v_a_1807_ = v_it_1816_;
v_b_1808_ = v___x_1822_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1806_);
return v_b_1808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_1844_, v___y_1845_, v___x_1846_, v___x_1847_, v_a_1848_, v_b_1849_);
lean_dec_ref(v___x_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object* v___x_1851_, lean_object* v___x_1852_, lean_object* v_____r_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1856_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v___x_1851_);
v___x_1857_ = lean_box(v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1852_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___y_1855_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object* v___x_1861_, lean_object* v___x_1862_, lean_object* v_____r_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1861_, v___x_1862_, v_____r_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1864_);
return v_res_1866_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0(void){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object* v_upperBound_1874_, lean_object* v___y_1875_, lean_object* v_a_1876_, lean_object* v_b_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___y_1881_; uint8_t v___x_1898_; 
v___x_1898_ = lean_nat_dec_lt(v_a_1876_, v_upperBound_1874_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_dec(v_a_1876_);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_b_1877_);
lean_ctor_set(v___x_1899_, 1, v___y_1879_);
return v___x_1899_;
}
else
{
lean_object* v_fst_1900_; lean_object* v_snd_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___y_1905_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v___y_1925_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_fst_1900_ = lean_ctor_get(v_b_1877_, 0);
lean_inc(v_fst_1900_);
v_snd_1901_ = lean_ctor_get(v_b_1877_, 1);
lean_inc(v_snd_1901_);
lean_dec_ref(v_b_1877_);
v___x_1902_ = lean_array_fget_borrowed(v___y_1875_, v_a_1876_);
lean_inc(v___x_1902_);
v___x_1903_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_snd_1901_, v___x_1902_);
lean_dec(v_snd_1901_);
v___x_1929_ = lean_unsigned_to_nat(1u);
v___x_1930_ = lean_nat_add(v_a_1876_, v___x_1929_);
v___x_1931_ = lean_array_get_size(v___y_1875_);
v___x_1932_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; 
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v___y_1925_ = v___x_1933_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_array_fget_borrowed(v___y_1875_, v___x_1930_);
lean_dec(v___x_1930_);
lean_inc(v___x_1934_);
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
v___y_1925_ = v___x_1935_;
goto v___jp_1924_;
}
v___jp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_box(0);
lean_inc(v___x_1902_);
v___x_1907_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1902_, v___x_1903_, v___x_1906_, v___y_1878_, v___y_1905_);
v___y_1881_ = v___x_1907_;
goto v___jp_1880_;
}
v___jp_1908_:
{
uint8_t v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_unbox(v_fst_1900_);
lean_dec(v_fst_1900_);
lean_inc(v___y_1909_);
lean_inc(v___x_1902_);
v___x_1912_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1902_, v___y_1909_, v___x_1911_, v___y_1910_, v___y_1878_, v___y_1879_);
if (lean_obj_tag(v___y_1909_) == 1)
{
lean_object* v_snd_1913_; lean_object* v___x_1914_; 
v_snd_1913_ = lean_ctor_get(v___x_1912_, 1);
lean_inc(v_snd_1913_);
lean_dec_ref(v___x_1912_);
lean_inc(v___x_1902_);
v___x_1914_ = l_Lean_Doc_RoleView_of(v___x_1902_);
if (lean_obj_tag(v___x_1914_) == 1)
{
lean_dec_ref_known(v___x_1914_, 1);
lean_dec_ref_known(v___y_1909_, 1);
v___y_1905_ = v_snd_1913_;
goto v___jp_1904_;
}
else
{
uint8_t v___x_1915_; 
lean_dec(v___x_1914_);
lean_inc(v___x_1902_);
v___x_1915_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v___x_1902_, v___y_1909_);
if (v___x_1915_ == 0)
{
v___y_1905_ = v_snd_1913_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v___x_1920_; 
v___x_1916_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1917_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1916_, v_snd_1913_);
v_fst_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_fst_1918_);
v_snd_1919_ = lean_ctor_get(v___x_1917_, 1);
lean_inc(v_snd_1919_);
lean_dec_ref(v___x_1917_);
lean_inc(v___x_1902_);
v___x_1920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1902_, v___x_1903_, v_fst_1918_, v___y_1878_, v_snd_1919_);
v___y_1881_ = v___x_1920_;
goto v___jp_1880_;
}
}
}
else
{
lean_object* v_snd_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec(v___y_1909_);
v_snd_1921_ = lean_ctor_get(v___x_1912_, 1);
lean_inc(v_snd_1921_);
lean_dec_ref(v___x_1912_);
v___x_1922_ = lean_box(0);
lean_inc(v___x_1902_);
v___x_1923_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1902_, v___x_1903_, v___x_1922_, v___y_1878_, v_snd_1921_);
v___y_1881_ = v___x_1923_;
goto v___jp_1880_;
}
}
v___jp_1924_:
{
if (lean_obj_tag(v___x_1903_) == 0)
{
uint8_t v___x_1926_; 
v___x_1926_ = 0;
v___y_1909_ = v___y_1925_;
v___y_1910_ = v___x_1926_;
goto v___jp_1908_;
}
else
{
lean_object* v_val_1927_; uint8_t v_alternate_1928_; 
v_val_1927_ = lean_ctor_get(v___x_1903_, 0);
v_alternate_1928_ = lean_ctor_get_uint8(v_val_1927_, 1);
v___y_1909_ = v___y_1925_;
v___y_1910_ = v_alternate_1928_;
goto v___jp_1908_;
}
}
}
v___jp_1880_:
{
lean_object* v_fst_1882_; 
v_fst_1882_ = lean_ctor_get(v___y_1881_, 0);
lean_inc(v_fst_1882_);
if (lean_obj_tag(v_fst_1882_) == 0)
{
lean_object* v_snd_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_a_1876_);
v_snd_1883_ = lean_ctor_get(v___y_1881_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___y_1881_);
if (v_isSharedCheck_1891_ == 0)
{
lean_object* v_unused_1892_; 
v_unused_1892_ = lean_ctor_get(v___y_1881_, 0);
lean_dec(v_unused_1892_);
v___x_1885_ = v___y_1881_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snd_1883_);
lean_dec(v___y_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_a_1887_; lean_object* v___x_1889_; 
v_a_1887_ = lean_ctor_get(v_fst_1882_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v_fst_1882_, 1);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v_a_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1887_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_snd_1883_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
lean_object* v_snd_1893_; lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_snd_1893_ = lean_ctor_get(v___y_1881_, 1);
lean_inc(v_snd_1893_);
lean_dec_ref(v___y_1881_);
v_a_1894_ = lean_ctor_get(v_fst_1882_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v_fst_1882_, 1);
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = lean_nat_add(v_a_1876_, v___x_1895_);
lean_dec(v_a_1876_);
v_a_1876_ = v___x_1896_;
v_b_1877_ = v_a_1894_;
v___y_1879_ = v_snd_1893_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object* v_stxs_1938_, uint8_t v_lineStart_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___y_1944_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_array_get_size(v_stxs_1938_);
v___x_1961_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0));
v___x_1962_ = lean_nat_dec_lt(v___x_1942_, v___x_1960_);
if (v___x_1962_ == 0)
{
v___y_1944_ = v___x_1961_;
goto v___jp_1943_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_nat_dec_le(v___x_1960_, v___x_1960_);
if (v___x_1963_ == 0)
{
if (v___x_1962_ == 0)
{
v___y_1944_ = v___x_1961_;
goto v___jp_1943_;
}
else
{
size_t v___x_1964_; size_t v___x_1965_; lean_object* v___x_1966_; 
v___x_1964_ = ((size_t)0ULL);
v___x_1965_ = lean_usize_of_nat(v___x_1960_);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1938_, v___x_1964_, v___x_1965_, v___x_1961_);
v___y_1944_ = v___x_1966_;
goto v___jp_1943_;
}
}
else
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = ((size_t)0ULL);
v___x_1968_ = lean_usize_of_nat(v___x_1960_);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1938_, v___x_1967_, v___x_1968_, v___x_1961_);
v___y_1944_ = v___x_1969_;
goto v___jp_1943_;
}
}
v___jp_1943_:
{
lean_object* v___x_1945_; lean_object* v_prev_x3f_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v_snd_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v___x_1945_ = lean_array_get_size(v___y_1944_);
v_prev_x3f_1946_ = lean_box(0);
v___x_1947_ = lean_box(v_lineStart_1939_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v_prev_x3f_1946_);
v___x_1949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v___x_1945_, v___y_1944_, v___x_1942_, v___x_1948_, v_a_1940_, v_a_1941_);
lean_dec_ref(v___y_1944_);
v_snd_1950_ = lean_ctor_get(v___x_1949_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v___x_1949_, 0);
lean_dec(v_unused_1959_);
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_snd_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_box(0);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1954_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_snd_1950_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t v_char_1970_, lean_object* v_inls_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_delim_1976_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___x_1987_; lean_object* v_snd_1988_; lean_object* v___y_1990_; lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1974_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_1975_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_1970_, v_inls_1971_);
v_delim_1976_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_1970_, v___x_1975_, v___x_1974_);
v___x_1987_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1976_, v_a_1973_);
v_snd_1988_ = lean_ctor_get(v___x_1987_, 1);
lean_inc(v_snd_1988_);
lean_dec_ref(v___x_1987_);
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = lean_array_get_size(v_inls_1971_);
v___x_1999_ = lean_nat_dec_lt(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_box(0);
v___y_1990_ = v___x_2000_;
goto v___jp_1989_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_array_fget_borrowed(v_inls_1971_, v___x_1997_);
lean_inc(v___x_2001_);
v___x_2002_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v___x_2001_);
v___y_1990_ = v___x_2002_;
goto v___jp_1989_;
}
v___jp_1977_:
{
size_t v_sz_1980_; size_t v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v_snd_1985_; lean_object* v___x_1986_; 
v_sz_1980_ = lean_array_size(v_inls_1971_);
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_1980_, v___x_1981_, v_inls_1971_);
v___x_1983_ = 0;
v___x_1984_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_1982_, v___x_1983_, v___y_1978_, v___y_1979_);
lean_dec_ref(v___x_1982_);
v_snd_1985_ = lean_ctor_get(v___x_1984_, 1);
lean_inc(v_snd_1985_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1976_, v_snd_1985_);
lean_dec_ref(v_delim_1976_);
return v___x_1986_;
}
v___jp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1991_ = lean_box_uint32(v_char_1970_);
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
v___x_1993_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v___y_1990_, v___x_1992_);
lean_dec_ref_known(v___x_1992_, 1);
lean_dec(v___y_1990_);
if (v___x_1993_ == 0)
{
v___y_1978_ = v_a_1972_;
v___y_1979_ = v_snd_1988_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v_snd_1996_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1995_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1994_, v_snd_1988_);
v_snd_1996_ = lean_ctor_get(v___x_1995_, 1);
lean_inc(v_snd_1996_);
lean_dec_ref(v___x_1995_);
v___y_1978_ = v_a_1972_;
v___y_1979_ = v_snd_1996_;
goto v___jp_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v___y_2009_, uint8_t v___x_2010_, lean_object* v_as_2011_, size_t v_sz_2012_, size_t v_i_2013_, lean_object* v_b_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_lt(v_i_2013_, v_sz_2012_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec_ref(v___y_2009_);
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_b_2014_);
lean_ctor_set(v___x_2018_, 1, v___y_2016_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v_snd_2020_; lean_object* v_a_2021_; lean_object* v_contents_2022_; lean_object* v___x_2023_; lean_object* v_snd_2024_; size_t v_sz_2025_; size_t v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v_snd_2031_; lean_object* v___x_2032_; lean_object* v_snd_2033_; lean_object* v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; 
v___x_2019_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2015_, v___y_2016_);
v_snd_2020_ = lean_ctor_get(v___x_2019_, 1);
lean_inc(v_snd_2020_);
lean_dec_ref(v___x_2019_);
v_a_2021_ = lean_array_uget_borrowed(v_as_2011_, v_i_2013_);
v_contents_2022_ = lean_ctor_get(v_a_2021_, 2);
lean_inc_ref(v___y_2009_);
v___x_2023_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2009_, v_contents_2022_, v_snd_2020_);
v_snd_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_snd_2024_);
lean_dec_ref(v___x_2023_);
v_sz_2025_ = lean_array_size(v_contents_2022_);
v___x_2026_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2022_);
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2025_, v___x_2026_, v_contents_2022_);
v___x_2028_ = lean_string_length(v___y_2009_);
v___x_2029_ = lean_nat_add(v___y_2015_, v___x_2028_);
v___x_2030_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2027_, v___x_2010_, v___x_2029_, v_snd_2024_);
lean_dec(v___x_2029_);
lean_dec_ref(v___x_2027_);
v_snd_2031_ = lean_ctor_get(v___x_2030_, 1);
lean_inc(v_snd_2031_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2031_);
v_snd_2033_ = lean_ctor_get(v___x_2032_, 1);
lean_inc(v_snd_2033_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = lean_box(0);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2013_, v___x_2035_);
v_i_2013_ = v___x_2036_;
v_b_2014_ = v___x_2034_;
v___y_2016_ = v_snd_2033_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t v___x_2041_, uint8_t v_alternate_2042_, lean_object* v_as_2043_, size_t v_sz_2044_, size_t v_i_2045_, lean_object* v_b_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2045_, v_sz_2044_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_b_2046_);
lean_ctor_set(v___x_2050_, 1, v___y_2048_);
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; lean_object* v_snd_2052_; lean_object* v_a_2053_; lean_object* v___y_2055_; 
v___x_2051_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2047_, v___y_2048_);
v_snd_2052_ = lean_ctor_get(v___x_2051_, 1);
lean_inc(v_snd_2052_);
lean_dec_ref(v___x_2051_);
v_a_2053_ = lean_array_uget_borrowed(v_as_2043_, v_i_2045_);
if (v_alternate_2042_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_inc(v_b_2046_);
v___x_2073_ = l_Nat_reprFast(v_b_2046_);
v___x_2074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0));
v___x_2075_ = lean_string_append(v___x_2073_, v___x_2074_);
v___y_2055_ = v___x_2075_;
goto v___jp_2054_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_inc(v_b_2046_);
v___x_2076_ = l_Nat_reprFast(v_b_2046_);
v___x_2077_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1));
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
v___y_2055_ = v___x_2078_;
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v_contents_2056_; lean_object* v___x_2057_; lean_object* v_snd_2058_; size_t v_sz_2059_; size_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_snd_2065_; lean_object* v___x_2066_; lean_object* v_snd_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; 
v_contents_2056_ = lean_ctor_get(v_a_2053_, 2);
lean_inc_ref(v___y_2055_);
v___x_2057_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2055_, v_contents_2056_, v_snd_2052_);
v_snd_2058_ = lean_ctor_get(v___x_2057_, 1);
lean_inc(v_snd_2058_);
lean_dec_ref(v___x_2057_);
v_sz_2059_ = lean_array_size(v_contents_2056_);
v___x_2060_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2056_);
v___x_2061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2059_, v___x_2060_, v_contents_2056_);
v___x_2062_ = lean_string_length(v___y_2055_);
lean_dec_ref(v___y_2055_);
v___x_2063_ = lean_nat_add(v___y_2047_, v___x_2062_);
v___x_2064_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2061_, v___x_2041_, v___x_2063_, v_snd_2058_);
lean_dec(v___x_2063_);
lean_dec_ref(v___x_2061_);
v_snd_2065_ = lean_ctor_get(v___x_2064_, 1);
lean_inc(v_snd_2065_);
lean_dec_ref(v___x_2064_);
v___x_2066_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2065_);
v_snd_2067_ = lean_ctor_get(v___x_2066_, 1);
lean_inc(v_snd_2067_);
lean_dec_ref(v___x_2066_);
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_add(v_b_2046_, v___x_2068_);
lean_dec(v_b_2046_);
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_add(v_i_2045_, v___x_2070_);
v_i_2045_ = v___x_2071_;
v_b_2046_ = v___x_2069_;
v___y_2048_ = v_snd_2067_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t v___x_2079_, lean_object* v_as_2080_, size_t v_sz_2081_, size_t v_i_2082_, lean_object* v_b_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_lt(v_i_2082_, v_sz_2081_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v_b_2083_);
lean_ctor_set(v___x_2087_, 1, v___y_2085_);
return v___x_2087_;
}
else
{
lean_object* v___x_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_snd_2092_; lean_object* v_a_2093_; lean_object* v_term_2094_; lean_object* v___x_2095_; lean_object* v___y_2097_; lean_object* v___y_2098_; uint8_t v___x_2119_; 
v___x_2088_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2084_, v___y_2085_);
v_snd_2089_ = lean_ctor_get(v___x_2088_, 1);
lean_inc(v_snd_2089_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_2091_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2090_, v_snd_2089_);
v_snd_2092_ = lean_ctor_get(v___x_2091_, 1);
lean_inc(v_snd_2092_);
lean_dec_ref(v___x_2091_);
v_a_2093_ = lean_array_uget_borrowed(v_as_2080_, v_i_2082_);
v_term_2094_ = lean_ctor_get(v_a_2093_, 2);
v___x_2095_ = lean_box(0);
v___x_2119_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_term_2094_);
if (v___x_2119_ == 0)
{
v___y_2097_ = v___y_2084_;
v___y_2098_ = v_snd_2092_;
goto v___jp_2096_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v_snd_2122_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2121_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2120_, v_snd_2092_);
v_snd_2122_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_snd_2122_);
lean_dec_ref(v___x_2121_);
v___y_2097_ = v___y_2084_;
v___y_2098_ = v_snd_2122_;
goto v___jp_2096_;
}
v___jp_2096_:
{
lean_object* v_term_2099_; lean_object* v_desc_2100_; size_t v_sz_2101_; size_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v_snd_2105_; lean_object* v___x_2106_; lean_object* v_snd_2107_; size_t v_sz_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_snd_2113_; lean_object* v___x_2114_; lean_object* v_snd_2115_; size_t v___x_2116_; size_t v___x_2117_; 
v_term_2099_ = lean_ctor_get(v_a_2093_, 2);
v_desc_2100_ = lean_ctor_get(v_a_2093_, 3);
v_sz_2101_ = lean_array_size(v_term_2099_);
v___x_2102_ = ((size_t)0ULL);
lean_inc_ref(v_term_2099_);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2101_, v___x_2102_, v_term_2099_);
v___x_2104_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2103_, v___x_2079_, v___y_2097_, v___y_2098_);
lean_dec_ref(v___x_2103_);
v_snd_2105_ = lean_ctor_get(v___x_2104_, 1);
lean_inc(v_snd_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2105_);
v_snd_2107_ = lean_ctor_get(v___x_2106_, 1);
lean_inc(v_snd_2107_);
lean_dec_ref(v___x_2106_);
v_sz_2108_ = lean_array_size(v_desc_2100_);
lean_inc_ref(v_desc_2100_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2108_, v___x_2102_, v_desc_2100_);
v___x_2110_ = lean_unsigned_to_nat(2u);
v___x_2111_ = lean_nat_add(v___y_2097_, v___x_2110_);
v___x_2112_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2109_, v___x_2079_, v___x_2111_, v_snd_2107_);
lean_dec(v___x_2111_);
lean_dec_ref(v___x_2109_);
v_snd_2113_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_snd_2113_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2113_);
v_snd_2115_ = lean_ctor_get(v___x_2114_, 1);
lean_inc(v_snd_2115_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = ((size_t)1ULL);
v___x_2117_ = lean_usize_add(v_i_2082_, v___x_2116_);
v_i_2082_ = v___x_2117_;
v_b_2083_ = v___x_2095_;
v___y_2085_ = v_snd_2115_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_2126_, lean_object* v_next_x3f_2127_, uint8_t v_atLineStart_2128_, uint8_t v_alternate_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___y_2133_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
lean_inc(v_stx_2126_);
v___x_2163_ = l_Lean_Syntax_getKind(v_stx_2126_);
v___x_2164_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3));
v___x_2165_ = lean_name_eq(v___x_2163_, v___x_2164_);
lean_dec(v___x_2163_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_inc(v_stx_2126_);
v___x_2166_ = l_Lean_Doc_ArgValView_of(v_stx_2126_);
if (lean_obj_tag(v___x_2166_) == 1)
{
lean_object* v_val_2167_; 
lean_dec(v_next_x3f_2127_);
lean_dec(v_stx_2126_);
v_val_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_val_2167_);
lean_dec_ref_known(v___x_2166_, 1);
if (lean_obj_tag(v_val_2167_) == 1)
{
lean_object* v_x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_x_2168_ = lean_ctor_get(v_val_2167_, 0);
lean_inc(v_x_2168_);
lean_dec_ref_known(v_val_2167_, 1);
v___x_2169_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_x_2168_);
v___x_2170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2169_, v_a_2131_);
lean_dec_ref(v___x_2169_);
return v___x_2170_;
}
else
{
lean_object* v_lit_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_lit_2171_ = lean_ctor_get(v_val_2167_, 0);
lean_inc(v_lit_2171_);
lean_dec(v_val_2167_);
v___x_2172_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_lit_2171_);
v___x_2173_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2172_, v_a_2131_);
lean_dec_ref(v___x_2172_);
return v___x_2173_;
}
}
else
{
lean_object* v___x_2174_; 
lean_dec(v___x_2166_);
lean_inc(v_stx_2126_);
v___x_2174_ = l_Lean_Doc_ArgView_of(v_stx_2126_);
if (lean_obj_tag(v___x_2174_) == 1)
{
lean_object* v_val_2175_; 
lean_dec(v_next_x3f_2127_);
lean_dec(v_stx_2126_);
v_val_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v___x_2174_, 1);
switch(lean_obj_tag(v_val_2175_))
{
case 0:
{
lean_object* v_val_2176_; lean_object* v___x_2177_; 
v_val_2176_ = lean_ctor_get(v_val_2175_, 1);
lean_inc(v_val_2176_);
lean_dec_ref_known(v_val_2175_, 2);
v___x_2177_ = lean_box(0);
v_stx_2126_ = v_val_2176_;
v_next_x3f_2127_ = v___x_2177_;
v_atLineStart_2128_ = v___x_2165_;
v_alternate_2129_ = v___x_2165_;
goto _start;
}
case 1:
{
lean_object* v_name_2179_; lean_object* v_val_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_snd_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_snd_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v_snd_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v_snd_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v_name_2179_ = lean_ctor_get(v_val_2175_, 2);
lean_inc(v_name_2179_);
v_val_2180_ = lean_ctor_get(v_val_2175_, 4);
lean_inc(v_val_2180_);
lean_dec_ref_known(v_val_2175_, 5);
v___x_2181_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_2182_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2181_, v_a_2131_);
v_snd_2183_ = lean_ctor_get(v___x_2182_, 1);
lean_inc(v_snd_2183_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2179_);
v___x_2185_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2184_, v_snd_2183_);
lean_dec_ref(v___x_2184_);
v_snd_2186_ = lean_ctor_get(v___x_2185_, 1);
lean_inc(v_snd_2186_);
lean_dec_ref(v___x_2185_);
v___x_2187_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
v___x_2188_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2187_, v_snd_2186_);
v_snd_2189_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_snd_2189_);
lean_dec_ref(v___x_2188_);
v___x_2190_ = lean_box(0);
v___x_2191_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_val_2180_, v___x_2190_, v___x_2165_, v___x_2165_, v_a_2130_, v_snd_2189_);
v_snd_2192_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_snd_2192_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_2194_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2193_, v_snd_2192_);
return v___x_2194_;
}
default: 
{
lean_object* v_name_2195_; uint8_t v_isOn_2196_; lean_object* v___y_2198_; 
v_name_2195_ = lean_ctor_get(v_val_2175_, 2);
lean_inc(v_name_2195_);
v_isOn_2196_ = lean_ctor_get_uint8(v_val_2175_, sizeof(void*)*3);
lean_dec_ref_known(v_val_2175_, 3);
if (v_isOn_2196_ == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___y_2198_ = v___x_2203_;
goto v___jp_2197_;
}
else
{
lean_object* v___x_2204_; 
v___x_2204_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___y_2198_ = v___x_2204_;
goto v___jp_2197_;
}
v___jp_2197_:
{
lean_object* v___x_2199_; lean_object* v_snd_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2199_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2198_, v_a_2131_);
v_snd_2200_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_snd_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2195_);
v___x_2202_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2201_, v_snd_2200_);
lean_dec_ref(v___x_2201_);
return v___x_2202_;
}
}
}
}
else
{
lean_object* v___x_2205_; 
lean_dec(v___x_2174_);
lean_inc(v_stx_2126_);
v___x_2205_ = l_Lean_Doc_LinkTargetView_of(v_stx_2126_);
if (lean_obj_tag(v___x_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v___x_2207_; 
lean_dec(v_next_x3f_2127_);
lean_dec(v_stx_2126_);
v_val_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_val_2206_);
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_val_2206_, v_a_2131_);
lean_dec(v_val_2206_);
return v___x_2207_;
}
else
{
lean_object* v___x_2208_; 
lean_dec(v___x_2205_);
lean_inc(v_stx_2126_);
v___x_2208_ = l_Lean_Doc_InlineView_of(v_stx_2126_);
if (lean_obj_tag(v___x_2208_) == 1)
{
lean_object* v_val_2209_; 
lean_dec(v_stx_2126_);
v_val_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v___x_2208_, 1);
switch(lean_obj_tag(v_val_2209_))
{
case 0:
{
lean_object* v_view_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v_next_x3f_2127_);
v_view_2210_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2210_);
lean_dec_ref_known(v_val_2209_, 1);
v___x_2211_ = l_Lean_Doc_TextView_getVersoText(v_view_2210_);
lean_dec_ref(v_view_2210_);
v___x_2212_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_2128_, v___x_2211_);
v___x_2213_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2212_, v_a_2131_);
lean_dec_ref(v___x_2212_);
return v___x_2213_;
}
case 1:
{
lean_object* v_view_2214_; lean_object* v_content_2215_; uint32_t v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_next_x3f_2127_);
v_view_2214_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2214_);
lean_dec_ref_known(v_val_2209_, 1);
v_content_2215_ = lean_ctor_get(v_view_2214_, 2);
lean_inc_ref(v_content_2215_);
lean_dec_ref(v_view_2214_);
v___x_2216_ = 95;
v___x_2217_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2216_, v_content_2215_, v_a_2130_, v_a_2131_);
return v___x_2217_;
}
case 2:
{
lean_object* v_view_2218_; lean_object* v_content_2219_; uint32_t v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v_next_x3f_2127_);
v_view_2218_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2218_);
lean_dec_ref_known(v_val_2209_, 1);
v_content_2219_ = lean_ctor_get(v_view_2218_, 2);
lean_inc_ref(v_content_2219_);
lean_dec_ref(v_view_2218_);
v___x_2220_ = 42;
v___x_2221_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2220_, v_content_2219_, v_a_2130_, v_a_2131_);
return v___x_2221_;
}
case 3:
{
lean_object* v_view_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v_next_x3f_2127_);
v_view_2222_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2222_);
lean_dec_ref_known(v_val_2209_, 1);
v___x_2223_ = l_Lean_Doc_CodeView_getVersoCode(v_view_2222_);
lean_dec_ref(v_view_2222_);
v___x_2224_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2223_);
v___x_2225_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2224_, v_a_2131_);
lean_dec_ref(v___x_2224_);
return v___x_2225_;
}
case 4:
{
lean_object* v_view_2226_; lean_object* v___y_2228_; uint8_t v_mode_2234_; 
lean_dec(v_next_x3f_2127_);
v_view_2226_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2226_);
lean_dec_ref_known(v_val_2209_, 1);
v_mode_2234_ = lean_ctor_get_uint8(v_view_2226_, sizeof(void*)*3);
if (v_mode_2234_ == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5));
v___y_2228_ = v___x_2235_;
goto v___jp_2227_;
}
else
{
lean_object* v___x_2236_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
v___y_2228_ = v___x_2236_;
goto v___jp_2227_;
}
v___jp_2227_:
{
lean_object* v___x_2229_; lean_object* v_snd_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2229_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2228_, v_a_2131_);
v_snd_2230_ = lean_ctor_get(v___x_2229_, 1);
lean_inc(v_snd_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = l_Lean_Doc_MathView_getVersoCode(v_view_2226_);
lean_dec_ref(v_view_2226_);
v___x_2232_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2231_);
v___x_2233_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2232_, v_snd_2230_);
lean_dec_ref(v___x_2232_);
return v___x_2233_;
}
}
case 5:
{
lean_object* v_view_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v_snd_2240_; lean_object* v_content_2241_; lean_object* v_target_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v_snd_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_snd_2250_; lean_object* v___x_2251_; 
lean_dec(v_next_x3f_2127_);
v_view_2237_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2237_);
lean_dec_ref_known(v_val_2209_, 1);
v___x_2238_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2239_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2238_, v_a_2131_);
v_snd_2240_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_snd_2240_);
lean_dec_ref(v___x_2239_);
v_content_2241_ = lean_ctor_get(v_view_2237_, 2);
lean_inc_ref(v_content_2241_);
v_target_2242_ = lean_ctor_get(v_view_2237_, 4);
lean_inc_ref(v_target_2242_);
lean_dec_ref(v_view_2237_);
v_sz_2243_ = lean_array_size(v_content_2241_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2243_, v___x_2244_, v_content_2241_);
v___x_2246_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2245_, v___x_2165_, v_a_2130_, v_snd_2240_);
lean_dec_ref(v___x_2245_);
v_snd_2247_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_snd_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2249_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2248_, v_snd_2247_);
v_snd_2250_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_snd_2250_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2242_, v_snd_2250_);
lean_dec_ref(v_target_2242_);
return v___x_2251_;
}
case 6:
{
lean_object* v_view_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_snd_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v_snd_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_snd_2262_; lean_object* v_target_2263_; lean_object* v___x_2264_; 
lean_dec(v_next_x3f_2127_);
v_view_2252_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2252_);
lean_dec_ref_known(v_val_2209_, 1);
v___x_2253_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7));
v___x_2254_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2253_, v_a_2131_);
v_snd_2255_ = lean_ctor_get(v___x_2254_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = l_Lean_Doc_ImageView_getAlt(v_view_2252_);
v___x_2257_ = l_Lean_Doc_escapeVersoImageAlt(v___x_2256_);
lean_dec_ref(v___x_2256_);
v___x_2258_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2257_, v_snd_2255_);
lean_dec_ref(v___x_2257_);
v_snd_2259_ = lean_ctor_get(v___x_2258_, 1);
lean_inc(v_snd_2259_);
lean_dec_ref(v___x_2258_);
v___x_2260_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2261_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2260_, v_snd_2259_);
v_snd_2262_ = lean_ctor_get(v___x_2261_, 1);
lean_inc(v_snd_2262_);
lean_dec_ref(v___x_2261_);
v_target_2263_ = lean_ctor_get(v_view_2252_, 4);
lean_inc_ref(v_target_2263_);
lean_dec_ref(v_view_2252_);
v___x_2264_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2263_, v_snd_2262_);
lean_dec_ref(v_target_2263_);
return v___x_2264_;
}
case 7:
{
lean_object* v_view_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v_snd_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_snd_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v_next_x3f_2127_);
v_view_2265_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2265_);
lean_dec_ref_known(v_val_2209_, 1);
v___x_2266_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2267_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2266_, v_a_2131_);
v_snd_2268_ = lean_ctor_get(v___x_2267_, 1);
lean_inc(v_snd_2268_);
lean_dec_ref(v___x_2267_);
v___x_2269_ = l_Lean_Doc_FootnoteView_getName(v_view_2265_);
lean_dec_ref(v_view_2265_);
v___x_2270_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2269_, v_snd_2268_);
lean_dec_ref(v___x_2269_);
v_snd_2271_ = lean_ctor_get(v___x_2270_, 1);
lean_inc(v_snd_2271_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2273_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2272_, v_snd_2271_);
return v___x_2273_;
}
case 8:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec_ref_known(v_val_2209_, 1);
lean_dec(v_next_x3f_2127_);
v___x_2274_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2275_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2274_, v_a_2131_);
return v___x_2275_;
}
default: 
{
lean_object* v_view_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_snd_2279_; lean_object* v_name_2280_; lean_object* v_args_2281_; lean_object* v_content_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v_snd_2285_; lean_object* v___x_2286_; size_t v_sz_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v_snd_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_snd_2293_; lean_object* v___x_2304_; 
v_view_2276_ = lean_ctor_get(v_val_2209_, 0);
lean_inc_ref(v_view_2276_);
lean_dec_ref_known(v_val_2209_, 1);
v___x_2277_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2278_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2277_, v_a_2131_);
v_snd_2279_ = lean_ctor_get(v___x_2278_, 1);
lean_inc(v_snd_2279_);
lean_dec_ref(v___x_2278_);
v_name_2280_ = lean_ctor_get(v_view_2276_, 2);
lean_inc(v_name_2280_);
v_args_2281_ = lean_ctor_get(v_view_2276_, 3);
lean_inc_ref(v_args_2281_);
v_content_2282_ = lean_ctor_get(v_view_2276_, 6);
lean_inc_ref(v_content_2282_);
lean_dec_ref(v_view_2276_);
v___x_2283_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2280_);
v___x_2284_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2283_, v_snd_2279_);
lean_dec_ref(v___x_2283_);
v_snd_2285_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_snd_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = lean_box(0);
v_sz_2287_ = lean_array_size(v_args_2281_);
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2165_, v_args_2281_, v_sz_2287_, v___x_2288_, v___x_2286_, v_a_2130_, v_snd_2285_);
lean_dec_ref(v_args_2281_);
v_snd_2290_ = lean_ctor_get(v___x_2289_, 1);
lean_inc(v_snd_2290_);
lean_dec_ref(v___x_2289_);
v___x_2291_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2292_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2291_, v_snd_2290_);
v_snd_2293_ = lean_ctor_get(v___x_2292_, 1);
lean_inc(v_snd_2293_);
lean_dec_ref(v___x_2292_);
v___x_2304_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_2282_);
if (lean_obj_tag(v___x_2304_) == 1)
{
lean_object* v_val_2305_; uint8_t v___x_2306_; 
v_val_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_val_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_val_2305_, v_next_x3f_2127_);
if (v___x_2306_ == 0)
{
size_t v_sz_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_sz_2307_ = lean_array_size(v_content_2282_);
v___x_2308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2307_, v___x_2288_, v_content_2282_);
v___x_2309_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2308_, v___x_2306_, v_a_2130_, v_snd_2293_);
lean_dec_ref(v___x_2308_);
return v___x_2309_;
}
else
{
goto v___jp_2294_;
}
}
else
{
lean_dec(v___x_2304_);
lean_dec(v_next_x3f_2127_);
goto v___jp_2294_;
}
v___jp_2294_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v_snd_2297_; size_t v_sz_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v_snd_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2295_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2296_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2295_, v_snd_2293_);
v_snd_2297_ = lean_ctor_get(v___x_2296_, 1);
lean_inc(v_snd_2297_);
lean_dec_ref(v___x_2296_);
v_sz_2298_ = lean_array_size(v_content_2282_);
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2298_, v___x_2288_, v_content_2282_);
v___x_2300_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2299_, v___x_2165_, v_a_2130_, v_snd_2297_);
lean_dec_ref(v___x_2299_);
v_snd_2301_ = lean_ctor_get(v___x_2300_, 1);
lean_inc(v_snd_2301_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2303_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2302_, v_snd_2301_);
return v___x_2303_;
}
}
}
}
else
{
lean_object* v___x_2310_; 
lean_dec(v___x_2208_);
lean_dec(v_next_x3f_2127_);
lean_inc(v_stx_2126_);
v___x_2310_ = l_Lean_Doc_BlockView_of(v_stx_2126_);
if (lean_obj_tag(v___x_2310_) == 1)
{
lean_object* v_val_2311_; 
v_val_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_val_2311_);
lean_dec_ref_known(v___x_2310_, 1);
switch(lean_obj_tag(v_val_2311_))
{
case 0:
{
lean_object* v_view_2312_; lean_object* v_content_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; uint8_t v___x_2316_; 
lean_dec(v_stx_2126_);
v_view_2312_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2312_);
lean_dec_ref_known(v_val_2311_, 1);
v_content_2313_ = lean_ctor_get(v_view_2312_, 1);
lean_inc_ref(v_content_2313_);
lean_dec_ref(v_view_2312_);
v___x_2314_ = lean_unsigned_to_nat(0u);
v___x_2315_ = lean_array_get_size(v_content_2313_);
v___x_2316_ = lean_nat_dec_lt(v___x_2314_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_dec_ref(v_content_2313_);
goto v___jp_2160_;
}
else
{
if (v___x_2316_ == 0)
{
lean_dec_ref(v_content_2313_);
goto v___jp_2160_;
}
else
{
size_t v___x_2317_; size_t v___x_2318_; uint8_t v___x_2319_; lean_object* v___y_2321_; lean_object* v___y_2322_; 
v___x_2317_ = ((size_t)0ULL);
v___x_2318_ = lean_usize_of_nat(v___x_2315_);
v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_2165_, v_content_2313_, v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_dec_ref(v_content_2313_);
goto v___jp_2160_;
}
else
{
if (v___x_2165_ == 0)
{
lean_object* v___x_2328_; lean_object* v_snd_2329_; 
v___x_2328_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2329_ = lean_ctor_get(v___x_2328_, 1);
lean_inc(v_snd_2329_);
lean_dec_ref(v___x_2328_);
if (v___x_2316_ == 0)
{
goto v___jp_2330_;
}
else
{
if (v___x_2316_ == 0)
{
goto v___jp_2330_;
}
else
{
uint8_t v___x_2334_; 
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_2319_, v___x_2165_, v_content_2313_, v___x_2317_, v___x_2318_);
if (v___x_2334_ == 0)
{
goto v___jp_2330_;
}
else
{
v___y_2321_ = v_a_2130_;
v___y_2322_ = v_snd_2329_;
goto v___jp_2320_;
}
}
}
v___jp_2330_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_snd_2333_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2332_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2331_, v_snd_2329_);
v_snd_2333_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_snd_2333_);
lean_dec_ref(v___x_2332_);
v___y_2321_ = v_a_2130_;
v___y_2322_ = v_snd_2333_;
goto v___jp_2320_;
}
}
else
{
lean_dec_ref(v_content_2313_);
goto v___jp_2160_;
}
}
v___jp_2320_:
{
size_t v_sz_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v_snd_2326_; lean_object* v___x_2327_; 
v_sz_2323_ = lean_array_size(v_content_2313_);
v___x_2324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2323_, v___x_2317_, v_content_2313_);
v___x_2325_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2324_, v___x_2319_, v___y_2321_, v___y_2322_);
lean_dec_ref(v___x_2324_);
v_snd_2326_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_snd_2326_);
lean_dec_ref(v___x_2325_);
v___x_2327_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2326_);
return v___x_2327_;
}
}
}
}
case 1:
{
lean_object* v_view_2335_; lean_object* v___y_2337_; 
lean_dec(v_stx_2126_);
v_view_2335_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2335_);
lean_dec_ref_known(v_val_2311_, 1);
if (v_alternate_2129_ == 0)
{
lean_object* v___x_2345_; 
v___x_2345_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11));
v___y_2337_ = v___x_2345_;
goto v___jp_2336_;
}
else
{
lean_object* v___x_2346_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___y_2337_ = v___x_2346_;
goto v___jp_2336_;
}
v___jp_2336_:
{
lean_object* v_items_2338_; lean_object* v___x_2339_; size_t v_sz_2340_; size_t v___x_2341_; lean_object* v___x_2342_; lean_object* v_snd_2343_; lean_object* v___x_2344_; 
v_items_2338_ = lean_ctor_get(v_view_2335_, 1);
lean_inc_ref(v_items_2338_);
lean_dec_ref(v_view_2335_);
v___x_2339_ = lean_box(0);
v_sz_2340_ = lean_array_size(v_items_2338_);
v___x_2341_ = ((size_t)0ULL);
lean_inc_ref(v___y_2337_);
v___x_2342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2337_, v___x_2165_, v_items_2338_, v_sz_2340_, v___x_2341_, v___x_2339_, v_a_2130_, v_a_2131_);
lean_dec_ref(v_items_2338_);
v_snd_2343_ = lean_ctor_get(v___x_2342_, 1);
lean_inc(v_snd_2343_);
lean_dec_ref(v___x_2342_);
v___x_2344_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2343_);
return v___x_2344_;
}
}
case 2:
{
lean_object* v_view_2347_; lean_object* v_start_2348_; lean_object* v_items_2349_; size_t v_sz_2350_; size_t v___x_2351_; lean_object* v___x_2352_; lean_object* v_snd_2353_; lean_object* v___x_2354_; 
lean_dec(v_stx_2126_);
v_view_2347_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2347_);
lean_dec_ref_known(v_val_2311_, 1);
v_start_2348_ = lean_ctor_get(v_view_2347_, 1);
lean_inc(v_start_2348_);
v_items_2349_ = lean_ctor_get(v_view_2347_, 2);
lean_inc_ref(v_items_2349_);
lean_dec_ref(v_view_2347_);
v_sz_2350_ = lean_array_size(v_items_2349_);
v___x_2351_ = ((size_t)0ULL);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_2165_, v_alternate_2129_, v_items_2349_, v_sz_2350_, v___x_2351_, v_start_2348_, v_a_2130_, v_a_2131_);
lean_dec_ref(v_items_2349_);
v_snd_2353_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v___x_2354_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2353_);
return v___x_2354_;
}
case 3:
{
lean_object* v_view_2355_; lean_object* v_items_2356_; lean_object* v___x_2357_; size_t v_sz_2358_; size_t v___x_2359_; lean_object* v___x_2360_; lean_object* v_snd_2361_; lean_object* v___x_2362_; 
lean_dec(v_stx_2126_);
v_view_2355_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2355_);
lean_dec_ref_known(v_val_2311_, 1);
v_items_2356_ = lean_ctor_get(v_view_2355_, 1);
lean_inc_ref(v_items_2356_);
lean_dec_ref(v_view_2355_);
v___x_2357_ = lean_box(0);
v_sz_2358_ = lean_array_size(v_items_2356_);
v___x_2359_ = ((size_t)0ULL);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_2165_, v_items_2356_, v_sz_2358_, v___x_2359_, v___x_2357_, v_a_2130_, v_a_2131_);
lean_dec_ref(v_items_2356_);
v_snd_2361_ = lean_ctor_get(v___x_2360_, 1);
lean_inc(v_snd_2361_);
lean_dec_ref(v___x_2360_);
v___x_2362_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2361_);
return v___x_2362_;
}
case 4:
{
lean_object* v_view_2363_; lean_object* v___x_2364_; lean_object* v_snd_2365_; lean_object* v_content_2366_; lean_object* v___y_2368_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
lean_dec(v_stx_2126_);
v_view_2363_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2363_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2364_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2365_ = lean_ctor_get(v___x_2364_, 1);
lean_inc(v_snd_2365_);
lean_dec_ref(v___x_2364_);
v_content_2366_ = lean_ctor_get(v_view_2363_, 2);
lean_inc_ref(v_content_2366_);
lean_dec_ref(v_view_2363_);
v___x_2379_ = lean_array_get_size(v_content_2366_);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = lean_nat_dec_eq(v___x_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
v___y_2368_ = v___x_2382_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2383_; 
v___x_2383_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___y_2368_ = v___x_2383_;
goto v___jp_2367_;
}
v___jp_2367_:
{
lean_object* v___x_2369_; lean_object* v_snd_2370_; size_t v_sz_2371_; size_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_snd_2377_; lean_object* v___x_2378_; 
v___x_2369_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2368_, v_snd_2365_);
v_snd_2370_ = lean_ctor_get(v___x_2369_, 1);
lean_inc(v_snd_2370_);
lean_dec_ref(v___x_2369_);
v_sz_2371_ = lean_array_size(v_content_2366_);
v___x_2372_ = ((size_t)0ULL);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2371_, v___x_2372_, v_content_2366_);
v___x_2374_ = lean_unsigned_to_nat(2u);
v___x_2375_ = lean_nat_add(v_a_2130_, v___x_2374_);
v___x_2376_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2373_, v___x_2165_, v___x_2375_, v_snd_2370_);
lean_dec(v___x_2375_);
lean_dec_ref(v___x_2373_);
v_snd_2377_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_snd_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2377_);
return v___x_2378_;
}
}
case 5:
{
lean_object* v_view_2384_; lean_object* v___x_2385_; lean_object* v_snd_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2411_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; uint8_t v___x_2430_; 
lean_dec(v_stx_2126_);
v_view_2384_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2384_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2385_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2386_ = lean_ctor_get(v___x_2385_, 1);
lean_inc(v_snd_2386_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2388_ = lean_unsigned_to_nat(3u);
v___x_2389_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_view_2384_);
v___x_2427_ = l_Lean_Doc_longestBacktickRun(v___x_2389_);
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = lean_nat_add(v___x_2427_, v___x_2428_);
lean_dec(v___x_2427_);
v___x_2430_ = lean_nat_dec_le(v___x_2388_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_dec(v___x_2429_);
v___y_2411_ = v___x_2388_;
goto v___jp_2410_;
}
else
{
v___y_2411_ = v___x_2429_;
goto v___jp_2410_;
}
v___jp_2390_:
{
lean_object* v___x_2395_; 
v___x_2395_ = lean_string_append(v___x_2389_, v___y_2393_);
v___y_2142_ = v___y_2391_;
v___y_2143_ = v___y_2392_;
v___y_2144_ = v___y_2393_;
v___y_2145_ = v___y_2394_;
v___y_2146_ = v___x_2395_;
goto v___jp_2141_;
}
v___jp_2396_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v_snd_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2401_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2400_, v___y_2399_);
v_snd_2402_ = lean_ctor_get(v___x_2401_, 1);
lean_inc(v_snd_2402_);
lean_dec_ref(v___x_2401_);
v___x_2403_ = lean_string_utf8_byte_size(v___x_2389_);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_nat_dec_eq(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_nat_dec_le(v___x_2406_, v___x_2403_);
if (v___x_2407_ == 0)
{
v___y_2391_ = v___y_2397_;
v___y_2392_ = v_snd_2402_;
v___y_2393_ = v___x_2400_;
v___y_2394_ = v___y_2398_;
goto v___jp_2390_;
}
else
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = lean_nat_sub(v___x_2403_, v___x_2406_);
v___x_2409_ = lean_string_memcmp(v___x_2389_, v___x_2400_, v___x_2408_, v___x_2404_, v___x_2406_);
lean_dec(v___x_2408_);
if (v___x_2409_ == 0)
{
v___y_2391_ = v___y_2397_;
v___y_2392_ = v_snd_2402_;
v___y_2393_ = v___x_2400_;
v___y_2394_ = v___y_2398_;
goto v___jp_2390_;
}
else
{
v___y_2142_ = v___y_2397_;
v___y_2143_ = v_snd_2402_;
v___y_2144_ = v___x_2400_;
v___y_2145_ = v___y_2398_;
v___y_2146_ = v___x_2389_;
goto v___jp_2141_;
}
}
}
else
{
v___y_2142_ = v___y_2397_;
v___y_2143_ = v_snd_2402_;
v___y_2144_ = v___x_2400_;
v___y_2145_ = v___y_2398_;
v___y_2146_ = v___x_2389_;
goto v___jp_2141_;
}
}
v___jp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v_name_x3f_2414_; 
v___x_2412_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___y_2411_, v___x_2387_);
v___x_2413_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2412_, v_snd_2386_);
v_name_x3f_2414_ = lean_ctor_get(v_view_2384_, 2);
lean_inc(v_name_x3f_2414_);
if (lean_obj_tag(v_name_x3f_2414_) == 1)
{
lean_object* v_snd_2415_; lean_object* v_args_2416_; lean_object* v_val_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_snd_2420_; lean_object* v___x_2421_; size_t v_sz_2422_; size_t v___x_2423_; lean_object* v___x_2424_; lean_object* v_snd_2425_; 
v_snd_2415_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_snd_2415_);
lean_dec_ref(v___x_2413_);
v_args_2416_ = lean_ctor_get(v_view_2384_, 3);
lean_inc_ref(v_args_2416_);
lean_dec_ref(v_view_2384_);
v_val_2417_ = lean_ctor_get(v_name_x3f_2414_, 0);
lean_inc(v_val_2417_);
lean_dec_ref_known(v_name_x3f_2414_, 1);
v___x_2418_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_val_2417_);
v___x_2419_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2418_, v_snd_2415_);
lean_dec_ref(v___x_2418_);
v_snd_2420_ = lean_ctor_get(v___x_2419_, 1);
lean_inc(v_snd_2420_);
lean_dec_ref(v___x_2419_);
v___x_2421_ = lean_box(0);
v_sz_2422_ = lean_array_size(v_args_2416_);
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2165_, v_args_2416_, v_sz_2422_, v___x_2423_, v___x_2421_, v_a_2130_, v_snd_2420_);
lean_dec_ref(v_args_2416_);
v_snd_2425_ = lean_ctor_get(v___x_2424_, 1);
lean_inc(v_snd_2425_);
lean_dec_ref(v___x_2424_);
v___y_2397_ = v___x_2412_;
v___y_2398_ = v_a_2130_;
v___y_2399_ = v_snd_2425_;
goto v___jp_2396_;
}
else
{
lean_object* v_snd_2426_; 
lean_dec(v_name_x3f_2414_);
lean_dec_ref(v_view_2384_);
v_snd_2426_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_snd_2426_);
lean_dec_ref(v___x_2413_);
v___y_2397_ = v___x_2412_;
v___y_2398_ = v_a_2130_;
v___y_2399_ = v_snd_2426_;
goto v___jp_2396_;
}
}
}
case 6:
{
lean_object* v_view_2431_; lean_object* v___x_2432_; lean_object* v_snd_2433_; lean_object* v_name_2434_; lean_object* v_args_2435_; lean_object* v_content_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v_snd_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_snd_2444_; lean_object* v___x_2445_; size_t v_sz_2446_; size_t v___x_2447_; lean_object* v___x_2448_; lean_object* v_snd_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v_snd_2452_; size_t v_sz_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v_snd_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_snd_2459_; lean_object* v___x_2460_; lean_object* v_snd_2461_; lean_object* v___x_2462_; 
lean_dec(v_stx_2126_);
v_view_2431_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2431_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2432_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2433_ = lean_ctor_get(v___x_2432_, 1);
lean_inc(v_snd_2433_);
lean_dec_ref(v___x_2432_);
v_name_2434_ = lean_ctor_get(v_view_2431_, 2);
lean_inc(v_name_2434_);
v_args_2435_ = lean_ctor_get(v_view_2431_, 3);
lean_inc_ref(v_args_2435_);
v_content_2436_ = lean_ctor_get(v_view_2431_, 4);
lean_inc_ref(v_content_2436_);
lean_dec_ref(v_view_2431_);
v___x_2437_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2438_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_content_2436_);
v___x_2439_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(v___x_2438_, v___x_2437_);
v___x_2440_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2439_, v_snd_2433_);
v_snd_2441_ = lean_ctor_get(v___x_2440_, 1);
lean_inc(v_snd_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2434_);
v___x_2443_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2442_, v_snd_2441_);
lean_dec_ref(v___x_2442_);
v_snd_2444_ = lean_ctor_get(v___x_2443_, 1);
lean_inc(v_snd_2444_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = lean_box(0);
v_sz_2446_ = lean_array_size(v_args_2435_);
v___x_2447_ = ((size_t)0ULL);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2165_, v_args_2435_, v_sz_2446_, v___x_2447_, v___x_2445_, v_a_2130_, v_snd_2444_);
lean_dec_ref(v_args_2435_);
v_snd_2449_ = lean_ctor_get(v___x_2448_, 1);
lean_inc(v_snd_2449_);
lean_dec_ref(v___x_2448_);
v___x_2450_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2451_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2450_, v_snd_2449_);
v_snd_2452_ = lean_ctor_get(v___x_2451_, 1);
lean_inc(v_snd_2452_);
lean_dec_ref(v___x_2451_);
v_sz_2453_ = lean_array_size(v_content_2436_);
v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2453_, v___x_2447_, v_content_2436_);
v___x_2455_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2454_, v___x_2165_, v_a_2130_, v_snd_2452_);
lean_dec_ref(v___x_2454_);
v_snd_2456_ = lean_ctor_get(v___x_2455_, 1);
lean_inc(v_snd_2456_);
lean_dec_ref(v___x_2455_);
lean_inc(v_a_2130_);
v___x_2457_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2130_, v___x_2437_);
v___x_2458_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2457_, v_snd_2456_);
lean_dec_ref(v___x_2457_);
v_snd_2459_ = lean_ctor_get(v___x_2458_, 1);
lean_inc(v_snd_2459_);
lean_dec_ref(v___x_2458_);
v___x_2460_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2439_, v_snd_2459_);
lean_dec_ref(v___x_2439_);
v_snd_2461_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_snd_2461_);
lean_dec_ref(v___x_2460_);
v___x_2462_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2461_);
return v___x_2462_;
}
case 7:
{
lean_object* v_view_2463_; lean_object* v___x_2464_; lean_object* v_snd_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v_snd_2468_; lean_object* v_name_2469_; lean_object* v_args_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; size_t v_sz_2475_; size_t v___x_2476_; lean_object* v___x_2477_; lean_object* v_snd_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v_snd_2481_; lean_object* v___x_2482_; 
lean_dec(v_stx_2126_);
v_view_2463_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2463_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2464_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2465_ = lean_ctor_get(v___x_2464_, 1);
lean_inc(v_snd_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2467_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2466_, v_snd_2465_);
v_snd_2468_ = lean_ctor_get(v___x_2467_, 1);
lean_inc(v_snd_2468_);
lean_dec_ref(v___x_2467_);
v_name_2469_ = lean_ctor_get(v_view_2463_, 2);
lean_inc(v_name_2469_);
v_args_2470_ = lean_ctor_get(v_view_2463_, 3);
lean_inc_ref(v_args_2470_);
lean_dec_ref(v_view_2463_);
v___x_2471_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2469_);
v___x_2472_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2471_, v_snd_2468_);
lean_dec_ref(v___x_2471_);
v_snd_2473_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_snd_2473_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = lean_box(0);
v_sz_2475_ = lean_array_size(v_args_2470_);
v___x_2476_ = ((size_t)0ULL);
v___x_2477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2165_, v_args_2470_, v_sz_2475_, v___x_2476_, v___x_2474_, v_a_2130_, v_snd_2473_);
lean_dec_ref(v_args_2470_);
v_snd_2478_ = lean_ctor_get(v___x_2477_, 1);
lean_inc(v_snd_2478_);
lean_dec_ref(v___x_2477_);
v___x_2479_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2480_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2479_, v_snd_2478_);
v_snd_2481_ = lean_ctor_get(v___x_2480_, 1);
lean_inc(v_snd_2481_);
lean_dec_ref(v___x_2480_);
v___x_2482_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2481_);
return v___x_2482_;
}
case 8:
{
lean_object* v_view_2483_; lean_object* v___x_2484_; lean_object* v_snd_2485_; lean_object* v_level_2486_; lean_object* v_content_2487_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v_snd_2502_; uint8_t v___x_2503_; 
lean_dec(v_stx_2126_);
v_view_2483_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2483_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2484_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2485_ = lean_ctor_get(v___x_2484_, 1);
lean_inc(v_snd_2485_);
lean_dec_ref(v___x_2484_);
v_level_2486_ = lean_ctor_get(v_view_2483_, 2);
lean_inc(v_level_2486_);
v_content_2487_ = lean_ctor_get(v_view_2483_, 3);
lean_inc_ref(v_content_2487_);
lean_dec_ref(v_view_2483_);
v___x_2497_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_2498_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(v_level_2486_, v___x_2497_);
v___x_2499_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2500_ = lean_string_append(v___x_2498_, v___x_2499_);
v___x_2501_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2500_, v_snd_2485_);
lean_dec_ref(v___x_2500_);
v_snd_2502_ = lean_ctor_get(v___x_2501_, 1);
lean_inc(v_snd_2502_);
lean_dec_ref(v___x_2501_);
v___x_2503_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2487_);
if (v___x_2503_ == 0)
{
v___y_2489_ = v_a_2130_;
v___y_2490_ = v_snd_2502_;
goto v___jp_2488_;
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v_snd_2506_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2505_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2504_, v_snd_2502_);
v_snd_2506_ = lean_ctor_get(v___x_2505_, 1);
lean_inc(v_snd_2506_);
lean_dec_ref(v___x_2505_);
v___y_2489_ = v_a_2130_;
v___y_2490_ = v_snd_2506_;
goto v___jp_2488_;
}
v___jp_2488_:
{
size_t v_sz_2491_; size_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_snd_2495_; lean_object* v___x_2496_; 
v_sz_2491_ = lean_array_size(v_content_2487_);
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2491_, v___x_2492_, v_content_2487_);
v___x_2494_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2493_, v___x_2165_, v___y_2489_, v___y_2490_);
lean_dec_ref(v___x_2493_);
v_snd_2495_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_snd_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2495_);
return v___x_2496_;
}
}
case 9:
{
lean_object* v_view_2507_; lean_object* v___x_2508_; lean_object* v_snd_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v_snd_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v_snd_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_snd_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v_snd_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_snd_2524_; lean_object* v___x_2525_; 
lean_dec(v_stx_2126_);
v_view_2507_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2507_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2508_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2509_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_snd_2509_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2511_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2510_, v_snd_2509_);
v_snd_2512_ = lean_ctor_get(v___x_2511_, 1);
lean_inc(v_snd_2512_);
lean_dec_ref(v___x_2511_);
v___x_2513_ = l_Lean_Doc_LinkRefView_getName(v_view_2507_);
v___x_2514_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2513_, v_snd_2512_);
lean_dec_ref(v___x_2513_);
v_snd_2515_ = lean_ctor_get(v___x_2514_, 1);
lean_inc(v_snd_2515_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2517_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2516_, v_snd_2515_);
v_snd_2518_ = lean_ctor_get(v___x_2517_, 1);
lean_inc(v_snd_2518_);
lean_dec_ref(v___x_2517_);
v___x_2519_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2520_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2519_, v_snd_2518_);
v_snd_2521_ = lean_ctor_get(v___x_2520_, 1);
lean_inc(v_snd_2521_);
lean_dec_ref(v___x_2520_);
v___x_2522_ = l_Lean_Doc_LinkRefView_getUrl(v_view_2507_);
lean_dec_ref(v_view_2507_);
v___x_2523_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2522_, v_snd_2521_);
lean_dec_ref(v___x_2522_);
v_snd_2524_ = lean_ctor_get(v___x_2523_, 1);
lean_inc(v_snd_2524_);
lean_dec_ref(v___x_2523_);
v___x_2525_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2524_);
return v___x_2525_;
}
case 10:
{
lean_object* v_view_2526_; lean_object* v___x_2527_; lean_object* v_snd_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_snd_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_snd_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_snd_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v_snd_2540_; lean_object* v_content_2541_; lean_object* v___y_2543_; lean_object* v___y_2544_; uint8_t v___x_2551_; 
lean_dec(v_stx_2126_);
v_view_2526_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2526_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2527_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2528_ = lean_ctor_get(v___x_2527_, 1);
lean_inc(v_snd_2528_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2530_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2529_, v_snd_2528_);
v_snd_2531_ = lean_ctor_get(v___x_2530_, 1);
lean_inc(v_snd_2531_);
lean_dec_ref(v___x_2530_);
v___x_2532_ = l_Lean_Doc_FootnoteRefView_getName(v_view_2526_);
v___x_2533_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2532_, v_snd_2531_);
lean_dec_ref(v___x_2532_);
v_snd_2534_ = lean_ctor_get(v___x_2533_, 1);
lean_inc(v_snd_2534_);
lean_dec_ref(v___x_2533_);
v___x_2535_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2536_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2535_, v_snd_2534_);
v_snd_2537_ = lean_ctor_get(v___x_2536_, 1);
lean_inc(v_snd_2537_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2539_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2538_, v_snd_2537_);
v_snd_2540_ = lean_ctor_get(v___x_2539_, 1);
lean_inc(v_snd_2540_);
lean_dec_ref(v___x_2539_);
v_content_2541_ = lean_ctor_get(v_view_2526_, 4);
lean_inc_ref(v_content_2541_);
lean_dec_ref(v_view_2526_);
v___x_2551_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2541_);
if (v___x_2551_ == 0)
{
v___y_2543_ = v_a_2130_;
v___y_2544_ = v_snd_2540_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_snd_2554_; 
v___x_2552_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2553_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2552_, v_snd_2540_);
v_snd_2554_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_snd_2554_);
lean_dec_ref(v___x_2553_);
v___y_2543_ = v_a_2130_;
v___y_2544_ = v_snd_2554_;
goto v___jp_2542_;
}
v___jp_2542_:
{
size_t v_sz_2545_; size_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_snd_2549_; lean_object* v___x_2550_; 
v_sz_2545_ = lean_array_size(v_content_2541_);
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2545_, v___x_2546_, v_content_2541_);
v___x_2548_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2547_, v___x_2165_, v___y_2543_, v___y_2544_);
lean_dec_ref(v___x_2547_);
v_snd_2549_ = lean_ctor_get(v___x_2548_, 1);
lean_inc(v_snd_2549_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2549_);
return v___x_2550_;
}
}
default: 
{
lean_object* v_view_2555_; lean_object* v___x_2556_; lean_object* v_snd_2557_; lean_object* v___y_2559_; lean_object* v___x_2572_; 
v_view_2555_ = lean_ctor_get(v_val_2311_, 0);
lean_inc_ref(v_view_2555_);
lean_dec_ref_known(v_val_2311_, 1);
v___x_2556_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2130_, v_a_2131_);
v_snd_2557_ = lean_ctor_get(v___x_2556_, 1);
lean_inc(v_snd_2557_);
lean_dec_ref(v___x_2556_);
v___x_2572_ = l_Lean_Syntax_getSubstring_x3f(v_stx_2126_, v___x_2165_, v___x_2165_);
lean_dec(v_stx_2126_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_contents_2573_; lean_object* v___x_2574_; 
v_contents_2573_ = lean_ctor_get(v_view_2555_, 2);
lean_inc(v_contents_2573_);
lean_dec_ref(v_view_2555_);
v___x_2574_ = l_Lean_Syntax_reprint(v_contents_2573_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___y_2559_ = v___x_2575_;
goto v___jp_2558_;
}
else
{
lean_object* v_val_2576_; 
v_val_2576_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_val_2576_);
lean_dec_ref_known(v___x_2574_, 1);
v___y_2559_ = v_val_2576_;
goto v___jp_2558_;
}
}
else
{
lean_object* v_val_2577_; lean_object* v_str_2578_; lean_object* v_startPos_2579_; lean_object* v_stopPos_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_snd_2584_; lean_object* v___x_2585_; 
lean_dec_ref(v_view_2555_);
v_val_2577_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_val_2577_);
lean_dec_ref_known(v___x_2572_, 1);
v_str_2578_ = lean_ctor_get(v_val_2577_, 0);
lean_inc_ref(v_str_2578_);
v_startPos_2579_ = lean_ctor_get(v_val_2577_, 1);
lean_inc(v_startPos_2579_);
v_stopPos_2580_ = lean_ctor_get(v_val_2577_, 2);
lean_inc(v_stopPos_2580_);
lean_dec(v_val_2577_);
v___x_2581_ = lean_string_utf8_extract(v_str_2578_, v_startPos_2579_, v_stopPos_2580_);
lean_dec(v_stopPos_2580_);
lean_dec(v_startPos_2579_);
lean_dec_ref(v_str_2578_);
lean_inc(v_a_2130_);
v___x_2582_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2130_, v___x_2581_);
v___x_2583_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2582_, v_snd_2557_);
lean_dec_ref(v___x_2582_);
v_snd_2584_ = lean_ctor_get(v___x_2583_, 1);
lean_inc(v_snd_2584_);
lean_dec_ref(v___x_2583_);
v___x_2585_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2584_);
return v___x_2585_;
}
v___jp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v_snd_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
v___x_2561_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2560_, v_snd_2557_);
v_snd_2562_ = lean_ctor_get(v___x_2561_, 1);
lean_inc(v_snd_2562_);
lean_dec_ref(v___x_2561_);
lean_inc(v_a_2130_);
v___x_2563_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2130_, v___y_2559_);
v___x_2564_ = lean_string_utf8_byte_size(v___x_2563_);
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = lean_nat_dec_eq(v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v_snd_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_snd_2571_; 
v___x_2567_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2563_, v_snd_2562_);
lean_dec_ref(v___x_2563_);
v_snd_2568_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_snd_2568_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2569_, v_snd_2568_);
v_snd_2571_ = lean_ctor_get(v___x_2570_, 1);
lean_inc(v_snd_2571_);
lean_dec_ref(v___x_2570_);
v___y_2133_ = v_snd_2571_;
goto v___jp_2132_;
}
else
{
lean_dec_ref(v___x_2563_);
v___y_2133_ = v_snd_2562_;
goto v___jp_2132_;
}
}
}
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v___x_2310_);
v___x_2586_ = lean_box(0);
v___x_2587_ = l_Lean_Syntax_formatStx(v_stx_2126_, v___x_2586_, v___x_2165_);
v___x_2588_ = l_Std_Format_defWidth;
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = l_Std_Format_pretty(v___x_2587_, v___x_2588_, v___x_2589_, v___x_2589_);
v___x_2591_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2590_, v_a_2131_);
lean_dec_ref(v___x_2590_);
return v___x_2591_;
}
}
}
}
}
}
else
{
lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; 
lean_dec(v_next_x3f_2127_);
v___x_2592_ = l_Lean_Syntax_getArgs(v_stx_2126_);
lean_dec(v_stx_2126_);
v___x_2593_ = 0;
v___x_2594_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2592_, v___x_2593_, v_a_2130_, v_a_2131_);
lean_dec_ref(v___x_2592_);
return v___x_2594_;
}
v___jp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_snd_2139_; lean_object* v___x_2140_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
lean_inc(v_a_2130_);
v___x_2135_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2130_, v___x_2134_);
v___x_2136_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_2137_ = lean_string_append(v___x_2135_, v___x_2136_);
v___x_2138_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2137_, v___y_2133_);
lean_dec_ref(v___x_2137_);
v_snd_2139_ = lean_ctor_get(v___x_2138_, 1);
lean_inc(v_snd_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2139_);
return v___x_2140_;
}
v___jp_2141_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_snd_2156_; lean_object* v___x_2157_; lean_object* v_snd_2158_; lean_object* v___x_2159_; 
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_string_utf8_byte_size(v___y_2146_);
lean_inc_ref(v___y_2146_);
v___x_2149_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2149_, 0, v___y_2146_);
lean_ctor_set(v___x_2149_, 1, v___x_2147_);
lean_ctor_set(v___x_2149_, 2, v___x_2148_);
v___x_2150_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
v___x_2151_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2152_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2145_, v___y_2146_, v___x_2149_, v___x_2148_, v___x_2150_, v___x_2151_);
lean_dec_ref_known(v___x_2149_, 3);
lean_dec_ref(v___y_2146_);
v___x_2153_ = lean_array_to_list(v___x_2152_);
v___x_2154_ = l_String_intercalate(v___y_2144_, v___x_2153_);
v___x_2155_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2154_, v___y_2143_);
lean_dec_ref(v___x_2154_);
v_snd_2156_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2142_, v_snd_2156_);
lean_dec_ref(v___y_2142_);
v_snd_2158_ = lean_ctor_get(v___x_2157_, 1);
lean_inc(v_snd_2158_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2158_);
return v___x_2159_;
}
v___jp_2160_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v_a_2131_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t v___x_2595_, lean_object* v_as_2596_, size_t v_sz_2597_, size_t v_i_2598_, lean_object* v_b_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
uint8_t v___x_2602_; 
v___x_2602_ = lean_usize_dec_lt(v_i_2598_, v_sz_2597_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v_b_2599_);
lean_ctor_set(v___x_2603_, 1, v___y_2601_);
return v___x_2603_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v_snd_2606_; lean_object* v_a_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_snd_2610_; lean_object* v___x_2611_; size_t v___x_2612_; size_t v___x_2613_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2605_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2604_, v___y_2601_);
v_snd_2606_ = lean_ctor_get(v___x_2605_, 1);
lean_inc(v_snd_2606_);
lean_dec_ref(v___x_2605_);
v_a_2607_ = lean_array_uget_borrowed(v_as_2596_, v_i_2598_);
v___x_2608_ = lean_box(0);
lean_inc(v_a_2607_);
v___x_2609_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2607_, v___x_2608_, v___x_2595_, v___x_2595_, v___y_2600_, v_snd_2606_);
v_snd_2610_ = lean_ctor_get(v___x_2609_, 1);
lean_inc(v_snd_2610_);
lean_dec_ref(v___x_2609_);
v___x_2611_ = lean_box(0);
v___x_2612_ = ((size_t)1ULL);
v___x_2613_ = lean_usize_add(v_i_2598_, v___x_2612_);
v_i_2598_ = v___x_2613_;
v_b_2599_ = v___x_2611_;
v___y_2601_ = v_snd_2610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v___x_2615_, lean_object* v_as_2616_, lean_object* v_sz_2617_, lean_object* v_i_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v___x_62075__boxed_2622_; size_t v_sz_boxed_2623_; size_t v_i_boxed_2624_; lean_object* v_res_2625_; 
v___x_62075__boxed_2622_ = lean_unbox(v___x_2615_);
v_sz_boxed_2623_ = lean_unbox_usize(v_sz_2617_);
lean_dec(v_sz_2617_);
v_i_boxed_2624_ = lean_unbox_usize(v_i_2618_);
lean_dec(v_i_2618_);
v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_62075__boxed_2622_, v_as_2616_, v_sz_boxed_2623_, v_i_boxed_2624_, v_b_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v_as_2616_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object* v___y_2626_, lean_object* v___x_2627_, lean_object* v_as_2628_, lean_object* v_sz_2629_, lean_object* v_i_2630_, lean_object* v_b_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v___x_62093__boxed_2634_; size_t v_sz_boxed_2635_; size_t v_i_boxed_2636_; lean_object* v_res_2637_; 
v___x_62093__boxed_2634_ = lean_unbox(v___x_2627_);
v_sz_boxed_2635_ = lean_unbox_usize(v_sz_2629_);
lean_dec(v_sz_2629_);
v_i_boxed_2636_ = lean_unbox_usize(v_i_2630_);
lean_dec(v_i_2630_);
v_res_2637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2626_, v___x_62093__boxed_2634_, v_as_2628_, v_sz_boxed_2635_, v_i_boxed_2636_, v_b_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v_as_2628_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object* v_stxs_2638_, lean_object* v_lineStart_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
uint8_t v_lineStart_boxed_2642_; lean_object* v_res_2643_; 
v_lineStart_boxed_2642_ = lean_unbox(v_lineStart_2639_);
v_res_2643_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v_stxs_2638_, v_lineStart_boxed_2642_, v_a_2640_, v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_stxs_2638_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object* v_char_2644_, lean_object* v_inls_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
uint32_t v_char_boxed_2648_; lean_object* v_res_2649_; 
v_char_boxed_2648_ = lean_unbox_uint32(v_char_2644_);
lean_dec(v_char_2644_);
v_res_2649_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v_char_boxed_2648_, v_inls_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2646_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object* v___x_2650_, lean_object* v_alternate_2651_, lean_object* v_as_2652_, lean_object* v_sz_2653_, lean_object* v_i_2654_, lean_object* v_b_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v___x_62173__boxed_2658_; uint8_t v_alternate_boxed_2659_; size_t v_sz_boxed_2660_; size_t v_i_boxed_2661_; lean_object* v_res_2662_; 
v___x_62173__boxed_2658_ = lean_unbox(v___x_2650_);
v_alternate_boxed_2659_ = lean_unbox(v_alternate_2651_);
v_sz_boxed_2660_ = lean_unbox_usize(v_sz_2653_);
lean_dec(v_sz_2653_);
v_i_boxed_2661_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_62173__boxed_2658_, v_alternate_boxed_2659_, v_as_2652_, v_sz_boxed_2660_, v_i_boxed_2661_, v_b_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v_as_2652_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object* v___x_2663_, lean_object* v_as_2664_, lean_object* v_sz_2665_, lean_object* v_i_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v___x_62207__boxed_2670_; size_t v_sz_boxed_2671_; size_t v_i_boxed_2672_; lean_object* v_res_2673_; 
v___x_62207__boxed_2670_ = lean_unbox(v___x_2663_);
v_sz_boxed_2671_ = lean_unbox_usize(v_sz_2665_);
lean_dec(v_sz_2665_);
v_i_boxed_2672_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_res_2673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_62207__boxed_2670_, v_as_2664_, v_sz_boxed_2671_, v_i_boxed_2672_, v_b_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v_as_2664_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object* v_upperBound_2674_, lean_object* v___y_2675_, lean_object* v_a_2676_, lean_object* v_b_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2674_, v___y_2675_, v_a_2676_, v_b_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2675_);
lean_dec(v_upperBound_2674_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object* v_stx_2681_, lean_object* v_next_x3f_2682_, lean_object* v_atLineStart_2683_, lean_object* v_alternate_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
uint8_t v_atLineStart_boxed_2687_; uint8_t v_alternate_boxed_2688_; lean_object* v_res_2689_; 
v_atLineStart_boxed_2687_ = lean_unbox(v_atLineStart_2683_);
v_alternate_boxed_2688_ = lean_unbox(v_alternate_2684_);
v_res_2689_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2681_, v_next_x3f_2682_, v_atLineStart_boxed_2687_, v_alternate_boxed_2688_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2685_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object* v_s_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object* v_s_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(v_s_2692_);
lean_dec_ref(v_s_2692_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object* v_upperBound_2694_, lean_object* v___y_2695_, lean_object* v_inst_2696_, lean_object* v_R_2697_, lean_object* v_a_2698_, lean_object* v_b_2699_, lean_object* v_c_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2694_, v___y_2695_, v_a_2698_, v_b_2699_, v___y_2701_, v___y_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object* v_upperBound_2704_, lean_object* v___y_2705_, lean_object* v_inst_2706_, lean_object* v_R_2707_, lean_object* v_a_2708_, lean_object* v_b_2709_, lean_object* v_c_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(v_upperBound_2704_, v___y_2705_, v_inst_2706_, v_R_2707_, v_a_2708_, v_b_2709_, v_c_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2705_);
lean_dec(v_upperBound_2704_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___x_2716_, lean_object* v___x_2717_, lean_object* v_inst_2718_, lean_object* v_R_2719_, lean_object* v_a_2720_, lean_object* v_b_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2714_, v___y_2715_, v___x_2716_, v___x_2717_, v_a_2720_, v_b_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___x_2725_, lean_object* v___x_2726_, lean_object* v_inst_2727_, lean_object* v_R_2728_, lean_object* v_a_2729_, lean_object* v_b_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(v___y_2723_, v___y_2724_, v___x_2725_, v___x_2726_, v_inst_2727_, v_R_2728_, v_a_2729_, v_b_2730_);
lean_dec_ref(v___x_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object* v_s_2732_, lean_object* v_pos_2733_){
_start:
{
lean_object* v_str_2734_; lean_object* v_startInclusive_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v_decide_2739_; 
v_str_2734_ = lean_ctor_get(v_s_2732_, 0);
v_startInclusive_2735_ = lean_ctor_get(v_s_2732_, 1);
v___x_2736_ = lean_nat_add(v_startInclusive_2735_, v_pos_2733_);
v___x_2737_ = lean_nat_sub(v___x_2736_, v_startInclusive_2735_);
v___x_2738_ = lean_unsigned_to_nat(0u);
v_decide_2739_ = lean_nat_dec_eq(v___x_2737_, v___x_2738_);
if (v_decide_2739_ == 0)
{
uint32_t v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint32_t v___x_2746_; uint8_t v___x_2747_; 
v___x_2740_ = 10;
lean_inc(v_startInclusive_2735_);
lean_inc_ref(v_str_2734_);
v___x_2741_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2741_, 0, v_str_2734_);
lean_ctor_set(v___x_2741_, 1, v_startInclusive_2735_);
lean_ctor_set(v___x_2741_, 2, v___x_2736_);
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_nat_sub(v___x_2737_, v___x_2742_);
lean_dec(v___x_2737_);
v___x_2744_ = l_String_Slice_posLE(v___x_2741_, v___x_2743_);
lean_dec_ref_known(v___x_2741_, 3);
v___x_2745_ = lean_nat_add(v_startInclusive_2735_, v___x_2744_);
v___x_2746_ = lean_string_utf8_get_fast(v_str_2734_, v___x_2745_);
lean_dec(v___x_2745_);
v___x_2747_ = lean_uint32_dec_eq(v___x_2746_, v___x_2740_);
if (v___x_2747_ == 0)
{
lean_dec(v___x_2744_);
return v_pos_2733_;
}
else
{
lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2748_ = lean_nat_add(v___x_2744_, v___x_2742_);
v___x_2749_ = lean_nat_dec_le(v___x_2748_, v_pos_2733_);
lean_dec(v___x_2748_);
if (v___x_2749_ == 0)
{
lean_dec(v___x_2744_);
return v_pos_2733_;
}
else
{
lean_dec(v_pos_2733_);
v_pos_2733_ = v___x_2744_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2737_);
lean_dec(v___x_2736_);
return v_pos_2733_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object* v_s_2751_, lean_object* v_pos_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v_s_2751_, v_pos_2752_);
lean_dec_ref(v_s_2751_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object* v_s_2754_){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2755_ = lean_string_utf8_byte_size(v_s_2754_);
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = lean_nat_dec_le(v___x_2756_, v___x_2755_);
if (v___x_2757_ == 0)
{
return v_s_2754_;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2758_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2759_ = lean_unsigned_to_nat(0u);
v___x_2760_ = lean_nat_sub(v___x_2755_, v___x_2756_);
v___x_2761_ = lean_string_memcmp(v_s_2754_, v___x_2758_, v___x_2760_, v___x_2759_, v___x_2756_);
lean_dec(v___x_2760_);
if (v___x_2761_ == 0)
{
return v_s_2754_;
}
else
{
uint32_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2762_ = 10;
lean_inc_ref(v_s_2754_);
v___x_2763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2763_, 0, v_s_2754_);
lean_ctor_set(v___x_2763_, 1, v___x_2759_);
lean_ctor_set(v___x_2763_, 2, v___x_2755_);
v___x_2764_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v___x_2763_, v___x_2755_);
lean_dec_ref_known(v___x_2763_, 3);
v___x_2765_ = lean_string_utf8_extract_fast(v_s_2754_, v___x_2759_, v___x_2764_);
lean_dec(v___x_2764_);
lean_dec_ref(v_s_2754_);
v___x_2766_ = lean_string_push(v___x_2765_, v___x_2762_);
return v___x_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object* v_stx_2767_, uint8_t v_alternate_2768_){
_start:
{
lean_object* v___x_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v_snd_2774_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = 0;
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2773_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2767_, v___x_2769_, v___x_2770_, v_alternate_2768_, v___x_2771_, v___x_2772_);
v_snd_2774_ = lean_ctor_get(v___x_2773_, 1);
lean_inc(v_snd_2774_);
lean_dec_ref(v___x_2773_);
return v_snd_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object* v_stx_2775_, lean_object* v_alternate_2776_){
_start:
{
uint8_t v_alternate_boxed_2777_; lean_object* v_res_2778_; 
v_alternate_boxed_2777_ = lean_unbox(v_alternate_2776_);
v_res_2778_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2775_, v_alternate_boxed_2777_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_2779_, uint8_t v_alternate_2780_){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2779_, v_alternate_2780_);
v___x_2782_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object* v_stx_2783_, lean_object* v_alternate_2784_){
_start:
{
uint8_t v_alternate_boxed_2785_; lean_object* v_res_2786_; 
v_alternate_boxed_2785_ = lean_unbox(v_alternate_2784_);
v_res_2786_ = l_Lean_Doc_Parser_versoSyntaxToString(v_stx_2783_, v_alternate_boxed_2785_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object* v_b_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v___x_2789_; 
lean_inc(v_b_2787_);
v___x_2789_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_b_2787_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; uint8_t v___y_2792_; 
lean_inc(v_b_2787_);
v___x_2790_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v___y_2788_, v_b_2787_);
lean_dec(v___y_2788_);
if (lean_obj_tag(v___x_2790_) == 0)
{
v___y_2792_ = v___x_2789_;
goto v___jp_2791_;
}
else
{
lean_object* v_val_2795_; uint8_t v_alternate_2796_; 
v_val_2795_ = lean_ctor_get(v___x_2790_, 0);
v_alternate_2796_ = lean_ctor_get_uint8(v_val_2795_, 1);
v___y_2792_ = v_alternate_2796_;
goto v___jp_2791_;
}
v___jp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_b_2787_, v___y_2792_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v___x_2790_);
return v___x_2794_;
}
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec(v_b_2787_);
v___x_2797_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v___y_2788_);
return v___x_2798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object* v_n_2799_, lean_object* v_f_2800_, lean_object* v_xs_2801_, lean_object* v_k_2802_, lean_object* v_acc_2803_, lean_object* v___y_2804_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = lean_nat_dec_lt(v_k_2802_, v_n_2799_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_dec(v_k_2802_);
lean_dec_ref(v_f_2800_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_acc_2803_);
lean_ctor_set(v___x_2806_, 1, v___y_2804_);
return v___x_2806_;
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v_fst_2809_; lean_object* v_snd_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2807_ = lean_array_fget_borrowed(v_xs_2801_, v_k_2802_);
lean_inc_ref(v_f_2800_);
lean_inc(v___x_2807_);
v___x_2808_ = lean_apply_2(v_f_2800_, v___x_2807_, v___y_2804_);
v_fst_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_fst_2809_);
v_snd_2810_ = lean_ctor_get(v___x_2808_, 1);
lean_inc(v_snd_2810_);
lean_dec_ref(v___x_2808_);
v___x_2811_ = lean_unsigned_to_nat(1u);
v___x_2812_ = lean_nat_add(v_k_2802_, v___x_2811_);
lean_dec(v_k_2802_);
v___x_2813_ = lean_array_push(v_acc_2803_, v_fst_2809_);
v_k_2802_ = v___x_2812_;
v_acc_2803_ = v___x_2813_;
v___y_2804_ = v_snd_2810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object* v_n_2815_, lean_object* v_f_2816_, lean_object* v_xs_2817_, lean_object* v_k_2818_, lean_object* v_acc_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2815_, v_f_2816_, v_xs_2817_, v_k_2818_, v_acc_2819_, v___y_2820_);
lean_dec_ref(v_xs_2817_);
lean_dec(v_n_2815_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object* v_blocks_2823_){
_start:
{
lean_object* v___f_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_fst_2830_; 
v___f_2824_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0));
v___x_2825_ = lean_array_get_size(v_blocks_2823_);
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2828_ = lean_box(0);
v___x_2829_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v___x_2825_, v___f_2824_, v_blocks_2823_, v___x_2826_, v___x_2827_, v___x_2828_);
v_fst_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_fst_2830_);
lean_dec_ref(v___x_2829_);
return v_fst_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object* v_blocks_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2831_);
lean_dec_ref(v_blocks_2831_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object* v_00_u03b1_2833_, lean_object* v_00_u03b2_2834_, lean_object* v_n_2835_, lean_object* v_f_2836_, lean_object* v_xs_2837_, lean_object* v_k_2838_, lean_object* v_h_2839_, lean_object* v_acc_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2835_, v_f_2836_, v_xs_2837_, v_k_2838_, v_acc_2840_, v___y_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object* v_00_u03b1_2843_, lean_object* v_00_u03b2_2844_, lean_object* v_n_2845_, lean_object* v_f_2846_, lean_object* v_xs_2847_, lean_object* v_k_2848_, lean_object* v_h_2849_, lean_object* v_acc_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(v_00_u03b1_2843_, v_00_u03b2_2844_, v_n_2845_, v_f_2846_, v_xs_2847_, v_k_2848_, v_h_2849_, v_acc_2850_, v___y_2851_);
lean_dec_ref(v_xs_2847_);
lean_dec(v_n_2845_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object* v_as_2853_, size_t v_i_2854_, size_t v_stop_2855_, lean_object* v_b_2856_){
_start:
{
uint8_t v___x_2857_; 
v___x_2857_ = lean_usize_dec_eq(v_i_2854_, v_stop_2855_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; size_t v___x_2860_; size_t v___x_2861_; 
v___x_2858_ = lean_array_uget_borrowed(v_as_2853_, v_i_2854_);
v___x_2859_ = lean_string_append(v_b_2856_, v___x_2858_);
v___x_2860_ = ((size_t)1ULL);
v___x_2861_ = lean_usize_add(v_i_2854_, v___x_2860_);
v_i_2854_ = v___x_2861_;
v_b_2856_ = v___x_2859_;
goto _start;
}
else
{
return v_b_2856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object* v_as_2863_, lean_object* v_i_2864_, lean_object* v_stop_2865_, lean_object* v_b_2866_){
_start:
{
size_t v_i_boxed_2867_; size_t v_stop_boxed_2868_; lean_object* v_res_2869_; 
v_i_boxed_2867_ = lean_unbox_usize(v_i_2864_);
lean_dec(v_i_2864_);
v_stop_boxed_2868_ = lean_unbox_usize(v_stop_2865_);
lean_dec(v_stop_2865_);
v_res_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v_as_2863_, v_i_boxed_2867_, v_stop_boxed_2868_, v_b_2866_);
lean_dec_ref(v_as_2863_);
return v_res_2869_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2871_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object* v_blocks_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2874_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2872_);
v___x_2875_ = lean_unsigned_to_nat(0u);
v___x_2876_ = lean_array_get_size(v___x_2874_);
v___x_2877_ = lean_nat_dec_lt(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_dec_ref(v___x_2874_);
v___x_2878_ = lean_obj_once(&l_Lean_Doc_Parser_versoDocumentToString___closed__0, &l_Lean_Doc_Parser_versoDocumentToString___closed__0_once, _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0);
return v___x_2878_;
}
else
{
size_t v___x_2879_; size_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2879_ = ((size_t)0ULL);
v___x_2880_ = lean_usize_of_nat(v___x_2876_);
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v___x_2874_, v___x_2879_, v___x_2880_, v___x_2873_);
lean_dec_ref(v___x_2874_);
v___x_2882_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2881_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object* v_blocks_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Doc_Parser_versoDocumentToString(v_blocks_2883_);
lean_dec_ref(v_blocks_2883_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2887_; lean_object* v_stxTrav_2888_; lean_object* v_cur_2889_; lean_object* v___x_2890_; 
v___x_2887_ = lean_st_ref_get(v___y_2885_);
v_stxTrav_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc_ref(v_stxTrav_2888_);
lean_dec(v___x_2887_);
v_cur_2889_ = lean_ctor_get(v_stxTrav_2888_, 0);
lean_inc(v_cur_2889_);
lean_dec_ref(v_stxTrav_2888_);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v_cur_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2891_);
lean_dec(v___y_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2895_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object* v___y_2906_){
_start:
{
lean_object* v___x_2908_; lean_object* v_stxTrav_2909_; lean_object* v_leadWord_2910_; uint8_t v_leadWordIdent_2911_; uint8_t v_isUngrouped_2912_; uint8_t v_mustBeGrouped_2913_; lean_object* v_stack_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2925_; 
v___x_2908_ = lean_st_ref_take(v___y_2906_);
v_stxTrav_2909_ = lean_ctor_get(v___x_2908_, 0);
v_leadWord_2910_ = lean_ctor_get(v___x_2908_, 1);
v_leadWordIdent_2911_ = lean_ctor_get_uint8(v___x_2908_, sizeof(void*)*3);
v_isUngrouped_2912_ = lean_ctor_get_uint8(v___x_2908_, sizeof(void*)*3 + 1);
v_mustBeGrouped_2913_ = lean_ctor_get_uint8(v___x_2908_, sizeof(void*)*3 + 2);
v_stack_2914_ = lean_ctor_get(v___x_2908_, 2);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2916_ = v___x_2908_;
v_isShared_2917_ = v_isSharedCheck_2925_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_stack_2914_);
lean_inc(v_leadWord_2910_);
lean_inc(v_stxTrav_2909_);
lean_dec(v___x_2908_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2925_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2918_ = lean_box(0);
v___x_2919_ = l_Lean_Syntax_Traverser_left(v_stxTrav_2909_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2919_);
v___x_2921_ = v___x_2916_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_leadWord_2910_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_stack_2914_);
lean_ctor_set_uint8(v_reuseFailAlloc_2924_, sizeof(void*)*3, v_leadWordIdent_2911_);
lean_ctor_set_uint8(v_reuseFailAlloc_2924_, sizeof(void*)*3 + 1, v_isUngrouped_2912_);
lean_ctor_set_uint8(v_reuseFailAlloc_2924_, sizeof(void*)*3 + 2, v_mustBeGrouped_2913_);
v___x_2921_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_st_ref_put(v___y_2906_, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2918_);
return v___x_2923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2926_);
lean_dec(v___y_2926_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2930_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object* v_upperBound_2941_, lean_object* v___x_2942_, lean_object* v_rendered_2943_, lean_object* v_a_2944_, lean_object* v_b_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v___x_2951_; 
v___x_2951_ = lean_nat_dec_lt(v_a_2944_, v_upperBound_2941_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_dec(v_a_2944_);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_b_2945_);
return v___x_2952_;
}
else
{
lean_object* v___x_2953_; lean_object* v___y_2955_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2953_ = lean_box(0);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = lean_unsigned_to_nat(1u);
v___x_2963_ = lean_nat_sub(v___x_2942_, v___x_2962_);
v___x_2964_ = lean_nat_sub(v___x_2963_, v_a_2944_);
lean_dec(v___x_2963_);
v___x_2965_ = lean_array_fget_borrowed(v_rendered_2943_, v___x_2964_);
lean_dec(v___x_2964_);
v___x_2966_ = lean_nat_dec_eq(v_a_2944_, v___x_2961_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
lean_inc(v___x_2965_);
v___x_2967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
v___y_2955_ = v___x_2967_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_inc(v___x_2965_);
v___x_2968_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2965_);
v___x_2969_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
v___y_2955_ = v___x_2969_;
goto v___jp_2954_;
}
v___jp_2954_:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___y_2955_, v___y_2947_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v___x_2957_; 
lean_dec_ref_known(v___x_2956_, 1);
v___x_2957_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2947_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_dec_ref_known(v___x_2957_, 1);
v___x_2958_ = lean_unsigned_to_nat(1u);
v___x_2959_ = lean_nat_add(v_a_2944_, v___x_2958_);
lean_dec(v_a_2944_);
v_a_2944_ = v___x_2959_;
v_b_2945_ = v___x_2953_;
goto _start;
}
else
{
lean_dec(v_a_2944_);
return v___x_2957_;
}
}
else
{
lean_dec(v_a_2944_);
return v___x_2956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object* v_upperBound_2970_, lean_object* v___x_2971_, lean_object* v_rendered_2972_, lean_object* v_a_2973_, lean_object* v_b_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_2970_, v___x_2971_, v_rendered_2972_, v_a_2973_, v_b_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec_ref(v_rendered_2972_);
lean_dec(v___x_2971_);
lean_dec(v_upperBound_2970_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_2981_, lean_object* v_rendered_2982_, lean_object* v___x_2983_, lean_object* v___x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v___x_2981_, v___x_2981_, v_rendered_2982_, v___x_2983_, v___x_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v___x_2990_, 0);
lean_dec(v_unused_2998_);
v___x_2992_ = v___x_2990_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v___x_2990_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_2984_);
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2984_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
else
{
return v___x_2990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_2999_, lean_object* v_rendered_3000_, lean_object* v___x_3001_, lean_object* v___x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_2999_, v_rendered_3000_, v___x_3001_, v___x_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec_ref(v_rendered_3000_);
lean_dec(v___x_2999_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; lean_object* v_a_3015_; lean_object* v_blocks_3016_; lean_object* v_rendered_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___f_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3014_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_3010_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
v_blocks_3016_ = l_Lean_TSyntax_getVersoBlocks(v_a_3015_);
lean_dec(v_a_3015_);
v_rendered_3017_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_3016_);
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3019_ = lean_array_get_size(v_blocks_3016_);
lean_dec_ref(v_blocks_3016_);
v___x_3020_ = lean_box(0);
v___f_3021_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3021_, 0, v___x_3019_);
lean_closure_set(v___f_3021_, 1, v_rendered_3017_);
lean_closure_set(v___f_3021_, 2, v___x_3018_);
lean_closure_set(v___f_3021_, 3, v___x_3020_);
v___x_3022_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs___boxed), 6, 1);
lean_closure_set(v___x_3022_, 0, v___f_3021_);
v___x_3023_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3022_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___f_3036_; lean_object* v___x_3037_; 
v___f_3036_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_3037_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_3036_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_Doc_Parser_document_formatter(v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object* v_upperBound_3044_, lean_object* v___x_3045_, lean_object* v_rendered_3046_, lean_object* v_inst_3047_, lean_object* v_R_3048_, lean_object* v_a_3049_, lean_object* v_b_3050_, lean_object* v_c_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_){
_start:
{
lean_object* v___x_3057_; 
v___x_3057_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_3044_, v___x_3045_, v_rendered_3046_, v_a_3049_, v_b_3050_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object* v_upperBound_3058_, lean_object* v___x_3059_, lean_object* v_rendered_3060_, lean_object* v_inst_3061_, lean_object* v_R_3062_, lean_object* v_a_3063_, lean_object* v_b_3064_, lean_object* v_c_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(v_upperBound_3058_, v___x_3059_, v_rendered_3060_, v_inst_3061_, v_R_3062_, v_a_3063_, v_b_3064_, v_c_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec_ref(v_rendered_3060_);
lean_dec(v___x_3059_);
lean_dec(v_upperBound_3058_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1(){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3089_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3090_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4));
v___x_3091_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6));
v___x_3092_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___boxed), 5, 0);
v___x_3093_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
return v_res_3095_;
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
