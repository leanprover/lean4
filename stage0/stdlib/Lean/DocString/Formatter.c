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
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Doc_InlineView_of(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_afterDigits_465_; uint8_t v___y_467_; uint8_t v___y_478_; lean_object* v___x_543_; uint8_t v___x_544_; 
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
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_dec_le(v___x_543_, v___x_462_);
if (v___x_544_ == 0)
{
goto v___jp_538_;
}
else
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_546_ = lean_string_memcmp(v_text_460_, v___x_545_, v___x_461_, v___x_461_, v___x_543_);
if (v___x_546_ == 0)
{
goto v___jp_538_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_546_;
}
}
v___jp_466_:
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
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_sub(v___x_462_, v___x_464_);
v___x_481_ = lean_nat_dec_le(v___x_479_, v___x_480_);
lean_dec(v___x_480_);
if (v___x_481_ == 0)
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_483_ = lean_string_memcmp(v_text_460_, v___x_482_, v___x_464_, v___x_461_, v___x_479_);
if (v___x_483_ == 0)
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___x_483_;
}
else
{
v___y_467_ = v___y_478_;
goto v___jp_466_;
}
}
}
v___jp_484_:
{
lean_object* v___x_485_; 
v___x_485_ = l_String_Slice_Pos_get_x3f(v___x_463_, v___x_461_);
lean_dec_ref_known(v___x_463_, 3);
if (lean_obj_tag(v___x_485_) == 0)
{
uint8_t v___x_486_; 
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
v___x_486_ = 0;
return v___x_486_;
}
else
{
lean_object* v_val_487_; uint32_t v___x_488_; uint32_t v___x_489_; uint8_t v___x_490_; 
v_val_487_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_val_487_);
lean_dec_ref_known(v___x_485_, 1);
v___x_488_ = 48;
v___x_489_ = lean_unbox_uint32(v_val_487_);
v___x_490_ = lean_uint32_dec_le(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_dec(v_val_487_);
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___x_490_;
}
else
{
uint32_t v___x_491_; uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_491_ = 57;
v___x_492_ = lean_unbox_uint32(v_val_487_);
lean_dec(v_val_487_);
v___x_493_ = lean_uint32_dec_le(v___x_492_, v___x_491_);
if (v___x_493_ == 0)
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref(v_text_460_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_sub(v___x_462_, v___x_464_);
v___x_496_ = lean_nat_dec_le(v___x_494_, v___x_495_);
lean_dec(v___x_495_);
if (v___x_496_ == 0)
{
v___y_478_ = v___x_493_;
goto v___jp_477_;
}
else
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1));
v___x_498_ = lean_string_memcmp(v_text_460_, v___x_497_, v___x_464_, v___x_461_, v___x_494_);
if (v___x_498_ == 0)
{
v___y_478_ = v___x_493_;
goto v___jp_477_;
}
else
{
v___y_467_ = v___x_493_;
goto v___jp_466_;
}
}
}
}
}
}
v___jp_499_:
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(3u);
v___x_501_ = lean_nat_dec_le(v___x_500_, v___x_462_);
if (v___x_501_ == 0)
{
goto v___jp_484_;
}
else
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_503_ = lean_string_memcmp(v_text_460_, v___x_502_, v___x_461_, v___x_461_, v___x_500_);
if (v___x_503_ == 0)
{
goto v___jp_484_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_503_;
}
}
}
v___jp_504_:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(3u);
v___x_506_ = lean_nat_dec_le(v___x_505_, v___x_462_);
if (v___x_506_ == 0)
{
goto v___jp_499_;
}
else
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3));
v___x_508_ = lean_string_memcmp(v_text_460_, v___x_507_, v___x_461_, v___x_461_, v___x_505_);
if (v___x_508_ == 0)
{
goto v___jp_499_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_508_;
}
}
}
v___jp_509_:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(2u);
v___x_511_ = lean_nat_dec_le(v___x_510_, v___x_462_);
if (v___x_511_ == 0)
{
goto v___jp_504_;
}
else
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_513_ = lean_string_memcmp(v_text_460_, v___x_512_, v___x_461_, v___x_461_, v___x_510_);
if (v___x_513_ == 0)
{
goto v___jp_504_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_513_;
}
}
}
v___jp_514_:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___x_516_ = lean_string_dec_eq(v_text_460_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(2u);
v___x_518_ = lean_nat_dec_le(v___x_517_, v___x_462_);
if (v___x_518_ == 0)
{
goto v___jp_509_;
}
else
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_520_ = lean_string_memcmp(v_text_460_, v___x_519_, v___x_461_, v___x_461_, v___x_517_);
if (v___x_520_ == 0)
{
goto v___jp_509_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_520_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_516_;
}
}
v___jp_521_:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___x_523_ = lean_string_dec_eq(v_text_460_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(2u);
v___x_525_ = lean_nat_dec_le(v___x_524_, v___x_462_);
if (v___x_525_ == 0)
{
goto v___jp_514_;
}
else
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_527_ = lean_string_memcmp(v_text_460_, v___x_526_, v___x_461_, v___x_461_, v___x_524_);
if (v___x_527_ == 0)
{
goto v___jp_514_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_527_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_523_;
}
}
v___jp_528_:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_dec_le(v___x_529_, v___x_462_);
if (v___x_530_ == 0)
{
goto v___jp_521_;
}
else
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___x_532_ = lean_string_memcmp(v_text_460_, v___x_531_, v___x_461_, v___x_461_, v___x_529_);
if (v___x_532_ == 0)
{
goto v___jp_521_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_532_;
}
}
}
v___jp_533_:
{
lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_dec_le(v___x_534_, v___x_462_);
if (v___x_535_ == 0)
{
goto v___jp_528_;
}
else
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_537_ = lean_string_memcmp(v_text_460_, v___x_536_, v___x_461_, v___x_461_, v___x_534_);
if (v___x_537_ == 0)
{
goto v___jp_528_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_537_;
}
}
}
v___jp_538_:
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_nat_dec_le(v___x_539_, v___x_462_);
if (v___x_540_ == 0)
{
goto v___jp_533_;
}
else
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_542_ = lean_string_memcmp(v_text_460_, v___x_541_, v___x_461_, v___x_461_, v___x_539_);
if (v___x_542_ == 0)
{
goto v___jp_533_;
}
else
{
lean_dec_ref_known(v_afterDigits_465_, 3);
lean_dec(v___x_464_);
lean_dec_ref_known(v___x_463_, 3);
lean_dec_ref(v_text_460_);
return v___x_542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object* v_text_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_text_547_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t v_atLineStart_551_, lean_object* v_value_552_){
_start:
{
lean_object* v_text_553_; 
v_text_553_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_552_);
if (v_atLineStart_551_ == 0)
{
lean_dec_ref(v_value_552_);
return v_text_553_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_value_552_);
if (v___x_554_ == 0)
{
return v_text_553_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_556_ = lean_string_append(v___x_555_, v_text_553_);
lean_dec_ref(v_text_553_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object* v_atLineStart_557_, lean_object* v_value_558_){
_start:
{
uint8_t v_atLineStart_boxed_559_; lean_object* v_res_560_; 
v_atLineStart_boxed_559_ = lean_unbox(v_atLineStart_557_);
v_res_560_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_boxed_559_, v_value_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object* v_s_561_, lean_object* v_pos_562_){
_start:
{
lean_object* v_str_563_; lean_object* v_startInclusive_564_; lean_object* v_endExclusive_565_; lean_object* v___x_566_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v_decide_577_; 
v_str_563_ = lean_ctor_get(v_s_561_, 0);
v_startInclusive_564_ = lean_ctor_get(v_s_561_, 1);
v_endExclusive_565_ = lean_ctor_get(v_s_561_, 2);
v___x_566_ = lean_nat_add(v_startInclusive_564_, v_pos_562_);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_nat_sub(v_endExclusive_565_, v___x_566_);
v_decide_577_ = lean_nat_dec_eq(v___x_575_, v___x_576_);
lean_dec(v___x_576_);
if (v_decide_577_ == 0)
{
uint32_t v___x_578_; uint32_t v___x_579_; uint8_t v___x_580_; 
v___x_578_ = lean_string_utf8_get_fast(v_str_563_, v___x_566_);
v___x_579_ = 32;
v___x_580_ = lean_uint32_dec_eq(v___x_578_, v___x_579_);
if (v___x_580_ == 0)
{
uint32_t v___x_581_; uint8_t v___x_582_; 
v___x_581_ = 9;
v___x_582_ = lean_uint32_dec_eq(v___x_578_, v___x_581_);
if (v___x_582_ == 0)
{
uint32_t v___x_583_; uint8_t v___x_584_; 
v___x_583_ = 13;
v___x_584_ = lean_uint32_dec_eq(v___x_578_, v___x_583_);
if (v___x_584_ == 0)
{
uint32_t v___x_585_; uint8_t v___x_586_; 
v___x_585_ = 10;
v___x_586_ = lean_uint32_dec_eq(v___x_578_, v___x_585_);
if (v___x_586_ == 0)
{
lean_dec(v___x_566_);
return v_pos_562_;
}
else
{
goto v___jp_567_;
}
}
else
{
goto v___jp_567_;
}
}
else
{
goto v___jp_567_;
}
}
else
{
goto v___jp_567_;
}
}
else
{
lean_dec(v___x_566_);
return v_pos_562_;
}
v___jp_567_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_568_ = lean_string_utf8_next_fast(v_str_563_, v___x_566_);
v___x_569_ = lean_nat_sub(v___x_568_, v___x_566_);
lean_dec(v___x_566_);
v___x_570_ = lean_nat_add(v_pos_562_, v___x_569_);
lean_dec(v___x_569_);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v_pos_562_, v___x_571_);
v___x_573_ = lean_nat_dec_le(v___x_572_, v___x_570_);
lean_dec(v___x_572_);
if (v___x_573_ == 0)
{
lean_dec(v___x_570_);
return v_pos_562_;
}
else
{
lean_dec(v_pos_562_);
v_pos_562_ = v___x_570_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object* v_s_587_, lean_object* v_pos_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_587_, v_pos_588_);
lean_dec_ref(v_s_587_);
return v_res_589_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object* v_s_590_){
_start:
{
lean_object* v_startInclusive_591_; lean_object* v_endExclusive_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v_decide_596_; 
v_startInclusive_591_ = lean_ctor_get(v_s_590_, 1);
v_endExclusive_592_ = lean_ctor_get(v_s_590_, 2);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_590_, v___x_593_);
v___x_595_ = lean_nat_sub(v_endExclusive_592_, v_startInclusive_591_);
v_decide_596_ = lean_nat_dec_eq(v___x_594_, v___x_595_);
lean_dec(v___x_595_);
lean_dec(v___x_594_);
return v_decide_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object* v_s_597_){
_start:
{
uint8_t v_res_598_; lean_object* v_r_599_; 
v_res_598_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v_s_597_);
lean_dec_ref(v_s_597_);
v_r_599_ = lean_box(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object* v_s_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_str_603_; lean_object* v_startInclusive_604_; lean_object* v_endExclusive_605_; lean_object* v___x_606_; uint8_t v_decide_607_; 
v_str_603_ = lean_ctor_get(v_s_600_, 0);
v_startInclusive_604_ = lean_ctor_get(v_s_600_, 1);
v_endExclusive_605_ = lean_ctor_get(v_s_600_, 2);
v___x_606_ = lean_nat_sub(v_endExclusive_605_, v_startInclusive_604_);
v_decide_607_ = lean_nat_dec_eq(v_a_601_, v___x_606_);
lean_dec(v___x_606_);
if (v_decide_607_ == 0)
{
lean_object* v___x_608_; uint32_t v___x_609_; uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_608_ = lean_nat_add(v_startInclusive_604_, v_a_601_);
lean_dec(v_a_601_);
v___x_609_ = lean_string_utf8_get_fast(v_str_603_, v___x_608_);
v___x_610_ = 32;
v___x_611_ = lean_uint32_dec_eq(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v___x_608_);
return v_b_602_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = lean_string_utf8_next_fast(v_str_603_, v___x_608_);
lean_dec(v___x_608_);
v___x_613_ = lean_nat_sub(v___x_612_, v_startInclusive_604_);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_add(v_b_602_, v___x_614_);
lean_dec(v_b_602_);
v_a_601_ = v___x_613_;
v_b_602_ = v___x_615_;
goto _start;
}
}
else
{
lean_dec(v_a_601_);
return v_b_602_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object* v_s_617_, lean_object* v_a_618_, lean_object* v_b_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_617_, v_a_618_, v_b_619_);
lean_dec_ref(v_s_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object* v_s_621_){
_start:
{
lean_object* v_n_622_; lean_object* v___x_623_; 
v_n_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_621_, v_n_622_, v_n_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object* v_s_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v_s_624_);
lean_dec_ref(v_s_624_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object* v_s_626_, lean_object* v_inst_627_, lean_object* v_R_628_, lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v_c_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_626_, v_a_629_, v_b_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object* v_s_633_, lean_object* v_inst_634_, lean_object* v_R_635_, lean_object* v_a_636_, lean_object* v_b_637_, lean_object* v_c_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(v_s_633_, v_inst_634_, v_R_635_, v_a_636_, v_b_637_, v_c_638_);
lean_dec_ref(v_s_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v_src_642_, lean_object* v___x_643_, lean_object* v_a_644_, lean_object* v_b_645_){
_start:
{
lean_object* v_it_647_; lean_object* v_out_648_; 
if (lean_obj_tag(v_a_644_) == 0)
{
lean_object* v_currPos_667_; lean_object* v_searcher_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_697_; 
v_currPos_667_ = lean_ctor_get(v_a_644_, 0);
v_searcher_668_ = lean_ctor_get(v_a_644_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_697_ == 0)
{
v___x_670_ = v_a_644_;
v_isShared_671_ = v_isSharedCheck_697_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_searcher_668_);
lean_inc(v_currPos_667_);
lean_dec(v_a_644_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_697_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v_str_672_; lean_object* v_startInclusive_673_; lean_object* v_endExclusive_674_; lean_object* v___x_675_; uint8_t v_decide_676_; 
v_str_672_ = lean_ctor_get(v___x_640_, 0);
v_startInclusive_673_ = lean_ctor_get(v___x_640_, 1);
v_endExclusive_674_ = lean_ctor_get(v___x_640_, 2);
v___x_675_ = lean_nat_sub(v_endExclusive_674_, v_startInclusive_673_);
v_decide_676_ = lean_nat_dec_eq(v_searcher_668_, v___x_675_);
lean_dec(v___x_675_);
if (v_decide_676_ == 0)
{
uint32_t v___x_677_; lean_object* v___x_678_; uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_677_ = 10;
v___x_678_ = lean_nat_add(v_startInclusive_673_, v_searcher_668_);
v___x_679_ = lean_string_utf8_get_fast(v_str_672_, v___x_678_);
v___x_680_ = lean_uint32_dec_eq(v___x_679_, v___x_677_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
lean_dec(v_searcher_668_);
v___x_681_ = lean_string_utf8_next_fast(v_str_672_, v___x_678_);
lean_dec(v___x_678_);
v___x_682_ = lean_nat_sub(v___x_681_, v_startInclusive_673_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_682_);
v___x_684_ = v___x_670_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_currPos_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_682_);
v___x_684_ = v_reuseFailAlloc_686_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v_a_644_ = v___x_684_;
goto _start;
}
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_slice_690_; lean_object* v_nextIt_692_; 
v___x_687_ = lean_string_utf8_next_fast(v_str_672_, v___x_678_);
v___x_688_ = lean_nat_sub(v___x_687_, v___x_678_);
lean_dec(v___x_678_);
v___x_689_ = lean_nat_add(v_searcher_668_, v___x_688_);
lean_dec(v___x_688_);
lean_dec(v_searcher_668_);
lean_inc_ref(v___x_640_);
v_slice_690_ = l_String_Slice_slice_x21(v___x_640_, v_currPos_667_, v___x_689_);
lean_dec(v_currPos_667_);
lean_inc(v___x_689_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_689_);
lean_ctor_set(v___x_670_, 0, v___x_689_);
v_nextIt_692_ = v___x_670_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_689_);
v_nextIt_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v_it_647_ = v_nextIt_692_;
v_out_648_ = v_slice_690_;
goto v___jp_646_;
}
}
}
else
{
uint8_t v_decide_694_; 
lean_del_object(v___x_670_);
lean_dec(v_searcher_668_);
v_decide_694_ = lean_nat_dec_eq(v_currPos_667_, v___x_641_);
if (v_decide_694_ == 0)
{
lean_object* v_slice_695_; lean_object* v___x_696_; 
lean_inc(v___x_643_);
lean_inc_ref(v_src_642_);
v_slice_695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_695_, 0, v_src_642_);
lean_ctor_set(v_slice_695_, 1, v_currPos_667_);
lean_ctor_set(v_slice_695_, 2, v___x_643_);
v___x_696_ = lean_box(1);
v_it_647_ = v___x_696_;
v_out_648_ = v_slice_695_;
goto v___jp_646_;
}
else
{
lean_dec(v_currPos_667_);
lean_dec(v___x_643_);
lean_dec_ref(v_src_642_);
lean_dec_ref(v___x_640_);
return v_b_645_;
}
}
}
}
else
{
lean_dec(v___x_643_);
lean_dec_ref(v_src_642_);
lean_dec_ref(v___x_640_);
return v_b_645_;
}
v___jp_646_:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = l_String_Slice_lines_lineMap(v_out_648_);
v___x_650_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_649_);
lean_dec_ref(v___x_649_);
if (lean_obj_tag(v_b_645_) == 0)
{
lean_object* v___x_652_; 
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
v_a_644_ = v_it_647_;
v_b_645_ = v___x_652_;
goto _start;
}
else
{
lean_object* v_val_654_; uint8_t v___x_655_; 
v_val_654_ = lean_ctor_get(v_b_645_, 0);
v___x_655_ = lean_nat_dec_le(v___x_651_, v_val_654_);
if (v___x_655_ == 0)
{
lean_dec(v___x_651_);
v_a_644_ = v_it_647_;
goto _start;
}
else
{
lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_isSharedCheck_664_ = !lean_is_exclusive(v_b_645_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_b_645_, 0);
lean_dec(v_unused_665_);
v___x_658_ = v_b_645_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_dec(v_b_645_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_651_);
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_651_);
v___x_661_ = v_reuseFailAlloc_663_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
v_a_644_ = v_it_647_;
v_b_645_ = v___x_661_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_649_);
v_a_644_ = v_it_647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object* v___x_698_, lean_object* v___x_699_, lean_object* v_src_700_, lean_object* v___x_701_, lean_object* v_a_702_, lean_object* v_b_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_698_, v___x_699_, v_src_700_, v___x_701_, v_a_702_, v_b_703_);
lean_dec(v___x_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object* v___x_705_, lean_object* v___x_706_, lean_object* v_src_707_, lean_object* v___x_708_, lean_object* v_a_709_, lean_object* v_b_710_){
_start:
{
lean_object* v_it_712_; lean_object* v_out_713_; 
if (lean_obj_tag(v_a_709_) == 0)
{
lean_object* v_currPos_732_; lean_object* v_searcher_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_762_; 
v_currPos_732_ = lean_ctor_get(v_a_709_, 0);
v_searcher_733_ = lean_ctor_get(v_a_709_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_762_ == 0)
{
v___x_735_ = v_a_709_;
v_isShared_736_ = v_isSharedCheck_762_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_searcher_733_);
lean_inc(v_currPos_732_);
lean_dec(v_a_709_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_762_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_str_737_; lean_object* v_startInclusive_738_; lean_object* v_endExclusive_739_; lean_object* v___x_740_; uint8_t v_decide_741_; 
v_str_737_ = lean_ctor_get(v___x_705_, 0);
v_startInclusive_738_ = lean_ctor_get(v___x_705_, 1);
v_endExclusive_739_ = lean_ctor_get(v___x_705_, 2);
v___x_740_ = lean_nat_sub(v_endExclusive_739_, v_startInclusive_738_);
v_decide_741_ = lean_nat_dec_eq(v_searcher_733_, v___x_740_);
lean_dec(v___x_740_);
if (v_decide_741_ == 0)
{
lean_object* v___x_742_; uint32_t v___x_743_; uint32_t v___x_744_; uint8_t v___x_745_; 
v___x_742_ = lean_nat_add(v_startInclusive_738_, v_searcher_733_);
v___x_743_ = lean_string_utf8_get_fast(v_str_737_, v___x_742_);
v___x_744_ = 10;
v___x_745_ = lean_uint32_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
lean_dec(v_searcher_733_);
v___x_746_ = lean_string_utf8_next_fast(v_str_737_, v___x_742_);
lean_dec(v___x_742_);
v___x_747_ = lean_nat_sub(v___x_746_, v_startInclusive_738_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_747_);
v___x_749_ = v___x_735_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_currPos_732_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_705_, v___x_706_, v_src_707_, v___x_708_, v___x_749_, v_b_710_);
return v___x_750_;
}
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_slice_755_; lean_object* v_nextIt_757_; 
v___x_752_ = lean_string_utf8_next_fast(v_str_737_, v___x_742_);
v___x_753_ = lean_nat_sub(v___x_752_, v___x_742_);
lean_dec(v___x_742_);
v___x_754_ = lean_nat_add(v_searcher_733_, v___x_753_);
lean_dec(v___x_753_);
lean_dec(v_searcher_733_);
lean_inc_ref(v___x_705_);
v_slice_755_ = l_String_Slice_slice_x21(v___x_705_, v_currPos_732_, v___x_754_);
lean_dec(v_currPos_732_);
lean_inc(v___x_754_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___x_754_);
lean_ctor_set(v___x_735_, 0, v___x_754_);
v_nextIt_757_ = v___x_735_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_754_);
v_nextIt_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
v_it_712_ = v_nextIt_757_;
v_out_713_ = v_slice_755_;
goto v___jp_711_;
}
}
}
else
{
uint8_t v_decide_759_; 
lean_del_object(v___x_735_);
lean_dec(v_searcher_733_);
v_decide_759_ = lean_nat_dec_eq(v_currPos_732_, v___x_706_);
if (v_decide_759_ == 0)
{
lean_object* v_slice_760_; lean_object* v___x_761_; 
lean_inc(v___x_708_);
lean_inc_ref(v_src_707_);
v_slice_760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_760_, 0, v_src_707_);
lean_ctor_set(v_slice_760_, 1, v_currPos_732_);
lean_ctor_set(v_slice_760_, 2, v___x_708_);
v___x_761_ = lean_box(1);
v_it_712_ = v___x_761_;
v_out_713_ = v_slice_760_;
goto v___jp_711_;
}
else
{
lean_dec(v_currPos_732_);
lean_dec(v___x_708_);
lean_dec_ref(v_src_707_);
lean_dec_ref(v___x_705_);
return v_b_710_;
}
}
}
}
else
{
lean_dec(v___x_708_);
lean_dec_ref(v_src_707_);
lean_dec_ref(v___x_705_);
return v_b_710_;
}
v___jp_711_:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = l_String_Slice_lines_lineMap(v_out_713_);
v___x_715_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_714_);
lean_dec_ref(v___x_714_);
if (lean_obj_tag(v_b_710_) == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
v___x_718_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_705_, v___x_706_, v_src_707_, v___x_708_, v_it_712_, v___x_717_);
return v___x_718_;
}
else
{
lean_object* v_val_719_; uint8_t v___x_720_; 
v_val_719_ = lean_ctor_get(v_b_710_, 0);
v___x_720_ = lean_nat_dec_le(v___x_716_, v_val_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec(v___x_716_);
v___x_721_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_705_, v___x_706_, v_src_707_, v___x_708_, v_it_712_, v_b_710_);
return v___x_721_;
}
else
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_729_; 
v_isSharedCheck_729_ = !lean_is_exclusive(v_b_710_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_b_710_, 0);
lean_dec(v_unused_730_);
v___x_723_ = v_b_710_;
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
else
{
lean_dec(v_b_710_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_716_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_716_);
v___x_726_ = v_reuseFailAlloc_728_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_705_, v___x_706_, v_src_707_, v___x_708_, v_it_712_, v___x_726_);
return v___x_727_;
}
}
}
}
}
else
{
lean_object* v___x_731_; 
lean_dec_ref(v___x_714_);
v___x_731_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_705_, v___x_706_, v_src_707_, v___x_708_, v_it_712_, v_b_710_);
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object* v___x_763_, lean_object* v___x_764_, lean_object* v_src_765_, lean_object* v___x_766_, lean_object* v_a_767_, lean_object* v_b_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_763_, v___x_764_, v_src_765_, v___x_766_, v_a_767_, v_b_768_);
lean_dec(v___x_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object* v___x_770_, lean_object* v_i_771_, lean_object* v_out_772_, lean_object* v_pending_773_, lean_object* v___y_774_, lean_object* v_____r_775_, lean_object* v_out_776_){
_start:
{
lean_object* v_str_777_; lean_object* v_startInclusive_778_; lean_object* v_endExclusive_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_str_777_ = lean_ctor_get(v___x_770_, 0);
v_startInclusive_778_ = lean_ctor_get(v___x_770_, 1);
v_endExclusive_779_ = lean_ctor_get(v___x_770_, 2);
v___x_780_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_i_771_, v_out_772_);
v___x_781_ = lean_string_append(v_out_776_, v___x_780_);
lean_dec_ref(v___x_780_);
lean_inc(v_pending_773_);
v___x_782_ = l_String_Slice_Pos_nextn(v___x_770_, v_pending_773_, v___y_774_);
v___x_783_ = lean_nat_add(v_startInclusive_778_, v___x_782_);
lean_dec(v___x_782_);
v___x_784_ = lean_string_utf8_extract_fast(v_str_777_, v___x_783_, v_endExclusive_779_);
lean_dec(v___x_783_);
v___x_785_ = lean_string_append(v___x_781_, v___x_784_);
lean_dec_ref(v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_pending_773_);
v___x_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object* v___x_788_, lean_object* v_i_789_, lean_object* v_out_790_, lean_object* v_pending_791_, lean_object* v___y_792_, lean_object* v_____r_793_, lean_object* v_out_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_788_, v_i_789_, v_out_790_, v_pending_791_, v___y_792_, v_____r_793_, v_out_794_);
lean_dec_ref(v___x_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object* v_i_796_, lean_object* v___y_797_, lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v_src_800_, lean_object* v___x_801_, lean_object* v_a_802_, lean_object* v_b_803_){
_start:
{
lean_object* v___y_805_; lean_object* v_val_806_; 
if (lean_obj_tag(v_a_802_) == 0)
{
lean_object* v_currPos_810_; lean_object* v_searcher_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_874_; 
v_currPos_810_ = lean_ctor_get(v_a_802_, 0);
v_searcher_811_ = lean_ctor_get(v_a_802_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_a_802_);
if (v_isSharedCheck_874_ == 0)
{
v___x_813_ = v_a_802_;
v_isShared_814_ = v_isSharedCheck_874_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_searcher_811_);
lean_inc(v_currPos_810_);
lean_dec(v_a_802_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_874_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_str_815_; lean_object* v_startInclusive_816_; lean_object* v_endExclusive_817_; lean_object* v_out_818_; lean_object* v_pending_819_; lean_object* v_it_821_; lean_object* v_out_822_; lean_object* v___x_852_; uint8_t v_decide_853_; 
v_str_815_ = lean_ctor_get(v___x_798_, 0);
v_startInclusive_816_ = lean_ctor_get(v___x_798_, 1);
v_endExclusive_817_ = lean_ctor_get(v___x_798_, 2);
v_out_818_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_819_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_nat_sub(v_endExclusive_817_, v_startInclusive_816_);
v_decide_853_ = lean_nat_dec_eq(v_searcher_811_, v___x_852_);
lean_dec(v___x_852_);
if (v_decide_853_ == 0)
{
uint32_t v___x_854_; lean_object* v___x_855_; uint32_t v___x_856_; uint8_t v___x_857_; 
v___x_854_ = 10;
v___x_855_ = lean_nat_add(v_startInclusive_816_, v_searcher_811_);
v___x_856_ = lean_string_utf8_get_fast(v_str_815_, v___x_855_);
v___x_857_ = lean_uint32_dec_eq(v___x_856_, v___x_854_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_searcher_811_);
v___x_858_ = lean_string_utf8_next_fast(v_str_815_, v___x_855_);
lean_dec(v___x_855_);
v___x_859_ = lean_nat_sub(v___x_858_, v_startInclusive_816_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_859_);
v___x_861_ = v___x_813_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_currPos_810_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_863_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
v_a_802_ = v___x_861_;
goto _start;
}
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_slice_867_; lean_object* v_nextIt_869_; 
v___x_864_ = lean_string_utf8_next_fast(v_str_815_, v___x_855_);
v___x_865_ = lean_nat_sub(v___x_864_, v___x_855_);
lean_dec(v___x_855_);
v___x_866_ = lean_nat_add(v_searcher_811_, v___x_865_);
lean_dec(v___x_865_);
lean_dec(v_searcher_811_);
lean_inc_ref(v___x_798_);
v_slice_867_ = l_String_Slice_slice_x21(v___x_798_, v_currPos_810_, v___x_866_);
lean_dec(v_currPos_810_);
lean_inc(v___x_866_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_866_);
lean_ctor_set(v___x_813_, 0, v___x_866_);
v_nextIt_869_ = v___x_813_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_866_);
v_nextIt_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
v_it_821_ = v_nextIt_869_;
v_out_822_ = v_slice_867_;
goto v___jp_820_;
}
}
}
else
{
uint8_t v_decide_871_; 
lean_del_object(v___x_813_);
lean_dec(v_searcher_811_);
v_decide_871_ = lean_nat_dec_eq(v_currPos_810_, v___x_799_);
if (v_decide_871_ == 0)
{
lean_object* v_slice_872_; lean_object* v___x_873_; 
lean_inc(v___x_801_);
lean_inc_ref(v_src_800_);
v_slice_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_872_, 0, v_src_800_);
lean_ctor_set(v_slice_872_, 1, v_currPos_810_);
lean_ctor_set(v_slice_872_, 2, v___x_801_);
v___x_873_ = lean_box(1);
v_it_821_ = v___x_873_;
v_out_822_ = v_slice_872_;
goto v___jp_820_;
}
else
{
lean_dec(v_currPos_810_);
lean_dec(v___x_801_);
lean_dec_ref(v_src_800_);
lean_dec_ref(v___x_798_);
lean_dec(v___y_797_);
lean_dec(v_i_796_);
return v_b_803_;
}
}
v___jp_820_:
{
lean_object* v_fst_823_; lean_object* v_snd_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_851_; 
v_fst_823_ = lean_ctor_get(v_b_803_, 0);
v_snd_824_ = lean_ctor_get(v_b_803_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_b_803_);
if (v_isSharedCheck_851_ == 0)
{
v___x_826_ = v_b_803_;
v_isShared_827_ = v_isSharedCheck_851_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_snd_824_);
lean_inc(v_fst_823_);
lean_dec(v_b_803_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_851_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = l_String_Slice_lines_lineMap(v_out_822_);
v___x_829_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
lean_del_object(v___x_826_);
v___x_830_ = lean_string_utf8_byte_size(v_fst_823_);
v___x_831_ = lean_nat_dec_eq(v___x_830_, v_pending_819_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_nat_add(v_snd_824_, v___x_832_);
lean_dec(v_snd_824_);
v___x_834_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_833_, v_fst_823_);
v___x_835_ = lean_box(0);
lean_inc(v___y_797_);
lean_inc(v_i_796_);
v___x_836_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_828_, v_i_796_, v_out_818_, v_pending_819_, v___y_797_, v___x_835_, v___x_834_);
lean_dec_ref(v___x_828_);
v___y_805_ = v_it_821_;
v_val_806_ = v___x_836_;
goto v___jp_804_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_snd_824_);
v___x_837_ = lean_box(0);
lean_inc(v___y_797_);
lean_inc(v_i_796_);
v___x_838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_828_, v_i_796_, v_out_818_, v_pending_819_, v___y_797_, v___x_837_, v_fst_823_);
lean_dec_ref(v___x_828_);
v___y_805_ = v_it_821_;
v_val_806_ = v___x_838_;
goto v___jp_804_;
}
}
else
{
lean_object* v___x_839_; uint8_t v___x_840_; 
lean_dec_ref(v___x_828_);
v___x_839_ = lean_string_utf8_byte_size(v_fst_823_);
v___x_840_ = lean_nat_dec_eq(v___x_839_, v_pending_819_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_snd_824_, v___x_841_);
lean_dec(v_snd_824_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v___x_842_);
v___x_844_ = v___x_826_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_fst_823_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_842_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
v_a_802_ = v_it_821_;
v_b_803_ = v___x_844_;
goto _start;
}
}
else
{
lean_object* v___x_848_; 
if (v_isShared_827_ == 0)
{
v___x_848_ = v___x_826_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_823_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_snd_824_);
v___x_848_ = v_reuseFailAlloc_850_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
v_a_802_ = v_it_821_;
v_b_803_ = v___x_848_;
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
lean_dec(v___x_801_);
lean_dec_ref(v_src_800_);
lean_dec_ref(v___x_798_);
lean_dec(v___y_797_);
lean_dec(v_i_796_);
return v_b_803_;
}
v___jp_804_:
{
if (lean_obj_tag(v_val_806_) == 0)
{
lean_object* v_a_807_; 
lean_dec(v___y_805_);
lean_dec(v___x_801_);
lean_dec_ref(v_src_800_);
lean_dec_ref(v___x_798_);
lean_dec(v___y_797_);
lean_dec(v_i_796_);
v_a_807_ = lean_ctor_get(v_val_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v_val_806_, 1);
return v_a_807_;
}
else
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v_val_806_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v_val_806_, 1);
v_a_802_ = v___y_805_;
v_b_803_ = v_a_808_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object* v_i_875_, lean_object* v___y_876_, lean_object* v___x_877_, lean_object* v___x_878_, lean_object* v_src_879_, lean_object* v___x_880_, lean_object* v_a_881_, lean_object* v_b_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_875_, v___y_876_, v___x_877_, v___x_878_, v_src_879_, v___x_880_, v_a_881_, v_b_882_);
lean_dec(v___x_878_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object* v_i_884_, lean_object* v___y_885_, lean_object* v___x_886_, lean_object* v___x_887_, lean_object* v_src_888_, lean_object* v___x_889_, lean_object* v_a_890_, lean_object* v_b_891_){
_start:
{
lean_object* v___y_893_; lean_object* v_val_894_; 
if (lean_obj_tag(v_a_890_) == 0)
{
lean_object* v_currPos_898_; lean_object* v_searcher_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_962_; 
v_currPos_898_ = lean_ctor_get(v_a_890_, 0);
v_searcher_899_ = lean_ctor_get(v_a_890_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_a_890_);
if (v_isSharedCheck_962_ == 0)
{
v___x_901_ = v_a_890_;
v_isShared_902_ = v_isSharedCheck_962_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_searcher_899_);
lean_inc(v_currPos_898_);
lean_dec(v_a_890_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_962_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_str_903_; lean_object* v_startInclusive_904_; lean_object* v_endExclusive_905_; lean_object* v_out_906_; lean_object* v_pending_907_; lean_object* v_it_909_; lean_object* v_out_910_; lean_object* v___x_940_; uint8_t v_decide_941_; 
v_str_903_ = lean_ctor_get(v___x_886_, 0);
v_startInclusive_904_ = lean_ctor_get(v___x_886_, 1);
v_endExclusive_905_ = lean_ctor_get(v___x_886_, 2);
v_out_906_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_907_ = lean_unsigned_to_nat(0u);
v___x_940_ = lean_nat_sub(v_endExclusive_905_, v_startInclusive_904_);
v_decide_941_ = lean_nat_dec_eq(v_searcher_899_, v___x_940_);
lean_dec(v___x_940_);
if (v_decide_941_ == 0)
{
lean_object* v___x_942_; uint32_t v___x_943_; uint32_t v___x_944_; uint8_t v___x_945_; 
v___x_942_ = lean_nat_add(v_startInclusive_904_, v_searcher_899_);
v___x_943_ = lean_string_utf8_get_fast(v_str_903_, v___x_942_);
v___x_944_ = 10;
v___x_945_ = lean_uint32_dec_eq(v___x_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec(v_searcher_899_);
v___x_946_ = lean_string_utf8_next_fast(v_str_903_, v___x_942_);
lean_dec(v___x_942_);
v___x_947_ = lean_nat_sub(v___x_946_, v_startInclusive_904_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_947_);
v___x_949_ = v___x_901_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_currPos_898_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_947_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_884_, v___y_885_, v___x_886_, v___x_887_, v_src_888_, v___x_889_, v___x_949_, v_b_891_);
return v___x_950_;
}
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_slice_955_; lean_object* v_nextIt_957_; 
v___x_952_ = lean_string_utf8_next_fast(v_str_903_, v___x_942_);
v___x_953_ = lean_nat_sub(v___x_952_, v___x_942_);
lean_dec(v___x_942_);
v___x_954_ = lean_nat_add(v_searcher_899_, v___x_953_);
lean_dec(v___x_953_);
lean_dec(v_searcher_899_);
lean_inc_ref(v___x_886_);
v_slice_955_ = l_String_Slice_slice_x21(v___x_886_, v_currPos_898_, v___x_954_);
lean_dec(v_currPos_898_);
lean_inc(v___x_954_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_954_);
lean_ctor_set(v___x_901_, 0, v___x_954_);
v_nextIt_957_ = v___x_901_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_954_);
v_nextIt_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
v_it_909_ = v_nextIt_957_;
v_out_910_ = v_slice_955_;
goto v___jp_908_;
}
}
}
else
{
uint8_t v_decide_959_; 
lean_del_object(v___x_901_);
lean_dec(v_searcher_899_);
v_decide_959_ = lean_nat_dec_eq(v_currPos_898_, v___x_887_);
if (v_decide_959_ == 0)
{
lean_object* v_slice_960_; lean_object* v___x_961_; 
lean_inc(v___x_889_);
lean_inc_ref(v_src_888_);
v_slice_960_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_960_, 0, v_src_888_);
lean_ctor_set(v_slice_960_, 1, v_currPos_898_);
lean_ctor_set(v_slice_960_, 2, v___x_889_);
v___x_961_ = lean_box(1);
v_it_909_ = v___x_961_;
v_out_910_ = v_slice_960_;
goto v___jp_908_;
}
else
{
lean_dec(v_currPos_898_);
lean_dec(v___x_889_);
lean_dec_ref(v_src_888_);
lean_dec_ref(v___x_886_);
lean_dec(v___y_885_);
lean_dec(v_i_884_);
return v_b_891_;
}
}
v___jp_908_:
{
lean_object* v_fst_911_; lean_object* v_snd_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_939_; 
v_fst_911_ = lean_ctor_get(v_b_891_, 0);
v_snd_912_ = lean_ctor_get(v_b_891_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_b_891_);
if (v_isSharedCheck_939_ == 0)
{
v___x_914_ = v_b_891_;
v_isShared_915_ = v_isSharedCheck_939_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snd_912_);
lean_inc(v_fst_911_);
lean_dec(v_b_891_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_939_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = l_String_Slice_lines_lineMap(v_out_910_);
v___x_917_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; uint8_t v___x_919_; 
lean_del_object(v___x_914_);
v___x_918_ = lean_string_utf8_byte_size(v_fst_911_);
v___x_919_ = lean_nat_dec_eq(v___x_918_, v_pending_907_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_snd_912_, v___x_920_);
lean_dec(v_snd_912_);
v___x_922_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_921_, v_fst_911_);
v___x_923_ = lean_box(0);
lean_inc(v___y_885_);
lean_inc(v_i_884_);
v___x_924_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_916_, v_i_884_, v_out_906_, v_pending_907_, v___y_885_, v___x_923_, v___x_922_);
lean_dec_ref(v___x_916_);
v___y_893_ = v_it_909_;
v_val_894_ = v___x_924_;
goto v___jp_892_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_snd_912_);
v___x_925_ = lean_box(0);
lean_inc(v___y_885_);
lean_inc(v_i_884_);
v___x_926_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_916_, v_i_884_, v_out_906_, v_pending_907_, v___y_885_, v___x_925_, v_fst_911_);
lean_dec_ref(v___x_916_);
v___y_893_ = v_it_909_;
v_val_894_ = v___x_926_;
goto v___jp_892_;
}
}
else
{
lean_object* v___x_927_; uint8_t v___x_928_; 
lean_dec_ref(v___x_916_);
v___x_927_ = lean_string_utf8_byte_size(v_fst_911_);
v___x_928_ = lean_nat_dec_eq(v___x_927_, v_pending_907_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_snd_912_, v___x_929_);
lean_dec(v_snd_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_930_);
v___x_932_ = v___x_914_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_fst_911_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_930_);
v___x_932_ = v_reuseFailAlloc_934_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; 
v___x_933_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_884_, v___y_885_, v___x_886_, v___x_887_, v_src_888_, v___x_889_, v_it_909_, v___x_932_);
return v___x_933_;
}
}
else
{
lean_object* v___x_936_; 
if (v_isShared_915_ == 0)
{
v___x_936_ = v___x_914_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_fst_911_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_snd_912_);
v___x_936_ = v_reuseFailAlloc_938_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; 
v___x_937_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_884_, v___y_885_, v___x_886_, v___x_887_, v_src_888_, v___x_889_, v_it_909_, v___x_936_);
return v___x_937_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_889_);
lean_dec_ref(v_src_888_);
lean_dec_ref(v___x_886_);
lean_dec(v___y_885_);
lean_dec(v_i_884_);
return v_b_891_;
}
v___jp_892_:
{
if (lean_obj_tag(v_val_894_) == 0)
{
lean_object* v_a_895_; 
lean_dec(v___y_893_);
lean_dec(v___x_889_);
lean_dec_ref(v_src_888_);
lean_dec_ref(v___x_886_);
lean_dec(v___y_885_);
lean_dec(v_i_884_);
v_a_895_ = lean_ctor_get(v_val_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v_val_894_, 1);
return v_a_895_;
}
else
{
lean_object* v_a_896_; lean_object* v___x_897_; 
v_a_896_ = lean_ctor_get(v_val_894_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v_val_894_, 1);
v___x_897_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_884_, v___y_885_, v___x_886_, v___x_887_, v_src_888_, v___x_889_, v___y_893_, v_a_896_);
return v___x_897_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object* v_i_963_, lean_object* v___y_964_, lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v_src_967_, lean_object* v___x_968_, lean_object* v_a_969_, lean_object* v_b_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_963_, v___y_964_, v___x_965_, v___x_966_, v_src_967_, v___x_968_, v_a_969_, v_b_970_);
lean_dec(v___x_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object* v_i_975_, lean_object* v_src_976_){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___y_983_; lean_object* v___x_987_; 
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_string_utf8_byte_size(v_src_976_);
lean_inc_ref_n(v_src_976_, 3);
v___x_979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_979_, 0, v_src_976_);
lean_ctor_set(v___x_979_, 1, v___x_977_);
lean_ctor_set(v___x_979_, 2, v___x_978_);
v___x_980_ = lean_box(0);
v___x_981_ = l_String_lines(v_src_976_);
lean_inc(v___x_981_);
lean_inc_ref(v___x_979_);
v___x_987_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_979_, v___x_978_, v_src_976_, v___x_978_, v___x_981_, v___x_980_);
if (lean_obj_tag(v___x_987_) == 0)
{
v___y_983_ = v___x_977_;
goto v___jp_982_;
}
else
{
lean_object* v_val_988_; 
v_val_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_val_988_);
lean_dec_ref_known(v___x_987_, 1);
v___y_983_ = v_val_988_;
goto v___jp_982_;
}
v___jp_982_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_fst_986_; 
v___x_984_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0));
v___x_985_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_975_, v___y_983_, v___x_979_, v___x_978_, v_src_976_, v___x_978_, v___x_981_, v___x_984_);
v_fst_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_fst_986_);
lean_dec_ref(v___x_985_);
return v_fst_986_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object* v_i_989_, lean_object* v___y_990_, lean_object* v___x_991_, lean_object* v___x_992_, lean_object* v_src_993_, lean_object* v___x_994_, lean_object* v_inst_995_, lean_object* v_R_996_, lean_object* v_a_997_, lean_object* v_b_998_, lean_object* v_c_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_989_, v___y_990_, v___x_991_, v___x_992_, v_src_993_, v___x_994_, v_a_997_, v_b_998_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object* v_i_1001_, lean_object* v___y_1002_, lean_object* v___x_1003_, lean_object* v___x_1004_, lean_object* v_src_1005_, lean_object* v___x_1006_, lean_object* v_inst_1007_, lean_object* v_R_1008_, lean_object* v_a_1009_, lean_object* v_b_1010_, lean_object* v_c_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(v_i_1001_, v___y_1002_, v___x_1003_, v___x_1004_, v_src_1005_, v___x_1006_, v_inst_1007_, v_R_1008_, v_a_1009_, v_b_1010_, v_c_1011_);
lean_dec(v___x_1004_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object* v___x_1013_, lean_object* v___x_1014_, lean_object* v_src_1015_, lean_object* v___x_1016_, lean_object* v_inst_1017_, lean_object* v_R_1018_, lean_object* v_a_1019_, lean_object* v_b_1020_, lean_object* v_c_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1013_, v___x_1014_, v_src_1015_, v___x_1016_, v_a_1019_, v_b_1020_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v_src_1025_, lean_object* v___x_1026_, lean_object* v_inst_1027_, lean_object* v_R_1028_, lean_object* v_a_1029_, lean_object* v_b_1030_, lean_object* v_c_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(v___x_1023_, v___x_1024_, v_src_1025_, v___x_1026_, v_inst_1027_, v_R_1028_, v_a_1029_, v_b_1030_, v_c_1031_);
lean_dec(v___x_1024_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object* v_i_1033_, lean_object* v___y_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_src_1037_, lean_object* v___x_1038_, lean_object* v_inst_1039_, lean_object* v_R_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_, lean_object* v_c_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_1033_, v___y_1034_, v___x_1035_, v___x_1036_, v_src_1037_, v___x_1038_, v_a_1041_, v_b_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object* v_i_1045_, lean_object* v___y_1046_, lean_object* v___x_1047_, lean_object* v___x_1048_, lean_object* v_src_1049_, lean_object* v___x_1050_, lean_object* v_inst_1051_, lean_object* v_R_1052_, lean_object* v_a_1053_, lean_object* v_b_1054_, lean_object* v_c_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(v_i_1045_, v___y_1046_, v___x_1047_, v___x_1048_, v_src_1049_, v___x_1050_, v_inst_1051_, v_R_1052_, v_a_1053_, v_b_1054_, v_c_1055_);
lean_dec(v___x_1048_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v_src_1059_, lean_object* v___x_1060_, lean_object* v_inst_1061_, lean_object* v_R_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v_c_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_1057_, v___x_1058_, v_src_1059_, v___x_1060_, v_a_1063_, v_b_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object* v___x_1067_, lean_object* v___x_1068_, lean_object* v_src_1069_, lean_object* v___x_1070_, lean_object* v_inst_1071_, lean_object* v_R_1072_, lean_object* v_a_1073_, lean_object* v_b_1074_, lean_object* v_c_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(v___x_1067_, v___x_1068_, v_src_1069_, v___x_1070_, v_inst_1071_, v_R_1072_, v_a_1073_, v_b_1074_, v_c_1075_);
lean_dec(v___x_1068_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v_zero_1079_; uint8_t v_isZero_1080_; 
v_zero_1079_ = lean_unsigned_to_nat(0u);
v_isZero_1080_ = lean_nat_dec_eq(v_x_1077_, v_zero_1079_);
if (v_isZero_1080_ == 1)
{
lean_dec(v_x_1077_);
return v_x_1078_;
}
else
{
uint32_t v___x_1081_; lean_object* v_one_1082_; lean_object* v_n_1083_; lean_object* v___x_1084_; 
v___x_1081_ = 96;
v_one_1082_ = lean_unsigned_to_nat(1u);
v_n_1083_ = lean_nat_sub(v_x_1077_, v_one_1082_);
lean_dec(v_x_1077_);
v___x_1084_ = lean_string_push(v_x_1078_, v___x_1081_);
v_x_1077_ = v_n_1083_;
v_x_1078_ = v___x_1084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object* v_value_1087_){
_start:
{
lean_object* v___y_1089_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1111_; 
v___x_1103_ = lean_string_utf8_byte_size(v_value_1087_);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1111_ = lean_nat_dec_eq(v___x_1103_, v___x_1104_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_nat_dec_le(v___x_1112_, v___x_1103_);
if (v___x_1113_ == 0)
{
goto v___jp_1105_;
}
else
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1115_ = lean_string_memcmp(v_value_1087_, v___x_1114_, v___x_1104_, v___x_1104_, v___x_1112_);
if (v___x_1115_ == 0)
{
goto v___jp_1105_;
}
else
{
goto v___jp_1097_;
}
}
}
else
{
lean_object* v___x_1116_; 
lean_dec_ref(v_value_1087_);
v___x_1116_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___y_1089_ = v___x_1116_;
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_delim_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1090_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_1091_ = l_Lean_Doc_longestBacktickRun(v___y_1089_);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_add(v___x_1091_, v___x_1092_);
lean_dec(v___x_1091_);
v_delim_1094_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___x_1093_, v___x_1090_);
lean_inc_ref(v_delim_1094_);
v___x_1095_ = lean_string_append(v_delim_1094_, v___y_1089_);
lean_dec_ref(v___y_1089_);
v___x_1096_ = lean_string_append(v___x_1095_, v_delim_1094_);
lean_dec_ref(v_delim_1094_);
return v___x_1096_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1099_ = lean_string_append(v___x_1098_, v_value_1087_);
lean_dec_ref(v_value_1087_);
v___x_1100_ = lean_string_append(v___x_1099_, v___x_1098_);
v___y_1089_ = v___x_1100_;
goto v___jp_1088_;
}
v___jp_1101_:
{
uint8_t v___x_1102_; 
lean_inc_ref(v_value_1087_);
v___x_1102_ = l_Lean_Doc_versoCodeBoundarySpaces(v_value_1087_);
if (v___x_1102_ == 0)
{
v___y_1089_ = v_value_1087_;
goto v___jp_1088_;
}
else
{
goto v___jp_1097_;
}
}
v___jp_1105_:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_dec_le(v___x_1106_, v___x_1103_);
if (v___x_1107_ == 0)
{
goto v___jp_1101_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1108_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1109_ = lean_nat_sub(v___x_1103_, v___x_1106_);
v___x_1110_ = lean_string_memcmp(v_value_1087_, v___x_1108_, v___x_1109_, v___x_1104_, v___x_1106_);
lean_dec(v___x_1109_);
if (v___x_1110_ == 0)
{
goto v___jp_1101_;
}
else
{
goto v___jp_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t v_char_1117_, lean_object* v_as_1118_, size_t v_i_1119_, size_t v_stop_1120_, lean_object* v_b_1121_){
_start:
{
lean_object* v___y_1123_; uint8_t v___x_1127_; 
v___x_1127_ = lean_usize_dec_eq(v_i_1119_, v_stop_1120_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_array_uget_borrowed(v_as_1118_, v_i_1119_);
lean_inc(v___x_1128_);
v___x_1129_ = l_Lean_Doc_InlineView_of(v___x_1128_);
if (lean_obj_tag(v___x_1129_) == 1)
{
lean_object* v_val_1130_; 
v_val_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_val_1130_);
lean_dec_ref_known(v___x_1129_, 1);
switch(lean_obj_tag(v_val_1130_))
{
case 1:
{
lean_object* v_view_1131_; lean_object* v___y_1133_; uint32_t v___x_1138_; uint8_t v___x_1139_; 
v_view_1131_ = lean_ctor_get(v_val_1130_, 0);
lean_inc_ref(v_view_1131_);
lean_dec_ref_known(v_val_1130_, 1);
v___x_1138_ = 95;
v___x_1139_ = lean_uint32_dec_eq(v_char_1117_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_unsigned_to_nat(0u);
v___y_1133_ = v___x_1140_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_unsigned_to_nat(1u);
v___y_1133_ = v___x_1141_;
goto v___jp_1132_;
}
v___jp_1132_:
{
lean_object* v_content_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_content_1134_ = lean_ctor_get(v_view_1131_, 2);
lean_inc_ref(v_content_1134_);
lean_dec_ref(v_view_1131_);
v___x_1135_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1117_, v_content_1134_);
lean_dec_ref(v_content_1134_);
v___x_1136_ = lean_nat_add(v___y_1133_, v___x_1135_);
lean_dec(v___x_1135_);
v___x_1137_ = lean_nat_dec_le(v_b_1121_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_dec(v___x_1136_);
v___y_1123_ = v_b_1121_;
goto v___jp_1122_;
}
else
{
lean_dec(v_b_1121_);
v___y_1123_ = v___x_1136_;
goto v___jp_1122_;
}
}
}
case 2:
{
lean_object* v_view_1142_; lean_object* v___y_1144_; uint32_t v___x_1149_; uint8_t v___x_1150_; 
v_view_1142_ = lean_ctor_get(v_val_1130_, 0);
lean_inc_ref(v_view_1142_);
lean_dec_ref_known(v_val_1130_, 1);
v___x_1149_ = 42;
v___x_1150_ = lean_uint32_dec_eq(v_char_1117_, v___x_1149_);
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
v___x_1146_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1117_, v_content_1145_);
lean_dec_ref(v_content_1145_);
v___x_1147_ = lean_nat_add(v___y_1144_, v___x_1146_);
lean_dec(v___x_1146_);
v___x_1148_ = lean_nat_dec_le(v_b_1121_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec(v___x_1147_);
v___y_1123_ = v_b_1121_;
goto v___jp_1122_;
}
else
{
lean_dec(v_b_1121_);
v___y_1123_ = v___x_1147_;
goto v___jp_1122_;
}
}
}
case 5:
{
lean_object* v_view_1153_; lean_object* v_content_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_view_1153_ = lean_ctor_get(v_val_1130_, 0);
lean_inc_ref(v_view_1153_);
lean_dec_ref_known(v_val_1130_, 1);
v_content_1154_ = lean_ctor_get(v_view_1153_, 2);
lean_inc_ref(v_content_1154_);
lean_dec_ref(v_view_1153_);
v___x_1155_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1117_, v_content_1154_);
lean_dec_ref(v_content_1154_);
v___x_1156_ = lean_nat_dec_le(v_b_1121_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec(v___x_1155_);
v___y_1123_ = v_b_1121_;
goto v___jp_1122_;
}
else
{
lean_dec(v_b_1121_);
v___y_1123_ = v___x_1155_;
goto v___jp_1122_;
}
}
case 9:
{
lean_object* v_view_1157_; lean_object* v_content_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_view_1157_ = lean_ctor_get(v_val_1130_, 0);
lean_inc_ref(v_view_1157_);
lean_dec_ref_known(v_val_1130_, 1);
v_content_1158_ = lean_ctor_get(v_view_1157_, 6);
lean_inc_ref(v_content_1158_);
lean_dec_ref(v_view_1157_);
v___x_1159_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1117_, v_content_1158_);
lean_dec_ref(v_content_1158_);
v___x_1160_ = lean_nat_dec_le(v_b_1121_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_dec(v___x_1159_);
v___y_1123_ = v_b_1121_;
goto v___jp_1122_;
}
else
{
lean_dec(v_b_1121_);
v___y_1123_ = v___x_1159_;
goto v___jp_1122_;
}
}
default: 
{
lean_dec(v_val_1130_);
v___y_1123_ = v_b_1121_;
goto v___jp_1122_;
}
}
}
else
{
lean_dec(v___x_1129_);
v___y_1123_ = v_b_1121_;
goto v___jp_1122_;
}
}
else
{
return v_b_1121_;
}
v___jp_1122_:
{
size_t v___x_1124_; size_t v___x_1125_; 
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_add(v_i_1119_, v___x_1124_);
v_i_1119_ = v___x_1125_;
v_b_1121_ = v___y_1123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t v_char_1161_, lean_object* v_inls_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_array_get_size(v_inls_1162_);
v___x_1165_ = lean_nat_dec_lt(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
return v___x_1163_;
}
else
{
size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = lean_usize_of_nat(v___x_1164_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1161_, v_inls_1162_, v___x_1166_, v___x_1167_, v___x_1163_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object* v_char_1169_, lean_object* v_inls_1170_){
_start:
{
uint32_t v_char_boxed_1171_; lean_object* v_res_1172_; 
v_char_boxed_1171_ = lean_unbox_uint32(v_char_1169_);
lean_dec(v_char_1169_);
v_res_1172_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_boxed_1171_, v_inls_1170_);
lean_dec_ref(v_inls_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object* v_char_1173_, lean_object* v_as_1174_, lean_object* v_i_1175_, lean_object* v_stop_1176_, lean_object* v_b_1177_){
_start:
{
uint32_t v_char_boxed_1178_; size_t v_i_boxed_1179_; size_t v_stop_boxed_1180_; lean_object* v_res_1181_; 
v_char_boxed_1178_ = lean_unbox_uint32(v_char_1173_);
lean_dec(v_char_1173_);
v_i_boxed_1179_ = lean_unbox_usize(v_i_1175_);
lean_dec(v_i_1175_);
v_stop_boxed_1180_ = lean_unbox_usize(v_stop_1176_);
lean_dec(v_stop_1176_);
v_res_1181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_boxed_1178_, v_as_1174_, v_i_boxed_1179_, v_stop_boxed_1180_, v_b_1177_);
lean_dec_ref(v_as_1174_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t v_char_1182_, lean_object* v_inls_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
v___x_1185_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1182_, v_inls_1183_);
v___x_1186_ = lean_nat_add(v___x_1184_, v___x_1185_);
lean_dec(v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object* v_char_1187_, lean_object* v_inls_1188_){
_start:
{
uint32_t v_char_boxed_1189_; lean_object* v_res_1190_; 
v_char_boxed_1189_ = lean_unbox_uint32(v_char_1187_);
lean_dec(v_char_1187_);
v_res_1190_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_boxed_1189_, v_inls_1188_);
lean_dec_ref(v_inls_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object* v_as_1191_, size_t v_i_1192_, size_t v_stop_1193_, lean_object* v_b_1194_){
_start:
{
lean_object* v___y_1196_; uint8_t v___x_1200_; 
v___x_1200_ = lean_usize_dec_eq(v_i_1192_, v_stop_1193_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v_contents_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1201_ = lean_array_uget_borrowed(v_as_1191_, v_i_1192_);
v_contents_1202_ = lean_ctor_get(v___x_1201_, 2);
v___x_1203_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1202_);
v___x_1204_ = lean_nat_dec_le(v_b_1194_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec(v___x_1203_);
v___y_1196_ = v_b_1194_;
goto v___jp_1195_;
}
else
{
lean_dec(v_b_1194_);
v___y_1196_ = v___x_1203_;
goto v___jp_1195_;
}
}
else
{
return v_b_1194_;
}
v___jp_1195_:
{
size_t v___x_1197_; size_t v___x_1198_; 
v___x_1197_ = ((size_t)1ULL);
v___x_1198_ = lean_usize_add(v_i_1192_, v___x_1197_);
v_i_1192_ = v___x_1198_;
v_b_1194_ = v___y_1196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object* v_as_1205_, size_t v_i_1206_, size_t v_stop_1207_, lean_object* v_b_1208_){
_start:
{
lean_object* v___y_1210_; uint8_t v___x_1214_; 
v___x_1214_ = lean_usize_dec_eq(v_i_1206_, v_stop_1207_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v_contents_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1215_ = lean_array_uget_borrowed(v_as_1205_, v_i_1206_);
v_contents_1216_ = lean_ctor_get(v___x_1215_, 2);
v___x_1217_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1216_);
v___x_1218_ = lean_nat_dec_le(v_b_1208_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_dec(v___x_1217_);
v___y_1210_ = v_b_1208_;
goto v___jp_1209_;
}
else
{
lean_dec(v_b_1208_);
v___y_1210_ = v___x_1217_;
goto v___jp_1209_;
}
}
else
{
return v_b_1208_;
}
v___jp_1209_:
{
size_t v___x_1211_; size_t v___x_1212_; 
v___x_1211_ = ((size_t)1ULL);
v___x_1212_ = lean_usize_add(v_i_1206_, v___x_1211_);
v_i_1206_ = v___x_1212_;
v_b_1208_ = v___y_1210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object* v_as_1219_, size_t v_i_1220_, size_t v_stop_1221_, lean_object* v_b_1222_){
_start:
{
lean_object* v___y_1224_; uint8_t v___x_1228_; 
v___x_1228_ = lean_usize_dec_eq(v_i_1220_, v_stop_1221_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v_desc_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1229_ = lean_array_uget_borrowed(v_as_1219_, v_i_1220_);
v_desc_1230_ = lean_ctor_get(v___x_1229_, 3);
v___x_1231_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_desc_1230_);
v___x_1232_ = lean_nat_dec_le(v_b_1222_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_dec(v___x_1231_);
v___y_1224_ = v_b_1222_;
goto v___jp_1223_;
}
else
{
lean_dec(v_b_1222_);
v___y_1224_ = v___x_1231_;
goto v___jp_1223_;
}
}
else
{
return v_b_1222_;
}
v___jp_1223_:
{
size_t v___x_1225_; size_t v___x_1226_; 
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_add(v_i_1220_, v___x_1225_);
v_i_1220_ = v___x_1226_;
v_b_1222_ = v___y_1224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object* v_as_1233_, size_t v_i_1234_, size_t v_stop_1235_, lean_object* v_b_1236_){
_start:
{
lean_object* v___y_1238_; lean_object* v___y_1243_; uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_eq(v_i_1234_, v_stop_1235_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_array_uget_borrowed(v_as_1233_, v_i_1234_);
lean_inc(v___x_1248_);
v___x_1249_ = l_Lean_Doc_BlockView_of(v___x_1248_);
if (lean_obj_tag(v___x_1249_) == 1)
{
lean_object* v_val_1250_; 
v_val_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_val_1250_);
lean_dec_ref_known(v___x_1249_, 1);
switch(lean_obj_tag(v_val_1250_))
{
case 6:
{
lean_object* v_view_1251_; lean_object* v_content_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_view_1251_ = lean_ctor_get(v_val_1250_, 0);
lean_inc_ref(v_view_1251_);
lean_dec_ref_known(v_val_1250_, 1);
v_content_1252_ = lean_ctor_get(v_view_1251_, 4);
lean_inc_ref(v_content_1252_);
lean_dec_ref(v_view_1251_);
v___x_1253_ = lean_unsigned_to_nat(3u);
v___x_1254_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1252_);
lean_dec_ref(v_content_1252_);
v___x_1255_ = lean_nat_dec_le(v___x_1253_, v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec(v___x_1254_);
v___y_1243_ = v___x_1253_;
goto v___jp_1242_;
}
else
{
v___y_1243_ = v___x_1254_;
goto v___jp_1242_;
}
}
case 4:
{
lean_object* v_view_1256_; lean_object* v_content_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_view_1256_ = lean_ctor_get(v_val_1250_, 0);
lean_inc_ref(v_view_1256_);
lean_dec_ref_known(v_val_1250_, 1);
v_content_1257_ = lean_ctor_get(v_view_1256_, 2);
lean_inc_ref(v_content_1257_);
lean_dec_ref(v_view_1256_);
v___x_1258_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1257_);
lean_dec_ref(v_content_1257_);
v___x_1259_ = lean_nat_dec_le(v_b_1236_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_dec(v___x_1258_);
v___y_1238_ = v_b_1236_;
goto v___jp_1237_;
}
else
{
lean_dec(v_b_1236_);
v___y_1238_ = v___x_1258_;
goto v___jp_1237_;
}
}
case 1:
{
lean_object* v_view_1260_; lean_object* v_items_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_view_1260_ = lean_ctor_get(v_val_1250_, 0);
lean_inc_ref(v_view_1260_);
lean_dec_ref_known(v_val_1250_, 1);
v_items_1261_ = lean_ctor_get(v_view_1260_, 1);
lean_inc_ref(v_items_1261_);
lean_dec_ref(v_view_1260_);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_array_get_size(v_items_1261_);
v___x_1264_ = lean_nat_dec_lt(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_dec_ref(v_items_1261_);
v___y_1238_ = v_b_1236_;
goto v___jp_1237_;
}
else
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((size_t)0ULL);
v___x_1266_ = lean_usize_of_nat(v___x_1263_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1261_, v___x_1265_, v___x_1266_, v_b_1236_);
lean_dec_ref(v_items_1261_);
v___y_1238_ = v___x_1267_;
goto v___jp_1237_;
}
}
case 2:
{
lean_object* v_view_1268_; lean_object* v_items_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_view_1268_ = lean_ctor_get(v_val_1250_, 0);
lean_inc_ref(v_view_1268_);
lean_dec_ref_known(v_val_1250_, 1);
v_items_1269_ = lean_ctor_get(v_view_1268_, 2);
lean_inc_ref(v_items_1269_);
lean_dec_ref(v_view_1268_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_array_get_size(v_items_1269_);
v___x_1272_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec_ref(v_items_1269_);
v___y_1238_ = v_b_1236_;
goto v___jp_1237_;
}
else
{
size_t v___x_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = lean_usize_of_nat(v___x_1271_);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1269_, v___x_1273_, v___x_1274_, v_b_1236_);
lean_dec_ref(v_items_1269_);
v___y_1238_ = v___x_1275_;
goto v___jp_1237_;
}
}
case 3:
{
lean_object* v_view_1276_; lean_object* v_items_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_view_1276_ = lean_ctor_get(v_val_1250_, 0);
lean_inc_ref(v_view_1276_);
lean_dec_ref_known(v_val_1250_, 1);
v_items_1277_ = lean_ctor_get(v_view_1276_, 1);
lean_inc_ref(v_items_1277_);
lean_dec_ref(v_view_1276_);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_array_get_size(v_items_1277_);
v___x_1280_ = lean_nat_dec_lt(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec_ref(v_items_1277_);
v___y_1238_ = v_b_1236_;
goto v___jp_1237_;
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1279_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1277_, v___x_1281_, v___x_1282_, v_b_1236_);
lean_dec_ref(v_items_1277_);
v___y_1238_ = v___x_1283_;
goto v___jp_1237_;
}
}
default: 
{
lean_dec(v_val_1250_);
v___y_1238_ = v_b_1236_;
goto v___jp_1237_;
}
}
}
else
{
lean_dec(v___x_1249_);
v___y_1238_ = v_b_1236_;
goto v___jp_1237_;
}
}
else
{
return v_b_1236_;
}
v___jp_1237_:
{
size_t v___x_1239_; size_t v___x_1240_; 
v___x_1239_ = ((size_t)1ULL);
v___x_1240_ = lean_usize_add(v_i_1234_, v___x_1239_);
v_i_1234_ = v___x_1240_;
v_b_1236_ = v___y_1238_;
goto _start;
}
v___jp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v___y_1243_, v___x_1244_);
lean_dec(v___y_1243_);
v___x_1246_ = lean_nat_dec_le(v_b_1236_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec(v___x_1245_);
v___y_1238_ = v_b_1236_;
goto v___jp_1237_;
}
else
{
lean_dec(v_b_1236_);
v___y_1238_ = v___x_1245_;
goto v___jp_1237_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object* v_blks_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_array_get_size(v_blks_1284_);
v___x_1287_ = lean_nat_dec_lt(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
return v___x_1285_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1286_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1284_, v___x_1288_, v___x_1289_, v___x_1285_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object* v_blks_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1291_);
lean_dec_ref(v_blks_1291_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object* v_as_1293_, lean_object* v_i_1294_, lean_object* v_stop_1295_, lean_object* v_b_1296_){
_start:
{
size_t v_i_boxed_1297_; size_t v_stop_boxed_1298_; lean_object* v_res_1299_; 
v_i_boxed_1297_ = lean_unbox_usize(v_i_1294_);
lean_dec(v_i_1294_);
v_stop_boxed_1298_ = lean_unbox_usize(v_stop_1295_);
lean_dec(v_stop_1295_);
v_res_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_as_1293_, v_i_boxed_1297_, v_stop_boxed_1298_, v_b_1296_);
lean_dec_ref(v_as_1293_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object* v_as_1300_, lean_object* v_i_1301_, lean_object* v_stop_1302_, lean_object* v_b_1303_){
_start:
{
size_t v_i_boxed_1304_; size_t v_stop_boxed_1305_; lean_object* v_res_1306_; 
v_i_boxed_1304_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_stop_boxed_1305_ = lean_unbox_usize(v_stop_1302_);
lean_dec(v_stop_1302_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_as_1300_, v_i_boxed_1304_, v_stop_boxed_1305_, v_b_1303_);
lean_dec_ref(v_as_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object* v_as_1307_, lean_object* v_i_1308_, lean_object* v_stop_1309_, lean_object* v_b_1310_){
_start:
{
size_t v_i_boxed_1311_; size_t v_stop_boxed_1312_; lean_object* v_res_1313_; 
v_i_boxed_1311_ = lean_unbox_usize(v_i_1308_);
lean_dec(v_i_1308_);
v_stop_boxed_1312_ = lean_unbox_usize(v_stop_1309_);
lean_dec(v_stop_1309_);
v_res_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_as_1307_, v_i_boxed_1311_, v_stop_boxed_1312_, v_b_1310_);
lean_dec_ref(v_as_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object* v_as_1314_, lean_object* v_i_1315_, lean_object* v_stop_1316_, lean_object* v_b_1317_){
_start:
{
size_t v_i_boxed_1318_; size_t v_stop_boxed_1319_; lean_object* v_res_1320_; 
v_i_boxed_1318_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_stop_boxed_1319_ = lean_unbox_usize(v_stop_1316_);
lean_dec(v_stop_1316_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_as_1314_, v_i_boxed_1318_, v_stop_boxed_1319_, v_b_1317_);
lean_dec_ref(v_as_1314_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object* v_blks_1321_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1322_ = lean_unsigned_to_nat(3u);
v___x_1323_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1321_);
v___x_1324_ = lean_nat_dec_le(v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec(v___x_1323_);
return v___x_1322_;
}
else
{
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object* v_blks_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_blks_1325_);
lean_dec_ref(v_blks_1325_);
return v_res_1326_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object* v_inl_1327_){
_start:
{
lean_object* v___x_1328_; 
lean_inc(v_inl_1327_);
v___x_1328_ = l_Lean_Doc_LinebreakView_of(v_inl_1327_);
if (lean_obj_tag(v___x_1328_) == 1)
{
uint8_t v___x_1329_; 
lean_dec_ref_known(v___x_1328_, 1);
lean_dec(v_inl_1327_);
v___x_1329_ = 1;
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; 
lean_dec(v___x_1328_);
v___x_1330_ = l_Lean_Doc_TextView_of(v_inl_1327_);
if (lean_obj_tag(v___x_1330_) == 1)
{
lean_object* v_val_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v_decide_1339_; 
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = 1;
v___x_1333_ = l_Lean_Doc_TextView_getVersoText(v_val_1331_);
lean_dec(v_val_1331_);
v___x_1334_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v___x_1332_, v___x_1333_);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_string_utf8_byte_size(v___x_1334_);
v___x_1337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1334_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
lean_ctor_set(v___x_1337_, 2, v___x_1336_);
v___x_1338_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1337_, v___x_1335_);
lean_dec_ref_known(v___x_1337_, 3);
v_decide_1339_ = lean_nat_dec_eq(v___x_1338_, v___x_1336_);
lean_dec(v___x_1338_);
return v_decide_1339_;
}
else
{
uint8_t v___x_1340_; 
lean_dec(v___x_1330_);
v___x_1340_ = 0;
return v___x_1340_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object* v_inl_1341_){
_start:
{
uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_res_1342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v_inl_1341_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object* v_stx_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_Doc_BlockView_of(v_stx_1344_);
if (lean_obj_tag(v___x_1345_) == 1)
{
lean_object* v_val_1346_; 
v_val_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___x_1345_, 1);
switch(lean_obj_tag(v_val_1346_))
{
case 8:
{
uint8_t v___x_1347_; 
lean_dec_ref_known(v_val_1346_, 1);
v___x_1347_ = 1;
return v___x_1347_;
}
case 9:
{
uint8_t v___x_1348_; 
lean_dec_ref_known(v_val_1346_, 1);
v___x_1348_ = 1;
return v___x_1348_;
}
case 10:
{
uint8_t v___x_1349_; 
lean_dec_ref_known(v_val_1346_, 1);
v___x_1349_ = 1;
return v___x_1349_;
}
case 11:
{
uint8_t v___x_1350_; 
lean_dec_ref_known(v_val_1346_, 1);
v___x_1350_ = 1;
return v___x_1350_;
}
default: 
{
uint8_t v___x_1351_; 
lean_dec(v_val_1346_);
v___x_1351_ = 0;
return v___x_1351_;
}
}
}
else
{
uint8_t v___x_1352_; 
lean_dec(v___x_1345_);
v___x_1352_ = 0;
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object* v_stx_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v_stx_1353_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object* v_inl_1356_){
_start:
{
lean_object* v___x_1357_; 
lean_inc(v_inl_1356_);
v___x_1357_ = l_Lean_Doc_LinebreakView_of(v_inl_1356_);
if (lean_obj_tag(v___x_1357_) == 1)
{
uint8_t v___x_1358_; 
lean_dec_ref_known(v___x_1357_, 1);
lean_dec(v_inl_1356_);
v___x_1358_ = 1;
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; 
lean_dec(v___x_1357_);
v___x_1359_ = l_Lean_Doc_TextView_of(v_inl_1356_);
if (lean_obj_tag(v___x_1359_) == 1)
{
lean_object* v_val_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v_decide_1366_; 
v_val_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = l_Lean_Doc_TextView_getVersoTextSource(v_val_1360_);
lean_dec(v_val_1360_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_string_utf8_byte_size(v___x_1361_);
v___x_1364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1361_);
lean_ctor_set(v___x_1364_, 1, v___x_1362_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
v___x_1365_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1364_, v___x_1362_);
lean_dec_ref_known(v___x_1364_, 3);
v_decide_1366_ = lean_nat_dec_eq(v___x_1365_, v___x_1363_);
lean_dec(v___x_1365_);
return v_decide_1366_;
}
else
{
uint8_t v___x_1367_; 
lean_dec(v___x_1359_);
v___x_1367_ = 0;
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object* v_inl_1368_){
_start:
{
uint8_t v_res_1369_; lean_object* v_r_1370_; 
v_res_1369_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v_inl_1368_);
v_r_1370_ = lean_box(v_res_1369_);
return v_r_1370_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object* v_as_1371_, size_t v_i_1372_, size_t v_stop_1373_){
_start:
{
uint8_t v___x_1374_; 
v___x_1374_ = lean_usize_dec_eq(v_i_1372_, v_stop_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_array_uget_borrowed(v_as_1371_, v_i_1372_);
lean_inc(v___x_1375_);
v___x_1376_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1375_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
v___x_1377_ = 1;
return v___x_1377_;
}
else
{
size_t v___x_1378_; size_t v___x_1379_; 
v___x_1378_ = ((size_t)1ULL);
v___x_1379_ = lean_usize_add(v_i_1372_, v___x_1378_);
v_i_1372_ = v___x_1379_;
goto _start;
}
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = 0;
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object* v_as_1382_, lean_object* v_i_1383_, lean_object* v_stop_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1383_);
lean_dec(v_i_1383_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1384_);
lean_dec(v_stop_1384_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_as_1382_, v_i_boxed_1385_, v_stop_boxed_1386_);
lean_dec_ref(v_as_1382_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object* v_stx_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Doc_ParaView_of(v_stx_1389_);
if (lean_obj_tag(v___x_1390_) == 1)
{
lean_object* v_val_1391_; lean_object* v_content_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_val_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v_content_1392_ = lean_ctor_get(v_val_1391_, 1);
lean_inc_ref(v_content_1392_);
lean_dec(v_val_1391_);
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_array_get_size(v_content_1392_);
v___x_1395_ = lean_nat_dec_lt(v___x_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
uint8_t v___x_1396_; 
lean_dec_ref(v_content_1392_);
v___x_1396_ = 1;
return v___x_1396_;
}
else
{
if (v___x_1395_ == 0)
{
lean_dec_ref(v_content_1392_);
return v___x_1395_;
}
else
{
size_t v___x_1397_; size_t v___x_1398_; uint8_t v___x_1399_; 
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = lean_usize_of_nat(v___x_1394_);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_content_1392_, v___x_1397_, v___x_1398_);
lean_dec_ref(v_content_1392_);
if (v___x_1399_ == 0)
{
return v___x_1395_;
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = 0;
return v___x_1400_;
}
}
}
}
else
{
uint8_t v___x_1401_; 
lean_dec(v___x_1390_);
v___x_1401_ = 0;
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object* v_stx_1402_){
_start:
{
uint8_t v_res_1403_; lean_object* v_r_1404_; 
v_res_1403_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_stx_1402_);
v_r_1404_ = lean_box(v_res_1403_);
return v_r_1404_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object* v_stx_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_Doc_LinebreakView_of(v_stx_1405_);
if (lean_obj_tag(v___x_1406_) == 1)
{
uint8_t v___x_1407_; 
lean_dec_ref_known(v___x_1406_, 1);
v___x_1407_ = 1;
return v___x_1407_;
}
else
{
uint8_t v___x_1408_; 
lean_dec(v___x_1406_);
v___x_1408_ = 0;
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object* v_stx_1409_){
_start:
{
uint8_t v_res_1410_; lean_object* v_r_1411_; 
v_res_1410_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v_stx_1409_);
v_r_1411_ = lean_box(v_res_1410_);
return v_r_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object* v_inls_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = lean_array_get_size(v_inls_1412_);
v___x_1414_ = lean_unsigned_to_nat(1u);
v___x_1415_ = lean_nat_dec_eq(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; lean_object* v_inl_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
v_inl_1418_ = lean_array_fget_borrowed(v_inls_1412_, v___x_1417_);
lean_inc(v_inl_1418_);
v___x_1419_ = l_Lean_Doc_InlineView_of(v_inl_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_box(0);
return v___x_1420_;
}
else
{
lean_object* v_val_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1444_; 
v_val_1421_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1423_ = v___x_1419_;
v_isShared_1424_ = v_isSharedCheck_1444_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_val_1421_);
lean_dec(v___x_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1444_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
switch(lean_obj_tag(v_val_1421_))
{
case 1:
{
lean_object* v___x_1426_; 
lean_dec_ref_known(v_val_1421_, 1);
lean_inc(v_inl_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_inl_1418_);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_inl_1418_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
case 2:
{
lean_object* v___x_1429_; 
lean_dec_ref_known(v_val_1421_, 1);
lean_inc(v_inl_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_inl_1418_);
v___x_1429_ = v___x_1423_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_inl_1418_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
case 3:
{
lean_object* v___x_1432_; 
lean_dec_ref_known(v_val_1421_, 1);
lean_inc(v_inl_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_inl_1418_);
v___x_1432_ = v___x_1423_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_inl_1418_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
case 4:
{
lean_object* v___x_1435_; 
lean_dec_ref_known(v_val_1421_, 1);
lean_inc(v_inl_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_inl_1418_);
v___x_1435_ = v___x_1423_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_inl_1418_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
case 6:
{
lean_object* v___x_1438_; 
lean_dec_ref_known(v_val_1421_, 1);
lean_inc(v_inl_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_inl_1418_);
v___x_1438_ = v___x_1423_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_inl_1418_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
case 9:
{
lean_object* v___x_1441_; 
lean_dec_ref_known(v_val_1421_, 1);
lean_inc(v_inl_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_inl_1418_);
v___x_1441_ = v___x_1423_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_inl_1418_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
default: 
{
lean_object* v___x_1443_; 
lean_del_object(v___x_1423_);
lean_dec(v_val_1421_);
v___x_1443_ = lean_box(0);
return v___x_1443_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object* v_inls_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_inls_1445_);
lean_dec_ref(v_inls_1445_);
return v_res_1446_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = 41;
v___x_1448_ = lean_box_uint32(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
v___x_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = 93;
v___x_1452_ = lean_box_uint32(v___x_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object* v_a_1455_){
_start:
{
if (lean_obj_tag(v_a_1455_) == 0)
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_a_1458_);
lean_dec_ref(v_a_1458_);
return v_res_1459_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = 95;
v___x_1461_ = lean_box_uint32(v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = 42;
v___x_1465_ = lean_box_uint32(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = 96;
v___x_1469_ = lean_box_uint32(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object* v_inl_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Doc_InlineView_of(v_inl_1472_);
if (lean_obj_tag(v___x_1473_) == 1)
{
lean_object* v_val_1474_; 
v_val_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1474_);
lean_dec_ref_known(v___x_1473_, 1);
switch(lean_obj_tag(v_val_1474_))
{
case 1:
{
lean_object* v___x_1475_; 
lean_dec_ref_known(v_val_1474_, 1);
v___x_1475_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1475_;
}
case 2:
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v_val_1474_, 1);
v___x_1476_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1476_;
}
case 3:
{
lean_object* v___x_1477_; 
lean_dec_ref_known(v_val_1474_, 1);
v___x_1477_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1477_;
}
case 4:
{
lean_object* v___x_1478_; 
lean_dec_ref_known(v_val_1474_, 1);
v___x_1478_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1478_;
}
case 5:
{
lean_object* v_view_1479_; lean_object* v_target_1480_; lean_object* v___x_1481_; 
v_view_1479_ = lean_ctor_get(v_val_1474_, 0);
lean_inc_ref(v_view_1479_);
lean_dec_ref_known(v_val_1474_, 1);
v_target_1480_ = lean_ctor_get(v_view_1479_, 4);
lean_inc_ref(v_target_1480_);
lean_dec_ref(v_view_1479_);
v___x_1481_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1480_);
lean_dec_ref(v_target_1480_);
return v___x_1481_;
}
case 6:
{
lean_object* v_view_1482_; lean_object* v_target_1483_; lean_object* v___x_1484_; 
v_view_1482_ = lean_ctor_get(v_val_1474_, 0);
lean_inc_ref(v_view_1482_);
lean_dec_ref_known(v_val_1474_, 1);
v_target_1483_ = lean_ctor_get(v_view_1482_, 4);
lean_inc_ref(v_target_1483_);
lean_dec_ref(v_view_1482_);
v___x_1484_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1483_);
lean_dec_ref(v_target_1483_);
return v___x_1484_;
}
case 7:
{
lean_object* v___x_1485_; 
lean_dec_ref_known(v_val_1474_, 1);
v___x_1485_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1485_;
}
case 9:
{
lean_object* v_view_1486_; lean_object* v_content_1487_; lean_object* v___x_1488_; 
v_view_1486_ = lean_ctor_get(v_val_1474_, 0);
lean_inc_ref(v_view_1486_);
lean_dec_ref_known(v_val_1474_, 1);
v_content_1487_ = lean_ctor_get(v_view_1486_, 6);
lean_inc_ref(v_content_1487_);
lean_dec_ref(v_view_1486_);
v___x_1488_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_1487_);
lean_dec_ref(v_content_1487_);
if (lean_obj_tag(v___x_1488_) == 1)
{
lean_object* v_val_1489_; 
v_val_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v_inl_1472_ = v_val_1489_;
goto _start;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v___x_1488_);
v___x_1491_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1491_;
}
}
default: 
{
lean_object* v___x_1492_; 
lean_dec(v_val_1474_);
v___x_1492_ = lean_box(0);
return v___x_1492_;
}
}
}
else
{
lean_object* v___x_1493_; 
lean_dec(v___x_1473_);
v___x_1493_ = lean_box(0);
return v___x_1493_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = 36;
v___x_1495_ = lean_box_uint32(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object* v_stx_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Doc_InlineView_of(v_stx_1498_);
if (lean_obj_tag(v___x_1499_) == 1)
{
lean_object* v_val_1500_; 
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1499_, 1);
switch(lean_obj_tag(v_val_1500_))
{
case 1:
{
lean_object* v___x_1501_; 
lean_dec_ref_known(v_val_1500_, 1);
v___x_1501_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1501_;
}
case 2:
{
lean_object* v___x_1502_; 
lean_dec_ref_known(v_val_1500_, 1);
v___x_1502_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1502_;
}
case 3:
{
lean_object* v___x_1503_; 
lean_dec_ref_known(v_val_1500_, 1);
v___x_1503_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1503_;
}
case 4:
{
lean_object* v___x_1504_; 
lean_dec_ref_known(v_val_1500_, 1);
v___x_1504_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0);
return v___x_1504_;
}
default: 
{
lean_object* v___x_1505_; 
lean_dec(v_val_1500_);
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
}
}
else
{
lean_object* v___x_1506_; 
lean_dec(v___x_1499_);
v___x_1506_ = lean_box(0);
return v___x_1506_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object* v_inl_1507_, lean_object* v_next_x3f_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1507_);
if (lean_obj_tag(v___x_1509_) == 1)
{
if (lean_obj_tag(v_next_x3f_1508_) == 0)
{
uint8_t v___x_1510_; 
lean_dec_ref_known(v___x_1509_, 1);
v___x_1510_ = 0;
return v___x_1510_;
}
else
{
lean_object* v_val_1511_; lean_object* v_val_1512_; lean_object* v___x_1513_; 
v_val_1511_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_val_1511_);
lean_dec_ref_known(v___x_1509_, 1);
v_val_1512_ = lean_ctor_get(v_next_x3f_1508_, 0);
lean_inc(v_val_1512_);
lean_dec_ref_known(v_next_x3f_1508_, 1);
v___x_1513_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1512_);
if (lean_obj_tag(v___x_1513_) == 1)
{
lean_object* v_val_1514_; uint32_t v___x_1515_; uint32_t v___x_1516_; uint8_t v___x_1517_; 
v_val_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1515_ = lean_unbox_uint32(v_val_1511_);
lean_dec(v_val_1511_);
v___x_1516_ = lean_unbox_uint32(v_val_1514_);
lean_dec(v_val_1514_);
v___x_1517_ = lean_uint32_dec_eq(v___x_1515_, v___x_1516_);
return v___x_1517_;
}
else
{
uint8_t v___x_1518_; 
lean_dec(v___x_1513_);
lean_dec(v_val_1511_);
v___x_1518_ = 0;
return v___x_1518_;
}
}
}
else
{
uint8_t v___x_1519_; 
lean_dec(v___x_1509_);
lean_dec(v_next_x3f_1508_);
v___x_1519_ = 0;
return v___x_1519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object* v_inl_1520_, lean_object* v_next_x3f_1521_){
_start:
{
uint8_t v_res_1522_; lean_object* v_r_1523_; 
v_res_1522_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_inl_1520_, v_next_x3f_1521_);
v_r_1523_ = lean_box(v_res_1522_);
return v_r_1523_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object* v_inl_1524_, lean_object* v_next_x3f_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1524_);
if (lean_obj_tag(v___x_1526_) == 1)
{
lean_object* v_val_1527_; uint32_t v___x_1528_; uint32_t v___x_1529_; uint8_t v___x_1530_; 
v_val_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = 96;
v___x_1529_ = lean_unbox_uint32(v_val_1527_);
lean_dec(v_val_1527_);
v___x_1530_ = lean_uint32_dec_eq(v___x_1529_, v___x_1528_);
if (v___x_1530_ == 0)
{
lean_dec(v_next_x3f_1525_);
return v___x_1530_;
}
else
{
if (lean_obj_tag(v_next_x3f_1525_) == 0)
{
uint8_t v___x_1531_; 
v___x_1531_ = 0;
return v___x_1531_;
}
else
{
lean_object* v_val_1532_; lean_object* v___x_1533_; 
v_val_1532_ = lean_ctor_get(v_next_x3f_1525_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v_next_x3f_1525_, 1);
v___x_1533_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1532_);
if (lean_obj_tag(v___x_1533_) == 1)
{
lean_object* v_val_1534_; uint32_t v___x_1535_; uint8_t v___x_1536_; 
v_val_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = lean_unbox_uint32(v_val_1534_);
lean_dec(v_val_1534_);
v___x_1536_ = lean_uint32_dec_eq(v___x_1535_, v___x_1528_);
return v___x_1536_;
}
else
{
uint8_t v___x_1537_; 
lean_dec(v___x_1533_);
v___x_1537_ = 0;
return v___x_1537_;
}
}
}
}
else
{
uint8_t v___x_1538_; 
lean_dec(v___x_1526_);
lean_dec(v_next_x3f_1525_);
v___x_1538_ = 0;
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object* v_inl_1539_, lean_object* v_next_x3f_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v_inl_1539_, v_next_x3f_1540_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object* v_inls_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_array_get_size(v_inls_1543_);
v___x_1546_ = lean_nat_dec_lt(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_array_fget_borrowed(v_inls_1543_, v___x_1544_);
lean_inc(v___x_1547_);
v___x_1548_ = l_Lean_Doc_TextView_of(v___x_1547_);
if (lean_obj_tag(v___x_1548_) == 1)
{
lean_object* v_val_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_val_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = l_Lean_Doc_TextView_getVersoText(v_val_1549_);
lean_dec(v_val_1549_);
v___x_1551_ = lean_string_utf8_byte_size(v___x_1550_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v___x_1553_ = lean_nat_dec_le(v___x_1552_, v___x_1551_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v___x_1550_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1555_ = lean_string_memcmp(v___x_1550_, v___x_1554_, v___x_1544_, v___x_1544_, v___x_1552_);
lean_dec_ref(v___x_1550_);
return v___x_1555_;
}
}
else
{
uint8_t v___x_1556_; 
lean_dec(v___x_1548_);
v___x_1556_ = 0;
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object* v_inls_1557_){
_start:
{
uint8_t v_res_1558_; lean_object* v_r_1559_; 
v_res_1558_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_inls_1557_);
lean_dec_ref(v_inls_1557_);
v_r_1559_ = lean_box(v_res_1558_);
return v_r_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object* v_x_1563_, lean_object* v_a_1564_){
_start:
{
if (lean_obj_tag(v_x_1563_) == 0)
{
lean_object* v_url_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_snd_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_snd_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_url_1565_ = lean_ctor_get(v_x_1563_, 2);
v___x_1566_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_1567_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1566_, v_a_1564_);
v_snd_1568_ = lean_ctor_get(v___x_1567_, 1);
lean_inc(v_snd_1568_);
lean_dec_ref(v___x_1567_);
v___x_1569_ = l_Lean_TSyntax_getVersoLinkUrl(v_url_1565_);
v___x_1570_ = l_Lean_Doc_escapeVersoLinkUrl(v___x_1569_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1570_, v_snd_1568_);
lean_dec_ref(v___x_1570_);
v_snd_1572_ = lean_ctor_get(v___x_1571_, 1);
lean_inc(v_snd_1572_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_1574_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1573_, v_snd_1572_);
return v___x_1574_;
}
else
{
lean_object* v_name_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_snd_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_snd_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v_name_1575_ = lean_ctor_get(v_x_1563_, 2);
v___x_1576_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_1577_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1576_, v_a_1564_);
v_snd_1578_ = lean_ctor_get(v___x_1577_, 1);
lean_inc(v_snd_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l_Lean_TSyntax_getVersoRefName(v_name_1575_);
v___x_1580_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1579_, v_snd_1578_);
lean_dec_ref(v___x_1579_);
v_snd_1581_ = lean_ctor_get(v___x_1580_, 1);
lean_inc(v_snd_1581_);
lean_dec_ref(v___x_1580_);
v___x_1582_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_1583_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1582_, v_snd_1581_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object* v_x_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1584_, v_a_1585_);
lean_dec_ref(v_x_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object* v_x_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1587_, v_a_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object* v_x_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(v_x_1591_, v_a_1592_, v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_x_1591_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object* v_s_1595_, lean_object* v_pos_1596_){
_start:
{
lean_object* v_str_1597_; lean_object* v_startInclusive_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v_decide_1602_; 
v_str_1597_ = lean_ctor_get(v_s_1595_, 0);
v_startInclusive_1598_ = lean_ctor_get(v_s_1595_, 1);
v___x_1599_ = lean_nat_add(v_startInclusive_1598_, v_pos_1596_);
v___x_1600_ = lean_nat_sub(v___x_1599_, v_startInclusive_1598_);
v___x_1601_ = lean_unsigned_to_nat(0u);
v_decide_1602_ = lean_nat_dec_eq(v___x_1600_, v___x_1601_);
if (v_decide_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint32_t v___x_1608_; uint32_t v___x_1609_; uint8_t v___x_1610_; 
lean_inc(v_startInclusive_1598_);
lean_inc_ref(v_str_1597_);
v___x_1603_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1603_, 0, v_str_1597_);
lean_ctor_set(v___x_1603_, 1, v_startInclusive_1598_);
lean_ctor_set(v___x_1603_, 2, v___x_1599_);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_sub(v___x_1600_, v___x_1604_);
lean_dec(v___x_1600_);
v___x_1606_ = l_String_Slice_posLE(v___x_1603_, v___x_1605_);
lean_dec_ref_known(v___x_1603_, 3);
v___x_1607_ = lean_nat_add(v_startInclusive_1598_, v___x_1606_);
v___x_1608_ = lean_string_utf8_get_fast(v_str_1597_, v___x_1607_);
lean_dec(v___x_1607_);
v___x_1609_ = 32;
v___x_1610_ = lean_uint32_dec_eq(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_dec(v___x_1606_);
return v_pos_1596_;
}
else
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_nat_add(v___x_1606_, v___x_1604_);
v___x_1612_ = lean_nat_dec_le(v___x_1611_, v_pos_1596_);
lean_dec(v___x_1611_);
if (v___x_1612_ == 0)
{
lean_dec(v___x_1606_);
return v_pos_1596_;
}
else
{
lean_dec(v_pos_1596_);
v_pos_1596_ = v___x_1606_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1600_);
lean_dec(v___x_1599_);
return v_pos_1596_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object* v_s_1614_, lean_object* v_pos_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v_s_1614_, v_pos_1615_);
lean_dec_ref(v_s_1614_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object* v_marker_1617_, lean_object* v_contents_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_alone_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_string_utf8_byte_size(v_marker_1617_);
lean_inc_ref(v_marker_1617_);
v___x_1622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1622_, 0, v_marker_1617_);
lean_ctor_set(v___x_1622_, 1, v___x_1620_);
lean_ctor_set(v___x_1622_, 2, v___x_1621_);
v___x_1623_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v___x_1622_, v___x_1621_);
lean_dec_ref_known(v___x_1622_, 3);
v_alone_1624_ = lean_string_utf8_extract_fast(v_marker_1617_, v___x_1620_, v___x_1623_);
lean_dec(v___x_1623_);
v___x_1625_ = lean_array_get_size(v_contents_1618_);
v___x_1626_ = lean_nat_dec_lt(v___x_1620_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_dec_ref(v_marker_1617_);
v___x_1627_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_alone_1624_, v_a_1619_);
lean_dec_ref(v_alone_1624_);
return v___x_1627_;
}
else
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = lean_array_fget_borrowed(v_contents_1618_, v___x_1620_);
lean_inc(v___x_1628_);
v___x_1629_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_dec_ref(v_alone_1624_);
v___x_1630_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_marker_1617_, v_a_1619_);
lean_dec_ref(v_marker_1617_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v_marker_1617_);
v___x_1631_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_1632_ = lean_string_append(v_alone_1624_, v___x_1631_);
v___x_1633_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1632_, v_a_1619_);
lean_dec_ref(v___x_1632_);
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object* v_marker_1634_, lean_object* v_contents_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1634_, v_contents_1635_, v_a_1636_);
lean_dec_ref(v_contents_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object* v_marker_1638_, lean_object* v_contents_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1638_, v_contents_1639_, v_a_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object* v_marker_1643_, lean_object* v_contents_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(v_marker_1643_, v_contents_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_contents_1644_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object* v_as_1648_, size_t v_i_1649_, size_t v_stop_1650_, lean_object* v_b_1651_){
_start:
{
lean_object* v___y_1653_; uint8_t v___x_1657_; 
v___x_1657_ = lean_usize_dec_eq(v_i_1649_, v_stop_1650_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = lean_array_uget_borrowed(v_as_1648_, v_i_1649_);
lean_inc(v___x_1658_);
v___x_1659_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_inc(v___x_1658_);
v___x_1660_ = lean_array_push(v_b_1651_, v___x_1658_);
v___y_1653_ = v___x_1660_;
goto v___jp_1652_;
}
else
{
v___y_1653_ = v_b_1651_;
goto v___jp_1652_;
}
}
else
{
return v_b_1651_;
}
v___jp_1652_:
{
size_t v___x_1654_; size_t v___x_1655_; 
v___x_1654_ = ((size_t)1ULL);
v___x_1655_ = lean_usize_add(v_i_1649_, v___x_1654_);
v_i_1649_ = v___x_1655_;
v_b_1651_ = v___y_1653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object* v_as_1661_, lean_object* v_i_1662_, lean_object* v_stop_1663_, lean_object* v_b_1664_){
_start:
{
size_t v_i_boxed_1665_; size_t v_stop_boxed_1666_; lean_object* v_res_1667_; 
v_i_boxed_1665_ = lean_unbox_usize(v_i_1662_);
lean_dec(v_i_1662_);
v_stop_boxed_1666_ = lean_unbox_usize(v_stop_1663_);
lean_dec(v_stop_1663_);
v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_as_1661_, v_i_boxed_1665_, v_stop_boxed_1666_, v_b_1664_);
lean_dec_ref(v_as_1661_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t v_sz_1668_, size_t v_i_1669_, lean_object* v_bs_1670_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_usize_dec_lt(v_i_1669_, v_sz_1668_);
if (v___x_1671_ == 0)
{
return v_bs_1670_;
}
else
{
lean_object* v_v_1672_; lean_object* v___x_1673_; lean_object* v_bs_x27_1674_; size_t v___x_1675_; size_t v___x_1676_; lean_object* v___x_1677_; 
v_v_1672_ = lean_array_uget(v_bs_1670_, v_i_1669_);
v___x_1673_ = lean_unsigned_to_nat(0u);
v_bs_x27_1674_ = lean_array_uset(v_bs_1670_, v_i_1669_, v___x_1673_);
v___x_1675_ = ((size_t)1ULL);
v___x_1676_ = lean_usize_add(v_i_1669_, v___x_1675_);
v___x_1677_ = lean_array_uset(v_bs_x27_1674_, v_i_1669_, v_v_1672_);
v_i_1669_ = v___x_1676_;
v_bs_1670_ = v___x_1677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_sz_1679_, lean_object* v_i_1680_, lean_object* v_bs_1681_){
_start:
{
size_t v_sz_boxed_1682_; size_t v_i_boxed_1683_; lean_object* v_res_1684_; 
v_sz_boxed_1682_ = lean_unbox_usize(v_sz_1679_);
lean_dec(v_sz_1679_);
v_i_boxed_1683_ = lean_unbox_usize(v_i_1680_);
lean_dec(v_i_1680_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_boxed_1682_, v_i_boxed_1683_, v_bs_1681_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object* v_x_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v_zero_1687_; uint8_t v_isZero_1688_; 
v_zero_1687_ = lean_unsigned_to_nat(0u);
v_isZero_1688_ = lean_nat_dec_eq(v_x_1685_, v_zero_1687_);
if (v_isZero_1688_ == 1)
{
lean_dec(v_x_1685_);
return v_x_1686_;
}
else
{
uint32_t v___x_1689_; lean_object* v_one_1690_; lean_object* v_n_1691_; lean_object* v___x_1692_; 
v___x_1689_ = 35;
v_one_1690_ = lean_unsigned_to_nat(1u);
v_n_1691_ = lean_nat_sub(v_x_1685_, v_one_1690_);
lean_dec(v_x_1685_);
v___x_1692_ = lean_string_push(v_x_1686_, v___x_1689_);
v_x_1685_ = v_n_1691_;
v_x_1686_ = v___x_1692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_zero_1696_; uint8_t v_isZero_1697_; 
v_zero_1696_ = lean_unsigned_to_nat(0u);
v_isZero_1697_ = lean_nat_dec_eq(v_x_1694_, v_zero_1696_);
if (v_isZero_1697_ == 1)
{
lean_dec(v_x_1694_);
return v_x_1695_;
}
else
{
uint32_t v___x_1698_; lean_object* v_one_1699_; lean_object* v_n_1700_; lean_object* v___x_1701_; 
v___x_1698_ = 58;
v_one_1699_ = lean_unsigned_to_nat(1u);
v_n_1700_ = lean_nat_sub(v_x_1694_, v_one_1699_);
lean_dec(v_x_1694_);
v___x_1701_ = lean_string_push(v_x_1695_, v___x_1698_);
v_x_1694_ = v_n_1700_;
v_x_1695_ = v___x_1701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t v_char_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_){
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
lean_object* v_one_1708_; lean_object* v_n_1709_; lean_object* v___x_1710_; 
v_one_1708_ = lean_unsigned_to_nat(1u);
v_n_1709_ = lean_nat_sub(v_x_1704_, v_one_1708_);
lean_dec(v_x_1704_);
v___x_1710_ = lean_string_push(v_x_1705_, v_char_1703_);
v_x_1704_ = v_n_1709_;
v_x_1705_ = v___x_1710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object* v_char_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
uint32_t v_char_boxed_1715_; lean_object* v_res_1716_; 
v_char_boxed_1715_ = lean_unbox_uint32(v_char_1712_);
lean_dec(v_char_1712_);
v_res_1716_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_boxed_1715_, v_x_1713_, v_x_1714_);
return v_res_1716_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1717_) == 0)
{
if (lean_obj_tag(v_x_1718_) == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = 1;
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = 0;
return v___x_1720_;
}
}
else
{
if (lean_obj_tag(v_x_1718_) == 0)
{
uint8_t v___x_1721_; 
v___x_1721_ = 0;
return v___x_1721_;
}
else
{
lean_object* v_val_1722_; lean_object* v_val_1723_; uint32_t v___x_1724_; uint32_t v___x_1725_; uint8_t v___x_1726_; 
v_val_1722_ = lean_ctor_get(v_x_1717_, 0);
v_val_1723_ = lean_ctor_get(v_x_1718_, 0);
v___x_1724_ = lean_unbox_uint32(v_val_1722_);
v___x_1725_ = lean_unbox_uint32(v_val_1723_);
v___x_1726_ = lean_uint32_dec_eq(v___x_1724_, v___x_1725_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
uint8_t v_res_1729_; lean_object* v_r_1730_; 
v_res_1729_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v_x_1727_, v_x_1728_);
lean_dec(v_x_1728_);
lean_dec(v_x_1727_);
v_r_1730_ = lean_box(v_res_1729_);
return v_r_1730_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg(){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0));
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___boxed(lean_object* v___dummy_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v_res_1736_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t v___x_1737_, lean_object* v_as_1738_, size_t v_i_1739_, size_t v_stop_1740_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_eq(v_i_1739_, v_stop_1740_);
if (v___x_1741_ == 0)
{
uint8_t v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1742_ = 1;
v___x_1743_ = lean_array_uget_borrowed(v_as_1738_, v_i_1739_);
lean_inc(v___x_1743_);
v___x_1744_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1743_);
if (v___x_1744_ == 0)
{
return v___x_1742_;
}
else
{
if (v___x_1737_ == 0)
{
size_t v___x_1745_; size_t v___x_1746_; 
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1739_, v___x_1745_);
v_i_1739_ = v___x_1746_;
goto _start;
}
else
{
return v___x_1742_;
}
}
}
else
{
uint8_t v___x_1748_; 
v___x_1748_ = 0;
return v___x_1748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v___x_1749_, lean_object* v_as_1750_, lean_object* v_i_1751_, lean_object* v_stop_1752_){
_start:
{
uint8_t v___x_61936__boxed_1753_; size_t v_i_boxed_1754_; size_t v_stop_boxed_1755_; uint8_t v_res_1756_; lean_object* v_r_1757_; 
v___x_61936__boxed_1753_ = lean_unbox(v___x_1749_);
v_i_boxed_1754_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_stop_boxed_1755_ = lean_unbox_usize(v_stop_1752_);
lean_dec(v_stop_1752_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_61936__boxed_1753_, v_as_1750_, v_i_boxed_1754_, v_stop_boxed_1755_);
lean_dec_ref(v_as_1750_);
v_r_1757_ = lean_box(v_res_1756_);
return v_r_1757_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t v___x_1758_, uint8_t v___x_1759_, lean_object* v_as_1760_, size_t v_i_1761_, size_t v_stop_1762_){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_usize_dec_eq(v_i_1761_, v_stop_1762_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; uint8_t v___y_1766_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1764_ = 1;
v___x_1770_ = lean_array_uget_borrowed(v_as_1760_, v_i_1761_);
lean_inc(v___x_1770_);
v___x_1771_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v___x_1770_);
if (v___x_1771_ == 0)
{
v___y_1766_ = v___x_1758_;
goto v___jp_1765_;
}
else
{
v___y_1766_ = v___x_1759_;
goto v___jp_1765_;
}
v___jp_1765_:
{
if (v___y_1766_ == 0)
{
size_t v___x_1767_; size_t v___x_1768_; 
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1761_, v___x_1767_);
v_i_1761_ = v___x_1768_;
goto _start;
}
else
{
return v___x_1764_;
}
}
}
else
{
uint8_t v___x_1772_; 
v___x_1772_ = 0;
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v___x_1773_, lean_object* v___x_1774_, lean_object* v_as_1775_, lean_object* v_i_1776_, lean_object* v_stop_1777_){
_start:
{
uint8_t v___x_61955__boxed_1778_; uint8_t v___x_61956__boxed_1779_; size_t v_i_boxed_1780_; size_t v_stop_boxed_1781_; uint8_t v_res_1782_; lean_object* v_r_1783_; 
v___x_61955__boxed_1778_ = lean_unbox(v___x_1773_);
v___x_61956__boxed_1779_ = lean_unbox(v___x_1774_);
v_i_boxed_1780_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_stop_boxed_1781_ = lean_unbox_usize(v_stop_1777_);
lean_dec(v_stop_1777_);
v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_61955__boxed_1778_, v___x_61956__boxed_1779_, v_as_1775_, v_i_boxed_1780_, v_stop_boxed_1781_);
lean_dec_ref(v_as_1775_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___x_1786_, lean_object* v___x_1787_, lean_object* v_a_1788_, lean_object* v_b_1789_){
_start:
{
if (lean_obj_tag(v_a_1788_) == 0)
{
lean_object* v_currPos_1790_; lean_object* v_searcher_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1824_; 
v_currPos_1790_ = lean_ctor_get(v_a_1788_, 0);
v_searcher_1791_ = lean_ctor_get(v_a_1788_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1793_ = v_a_1788_;
v_isShared_1794_ = v_isSharedCheck_1824_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_searcher_1791_);
lean_inc(v_currPos_1790_);
lean_dec(v_a_1788_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1824_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v_it_1797_; lean_object* v_startInclusive_1798_; lean_object* v_endExclusive_1799_; uint8_t v_decide_1805_; 
v___x_1795_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_decide_1805_ = lean_nat_dec_eq(v_searcher_1791_, v___x_1787_);
if (v_decide_1805_ == 0)
{
uint32_t v___x_1806_; uint32_t v___x_1807_; uint8_t v___x_1808_; 
v___x_1806_ = 10;
v___x_1807_ = lean_string_utf8_get_fast(v___y_1785_, v_searcher_1791_);
v___x_1808_ = lean_uint32_dec_eq(v___x_1807_, v___x_1806_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_string_utf8_next_fast(v___y_1785_, v_searcher_1791_);
lean_dec(v_searcher_1791_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1809_);
v___x_1811_ = v___x_1793_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_currPos_1790_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v_a_1788_ = v___x_1811_;
goto _start;
}
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v_slice_1817_; lean_object* v_nextIt_1819_; 
v___x_1814_ = lean_string_utf8_next_fast(v___y_1785_, v_searcher_1791_);
v___x_1815_ = lean_nat_sub(v___x_1814_, v_searcher_1791_);
v___x_1816_ = lean_nat_add(v_searcher_1791_, v___x_1815_);
lean_dec(v___x_1815_);
v_slice_1817_ = l_String_Slice_subslice_x21(v___x_1786_, v_currPos_1790_, v_searcher_1791_);
lean_inc(v___x_1816_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1816_);
lean_ctor_set(v___x_1793_, 0, v___x_1816_);
v_nextIt_1819_ = v___x_1793_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v___x_1816_);
v_nextIt_1819_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v_startInclusive_1820_; lean_object* v_endExclusive_1821_; 
v_startInclusive_1820_ = lean_ctor_get(v_slice_1817_, 0);
lean_inc(v_startInclusive_1820_);
v_endExclusive_1821_ = lean_ctor_get(v_slice_1817_, 1);
lean_inc(v_endExclusive_1821_);
lean_dec_ref(v_slice_1817_);
v_it_1797_ = v_nextIt_1819_;
v_startInclusive_1798_ = v_startInclusive_1820_;
v_endExclusive_1799_ = v_endExclusive_1821_;
goto v___jp_1796_;
}
}
}
else
{
lean_object* v___x_1823_; 
lean_del_object(v___x_1793_);
lean_dec(v_searcher_1791_);
v___x_1823_ = lean_box(1);
lean_inc(v___x_1787_);
v_it_1797_ = v___x_1823_;
v_startInclusive_1798_ = v_currPos_1790_;
v_endExclusive_1799_ = v___x_1787_;
goto v___jp_1796_;
}
v___jp_1796_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_inc(v___y_1784_);
v___x_1800_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v___y_1784_, v___x_1795_);
v___x_1801_ = lean_string_utf8_extract_fast(v___y_1785_, v_startInclusive_1798_, v_endExclusive_1799_);
lean_dec(v_endExclusive_1799_);
lean_dec(v_startInclusive_1798_);
v___x_1802_ = lean_string_append(v___x_1800_, v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = lean_array_push(v_b_1789_, v___x_1802_);
v_a_1788_ = v_it_1797_;
v_b_1789_ = v___x_1803_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1787_);
return v_b_1789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v_a_1829_, lean_object* v_b_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_1825_, v___y_1826_, v___x_1827_, v___x_1828_, v_a_1829_, v_b_1830_);
lean_dec_ref(v___x_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object* v___x_1832_, lean_object* v___x_1833_, lean_object* v_____r_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1837_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v___x_1832_);
v___x_1838_ = lean_box(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1833_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v___y_1836_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object* v___x_1842_, lean_object* v___x_1843_, lean_object* v_____r_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1842_, v___x_1843_, v_____r_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1845_);
return v_res_1847_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0(void){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object* v_upperBound_1855_, lean_object* v___y_1856_, lean_object* v_a_1857_, lean_object* v_b_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___y_1862_; uint8_t v___x_1879_; 
v___x_1879_ = lean_nat_dec_lt(v_a_1857_, v_upperBound_1855_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec(v_a_1857_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v_b_1858_);
lean_ctor_set(v___x_1880_, 1, v___y_1860_);
return v___x_1880_;
}
else
{
lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___y_1886_; lean_object* v___y_1890_; uint8_t v___y_1891_; lean_object* v___y_1906_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_fst_1881_ = lean_ctor_get(v_b_1858_, 0);
lean_inc(v_fst_1881_);
v_snd_1882_ = lean_ctor_get(v_b_1858_, 1);
lean_inc(v_snd_1882_);
lean_dec_ref(v_b_1858_);
v___x_1883_ = lean_array_fget_borrowed(v___y_1856_, v_a_1857_);
lean_inc(v___x_1883_);
v___x_1884_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_snd_1882_, v___x_1883_);
lean_dec(v_snd_1882_);
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = lean_nat_add(v_a_1857_, v___x_1910_);
v___x_1912_ = lean_array_get_size(v___y_1856_);
v___x_1913_ = lean_nat_dec_lt(v___x_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v___y_1906_ = v___x_1914_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_array_fget_borrowed(v___y_1856_, v___x_1911_);
lean_dec(v___x_1911_);
lean_inc(v___x_1915_);
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
v___y_1906_ = v___x_1916_;
goto v___jp_1905_;
}
v___jp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_box(0);
lean_inc(v___x_1883_);
v___x_1888_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1883_, v___x_1884_, v___x_1887_, v___y_1859_, v___y_1886_);
v___y_1862_ = v___x_1888_;
goto v___jp_1861_;
}
v___jp_1889_:
{
uint8_t v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_unbox(v_fst_1881_);
lean_dec(v_fst_1881_);
lean_inc(v___y_1890_);
lean_inc(v___x_1883_);
v___x_1893_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1883_, v___y_1890_, v___x_1892_, v___y_1891_, v___y_1859_, v___y_1860_);
if (lean_obj_tag(v___y_1890_) == 1)
{
lean_object* v_snd_1894_; lean_object* v___x_1895_; 
v_snd_1894_ = lean_ctor_get(v___x_1893_, 1);
lean_inc(v_snd_1894_);
lean_dec_ref(v___x_1893_);
lean_inc(v___x_1883_);
v___x_1895_ = l_Lean_Doc_RoleView_of(v___x_1883_);
if (lean_obj_tag(v___x_1895_) == 1)
{
lean_dec_ref_known(v___x_1895_, 1);
lean_dec_ref_known(v___y_1890_, 1);
v___y_1886_ = v_snd_1894_;
goto v___jp_1885_;
}
else
{
uint8_t v___x_1896_; 
lean_dec(v___x_1895_);
lean_inc(v___x_1883_);
v___x_1896_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v___x_1883_, v___y_1890_);
if (v___x_1896_ == 0)
{
v___y_1886_ = v_snd_1894_;
goto v___jp_1885_;
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v_fst_1899_; lean_object* v_snd_1900_; lean_object* v___x_1901_; 
v___x_1897_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1898_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1897_, v_snd_1894_);
v_fst_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_fst_1899_);
v_snd_1900_ = lean_ctor_get(v___x_1898_, 1);
lean_inc(v_snd_1900_);
lean_dec_ref(v___x_1898_);
lean_inc(v___x_1883_);
v___x_1901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1883_, v___x_1884_, v_fst_1899_, v___y_1859_, v_snd_1900_);
v___y_1862_ = v___x_1901_;
goto v___jp_1861_;
}
}
}
else
{
lean_object* v_snd_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec(v___y_1890_);
v_snd_1902_ = lean_ctor_get(v___x_1893_, 1);
lean_inc(v_snd_1902_);
lean_dec_ref(v___x_1893_);
v___x_1903_ = lean_box(0);
lean_inc(v___x_1883_);
v___x_1904_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1883_, v___x_1884_, v___x_1903_, v___y_1859_, v_snd_1902_);
v___y_1862_ = v___x_1904_;
goto v___jp_1861_;
}
}
v___jp_1905_:
{
if (lean_obj_tag(v___x_1884_) == 0)
{
uint8_t v___x_1907_; 
v___x_1907_ = 0;
v___y_1890_ = v___y_1906_;
v___y_1891_ = v___x_1907_;
goto v___jp_1889_;
}
else
{
lean_object* v_val_1908_; uint8_t v_alternate_1909_; 
v_val_1908_ = lean_ctor_get(v___x_1884_, 0);
v_alternate_1909_ = lean_ctor_get_uint8(v_val_1908_, 1);
v___y_1890_ = v___y_1906_;
v___y_1891_ = v_alternate_1909_;
goto v___jp_1889_;
}
}
}
v___jp_1861_:
{
lean_object* v_fst_1863_; 
v_fst_1863_ = lean_ctor_get(v___y_1862_, 0);
lean_inc(v_fst_1863_);
if (lean_obj_tag(v_fst_1863_) == 0)
{
lean_object* v_snd_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_a_1857_);
v_snd_1864_ = lean_ctor_get(v___y_1862_, 1);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___y_1862_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v___y_1862_, 0);
lean_dec(v_unused_1873_);
v___x_1866_ = v___y_1862_;
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_snd_1864_);
lean_dec(v___y_1862_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1872_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v_a_1868_; lean_object* v___x_1870_; 
v_a_1868_ = lean_ctor_get(v_fst_1863_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v_fst_1863_, 1);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v_a_1868_);
v___x_1870_ = v___x_1866_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1868_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_snd_1864_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
else
{
lean_object* v_snd_1874_; lean_object* v_a_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_snd_1874_ = lean_ctor_get(v___y_1862_, 1);
lean_inc(v_snd_1874_);
lean_dec_ref(v___y_1862_);
v_a_1875_ = lean_ctor_get(v_fst_1863_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v_fst_1863_, 1);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = lean_nat_add(v_a_1857_, v___x_1876_);
lean_dec(v_a_1857_);
v_a_1857_ = v___x_1877_;
v_b_1858_ = v_a_1875_;
v___y_1860_ = v_snd_1874_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object* v_stxs_1919_, uint8_t v_lineStart_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___y_1925_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1941_ = lean_array_get_size(v_stxs_1919_);
v___x_1942_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0));
v___x_1943_ = lean_nat_dec_lt(v___x_1923_, v___x_1941_);
if (v___x_1943_ == 0)
{
v___y_1925_ = v___x_1942_;
goto v___jp_1924_;
}
else
{
size_t v___x_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = ((size_t)0ULL);
v___x_1945_ = lean_usize_of_nat(v___x_1941_);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1919_, v___x_1944_, v___x_1945_, v___x_1942_);
v___y_1925_ = v___x_1946_;
goto v___jp_1924_;
}
v___jp_1924_:
{
lean_object* v___x_1926_; lean_object* v_prev_x3f_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v_snd_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1939_; 
v___x_1926_ = lean_array_get_size(v___y_1925_);
v_prev_x3f_1927_ = lean_box(0);
v___x_1928_ = lean_box(v_lineStart_1920_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1928_);
lean_ctor_set(v___x_1929_, 1, v_prev_x3f_1927_);
v___x_1930_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v___x_1926_, v___y_1925_, v___x_1923_, v___x_1929_, v_a_1921_, v_a_1922_);
lean_dec_ref(v___y_1925_);
v_snd_1931_ = lean_ctor_get(v___x_1930_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1930_, 0);
lean_dec(v_unused_1940_);
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_snd_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_box(0);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_snd_1931_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t v_char_1947_, lean_object* v_inls_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_delim_1953_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___x_1964_; lean_object* v_snd_1965_; lean_object* v___y_1967_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1951_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_1952_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_1947_, v_inls_1948_);
v_delim_1953_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_1947_, v___x_1952_, v___x_1951_);
v___x_1964_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1953_, v_a_1950_);
v_snd_1965_ = lean_ctor_get(v___x_1964_, 1);
lean_inc(v_snd_1965_);
lean_dec_ref(v___x_1964_);
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_array_get_size(v_inls_1948_);
v___x_1976_ = lean_nat_dec_lt(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
v___x_1977_ = lean_box(0);
v___y_1967_ = v___x_1977_;
goto v___jp_1966_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_array_fget_borrowed(v_inls_1948_, v___x_1974_);
lean_inc(v___x_1978_);
v___x_1979_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v___x_1978_);
v___y_1967_ = v___x_1979_;
goto v___jp_1966_;
}
v___jp_1954_:
{
size_t v_sz_1957_; size_t v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v_snd_1962_; lean_object* v___x_1963_; 
v_sz_1957_ = lean_array_size(v_inls_1948_);
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_1957_, v___x_1958_, v_inls_1948_);
v___x_1960_ = 0;
v___x_1961_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_1959_, v___x_1960_, v___y_1955_, v___y_1956_);
lean_dec_ref(v___x_1959_);
v_snd_1962_ = lean_ctor_get(v___x_1961_, 1);
lean_inc(v_snd_1962_);
lean_dec_ref(v___x_1961_);
v___x_1963_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1953_, v_snd_1962_);
lean_dec_ref(v_delim_1953_);
return v___x_1963_;
}
v___jp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1968_ = lean_box_uint32(v_char_1947_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
v___x_1970_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v___y_1967_, v___x_1969_);
lean_dec_ref_known(v___x_1969_, 1);
lean_dec(v___y_1967_);
if (v___x_1970_ == 0)
{
v___y_1955_ = v_a_1949_;
v___y_1956_ = v_snd_1965_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_snd_1973_; 
v___x_1971_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1972_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1971_, v_snd_1965_);
v_snd_1973_ = lean_ctor_get(v___x_1972_, 1);
lean_inc(v_snd_1973_);
lean_dec_ref(v___x_1972_);
v___y_1955_ = v_a_1949_;
v___y_1956_ = v_snd_1973_;
goto v___jp_1954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v___y_1986_, uint8_t v___x_1987_, lean_object* v_as_1988_, size_t v_sz_1989_, size_t v_i_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_usize_dec_lt(v_i_1990_, v_sz_1989_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
lean_dec_ref(v___y_1986_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v_b_1991_);
lean_ctor_set(v___x_1995_, 1, v___y_1993_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; lean_object* v_snd_1997_; lean_object* v_a_1998_; lean_object* v_contents_1999_; lean_object* v___x_2000_; lean_object* v_snd_2001_; size_t v_sz_2002_; size_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_snd_2008_; lean_object* v___x_2009_; lean_object* v_snd_2010_; lean_object* v___x_2011_; size_t v___x_2012_; size_t v___x_2013_; 
v___x_1996_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_1992_, v___y_1993_);
v_snd_1997_ = lean_ctor_get(v___x_1996_, 1);
lean_inc(v_snd_1997_);
lean_dec_ref(v___x_1996_);
v_a_1998_ = lean_array_uget_borrowed(v_as_1988_, v_i_1990_);
v_contents_1999_ = lean_ctor_get(v_a_1998_, 2);
lean_inc_ref(v___y_1986_);
v___x_2000_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_1986_, v_contents_1999_, v_snd_1997_);
v_snd_2001_ = lean_ctor_get(v___x_2000_, 1);
lean_inc(v_snd_2001_);
lean_dec_ref(v___x_2000_);
v_sz_2002_ = lean_array_size(v_contents_1999_);
v___x_2003_ = ((size_t)0ULL);
lean_inc_ref(v_contents_1999_);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2002_, v___x_2003_, v_contents_1999_);
v___x_2005_ = lean_string_length(v___y_1986_);
v___x_2006_ = lean_nat_add(v___y_1992_, v___x_2005_);
v___x_2007_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2004_, v___x_1987_, v___x_2006_, v_snd_2001_);
lean_dec(v___x_2006_);
lean_dec_ref(v___x_2004_);
v_snd_2008_ = lean_ctor_get(v___x_2007_, 1);
lean_inc(v_snd_2008_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2008_);
v_snd_2010_ = lean_ctor_get(v___x_2009_, 1);
lean_inc(v_snd_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = lean_box(0);
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_1990_, v___x_2012_);
v_i_1990_ = v___x_2013_;
v_b_1991_ = v___x_2011_;
v___y_1993_ = v_snd_2010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t v___x_2018_, uint8_t v_alternate_2019_, lean_object* v_as_2020_, size_t v_sz_2021_, size_t v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_usize_dec_lt(v_i_2022_, v_sz_2021_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_b_2023_);
lean_ctor_set(v___x_2027_, 1, v___y_2025_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v_snd_2029_; lean_object* v_a_2030_; lean_object* v___y_2032_; 
v___x_2028_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2024_, v___y_2025_);
v_snd_2029_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_snd_2029_);
lean_dec_ref(v___x_2028_);
v_a_2030_ = lean_array_uget_borrowed(v_as_2020_, v_i_2022_);
if (v_alternate_2019_ == 0)
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_inc(v_b_2023_);
v___x_2050_ = l_Nat_reprFast(v_b_2023_);
v___x_2051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0));
v___x_2052_ = lean_string_append(v___x_2050_, v___x_2051_);
v___y_2032_ = v___x_2052_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_inc(v_b_2023_);
v___x_2053_ = l_Nat_reprFast(v_b_2023_);
v___x_2054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1));
v___x_2055_ = lean_string_append(v___x_2053_, v___x_2054_);
v___y_2032_ = v___x_2055_;
goto v___jp_2031_;
}
v___jp_2031_:
{
lean_object* v_contents_2033_; lean_object* v___x_2034_; lean_object* v_snd_2035_; size_t v_sz_2036_; size_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v_snd_2042_; lean_object* v___x_2043_; lean_object* v_snd_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; size_t v___x_2047_; size_t v___x_2048_; 
v_contents_2033_ = lean_ctor_get(v_a_2030_, 2);
lean_inc_ref(v___y_2032_);
v___x_2034_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2032_, v_contents_2033_, v_snd_2029_);
v_snd_2035_ = lean_ctor_get(v___x_2034_, 1);
lean_inc(v_snd_2035_);
lean_dec_ref(v___x_2034_);
v_sz_2036_ = lean_array_size(v_contents_2033_);
v___x_2037_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2033_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2036_, v___x_2037_, v_contents_2033_);
v___x_2039_ = lean_string_length(v___y_2032_);
lean_dec_ref(v___y_2032_);
v___x_2040_ = lean_nat_add(v___y_2024_, v___x_2039_);
v___x_2041_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2038_, v___x_2018_, v___x_2040_, v_snd_2035_);
lean_dec(v___x_2040_);
lean_dec_ref(v___x_2038_);
v_snd_2042_ = lean_ctor_get(v___x_2041_, 1);
lean_inc(v_snd_2042_);
lean_dec_ref(v___x_2041_);
v___x_2043_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2042_);
v_snd_2044_ = lean_ctor_get(v___x_2043_, 1);
lean_inc(v_snd_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_add(v_b_2023_, v___x_2045_);
lean_dec(v_b_2023_);
v___x_2047_ = ((size_t)1ULL);
v___x_2048_ = lean_usize_add(v_i_2022_, v___x_2047_);
v_i_2022_ = v___x_2048_;
v_b_2023_ = v___x_2046_;
v___y_2025_ = v_snd_2044_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t v___x_2056_, lean_object* v_as_2057_, size_t v_sz_2058_, size_t v_i_2059_, lean_object* v_b_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_usize_dec_lt(v_i_2059_, v_sz_2058_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_b_2060_);
lean_ctor_set(v___x_2064_, 1, v___y_2062_);
return v___x_2064_;
}
else
{
lean_object* v___x_2065_; lean_object* v_snd_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_snd_2069_; lean_object* v_a_2070_; lean_object* v_term_2071_; lean_object* v_desc_2072_; lean_object* v___x_2073_; lean_object* v___y_2075_; lean_object* v___y_2076_; uint8_t v___x_2095_; 
v___x_2065_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2061_, v___y_2062_);
v_snd_2066_ = lean_ctor_get(v___x_2065_, 1);
lean_inc(v_snd_2066_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_2068_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2067_, v_snd_2066_);
v_snd_2069_ = lean_ctor_get(v___x_2068_, 1);
lean_inc(v_snd_2069_);
lean_dec_ref(v___x_2068_);
v_a_2070_ = lean_array_uget_borrowed(v_as_2057_, v_i_2059_);
v_term_2071_ = lean_ctor_get(v_a_2070_, 2);
v_desc_2072_ = lean_ctor_get(v_a_2070_, 3);
v___x_2073_ = lean_box(0);
v___x_2095_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_term_2071_);
if (v___x_2095_ == 0)
{
v___y_2075_ = v___y_2061_;
v___y_2076_ = v_snd_2069_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_snd_2098_; 
v___x_2096_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2097_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2096_, v_snd_2069_);
v_snd_2098_ = lean_ctor_get(v___x_2097_, 1);
lean_inc(v_snd_2098_);
lean_dec_ref(v___x_2097_);
v___y_2075_ = v___y_2061_;
v___y_2076_ = v_snd_2098_;
goto v___jp_2074_;
}
v___jp_2074_:
{
size_t v_sz_2077_; size_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v_snd_2081_; lean_object* v___x_2082_; lean_object* v_snd_2083_; size_t v_sz_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_snd_2089_; lean_object* v___x_2090_; lean_object* v_snd_2091_; size_t v___x_2092_; size_t v___x_2093_; 
v_sz_2077_ = lean_array_size(v_term_2071_);
v___x_2078_ = ((size_t)0ULL);
lean_inc_ref(v_term_2071_);
v___x_2079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2077_, v___x_2078_, v_term_2071_);
v___x_2080_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2079_, v___x_2056_, v___y_2075_, v___y_2076_);
lean_dec_ref(v___x_2079_);
v_snd_2081_ = lean_ctor_get(v___x_2080_, 1);
lean_inc(v_snd_2081_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2081_);
v_snd_2083_ = lean_ctor_get(v___x_2082_, 1);
lean_inc(v_snd_2083_);
lean_dec_ref(v___x_2082_);
v_sz_2084_ = lean_array_size(v_desc_2072_);
lean_inc_ref(v_desc_2072_);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2084_, v___x_2078_, v_desc_2072_);
v___x_2086_ = lean_unsigned_to_nat(2u);
v___x_2087_ = lean_nat_add(v___y_2075_, v___x_2086_);
v___x_2088_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2085_, v___x_2056_, v___x_2087_, v_snd_2083_);
lean_dec(v___x_2087_);
lean_dec_ref(v___x_2085_);
v_snd_2089_ = lean_ctor_get(v___x_2088_, 1);
lean_inc(v_snd_2089_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2089_);
v_snd_2091_ = lean_ctor_get(v___x_2090_, 1);
lean_inc(v_snd_2091_);
lean_dec_ref(v___x_2090_);
v___x_2092_ = ((size_t)1ULL);
v___x_2093_ = lean_usize_add(v_i_2059_, v___x_2092_);
v_i_2059_ = v___x_2093_;
v_b_2060_ = v___x_2073_;
v___y_2062_ = v_snd_2091_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_2102_, lean_object* v_next_x3f_2103_, uint8_t v_atLineStart_2104_, uint8_t v_alternate_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___y_2109_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
lean_inc(v_stx_2102_);
v___x_2139_ = l_Lean_Syntax_getKind(v_stx_2102_);
v___x_2140_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3));
v___x_2141_ = lean_name_eq(v___x_2139_, v___x_2140_);
lean_dec(v___x_2139_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_inc(v_stx_2102_);
v___x_2142_ = l_Lean_Doc_ArgValView_of(v_stx_2102_);
if (lean_obj_tag(v___x_2142_) == 1)
{
lean_object* v_val_2143_; 
lean_dec(v_next_x3f_2103_);
lean_dec(v_stx_2102_);
v_val_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_val_2143_);
lean_dec_ref_known(v___x_2142_, 1);
if (lean_obj_tag(v_val_2143_) == 1)
{
lean_object* v_x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_x_2144_ = lean_ctor_get(v_val_2143_, 0);
lean_inc(v_x_2144_);
lean_dec_ref_known(v_val_2143_, 1);
v___x_2145_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_x_2144_);
v___x_2146_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2145_, v_a_2107_);
lean_dec_ref(v___x_2145_);
return v___x_2146_;
}
else
{
lean_object* v_lit_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_lit_2147_ = lean_ctor_get(v_val_2143_, 0);
lean_inc(v_lit_2147_);
lean_dec(v_val_2143_);
v___x_2148_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_lit_2147_);
v___x_2149_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2148_, v_a_2107_);
lean_dec_ref(v___x_2148_);
return v___x_2149_;
}
}
else
{
lean_object* v___x_2150_; 
lean_dec(v___x_2142_);
lean_inc(v_stx_2102_);
v___x_2150_ = l_Lean_Doc_ArgView_of(v_stx_2102_);
if (lean_obj_tag(v___x_2150_) == 1)
{
lean_object* v_val_2151_; 
lean_dec(v_next_x3f_2103_);
lean_dec(v_stx_2102_);
v_val_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v___x_2150_, 1);
switch(lean_obj_tag(v_val_2151_))
{
case 0:
{
lean_object* v_val_2152_; lean_object* v___x_2153_; 
v_val_2152_ = lean_ctor_get(v_val_2151_, 1);
lean_inc(v_val_2152_);
lean_dec_ref_known(v_val_2151_, 2);
v___x_2153_ = lean_box(0);
v_stx_2102_ = v_val_2152_;
v_next_x3f_2103_ = v___x_2153_;
v_atLineStart_2104_ = v___x_2141_;
v_alternate_2105_ = v___x_2141_;
goto _start;
}
case 1:
{
lean_object* v_name_2155_; lean_object* v_val_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v_snd_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v_snd_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_snd_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_name_2155_ = lean_ctor_get(v_val_2151_, 2);
lean_inc(v_name_2155_);
v_val_2156_ = lean_ctor_get(v_val_2151_, 4);
lean_inc(v_val_2156_);
lean_dec_ref_known(v_val_2151_, 5);
v___x_2157_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_2158_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2157_, v_a_2107_);
v_snd_2159_ = lean_ctor_get(v___x_2158_, 1);
lean_inc(v_snd_2159_);
lean_dec_ref(v___x_2158_);
v___x_2160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2155_);
v___x_2161_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2160_, v_snd_2159_);
lean_dec_ref(v___x_2160_);
v_snd_2162_ = lean_ctor_get(v___x_2161_, 1);
lean_inc(v_snd_2162_);
lean_dec_ref(v___x_2161_);
v___x_2163_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
v___x_2164_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2163_, v_snd_2162_);
v_snd_2165_ = lean_ctor_get(v___x_2164_, 1);
lean_inc(v_snd_2165_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = lean_box(0);
v___x_2167_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_val_2156_, v___x_2166_, v___x_2141_, v___x_2141_, v_a_2106_, v_snd_2165_);
v_snd_2168_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_snd_2168_);
lean_dec_ref(v___x_2167_);
v___x_2169_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_2170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2169_, v_snd_2168_);
return v___x_2170_;
}
default: 
{
lean_object* v_name_2171_; uint8_t v_isOn_2172_; lean_object* v___y_2174_; 
v_name_2171_ = lean_ctor_get(v_val_2151_, 2);
lean_inc(v_name_2171_);
v_isOn_2172_ = lean_ctor_get_uint8(v_val_2151_, sizeof(void*)*3);
lean_dec_ref_known(v_val_2151_, 3);
if (v_isOn_2172_ == 0)
{
lean_object* v___x_2179_; 
v___x_2179_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___y_2174_ = v___x_2179_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___y_2174_ = v___x_2180_;
goto v___jp_2173_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; lean_object* v_snd_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2174_, v_a_2107_);
v_snd_2176_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_snd_2176_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2171_);
v___x_2178_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2177_, v_snd_2176_);
lean_dec_ref(v___x_2177_);
return v___x_2178_;
}
}
}
}
else
{
lean_object* v___x_2181_; 
lean_dec(v___x_2150_);
lean_inc(v_stx_2102_);
v___x_2181_ = l_Lean_Doc_LinkTargetView_of(v_stx_2102_);
if (lean_obj_tag(v___x_2181_) == 1)
{
lean_object* v_val_2182_; lean_object* v___x_2183_; 
lean_dec(v_next_x3f_2103_);
lean_dec(v_stx_2102_);
v_val_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2183_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_val_2182_, v_a_2107_);
lean_dec(v_val_2182_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; 
lean_dec(v___x_2181_);
lean_inc(v_stx_2102_);
v___x_2184_ = l_Lean_Doc_InlineView_of(v_stx_2102_);
if (lean_obj_tag(v___x_2184_) == 1)
{
lean_object* v_val_2185_; 
lean_dec(v_stx_2102_);
v_val_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_val_2185_);
lean_dec_ref_known(v___x_2184_, 1);
switch(lean_obj_tag(v_val_2185_))
{
case 0:
{
lean_object* v_view_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v_next_x3f_2103_);
v_view_2186_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2186_);
lean_dec_ref_known(v_val_2185_, 1);
v___x_2187_ = l_Lean_Doc_TextView_getVersoText(v_view_2186_);
lean_dec_ref(v_view_2186_);
v___x_2188_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_2104_, v___x_2187_);
v___x_2189_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2188_, v_a_2107_);
lean_dec_ref(v___x_2188_);
return v___x_2189_;
}
case 1:
{
lean_object* v_view_2190_; lean_object* v_content_2191_; uint32_t v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v_next_x3f_2103_);
v_view_2190_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2190_);
lean_dec_ref_known(v_val_2185_, 1);
v_content_2191_ = lean_ctor_get(v_view_2190_, 2);
lean_inc_ref(v_content_2191_);
lean_dec_ref(v_view_2190_);
v___x_2192_ = 95;
v___x_2193_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2192_, v_content_2191_, v_a_2106_, v_a_2107_);
return v___x_2193_;
}
case 2:
{
lean_object* v_view_2194_; lean_object* v_content_2195_; uint32_t v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_next_x3f_2103_);
v_view_2194_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2194_);
lean_dec_ref_known(v_val_2185_, 1);
v_content_2195_ = lean_ctor_get(v_view_2194_, 2);
lean_inc_ref(v_content_2195_);
lean_dec_ref(v_view_2194_);
v___x_2196_ = 42;
v___x_2197_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2196_, v_content_2195_, v_a_2106_, v_a_2107_);
return v___x_2197_;
}
case 3:
{
lean_object* v_view_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v_next_x3f_2103_);
v_view_2198_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2198_);
lean_dec_ref_known(v_val_2185_, 1);
v___x_2199_ = l_Lean_Doc_CodeView_getVersoCode(v_view_2198_);
lean_dec_ref(v_view_2198_);
v___x_2200_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2199_);
v___x_2201_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2200_, v_a_2107_);
lean_dec_ref(v___x_2200_);
return v___x_2201_;
}
case 4:
{
lean_object* v_view_2202_; lean_object* v___y_2204_; uint8_t v_mode_2210_; 
lean_dec(v_next_x3f_2103_);
v_view_2202_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2202_);
lean_dec_ref_known(v_val_2185_, 1);
v_mode_2210_ = lean_ctor_get_uint8(v_view_2202_, sizeof(void*)*3);
if (v_mode_2210_ == 0)
{
lean_object* v___x_2211_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5));
v___y_2204_ = v___x_2211_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2212_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
v___y_2204_ = v___x_2212_;
goto v___jp_2203_;
}
v___jp_2203_:
{
lean_object* v___x_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2205_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2204_, v_a_2107_);
v_snd_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = l_Lean_Doc_MathView_getVersoCode(v_view_2202_);
lean_dec_ref(v_view_2202_);
v___x_2208_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2207_);
v___x_2209_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2208_, v_snd_2206_);
lean_dec_ref(v___x_2208_);
return v___x_2209_;
}
}
case 5:
{
lean_object* v_view_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_snd_2216_; lean_object* v_content_2217_; lean_object* v_target_2218_; size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_snd_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_snd_2226_; lean_object* v___x_2227_; 
lean_dec(v_next_x3f_2103_);
v_view_2213_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2213_);
lean_dec_ref_known(v_val_2185_, 1);
v___x_2214_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2215_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2214_, v_a_2107_);
v_snd_2216_ = lean_ctor_get(v___x_2215_, 1);
lean_inc(v_snd_2216_);
lean_dec_ref(v___x_2215_);
v_content_2217_ = lean_ctor_get(v_view_2213_, 2);
lean_inc_ref(v_content_2217_);
v_target_2218_ = lean_ctor_get(v_view_2213_, 4);
lean_inc_ref(v_target_2218_);
lean_dec_ref(v_view_2213_);
v_sz_2219_ = lean_array_size(v_content_2217_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2219_, v___x_2220_, v_content_2217_);
v___x_2222_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2221_, v___x_2141_, v_a_2106_, v_snd_2216_);
lean_dec_ref(v___x_2221_);
v_snd_2223_ = lean_ctor_get(v___x_2222_, 1);
lean_inc(v_snd_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2225_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2224_, v_snd_2223_);
v_snd_2226_ = lean_ctor_get(v___x_2225_, 1);
lean_inc(v_snd_2226_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2218_, v_snd_2226_);
lean_dec_ref(v_target_2218_);
return v___x_2227_;
}
case 6:
{
lean_object* v_view_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v_snd_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v_snd_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v_snd_2238_; lean_object* v_target_2239_; lean_object* v___x_2240_; 
lean_dec(v_next_x3f_2103_);
v_view_2228_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2228_);
lean_dec_ref_known(v_val_2185_, 1);
v___x_2229_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7));
v___x_2230_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2229_, v_a_2107_);
v_snd_2231_ = lean_ctor_get(v___x_2230_, 1);
lean_inc(v_snd_2231_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = l_Lean_Doc_ImageView_getAlt(v_view_2228_);
v___x_2233_ = l_Lean_Doc_escapeVersoImageAlt(v___x_2232_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2233_, v_snd_2231_);
lean_dec_ref(v___x_2233_);
v_snd_2235_ = lean_ctor_get(v___x_2234_, 1);
lean_inc(v_snd_2235_);
lean_dec_ref(v___x_2234_);
v___x_2236_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2237_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2236_, v_snd_2235_);
v_snd_2238_ = lean_ctor_get(v___x_2237_, 1);
lean_inc(v_snd_2238_);
lean_dec_ref(v___x_2237_);
v_target_2239_ = lean_ctor_get(v_view_2228_, 4);
lean_inc_ref(v_target_2239_);
lean_dec_ref(v_view_2228_);
v___x_2240_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2239_, v_snd_2238_);
lean_dec_ref(v_target_2239_);
return v___x_2240_;
}
case 7:
{
lean_object* v_view_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v_snd_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v_snd_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec(v_next_x3f_2103_);
v_view_2241_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2241_);
lean_dec_ref_known(v_val_2185_, 1);
v___x_2242_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2243_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2242_, v_a_2107_);
v_snd_2244_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_snd_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = l_Lean_Doc_FootnoteView_getName(v_view_2241_);
lean_dec_ref(v_view_2241_);
v___x_2246_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2245_, v_snd_2244_);
lean_dec_ref(v___x_2245_);
v_snd_2247_ = lean_ctor_get(v___x_2246_, 1);
lean_inc(v_snd_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2249_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2248_, v_snd_2247_);
return v___x_2249_;
}
case 8:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec_ref_known(v_val_2185_, 1);
lean_dec(v_next_x3f_2103_);
v___x_2250_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2251_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2250_, v_a_2107_);
return v___x_2251_;
}
default: 
{
lean_object* v_view_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_snd_2255_; lean_object* v_name_2256_; lean_object* v_args_2257_; lean_object* v_content_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_snd_2261_; lean_object* v___x_2262_; size_t v_sz_2263_; size_t v___x_2264_; lean_object* v___x_2265_; lean_object* v_snd_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_snd_2269_; lean_object* v___x_2280_; 
v_view_2252_ = lean_ctor_get(v_val_2185_, 0);
lean_inc_ref(v_view_2252_);
lean_dec_ref_known(v_val_2185_, 1);
v___x_2253_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2254_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2253_, v_a_2107_);
v_snd_2255_ = lean_ctor_get(v___x_2254_, 1);
lean_inc(v_snd_2255_);
lean_dec_ref(v___x_2254_);
v_name_2256_ = lean_ctor_get(v_view_2252_, 2);
lean_inc(v_name_2256_);
v_args_2257_ = lean_ctor_get(v_view_2252_, 3);
lean_inc_ref(v_args_2257_);
v_content_2258_ = lean_ctor_get(v_view_2252_, 6);
lean_inc_ref(v_content_2258_);
lean_dec_ref(v_view_2252_);
v___x_2259_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2256_);
v___x_2260_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2259_, v_snd_2255_);
lean_dec_ref(v___x_2259_);
v_snd_2261_ = lean_ctor_get(v___x_2260_, 1);
lean_inc(v_snd_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = lean_box(0);
v_sz_2263_ = lean_array_size(v_args_2257_);
v___x_2264_ = ((size_t)0ULL);
v___x_2265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2141_, v_args_2257_, v_sz_2263_, v___x_2264_, v___x_2262_, v_a_2106_, v_snd_2261_);
lean_dec_ref(v_args_2257_);
v_snd_2266_ = lean_ctor_get(v___x_2265_, 1);
lean_inc(v_snd_2266_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2268_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2267_, v_snd_2266_);
v_snd_2269_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_snd_2269_);
lean_dec_ref(v___x_2268_);
v___x_2280_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_2258_);
if (lean_obj_tag(v___x_2280_) == 1)
{
lean_object* v_val_2281_; uint8_t v___x_2282_; 
v_val_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_val_2281_, v_next_x3f_2103_);
if (v___x_2282_ == 0)
{
size_t v_sz_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v_sz_2283_ = lean_array_size(v_content_2258_);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2283_, v___x_2264_, v_content_2258_);
v___x_2285_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2284_, v___x_2282_, v_a_2106_, v_snd_2269_);
lean_dec_ref(v___x_2284_);
return v___x_2285_;
}
else
{
goto v___jp_2270_;
}
}
else
{
lean_dec(v___x_2280_);
lean_dec(v_next_x3f_2103_);
goto v___jp_2270_;
}
v___jp_2270_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v_snd_2273_; size_t v_sz_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v_snd_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2272_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2271_, v_snd_2269_);
v_snd_2273_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2273_);
lean_dec_ref(v___x_2272_);
v_sz_2274_ = lean_array_size(v_content_2258_);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2274_, v___x_2264_, v_content_2258_);
v___x_2276_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2275_, v___x_2141_, v_a_2106_, v_snd_2273_);
lean_dec_ref(v___x_2275_);
v_snd_2277_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_snd_2277_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2279_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2278_, v_snd_2277_);
return v___x_2279_;
}
}
}
}
else
{
lean_object* v___x_2286_; 
lean_dec(v___x_2184_);
lean_dec(v_next_x3f_2103_);
lean_inc(v_stx_2102_);
v___x_2286_ = l_Lean_Doc_BlockView_of(v_stx_2102_);
if (lean_obj_tag(v___x_2286_) == 1)
{
lean_object* v_val_2287_; 
v_val_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_val_2287_);
lean_dec_ref_known(v___x_2286_, 1);
switch(lean_obj_tag(v_val_2287_))
{
case 0:
{
lean_object* v_view_2288_; lean_object* v_content_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; 
lean_dec(v_stx_2102_);
v_view_2288_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2288_);
lean_dec_ref_known(v_val_2287_, 1);
v_content_2289_ = lean_ctor_get(v_view_2288_, 1);
lean_inc_ref(v_content_2289_);
lean_dec_ref(v_view_2288_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v___x_2291_ = lean_array_get_size(v_content_2289_);
v___x_2292_ = lean_nat_dec_lt(v___x_2290_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec_ref(v_content_2289_);
goto v___jp_2136_;
}
else
{
if (v___x_2292_ == 0)
{
lean_dec_ref(v_content_2289_);
goto v___jp_2136_;
}
else
{
size_t v___x_2293_; size_t v___x_2294_; uint8_t v___x_2295_; lean_object* v___y_2297_; lean_object* v___y_2298_; 
v___x_2293_ = ((size_t)0ULL);
v___x_2294_ = lean_usize_of_nat(v___x_2291_);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_2141_, v_content_2289_, v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_dec_ref(v_content_2289_);
goto v___jp_2136_;
}
else
{
lean_object* v___x_2304_; lean_object* v_snd_2305_; 
v___x_2304_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2305_ = lean_ctor_get(v___x_2304_, 1);
lean_inc(v_snd_2305_);
lean_dec_ref(v___x_2304_);
if (v___x_2292_ == 0)
{
goto v___jp_2306_;
}
else
{
if (v___x_2292_ == 0)
{
goto v___jp_2306_;
}
else
{
uint8_t v___x_2310_; 
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_2295_, v___x_2141_, v_content_2289_, v___x_2293_, v___x_2294_);
if (v___x_2310_ == 0)
{
goto v___jp_2306_;
}
else
{
v___y_2297_ = v_a_2106_;
v___y_2298_ = v_snd_2305_;
goto v___jp_2296_;
}
}
}
v___jp_2306_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_snd_2309_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2308_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2307_, v_snd_2305_);
v_snd_2309_ = lean_ctor_get(v___x_2308_, 1);
lean_inc(v_snd_2309_);
lean_dec_ref(v___x_2308_);
v___y_2297_ = v_a_2106_;
v___y_2298_ = v_snd_2309_;
goto v___jp_2296_;
}
}
v___jp_2296_:
{
size_t v_sz_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v_snd_2302_; lean_object* v___x_2303_; 
v_sz_2299_ = lean_array_size(v_content_2289_);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2299_, v___x_2293_, v_content_2289_);
v___x_2301_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2300_, v___x_2295_, v___y_2297_, v___y_2298_);
lean_dec_ref(v___x_2300_);
v_snd_2302_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_snd_2302_);
lean_dec_ref(v___x_2301_);
v___x_2303_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2302_);
return v___x_2303_;
}
}
}
}
case 1:
{
lean_object* v_view_2311_; lean_object* v___y_2313_; 
lean_dec(v_stx_2102_);
v_view_2311_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2311_);
lean_dec_ref_known(v_val_2287_, 1);
if (v_alternate_2105_ == 0)
{
lean_object* v___x_2321_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11));
v___y_2313_ = v___x_2321_;
goto v___jp_2312_;
}
else
{
lean_object* v___x_2322_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___y_2313_ = v___x_2322_;
goto v___jp_2312_;
}
v___jp_2312_:
{
lean_object* v_items_2314_; lean_object* v___x_2315_; size_t v_sz_2316_; size_t v___x_2317_; lean_object* v___x_2318_; lean_object* v_snd_2319_; lean_object* v___x_2320_; 
v_items_2314_ = lean_ctor_get(v_view_2311_, 1);
lean_inc_ref(v_items_2314_);
lean_dec_ref(v_view_2311_);
v___x_2315_ = lean_box(0);
v_sz_2316_ = lean_array_size(v_items_2314_);
v___x_2317_ = ((size_t)0ULL);
lean_inc_ref(v___y_2313_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2313_, v___x_2141_, v_items_2314_, v_sz_2316_, v___x_2317_, v___x_2315_, v_a_2106_, v_a_2107_);
lean_dec_ref(v_items_2314_);
v_snd_2319_ = lean_ctor_get(v___x_2318_, 1);
lean_inc(v_snd_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2319_);
return v___x_2320_;
}
}
case 2:
{
lean_object* v_view_2323_; lean_object* v_start_2324_; lean_object* v_items_2325_; size_t v_sz_2326_; size_t v___x_2327_; lean_object* v___x_2328_; lean_object* v_snd_2329_; lean_object* v___x_2330_; 
lean_dec(v_stx_2102_);
v_view_2323_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2323_);
lean_dec_ref_known(v_val_2287_, 1);
v_start_2324_ = lean_ctor_get(v_view_2323_, 1);
lean_inc(v_start_2324_);
v_items_2325_ = lean_ctor_get(v_view_2323_, 2);
lean_inc_ref(v_items_2325_);
lean_dec_ref(v_view_2323_);
v_sz_2326_ = lean_array_size(v_items_2325_);
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_2141_, v_alternate_2105_, v_items_2325_, v_sz_2326_, v___x_2327_, v_start_2324_, v_a_2106_, v_a_2107_);
lean_dec_ref(v_items_2325_);
v_snd_2329_ = lean_ctor_get(v___x_2328_, 1);
lean_inc(v_snd_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2329_);
return v___x_2330_;
}
case 3:
{
lean_object* v_view_2331_; lean_object* v_items_2332_; lean_object* v___x_2333_; size_t v_sz_2334_; size_t v___x_2335_; lean_object* v___x_2336_; lean_object* v_snd_2337_; lean_object* v___x_2338_; 
lean_dec(v_stx_2102_);
v_view_2331_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2331_);
lean_dec_ref_known(v_val_2287_, 1);
v_items_2332_ = lean_ctor_get(v_view_2331_, 1);
lean_inc_ref(v_items_2332_);
lean_dec_ref(v_view_2331_);
v___x_2333_ = lean_box(0);
v_sz_2334_ = lean_array_size(v_items_2332_);
v___x_2335_ = ((size_t)0ULL);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_2141_, v_items_2332_, v_sz_2334_, v___x_2335_, v___x_2333_, v_a_2106_, v_a_2107_);
lean_dec_ref(v_items_2332_);
v_snd_2337_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_snd_2337_);
lean_dec_ref(v___x_2336_);
v___x_2338_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2337_);
return v___x_2338_;
}
case 4:
{
lean_object* v_view_2339_; lean_object* v___x_2340_; lean_object* v_snd_2341_; lean_object* v_content_2342_; lean_object* v___y_2344_; lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
lean_dec(v_stx_2102_);
v_view_2339_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2339_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2340_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2341_ = lean_ctor_get(v___x_2340_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v___x_2340_);
v_content_2342_ = lean_ctor_get(v_view_2339_, 2);
lean_inc_ref(v_content_2342_);
lean_dec_ref(v_view_2339_);
v___x_2355_ = lean_array_get_size(v_content_2342_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = lean_nat_dec_eq(v___x_2355_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_object* v___x_2358_; 
v___x_2358_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
v___y_2344_ = v___x_2358_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2359_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___y_2344_ = v___x_2359_;
goto v___jp_2343_;
}
v___jp_2343_:
{
lean_object* v___x_2345_; lean_object* v_snd_2346_; size_t v_sz_2347_; size_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v_snd_2353_; lean_object* v___x_2354_; 
v___x_2345_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2344_, v_snd_2341_);
v_snd_2346_ = lean_ctor_get(v___x_2345_, 1);
lean_inc(v_snd_2346_);
lean_dec_ref(v___x_2345_);
v_sz_2347_ = lean_array_size(v_content_2342_);
v___x_2348_ = ((size_t)0ULL);
v___x_2349_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2347_, v___x_2348_, v_content_2342_);
v___x_2350_ = lean_unsigned_to_nat(2u);
v___x_2351_ = lean_nat_add(v_a_2106_, v___x_2350_);
v___x_2352_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2349_, v___x_2141_, v___x_2351_, v_snd_2346_);
lean_dec(v___x_2351_);
lean_dec_ref(v___x_2349_);
v_snd_2353_ = lean_ctor_get(v___x_2352_, 1);
lean_inc(v_snd_2353_);
lean_dec_ref(v___x_2352_);
v___x_2354_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2353_);
return v___x_2354_;
}
}
case 5:
{
lean_object* v_view_2360_; lean_object* v___x_2361_; lean_object* v_snd_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2387_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
lean_dec(v_stx_2102_);
v_view_2360_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2360_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2361_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2362_ = lean_ctor_get(v___x_2361_, 1);
lean_inc(v_snd_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2364_ = lean_unsigned_to_nat(3u);
v___x_2365_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_view_2360_);
v___x_2403_ = l_Lean_Doc_longestBacktickRun(v___x_2365_);
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_nat_add(v___x_2403_, v___x_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_nat_dec_le(v___x_2364_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec(v___x_2405_);
v___y_2387_ = v___x_2364_;
goto v___jp_2386_;
}
else
{
v___y_2387_ = v___x_2405_;
goto v___jp_2386_;
}
v___jp_2366_:
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_string_append(v___x_2365_, v___y_2368_);
v___y_2118_ = v___y_2367_;
v___y_2119_ = v___y_2368_;
v___y_2120_ = v___y_2369_;
v___y_2121_ = v___y_2370_;
v___y_2122_ = v___x_2371_;
goto v___jp_2117_;
}
v___jp_2372_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_snd_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2377_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2376_, v___y_2375_);
v_snd_2378_ = lean_ctor_get(v___x_2377_, 1);
lean_inc(v_snd_2378_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = lean_string_utf8_byte_size(v___x_2365_);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___x_2381_ = lean_nat_dec_eq(v___x_2379_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = lean_unsigned_to_nat(1u);
v___x_2383_ = lean_nat_dec_le(v___x_2382_, v___x_2379_);
if (v___x_2383_ == 0)
{
v___y_2367_ = v___y_2373_;
v___y_2368_ = v___x_2376_;
v___y_2369_ = v___y_2374_;
v___y_2370_ = v_snd_2378_;
goto v___jp_2366_;
}
else
{
lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = lean_nat_sub(v___x_2379_, v___x_2382_);
v___x_2385_ = lean_string_memcmp(v___x_2365_, v___x_2376_, v___x_2384_, v___x_2380_, v___x_2382_);
lean_dec(v___x_2384_);
if (v___x_2385_ == 0)
{
v___y_2367_ = v___y_2373_;
v___y_2368_ = v___x_2376_;
v___y_2369_ = v___y_2374_;
v___y_2370_ = v_snd_2378_;
goto v___jp_2366_;
}
else
{
v___y_2118_ = v___y_2373_;
v___y_2119_ = v___x_2376_;
v___y_2120_ = v___y_2374_;
v___y_2121_ = v_snd_2378_;
v___y_2122_ = v___x_2365_;
goto v___jp_2117_;
}
}
}
else
{
v___y_2118_ = v___y_2373_;
v___y_2119_ = v___x_2376_;
v___y_2120_ = v___y_2374_;
v___y_2121_ = v_snd_2378_;
v___y_2122_ = v___x_2365_;
goto v___jp_2117_;
}
}
v___jp_2386_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_name_x3f_2390_; 
v___x_2388_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___y_2387_, v___x_2363_);
v___x_2389_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2388_, v_snd_2362_);
v_name_x3f_2390_ = lean_ctor_get(v_view_2360_, 2);
lean_inc(v_name_x3f_2390_);
if (lean_obj_tag(v_name_x3f_2390_) == 1)
{
lean_object* v_snd_2391_; lean_object* v_args_2392_; lean_object* v_val_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_snd_2396_; lean_object* v___x_2397_; size_t v_sz_2398_; size_t v___x_2399_; lean_object* v___x_2400_; lean_object* v_snd_2401_; 
v_snd_2391_ = lean_ctor_get(v___x_2389_, 1);
lean_inc(v_snd_2391_);
lean_dec_ref(v___x_2389_);
v_args_2392_ = lean_ctor_get(v_view_2360_, 3);
lean_inc_ref(v_args_2392_);
lean_dec_ref(v_view_2360_);
v_val_2393_ = lean_ctor_get(v_name_x3f_2390_, 0);
lean_inc(v_val_2393_);
lean_dec_ref_known(v_name_x3f_2390_, 1);
v___x_2394_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_val_2393_);
v___x_2395_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2394_, v_snd_2391_);
lean_dec_ref(v___x_2394_);
v_snd_2396_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_snd_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = lean_box(0);
v_sz_2398_ = lean_array_size(v_args_2392_);
v___x_2399_ = ((size_t)0ULL);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2141_, v_args_2392_, v_sz_2398_, v___x_2399_, v___x_2397_, v_a_2106_, v_snd_2396_);
lean_dec_ref(v_args_2392_);
v_snd_2401_ = lean_ctor_get(v___x_2400_, 1);
lean_inc(v_snd_2401_);
lean_dec_ref(v___x_2400_);
v___y_2373_ = v___x_2388_;
v___y_2374_ = v_a_2106_;
v___y_2375_ = v_snd_2401_;
goto v___jp_2372_;
}
else
{
lean_object* v_snd_2402_; 
lean_dec(v_name_x3f_2390_);
lean_dec_ref(v_view_2360_);
v_snd_2402_ = lean_ctor_get(v___x_2389_, 1);
lean_inc(v_snd_2402_);
lean_dec_ref(v___x_2389_);
v___y_2373_ = v___x_2388_;
v___y_2374_ = v_a_2106_;
v___y_2375_ = v_snd_2402_;
goto v___jp_2372_;
}
}
}
case 6:
{
lean_object* v_view_2407_; lean_object* v___x_2408_; lean_object* v_snd_2409_; lean_object* v_name_2410_; lean_object* v_args_2411_; lean_object* v_content_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_snd_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_snd_2420_; lean_object* v___x_2421_; size_t v_sz_2422_; size_t v___x_2423_; lean_object* v___x_2424_; lean_object* v_snd_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_snd_2428_; size_t v_sz_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_snd_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_snd_2435_; lean_object* v___x_2436_; lean_object* v_snd_2437_; lean_object* v___x_2438_; 
lean_dec(v_stx_2102_);
v_view_2407_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2407_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2408_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2409_ = lean_ctor_get(v___x_2408_, 1);
lean_inc(v_snd_2409_);
lean_dec_ref(v___x_2408_);
v_name_2410_ = lean_ctor_get(v_view_2407_, 2);
lean_inc(v_name_2410_);
v_args_2411_ = lean_ctor_get(v_view_2407_, 3);
lean_inc_ref(v_args_2411_);
v_content_2412_ = lean_ctor_get(v_view_2407_, 4);
lean_inc_ref(v_content_2412_);
lean_dec_ref(v_view_2407_);
v___x_2413_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2414_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_content_2412_);
v___x_2415_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(v___x_2414_, v___x_2413_);
v___x_2416_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2415_, v_snd_2409_);
v_snd_2417_ = lean_ctor_get(v___x_2416_, 1);
lean_inc(v_snd_2417_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2410_);
v___x_2419_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2418_, v_snd_2417_);
lean_dec_ref(v___x_2418_);
v_snd_2420_ = lean_ctor_get(v___x_2419_, 1);
lean_inc(v_snd_2420_);
lean_dec_ref(v___x_2419_);
v___x_2421_ = lean_box(0);
v_sz_2422_ = lean_array_size(v_args_2411_);
v___x_2423_ = ((size_t)0ULL);
v___x_2424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2141_, v_args_2411_, v_sz_2422_, v___x_2423_, v___x_2421_, v_a_2106_, v_snd_2420_);
lean_dec_ref(v_args_2411_);
v_snd_2425_ = lean_ctor_get(v___x_2424_, 1);
lean_inc(v_snd_2425_);
lean_dec_ref(v___x_2424_);
v___x_2426_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2427_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2426_, v_snd_2425_);
v_snd_2428_ = lean_ctor_get(v___x_2427_, 1);
lean_inc(v_snd_2428_);
lean_dec_ref(v___x_2427_);
v_sz_2429_ = lean_array_size(v_content_2412_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2429_, v___x_2423_, v_content_2412_);
v___x_2431_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2430_, v___x_2141_, v_a_2106_, v_snd_2428_);
lean_dec_ref(v___x_2430_);
v_snd_2432_ = lean_ctor_get(v___x_2431_, 1);
lean_inc(v_snd_2432_);
lean_dec_ref(v___x_2431_);
lean_inc(v_a_2106_);
v___x_2433_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2106_, v___x_2413_);
v___x_2434_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2433_, v_snd_2432_);
lean_dec_ref(v___x_2433_);
v_snd_2435_ = lean_ctor_get(v___x_2434_, 1);
lean_inc(v_snd_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2415_, v_snd_2435_);
lean_dec_ref(v___x_2415_);
v_snd_2437_ = lean_ctor_get(v___x_2436_, 1);
lean_inc(v_snd_2437_);
lean_dec_ref(v___x_2436_);
v___x_2438_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2437_);
return v___x_2438_;
}
case 7:
{
lean_object* v_view_2439_; lean_object* v___x_2440_; lean_object* v_snd_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_snd_2444_; lean_object* v_name_2445_; lean_object* v_args_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_snd_2449_; lean_object* v___x_2450_; size_t v_sz_2451_; size_t v___x_2452_; lean_object* v___x_2453_; lean_object* v_snd_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; 
lean_dec(v_stx_2102_);
v_view_2439_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2439_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2440_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2441_ = lean_ctor_get(v___x_2440_, 1);
lean_inc(v_snd_2441_);
lean_dec_ref(v___x_2440_);
v___x_2442_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2443_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2442_, v_snd_2441_);
v_snd_2444_ = lean_ctor_get(v___x_2443_, 1);
lean_inc(v_snd_2444_);
lean_dec_ref(v___x_2443_);
v_name_2445_ = lean_ctor_get(v_view_2439_, 2);
lean_inc(v_name_2445_);
v_args_2446_ = lean_ctor_get(v_view_2439_, 3);
lean_inc_ref(v_args_2446_);
lean_dec_ref(v_view_2439_);
v___x_2447_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2445_);
v___x_2448_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2447_, v_snd_2444_);
lean_dec_ref(v___x_2447_);
v_snd_2449_ = lean_ctor_get(v___x_2448_, 1);
lean_inc(v_snd_2449_);
lean_dec_ref(v___x_2448_);
v___x_2450_ = lean_box(0);
v_sz_2451_ = lean_array_size(v_args_2446_);
v___x_2452_ = ((size_t)0ULL);
v___x_2453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2141_, v_args_2446_, v_sz_2451_, v___x_2452_, v___x_2450_, v_a_2106_, v_snd_2449_);
lean_dec_ref(v_args_2446_);
v_snd_2454_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_snd_2454_);
lean_dec_ref(v___x_2453_);
v___x_2455_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2456_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2455_, v_snd_2454_);
v_snd_2457_ = lean_ctor_get(v___x_2456_, 1);
lean_inc(v_snd_2457_);
lean_dec_ref(v___x_2456_);
v___x_2458_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2457_);
return v___x_2458_;
}
case 8:
{
lean_object* v_view_2459_; lean_object* v___x_2460_; lean_object* v_snd_2461_; lean_object* v_level_2462_; lean_object* v_content_2463_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v_snd_2478_; uint8_t v___x_2479_; 
lean_dec(v_stx_2102_);
v_view_2459_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2459_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2460_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2461_ = lean_ctor_get(v___x_2460_, 1);
lean_inc(v_snd_2461_);
lean_dec_ref(v___x_2460_);
v_level_2462_ = lean_ctor_get(v_view_2459_, 2);
lean_inc(v_level_2462_);
v_content_2463_ = lean_ctor_get(v_view_2459_, 3);
lean_inc_ref(v_content_2463_);
lean_dec_ref(v_view_2459_);
v___x_2473_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_2474_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(v_level_2462_, v___x_2473_);
v___x_2475_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2476_ = lean_string_append(v___x_2474_, v___x_2475_);
v___x_2477_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2476_, v_snd_2461_);
lean_dec_ref(v___x_2476_);
v_snd_2478_ = lean_ctor_get(v___x_2477_, 1);
lean_inc(v_snd_2478_);
lean_dec_ref(v___x_2477_);
v___x_2479_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2463_);
if (v___x_2479_ == 0)
{
v___y_2465_ = v_a_2106_;
v___y_2466_ = v_snd_2478_;
goto v___jp_2464_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_snd_2482_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2481_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2480_, v_snd_2478_);
v_snd_2482_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_snd_2482_);
lean_dec_ref(v___x_2481_);
v___y_2465_ = v_a_2106_;
v___y_2466_ = v_snd_2482_;
goto v___jp_2464_;
}
v___jp_2464_:
{
size_t v_sz_2467_; size_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_snd_2471_; lean_object* v___x_2472_; 
v_sz_2467_ = lean_array_size(v_content_2463_);
v___x_2468_ = ((size_t)0ULL);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2467_, v___x_2468_, v_content_2463_);
v___x_2470_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2469_, v___x_2141_, v___y_2465_, v___y_2466_);
lean_dec_ref(v___x_2469_);
v_snd_2471_ = lean_ctor_get(v___x_2470_, 1);
lean_inc(v_snd_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2471_);
return v___x_2472_;
}
}
case 9:
{
lean_object* v_view_2483_; lean_object* v___x_2484_; lean_object* v_snd_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v_snd_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v_snd_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v_snd_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v_snd_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v_snd_2500_; lean_object* v___x_2501_; 
lean_dec(v_stx_2102_);
v_view_2483_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2483_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2484_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2485_ = lean_ctor_get(v___x_2484_, 1);
lean_inc(v_snd_2485_);
lean_dec_ref(v___x_2484_);
v___x_2486_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2487_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2486_, v_snd_2485_);
v_snd_2488_ = lean_ctor_get(v___x_2487_, 1);
lean_inc(v_snd_2488_);
lean_dec_ref(v___x_2487_);
v___x_2489_ = l_Lean_Doc_LinkRefView_getName(v_view_2483_);
v___x_2490_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2489_, v_snd_2488_);
lean_dec_ref(v___x_2489_);
v_snd_2491_ = lean_ctor_get(v___x_2490_, 1);
lean_inc(v_snd_2491_);
lean_dec_ref(v___x_2490_);
v___x_2492_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2493_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2492_, v_snd_2491_);
v_snd_2494_ = lean_ctor_get(v___x_2493_, 1);
lean_inc(v_snd_2494_);
lean_dec_ref(v___x_2493_);
v___x_2495_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2496_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2495_, v_snd_2494_);
v_snd_2497_ = lean_ctor_get(v___x_2496_, 1);
lean_inc(v_snd_2497_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = l_Lean_Doc_LinkRefView_getUrl(v_view_2483_);
lean_dec_ref(v_view_2483_);
v___x_2499_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2498_, v_snd_2497_);
lean_dec_ref(v___x_2498_);
v_snd_2500_ = lean_ctor_get(v___x_2499_, 1);
lean_inc(v_snd_2500_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2500_);
return v___x_2501_;
}
case 10:
{
lean_object* v_view_2502_; lean_object* v___x_2503_; lean_object* v_snd_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v_snd_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v_snd_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_snd_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_snd_2516_; lean_object* v_content_2517_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint8_t v___x_2527_; 
lean_dec(v_stx_2102_);
v_view_2502_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2502_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2503_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2504_ = lean_ctor_get(v___x_2503_, 1);
lean_inc(v_snd_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2506_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2505_, v_snd_2504_);
v_snd_2507_ = lean_ctor_get(v___x_2506_, 1);
lean_inc(v_snd_2507_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = l_Lean_Doc_FootnoteRefView_getName(v_view_2502_);
v___x_2509_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2508_, v_snd_2507_);
lean_dec_ref(v___x_2508_);
v_snd_2510_ = lean_ctor_get(v___x_2509_, 1);
lean_inc(v_snd_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2512_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2511_, v_snd_2510_);
v_snd_2513_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_snd_2513_);
lean_dec_ref(v___x_2512_);
v___x_2514_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2515_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2514_, v_snd_2513_);
v_snd_2516_ = lean_ctor_get(v___x_2515_, 1);
lean_inc(v_snd_2516_);
lean_dec_ref(v___x_2515_);
v_content_2517_ = lean_ctor_get(v_view_2502_, 4);
lean_inc_ref(v_content_2517_);
lean_dec_ref(v_view_2502_);
v___x_2527_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2517_);
if (v___x_2527_ == 0)
{
v___y_2519_ = v_a_2106_;
v___y_2520_ = v_snd_2516_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_snd_2530_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2529_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2528_, v_snd_2516_);
v_snd_2530_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_snd_2530_);
lean_dec_ref(v___x_2529_);
v___y_2519_ = v_a_2106_;
v___y_2520_ = v_snd_2530_;
goto v___jp_2518_;
}
v___jp_2518_:
{
size_t v_sz_2521_; size_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v_snd_2525_; lean_object* v___x_2526_; 
v_sz_2521_ = lean_array_size(v_content_2517_);
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2521_, v___x_2522_, v_content_2517_);
v___x_2524_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2523_, v___x_2141_, v___y_2519_, v___y_2520_);
lean_dec_ref(v___x_2523_);
v_snd_2525_ = lean_ctor_get(v___x_2524_, 1);
lean_inc(v_snd_2525_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2525_);
return v___x_2526_;
}
}
default: 
{
lean_object* v_view_2531_; lean_object* v___x_2532_; lean_object* v_snd_2533_; lean_object* v___y_2535_; lean_object* v___x_2548_; 
v_view_2531_ = lean_ctor_get(v_val_2287_, 0);
lean_inc_ref(v_view_2531_);
lean_dec_ref_known(v_val_2287_, 1);
v___x_2532_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2106_, v_a_2107_);
v_snd_2533_ = lean_ctor_get(v___x_2532_, 1);
lean_inc(v_snd_2533_);
lean_dec_ref(v___x_2532_);
v___x_2548_ = l_Lean_Syntax_getSubstring_x3f(v_stx_2102_, v___x_2141_, v___x_2141_);
lean_dec(v_stx_2102_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_contents_2549_; lean_object* v___x_2550_; 
v_contents_2549_ = lean_ctor_get(v_view_2531_, 2);
lean_inc(v_contents_2549_);
lean_dec_ref(v_view_2531_);
v___x_2550_ = l_Lean_Syntax_reprint(v_contents_2549_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___y_2535_ = v___x_2551_;
goto v___jp_2534_;
}
else
{
lean_object* v_val_2552_; 
v_val_2552_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v___x_2550_, 1);
v___y_2535_ = v_val_2552_;
goto v___jp_2534_;
}
}
else
{
lean_object* v_val_2553_; lean_object* v_str_2554_; lean_object* v_startPos_2555_; lean_object* v_stopPos_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; 
lean_dec_ref(v_view_2531_);
v_val_2553_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v___x_2548_, 1);
v_str_2554_ = lean_ctor_get(v_val_2553_, 0);
lean_inc_ref(v_str_2554_);
v_startPos_2555_ = lean_ctor_get(v_val_2553_, 1);
lean_inc(v_startPos_2555_);
v_stopPos_2556_ = lean_ctor_get(v_val_2553_, 2);
lean_inc(v_stopPos_2556_);
lean_dec(v_val_2553_);
v___x_2557_ = lean_string_utf8_extract(v_str_2554_, v_startPos_2555_, v_stopPos_2556_);
lean_dec(v_stopPos_2556_);
lean_dec(v_startPos_2555_);
lean_dec_ref(v_str_2554_);
lean_inc(v_a_2106_);
v___x_2558_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2106_, v___x_2557_);
v___x_2559_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2558_, v_snd_2533_);
lean_dec_ref(v___x_2558_);
v_snd_2560_ = lean_ctor_get(v___x_2559_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v___x_2559_);
v___x_2561_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2560_);
return v___x_2561_;
}
v___jp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_snd_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2536_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
v___x_2537_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2536_, v_snd_2533_);
v_snd_2538_ = lean_ctor_get(v___x_2537_, 1);
lean_inc(v_snd_2538_);
lean_dec_ref(v___x_2537_);
lean_inc(v_a_2106_);
v___x_2539_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2106_, v___y_2535_);
v___x_2540_ = lean_string_utf8_byte_size(v___x_2539_);
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = lean_nat_dec_eq(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v_snd_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v_snd_2547_; 
v___x_2543_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2539_, v_snd_2538_);
lean_dec_ref(v___x_2539_);
v_snd_2544_ = lean_ctor_get(v___x_2543_, 1);
lean_inc(v_snd_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2546_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2545_, v_snd_2544_);
v_snd_2547_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_snd_2547_);
lean_dec_ref(v___x_2546_);
v___y_2109_ = v_snd_2547_;
goto v___jp_2108_;
}
else
{
lean_dec_ref(v___x_2539_);
v___y_2109_ = v_snd_2538_;
goto v___jp_2108_;
}
}
}
}
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v___x_2286_);
v___x_2562_ = lean_box(0);
v___x_2563_ = l_Lean_Syntax_formatStx(v_stx_2102_, v___x_2562_, v___x_2141_);
v___x_2564_ = l_Std_Format_defWidth;
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = l_Std_Format_pretty(v___x_2563_, v___x_2564_, v___x_2565_, v___x_2565_);
v___x_2567_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2566_, v_a_2107_);
lean_dec_ref(v___x_2566_);
return v___x_2567_;
}
}
}
}
}
}
else
{
lean_object* v___x_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; 
lean_dec(v_next_x3f_2103_);
v___x_2568_ = l_Lean_Syntax_getArgs(v_stx_2102_);
lean_dec(v_stx_2102_);
v___x_2569_ = 0;
v___x_2570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2568_, v___x_2569_, v_a_2106_, v_a_2107_);
lean_dec_ref(v___x_2568_);
return v___x_2570_;
}
v___jp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
lean_inc(v_a_2106_);
v___x_2111_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2106_, v___x_2110_);
v___x_2112_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_2113_ = lean_string_append(v___x_2111_, v___x_2112_);
v___x_2114_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2113_, v___y_2109_);
lean_dec_ref(v___x_2113_);
v_snd_2115_ = lean_ctor_get(v___x_2114_, 1);
lean_inc(v_snd_2115_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2115_);
return v___x_2116_;
}
v___jp_2117_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v_snd_2132_; lean_object* v___x_2133_; lean_object* v_snd_2134_; lean_object* v___x_2135_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = lean_string_utf8_byte_size(v___y_2122_);
lean_inc_ref(v___y_2122_);
v___x_2125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2125_, 0, v___y_2122_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
lean_ctor_set(v___x_2125_, 2, v___x_2124_);
v___x_2126_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
v___x_2127_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2128_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2120_, v___y_2122_, v___x_2125_, v___x_2124_, v___x_2126_, v___x_2127_);
lean_dec_ref_known(v___x_2125_, 3);
lean_dec_ref(v___y_2122_);
v___x_2129_ = lean_array_to_list(v___x_2128_);
v___x_2130_ = l_String_intercalate(v___y_2119_, v___x_2129_);
v___x_2131_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2130_, v___y_2121_);
lean_dec_ref(v___x_2130_);
v_snd_2132_ = lean_ctor_get(v___x_2131_, 1);
lean_inc(v_snd_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2118_, v_snd_2132_);
lean_dec_ref(v___y_2118_);
v_snd_2134_ = lean_ctor_get(v___x_2133_, 1);
lean_inc(v_snd_2134_);
lean_dec_ref(v___x_2133_);
v___x_2135_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2134_);
return v___x_2135_;
}
v___jp_2136_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v_a_2107_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t v___x_2571_, lean_object* v_as_2572_, size_t v_sz_2573_, size_t v_i_2574_, lean_object* v_b_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_usize_dec_lt(v_i_2574_, v_sz_2573_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_b_2575_);
lean_ctor_set(v___x_2579_, 1, v___y_2577_);
return v___x_2579_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_snd_2582_; lean_object* v_a_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_snd_2586_; lean_object* v___x_2587_; size_t v___x_2588_; size_t v___x_2589_; 
v___x_2580_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2581_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2580_, v___y_2577_);
v_snd_2582_ = lean_ctor_get(v___x_2581_, 1);
lean_inc(v_snd_2582_);
lean_dec_ref(v___x_2581_);
v_a_2583_ = lean_array_uget_borrowed(v_as_2572_, v_i_2574_);
v___x_2584_ = lean_box(0);
lean_inc(v_a_2583_);
v___x_2585_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2583_, v___x_2584_, v___x_2571_, v___x_2571_, v___y_2576_, v_snd_2582_);
v_snd_2586_ = lean_ctor_get(v___x_2585_, 1);
lean_inc(v_snd_2586_);
lean_dec_ref(v___x_2585_);
v___x_2587_ = lean_box(0);
v___x_2588_ = ((size_t)1ULL);
v___x_2589_ = lean_usize_add(v_i_2574_, v___x_2588_);
v_i_2574_ = v___x_2589_;
v_b_2575_ = v___x_2587_;
v___y_2577_ = v_snd_2586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v___x_2591_, lean_object* v_as_2592_, lean_object* v_sz_2593_, lean_object* v_i_2594_, lean_object* v_b_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
uint8_t v___x_62137__boxed_2598_; size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v___x_62137__boxed_2598_ = lean_unbox(v___x_2591_);
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2593_);
lean_dec(v_sz_2593_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_62137__boxed_2598_, v_as_2592_, v_sz_boxed_2599_, v_i_boxed_2600_, v_b_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v_as_2592_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object* v_stxs_2602_, lean_object* v_lineStart_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
uint8_t v_lineStart_boxed_2606_; lean_object* v_res_2607_; 
v_lineStart_boxed_2606_ = lean_unbox(v_lineStart_2603_);
v_res_2607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v_stxs_2602_, v_lineStart_boxed_2606_, v_a_2604_, v_a_2605_);
lean_dec(v_a_2604_);
lean_dec_ref(v_stxs_2602_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object* v___y_2608_, lean_object* v___x_2609_, lean_object* v_as_2610_, lean_object* v_sz_2611_, lean_object* v_i_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
uint8_t v___x_62174__boxed_2616_; size_t v_sz_boxed_2617_; size_t v_i_boxed_2618_; lean_object* v_res_2619_; 
v___x_62174__boxed_2616_ = lean_unbox(v___x_2609_);
v_sz_boxed_2617_ = lean_unbox_usize(v_sz_2611_);
lean_dec(v_sz_2611_);
v_i_boxed_2618_ = lean_unbox_usize(v_i_2612_);
lean_dec(v_i_2612_);
v_res_2619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2608_, v___x_62174__boxed_2616_, v_as_2610_, v_sz_boxed_2617_, v_i_boxed_2618_, v_b_2613_, v___y_2614_, v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v_as_2610_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object* v_char_2620_, lean_object* v_inls_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
uint32_t v_char_boxed_2624_; lean_object* v_res_2625_; 
v_char_boxed_2624_ = lean_unbox_uint32(v_char_2620_);
lean_dec(v_char_2620_);
v_res_2625_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v_char_boxed_2624_, v_inls_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2622_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object* v___x_2626_, lean_object* v_alternate_2627_, lean_object* v_as_2628_, lean_object* v_sz_2629_, lean_object* v_i_2630_, lean_object* v_b_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v___x_62231__boxed_2634_; uint8_t v_alternate_boxed_2635_; size_t v_sz_boxed_2636_; size_t v_i_boxed_2637_; lean_object* v_res_2638_; 
v___x_62231__boxed_2634_ = lean_unbox(v___x_2626_);
v_alternate_boxed_2635_ = lean_unbox(v_alternate_2627_);
v_sz_boxed_2636_ = lean_unbox_usize(v_sz_2629_);
lean_dec(v_sz_2629_);
v_i_boxed_2637_ = lean_unbox_usize(v_i_2630_);
lean_dec(v_i_2630_);
v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_62231__boxed_2634_, v_alternate_boxed_2635_, v_as_2628_, v_sz_boxed_2636_, v_i_boxed_2637_, v_b_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v_as_2628_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object* v___x_2639_, lean_object* v_as_2640_, lean_object* v_sz_2641_, lean_object* v_i_2642_, lean_object* v_b_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
uint8_t v___x_62265__boxed_2646_; size_t v_sz_boxed_2647_; size_t v_i_boxed_2648_; lean_object* v_res_2649_; 
v___x_62265__boxed_2646_ = lean_unbox(v___x_2639_);
v_sz_boxed_2647_ = lean_unbox_usize(v_sz_2641_);
lean_dec(v_sz_2641_);
v_i_boxed_2648_ = lean_unbox_usize(v_i_2642_);
lean_dec(v_i_2642_);
v_res_2649_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_62265__boxed_2646_, v_as_2640_, v_sz_boxed_2647_, v_i_boxed_2648_, v_b_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v_as_2640_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object* v_upperBound_2650_, lean_object* v___y_2651_, lean_object* v_a_2652_, lean_object* v_b_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2650_, v___y_2651_, v_a_2652_, v_b_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2651_);
lean_dec(v_upperBound_2650_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object* v_stx_2657_, lean_object* v_next_x3f_2658_, lean_object* v_atLineStart_2659_, lean_object* v_alternate_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
uint8_t v_atLineStart_boxed_2663_; uint8_t v_alternate_boxed_2664_; lean_object* v_res_2665_; 
v_atLineStart_boxed_2663_ = lean_unbox(v_atLineStart_2659_);
v_alternate_boxed_2664_ = lean_unbox(v_alternate_2660_);
v_res_2665_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2657_, v_next_x3f_2658_, v_atLineStart_boxed_2663_, v_alternate_boxed_2664_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2661_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object* v_s_2666_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object* v_s_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(v_s_2668_);
lean_dec_ref(v_s_2668_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object* v_upperBound_2670_, lean_object* v___y_2671_, lean_object* v_inst_2672_, lean_object* v_R_2673_, lean_object* v_a_2674_, lean_object* v_b_2675_, lean_object* v_c_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2670_, v___y_2671_, v_a_2674_, v_b_2675_, v___y_2677_, v___y_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object* v_upperBound_2680_, lean_object* v___y_2681_, lean_object* v_inst_2682_, lean_object* v_R_2683_, lean_object* v_a_2684_, lean_object* v_b_2685_, lean_object* v_c_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(v_upperBound_2680_, v___y_2681_, v_inst_2682_, v_R_2683_, v_a_2684_, v_b_2685_, v_c_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2681_);
lean_dec(v_upperBound_2680_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___x_2692_, lean_object* v___x_2693_, lean_object* v_inst_2694_, lean_object* v_R_2695_, lean_object* v_a_2696_, lean_object* v_b_2697_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2690_, v___y_2691_, v___x_2692_, v___x_2693_, v_a_2696_, v_b_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___x_2701_, lean_object* v___x_2702_, lean_object* v_inst_2703_, lean_object* v_R_2704_, lean_object* v_a_2705_, lean_object* v_b_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(v___y_2699_, v___y_2700_, v___x_2701_, v___x_2702_, v_inst_2703_, v_R_2704_, v_a_2705_, v_b_2706_);
lean_dec_ref(v___x_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object* v_s_2708_, lean_object* v_pos_2709_){
_start:
{
lean_object* v_str_2710_; lean_object* v_startInclusive_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v_decide_2715_; 
v_str_2710_ = lean_ctor_get(v_s_2708_, 0);
v_startInclusive_2711_ = lean_ctor_get(v_s_2708_, 1);
v___x_2712_ = lean_nat_add(v_startInclusive_2711_, v_pos_2709_);
v___x_2713_ = lean_nat_sub(v___x_2712_, v_startInclusive_2711_);
v___x_2714_ = lean_unsigned_to_nat(0u);
v_decide_2715_ = lean_nat_dec_eq(v___x_2713_, v___x_2714_);
if (v_decide_2715_ == 0)
{
uint32_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint32_t v___x_2722_; uint8_t v___x_2723_; 
v___x_2716_ = 10;
lean_inc(v_startInclusive_2711_);
lean_inc_ref(v_str_2710_);
v___x_2717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2717_, 0, v_str_2710_);
lean_ctor_set(v___x_2717_, 1, v_startInclusive_2711_);
lean_ctor_set(v___x_2717_, 2, v___x_2712_);
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = lean_nat_sub(v___x_2713_, v___x_2718_);
lean_dec(v___x_2713_);
v___x_2720_ = l_String_Slice_posLE(v___x_2717_, v___x_2719_);
lean_dec_ref_known(v___x_2717_, 3);
v___x_2721_ = lean_nat_add(v_startInclusive_2711_, v___x_2720_);
v___x_2722_ = lean_string_utf8_get_fast(v_str_2710_, v___x_2721_);
lean_dec(v___x_2721_);
v___x_2723_ = lean_uint32_dec_eq(v___x_2722_, v___x_2716_);
if (v___x_2723_ == 0)
{
lean_dec(v___x_2720_);
return v_pos_2709_;
}
else
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2724_ = lean_nat_add(v___x_2720_, v___x_2718_);
v___x_2725_ = lean_nat_dec_le(v___x_2724_, v_pos_2709_);
lean_dec(v___x_2724_);
if (v___x_2725_ == 0)
{
lean_dec(v___x_2720_);
return v_pos_2709_;
}
else
{
lean_dec(v_pos_2709_);
v_pos_2709_ = v___x_2720_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2713_);
lean_dec(v___x_2712_);
return v_pos_2709_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object* v_s_2727_, lean_object* v_pos_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v_s_2727_, v_pos_2728_);
lean_dec_ref(v_s_2727_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object* v_s_2730_){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2731_ = lean_string_utf8_byte_size(v_s_2730_);
v___x_2732_ = lean_unsigned_to_nat(1u);
v___x_2733_ = lean_nat_dec_le(v___x_2732_, v___x_2731_);
if (v___x_2733_ == 0)
{
return v_s_2730_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2734_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2735_ = lean_unsigned_to_nat(0u);
v___x_2736_ = lean_nat_sub(v___x_2731_, v___x_2732_);
v___x_2737_ = lean_string_memcmp(v_s_2730_, v___x_2734_, v___x_2736_, v___x_2735_, v___x_2732_);
lean_dec(v___x_2736_);
if (v___x_2737_ == 0)
{
return v_s_2730_;
}
else
{
uint32_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2738_ = 10;
lean_inc_ref(v_s_2730_);
v___x_2739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2739_, 0, v_s_2730_);
lean_ctor_set(v___x_2739_, 1, v___x_2735_);
lean_ctor_set(v___x_2739_, 2, v___x_2731_);
v___x_2740_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v___x_2739_, v___x_2731_);
lean_dec_ref_known(v___x_2739_, 3);
v___x_2741_ = lean_string_utf8_extract_fast(v_s_2730_, v___x_2735_, v___x_2740_);
lean_dec(v___x_2740_);
lean_dec_ref(v_s_2730_);
v___x_2742_ = lean_string_push(v___x_2741_, v___x_2738_);
return v___x_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object* v_stx_2743_, uint8_t v_alternate_2744_){
_start:
{
lean_object* v___x_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v_snd_2750_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = 0;
v___x_2747_ = lean_unsigned_to_nat(0u);
v___x_2748_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2749_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2743_, v___x_2745_, v___x_2746_, v_alternate_2744_, v___x_2747_, v___x_2748_);
v_snd_2750_ = lean_ctor_get(v___x_2749_, 1);
lean_inc(v_snd_2750_);
lean_dec_ref(v___x_2749_);
return v_snd_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object* v_stx_2751_, lean_object* v_alternate_2752_){
_start:
{
uint8_t v_alternate_boxed_2753_; lean_object* v_res_2754_; 
v_alternate_boxed_2753_ = lean_unbox(v_alternate_2752_);
v_res_2754_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2751_, v_alternate_boxed_2753_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_2755_, uint8_t v_alternate_2756_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2755_, v_alternate_2756_);
v___x_2758_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object* v_stx_2759_, lean_object* v_alternate_2760_){
_start:
{
uint8_t v_alternate_boxed_2761_; lean_object* v_res_2762_; 
v_alternate_boxed_2761_ = lean_unbox(v_alternate_2760_);
v_res_2762_ = l_Lean_Doc_Parser_versoSyntaxToString(v_stx_2759_, v_alternate_boxed_2761_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object* v_b_2763_, lean_object* v___y_2764_){
_start:
{
uint8_t v___x_2765_; 
lean_inc(v_b_2763_);
v___x_2765_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_b_2763_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; uint8_t v___y_2768_; 
lean_inc(v_b_2763_);
v___x_2766_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v___y_2764_, v_b_2763_);
lean_dec(v___y_2764_);
if (lean_obj_tag(v___x_2766_) == 0)
{
v___y_2768_ = v___x_2765_;
goto v___jp_2767_;
}
else
{
lean_object* v_val_2771_; uint8_t v_alternate_2772_; 
v_val_2771_ = lean_ctor_get(v___x_2766_, 0);
v_alternate_2772_ = lean_ctor_get_uint8(v_val_2771_, 1);
v___y_2768_ = v_alternate_2772_;
goto v___jp_2767_;
}
v___jp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_b_2763_, v___y_2768_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___x_2766_);
return v___x_2770_;
}
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec(v_b_2763_);
v___x_2773_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v___y_2764_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object* v_n_2775_, lean_object* v_f_2776_, lean_object* v_xs_2777_, lean_object* v_k_2778_, lean_object* v_acc_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_nat_dec_lt(v_k_2778_, v_n_2775_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; 
lean_dec(v_k_2778_);
lean_dec_ref(v_f_2776_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_acc_2779_);
lean_ctor_set(v___x_2782_, 1, v___y_2780_);
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2783_ = lean_array_fget_borrowed(v_xs_2777_, v_k_2778_);
lean_inc_ref(v_f_2776_);
lean_inc(v___x_2783_);
v___x_2784_ = lean_apply_2(v_f_2776_, v___x_2783_, v___y_2780_);
v_fst_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_fst_2785_);
v_snd_2786_ = lean_ctor_get(v___x_2784_, 1);
lean_inc(v_snd_2786_);
lean_dec_ref(v___x_2784_);
v___x_2787_ = lean_unsigned_to_nat(1u);
v___x_2788_ = lean_nat_add(v_k_2778_, v___x_2787_);
lean_dec(v_k_2778_);
v___x_2789_ = lean_array_push(v_acc_2779_, v_fst_2785_);
v_k_2778_ = v___x_2788_;
v_acc_2779_ = v___x_2789_;
v___y_2780_ = v_snd_2786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object* v_n_2791_, lean_object* v_f_2792_, lean_object* v_xs_2793_, lean_object* v_k_2794_, lean_object* v_acc_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2791_, v_f_2792_, v_xs_2793_, v_k_2794_, v_acc_2795_, v___y_2796_);
lean_dec_ref(v_xs_2793_);
lean_dec(v_n_2791_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object* v_blocks_2799_){
_start:
{
lean_object* v___f_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v_fst_2806_; 
v___f_2800_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0));
v___x_2801_ = lean_array_get_size(v_blocks_2799_);
v___x_2802_ = lean_unsigned_to_nat(0u);
v___x_2803_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2804_ = lean_box(0);
v___x_2805_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v___x_2801_, v___f_2800_, v_blocks_2799_, v___x_2802_, v___x_2803_, v___x_2804_);
v_fst_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_fst_2806_);
lean_dec_ref(v___x_2805_);
return v_fst_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object* v_blocks_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2807_);
lean_dec_ref(v_blocks_2807_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object* v_00_u03b1_2809_, lean_object* v_00_u03b2_2810_, lean_object* v_n_2811_, lean_object* v_f_2812_, lean_object* v_xs_2813_, lean_object* v_k_2814_, lean_object* v_h_2815_, lean_object* v_acc_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2811_, v_f_2812_, v_xs_2813_, v_k_2814_, v_acc_2816_, v___y_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object* v_00_u03b1_2819_, lean_object* v_00_u03b2_2820_, lean_object* v_n_2821_, lean_object* v_f_2822_, lean_object* v_xs_2823_, lean_object* v_k_2824_, lean_object* v_h_2825_, lean_object* v_acc_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(v_00_u03b1_2819_, v_00_u03b2_2820_, v_n_2821_, v_f_2822_, v_xs_2823_, v_k_2824_, v_h_2825_, v_acc_2826_, v___y_2827_);
lean_dec_ref(v_xs_2823_);
lean_dec(v_n_2821_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object* v_as_2829_, size_t v_i_2830_, size_t v_stop_2831_, lean_object* v_b_2832_){
_start:
{
uint8_t v___x_2833_; 
v___x_2833_ = lean_usize_dec_eq(v_i_2830_, v_stop_2831_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; size_t v___x_2836_; size_t v___x_2837_; 
v___x_2834_ = lean_array_uget_borrowed(v_as_2829_, v_i_2830_);
v___x_2835_ = lean_string_append(v_b_2832_, v___x_2834_);
v___x_2836_ = ((size_t)1ULL);
v___x_2837_ = lean_usize_add(v_i_2830_, v___x_2836_);
v_i_2830_ = v___x_2837_;
v_b_2832_ = v___x_2835_;
goto _start;
}
else
{
return v_b_2832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object* v_as_2839_, lean_object* v_i_2840_, lean_object* v_stop_2841_, lean_object* v_b_2842_){
_start:
{
size_t v_i_boxed_2843_; size_t v_stop_boxed_2844_; lean_object* v_res_2845_; 
v_i_boxed_2843_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_stop_boxed_2844_ = lean_unbox_usize(v_stop_2841_);
lean_dec(v_stop_2841_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v_as_2839_, v_i_boxed_2843_, v_stop_boxed_2844_, v_b_2842_);
lean_dec_ref(v_as_2839_);
return v_res_2845_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0(void){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2847_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object* v_blocks_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2849_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2850_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2848_);
v___x_2851_ = lean_unsigned_to_nat(0u);
v___x_2852_ = lean_array_get_size(v___x_2850_);
v___x_2853_ = lean_nat_dec_lt(v___x_2851_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref(v___x_2850_);
v___x_2854_ = lean_obj_once(&l_Lean_Doc_Parser_versoDocumentToString___closed__0, &l_Lean_Doc_Parser_versoDocumentToString___closed__0_once, _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0);
return v___x_2854_;
}
else
{
size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = lean_usize_of_nat(v___x_2852_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v___x_2850_, v___x_2855_, v___x_2856_, v___x_2849_);
lean_dec_ref(v___x_2850_);
v___x_2858_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2857_);
return v___x_2858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object* v_blocks_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_Doc_Parser_versoDocumentToString(v_blocks_2859_);
lean_dec_ref(v_blocks_2859_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; lean_object* v_stxTrav_2864_; lean_object* v_cur_2865_; lean_object* v___x_2866_; 
v___x_2863_ = lean_st_ref_get(v___y_2861_);
v_stxTrav_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc_ref(v_stxTrav_2864_);
lean_dec(v___x_2863_);
v_cur_2865_ = lean_ctor_get(v_stxTrav_2864_, 0);
lean_inc(v_cur_2865_);
lean_dec_ref(v_stxTrav_2864_);
v___x_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2866_, 0, v_cur_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2867_);
lean_dec(v___y_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2871_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object* v___y_2882_){
_start:
{
lean_object* v___x_2884_; lean_object* v_stxTrav_2885_; lean_object* v_leadWord_2886_; uint8_t v_leadWordIdent_2887_; uint8_t v_isUngrouped_2888_; uint8_t v_mustBeGrouped_2889_; lean_object* v_stack_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2901_; 
v___x_2884_ = lean_st_ref_take(v___y_2882_);
v_stxTrav_2885_ = lean_ctor_get(v___x_2884_, 0);
v_leadWord_2886_ = lean_ctor_get(v___x_2884_, 1);
v_leadWordIdent_2887_ = lean_ctor_get_uint8(v___x_2884_, sizeof(void*)*3);
v_isUngrouped_2888_ = lean_ctor_get_uint8(v___x_2884_, sizeof(void*)*3 + 1);
v_mustBeGrouped_2889_ = lean_ctor_get_uint8(v___x_2884_, sizeof(void*)*3 + 2);
v_stack_2890_ = lean_ctor_get(v___x_2884_, 2);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2892_ = v___x_2884_;
v_isShared_2893_ = v_isSharedCheck_2901_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_stack_2890_);
lean_inc(v_leadWord_2886_);
lean_inc(v_stxTrav_2885_);
lean_dec(v___x_2884_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2901_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2894_ = lean_box(0);
v___x_2895_ = l_Lean_Syntax_Traverser_left(v_stxTrav_2885_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2895_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_leadWord_2886_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_stack_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3, v_leadWordIdent_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3 + 1, v_isUngrouped_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3 + 2, v_mustBeGrouped_2889_);
v___x_2897_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_st_ref_put(v___y_2882_, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2894_);
return v___x_2899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2902_);
lean_dec(v___y_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2906_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object* v_upperBound_2917_, lean_object* v___x_2918_, lean_object* v_rendered_2919_, lean_object* v_a_2920_, lean_object* v_b_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_nat_dec_lt(v_a_2920_, v_upperBound_2917_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; 
lean_dec(v_a_2920_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_b_2921_);
return v___x_2928_;
}
else
{
lean_object* v___x_2929_; lean_object* v___y_2931_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v___x_2929_ = lean_box(0);
v___x_2937_ = lean_unsigned_to_nat(0u);
v___x_2938_ = lean_unsigned_to_nat(1u);
v___x_2939_ = lean_nat_sub(v___x_2918_, v___x_2938_);
v___x_2940_ = lean_nat_sub(v___x_2939_, v_a_2920_);
lean_dec(v___x_2939_);
v___x_2941_ = lean_array_fget_borrowed(v_rendered_2919_, v___x_2940_);
lean_dec(v___x_2940_);
v___x_2942_ = lean_nat_dec_eq(v_a_2920_, v___x_2937_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_inc(v___x_2941_);
v___x_2943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
v___y_2931_ = v___x_2943_;
goto v___jp_2930_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_inc(v___x_2941_);
v___x_2944_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2941_);
v___x_2945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
v___y_2931_ = v___x_2945_;
goto v___jp_2930_;
}
v___jp_2930_:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___y_2931_, v___y_2923_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; 
lean_dec_ref_known(v___x_2932_, 1);
v___x_2933_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2923_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec_ref_known(v___x_2933_, 1);
v___x_2934_ = lean_unsigned_to_nat(1u);
v___x_2935_ = lean_nat_add(v_a_2920_, v___x_2934_);
lean_dec(v_a_2920_);
v_a_2920_ = v___x_2935_;
v_b_2921_ = v___x_2929_;
goto _start;
}
else
{
lean_dec(v_a_2920_);
return v___x_2933_;
}
}
else
{
lean_dec(v_a_2920_);
return v___x_2932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object* v_upperBound_2946_, lean_object* v___x_2947_, lean_object* v_rendered_2948_, lean_object* v_a_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_2946_, v___x_2947_, v_rendered_2948_, v_a_2949_, v_b_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v_rendered_2948_);
lean_dec(v___x_2947_);
lean_dec(v_upperBound_2946_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_2957_, lean_object* v_rendered_2958_, lean_object* v___x_2959_, lean_object* v___x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v___x_2957_, v___x_2957_, v_rendered_2958_, v___x_2959_, v___x_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v___x_2966_, 0);
lean_dec(v_unused_2974_);
v___x_2968_ = v___x_2966_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_dec(v___x_2966_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2960_);
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2960_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
else
{
return v___x_2966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_2975_, lean_object* v_rendered_2976_, lean_object* v___x_2977_, lean_object* v___x_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_2975_, v_rendered_2976_, v___x_2977_, v___x_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v_rendered_2976_);
lean_dec(v___x_2975_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v_blocks_2992_; lean_object* v_rendered_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___f_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2990_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2986_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2990_);
v_blocks_2992_ = l_Lean_TSyntax_getVersoBlocks(v_a_2991_);
lean_dec(v_a_2991_);
v_rendered_2993_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2992_);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_array_get_size(v_blocks_2992_);
lean_dec_ref(v_blocks_2992_);
v___x_2996_ = lean_box(0);
v___f_2997_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2997_, 0, v___x_2995_);
lean_closure_set(v___f_2997_, 1, v_rendered_2993_);
lean_closure_set(v___f_2997_, 2, v___x_2994_);
lean_closure_set(v___f_2997_, 3, v___x_2996_);
v___x_2998_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs___boxed), 6, 1);
lean_closure_set(v___x_2998_, 0, v___f_2997_);
v___x_2999_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_2998_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v___f_3012_; lean_object* v___x_3013_; 
v___f_3012_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_3013_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_3012_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Doc_Parser_document_formatter(v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
lean_dec(v_a_3017_);
lean_dec_ref(v_a_3016_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object* v_upperBound_3020_, lean_object* v___x_3021_, lean_object* v_rendered_3022_, lean_object* v_inst_3023_, lean_object* v_R_3024_, lean_object* v_a_3025_, lean_object* v_b_3026_, lean_object* v_c_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_3020_, v___x_3021_, v_rendered_3022_, v_a_3025_, v_b_3026_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object* v_upperBound_3034_, lean_object* v___x_3035_, lean_object* v_rendered_3036_, lean_object* v_inst_3037_, lean_object* v_R_3038_, lean_object* v_a_3039_, lean_object* v_b_3040_, lean_object* v_c_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(v_upperBound_3034_, v___x_3035_, v_rendered_3036_, v_inst_3037_, v_R_3038_, v_a_3039_, v_b_3040_, v_c_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec_ref(v_rendered_3036_);
lean_dec(v___x_3035_);
lean_dec(v_upperBound_3034_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1(){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v___x_3065_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3066_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4));
v___x_3067_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6));
v___x_3068_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___boxed), 5, 0);
v___x_3069_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3065_, v___x_3066_, v___x_3067_, v___x_3068_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
return v_res_3071_;
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
