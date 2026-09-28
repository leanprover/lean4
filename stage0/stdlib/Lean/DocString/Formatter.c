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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(uint8_t v_x_46_){
_start:
{
if (v_x_46_ == 0)
{
lean_object* v___x_47_; 
v___x_47_ = lean_unsigned_to_nat(0u);
return v___x_47_;
}
else
{
lean_object* v___x_48_; 
v___x_48_ = lean_unsigned_to_nat(1u);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx___boxed(lean_object* v_x_49_){
_start:
{
uint8_t v_x_boxed_50_; lean_object* v_res_51_; 
v_x_boxed_50_ = lean_unbox(v_x_49_);
v_res_51_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(v_x_boxed_50_);
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
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(v_x_93_);
v___x_96_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_ListKind_ctorIdx(v_y_94_);
v___x_97_ = lean_nat_dec_eq(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
lean_dec(v___x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq___boxed(lean_object* v_x_98_, lean_object* v_y_99_){
_start:
{
uint8_t v_x_21__boxed_100_; uint8_t v_y_22__boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_x_21__boxed_100_ = lean_unbox(v_x_98_);
v_y_22__boxed_101_ = lean_unbox(v_y_99_);
v_res_102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v_x_21__boxed_100_, v_y_22__boxed_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(lean_object* v_stx_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Doc_BlockView_of(v_stx_112_);
if (lean_obj_tag(v___x_113_) == 1)
{
lean_object* v_val_114_; 
v_val_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v___x_113_, 1);
switch(lean_obj_tag(v_val_114_))
{
case 1:
{
lean_object* v___x_115_; 
lean_dec_ref_known(v_val_114_, 1);
v___x_115_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__0));
return v___x_115_;
}
case 2:
{
lean_object* v___x_116_; 
lean_dec_ref_known(v_val_114_, 1);
v___x_116_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f___closed__1));
return v___x_116_;
}
default: 
{
lean_object* v___x_117_; 
lean_dec(v_val_114_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
}
else
{
lean_object* v___x_118_; 
lean_dec(v___x_113_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(lean_object* v_prev_x3f_119_, lean_object* v_stx_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_listKind_x3f(v_stx_120_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v_val_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_141_; 
v_val_123_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_141_ == 0)
{
v___x_125_ = v___x_121_;
v_isShared_126_ = v_isSharedCheck_141_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_val_123_);
lean_dec(v___x_121_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_141_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v___y_128_; 
if (lean_obj_tag(v_prev_x3f_119_) == 0)
{
uint8_t v___x_134_; 
v___x_134_ = 0;
v___y_128_ = v___x_134_;
goto v___jp_127_;
}
else
{
lean_object* v_val_135_; uint8_t v_kind_136_; uint8_t v_alternate_137_; uint8_t v___x_138_; uint8_t v___x_139_; 
v_val_135_ = lean_ctor_get(v_prev_x3f_119_, 0);
v_kind_136_ = lean_ctor_get_uint8(v_val_135_, 0);
v_alternate_137_ = lean_ctor_get_uint8(v_val_135_, 1);
v___x_138_ = lean_unbox(v_val_123_);
v___x_139_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_instBEqListKind_beq(v___x_138_, v_kind_136_);
if (v___x_139_ == 0)
{
v___y_128_ = v___x_139_;
goto v___jp_127_;
}
else
{
if (v_alternate_137_ == 0)
{
v___y_128_ = v___x_139_;
goto v___jp_127_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
v___y_128_ = v___x_140_;
goto v___jp_127_;
}
}
}
v___jp_127_:
{
lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_132_; 
v___x_129_ = lean_alloc_ctor(0, 0, 2);
v___x_130_ = lean_unbox(v_val_123_);
lean_dec(v_val_123_);
lean_ctor_set_uint8(v___x_129_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_129_, 1, v___y_128_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_129_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor___boxed(lean_object* v_prev_x3f_142_, lean_object* v_stx_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_prev_x3f_142_, v_stx_143_);
lean_dec(v_prev_x3f_142_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(lean_object* v_s_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = lean_string_append(v_a_146_, v_s_145_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg___boxed(lean_object* v_s_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_150_, v_a_151_);
lean_dec_ref(v_s_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(lean_object* v_s_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_s_153_, v_a_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___boxed(lean_object* v_s_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out(v_s_157_, v_a_158_, v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_s_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_zero_163_; uint8_t v_isZero_164_; 
v_zero_163_ = lean_unsigned_to_nat(0u);
v_isZero_164_ = lean_nat_dec_eq(v_x_161_, v_zero_163_);
if (v_isZero_164_ == 1)
{
lean_dec(v_x_161_);
return v_x_162_;
}
else
{
uint32_t v___x_165_; lean_object* v_one_166_; lean_object* v_n_167_; lean_object* v___x_168_; 
v___x_165_ = 32;
v_one_166_ = lean_unsigned_to_nat(1u);
v_n_167_ = lean_nat_sub(v_x_161_, v_one_166_);
lean_dec(v_x_161_);
v___x_168_ = lean_string_push(v_x_162_, v___x_165_);
v_x_161_ = v_n_167_;
v_x_162_ = v___x_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_177_ = lean_string_utf8_byte_size(v_a_173_);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_dec_le(v___x_178_, v___x_177_);
if (v___x_179_ == 0)
{
goto v___jp_174_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_180_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_nat_sub(v___x_177_, v___x_178_);
v___x_183_ = lean_string_memcmp(v_a_173_, v___x_180_, v___x_182_, v___x_181_, v___x_178_);
lean_dec(v___x_182_);
if (v___x_183_ == 0)
{
goto v___jp_174_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
lean_inc(v_a_172_);
v___x_185_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_172_, v___x_184_);
v___x_186_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_185_, v_a_173_);
lean_dec_ref(v___x_185_);
return v___x_186_;
}
}
v___jp_174_:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_173_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___boxed(lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_187_, v_a_188_);
lean_dec(v_a_187_);
return v_res_189_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(uint8_t v___x_190_, lean_object* v___x_191_, lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v_a_194_, uint8_t v_b_195_){
_start:
{
lean_object* v___x_196_; uint8_t v_decide_197_; 
v___x_196_ = lean_nat_sub(v___x_191_, v___x_192_);
v_decide_197_ = lean_nat_dec_eq(v_a_194_, v___x_196_);
lean_dec(v___x_196_);
if (v_decide_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_nat_add(v___x_192_, v_a_194_);
lean_dec(v_a_194_);
v___x_199_ = lean_string_utf8_next_fast(v___x_193_, v___x_198_);
lean_dec(v___x_198_);
v___x_200_ = lean_nat_sub(v___x_199_, v___x_192_);
if (v_b_195_ == 0)
{
{
lean_object* _tmp_4 = v___x_200_;
uint8_t _tmp_5 = v___x_190_;
v_a_194_ = _tmp_4;
v_b_195_ = _tmp_5;
}
goto _start;
}
else
{
v_a_194_ = v___x_200_;
v_b_195_ = v_decide_197_;
goto _start;
}
}
else
{
lean_dec(v_a_194_);
return v_b_195_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg___boxed(lean_object* v___x_203_, lean_object* v___x_204_, lean_object* v___x_205_, lean_object* v___x_206_, lean_object* v_a_207_, lean_object* v_b_208_){
_start:
{
uint8_t v___x_1744__boxed_209_; uint8_t v_b_boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v___x_1744__boxed_209_ = lean_unbox(v___x_203_);
v_b_boxed_210_ = lean_unbox(v_b_208_);
v_res_211_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_1744__boxed_209_, v___x_204_, v___x_205_, v___x_206_, v_a_207_, v_b_boxed_210_);
lean_dec_ref(v___x_206_);
lean_dec(v___x_205_);
lean_dec(v___x_204_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(lean_object* v_s_213_, lean_object* v_pos_214_){
_start:
{
lean_object* v_str_215_; lean_object* v_startInclusive_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v_decide_220_; 
v_str_215_ = lean_ctor_get(v_s_213_, 0);
v_startInclusive_216_ = lean_ctor_get(v_s_213_, 1);
v___x_217_ = lean_nat_add(v_startInclusive_216_, v_pos_214_);
v___x_218_ = lean_nat_sub(v___x_217_, v_startInclusive_216_);
v___x_219_ = lean_unsigned_to_nat(0u);
v_decide_220_ = lean_nat_dec_eq(v___x_218_, v___x_219_);
if (v_decide_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint32_t v___x_226_; uint32_t v___x_227_; uint8_t v___x_228_; 
lean_inc(v_startInclusive_216_);
lean_inc_ref(v_str_215_);
v___x_221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_221_, 0, v_str_215_);
lean_ctor_set(v___x_221_, 1, v_startInclusive_216_);
lean_ctor_set(v___x_221_, 2, v___x_217_);
v___x_222_ = lean_unsigned_to_nat(1u);
v___x_223_ = lean_nat_sub(v___x_218_, v___x_222_);
lean_dec(v___x_218_);
v___x_224_ = l_String_Slice_posLE(v___x_221_, v___x_223_);
lean_dec_ref_known(v___x_221_, 3);
v___x_225_ = lean_nat_add(v_startInclusive_216_, v___x_224_);
v___x_226_ = lean_string_utf8_get_fast(v_str_215_, v___x_225_);
lean_dec(v___x_225_);
v___x_227_ = 92;
v___x_228_ = lean_uint32_dec_eq(v___x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec(v___x_224_);
return v_pos_214_;
}
else
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = lean_nat_add(v___x_224_, v___x_222_);
v___x_230_ = lean_nat_dec_le(v___x_229_, v_pos_214_);
lean_dec(v___x_229_);
if (v___x_230_ == 0)
{
lean_dec(v___x_224_);
return v_pos_214_;
}
else
{
lean_dec(v_pos_214_);
v_pos_214_ = v___x_224_;
goto _start;
}
}
}
else
{
lean_dec(v___x_218_);
lean_dec(v___x_217_);
return v_pos_214_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0___boxed(lean_object* v_s_232_, lean_object* v_pos_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v_s_232_, v_pos_233_);
lean_dec_ref(v_s_232_);
return v_res_234_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(lean_object* v_s_235_){
_start:
{
lean_object* v_str_236_; lean_object* v_startInclusive_237_; lean_object* v_endExclusive_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_str_236_ = lean_ctor_get(v_s_235_, 0);
lean_inc_ref(v_str_236_);
v_startInclusive_237_ = lean_ctor_get(v_s_235_, 1);
lean_inc(v_startInclusive_237_);
v_endExclusive_238_ = lean_ctor_get(v_s_235_, 2);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_sub(v_endExclusive_238_, v_startInclusive_237_);
v___x_241_ = lean_nat_dec_le(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_dec(v___x_240_);
lean_dec(v_startInclusive_237_);
lean_dec_ref(v_str_236_);
lean_dec_ref(v_s_235_);
return v___x_241_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_242_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_nat_sub(v___x_240_, v___x_239_);
v___x_245_ = lean_nat_add(v_startInclusive_237_, v___x_244_);
lean_dec(v___x_244_);
v___x_246_ = lean_string_memcmp(v_str_236_, v___x_242_, v___x_245_, v___x_243_, v___x_239_);
lean_dec(v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v___x_240_);
lean_dec(v_startInclusive_237_);
lean_dec_ref(v_str_236_);
lean_dec_ref(v_s_235_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_260_; 
v___x_247_ = l_String_Slice_Pos_prevn(v_s_235_, v___x_240_, v___x_239_);
v_isSharedCheck_260_ = !lean_is_exclusive(v_s_235_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_261_ = lean_ctor_get(v_s_235_, 2);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_s_235_, 1);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_s_235_, 0);
lean_dec(v_unused_263_);
v___x_249_ = v_s_235_;
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
else
{
lean_dec(v_s_235_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_260_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_nat_add(v_startInclusive_237_, v___x_247_);
lean_dec(v___x_247_);
lean_inc(v___x_251_);
lean_inc(v_startInclusive_237_);
lean_inc_ref(v_str_236_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 2, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_str_236_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_startInclusive_237_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v___x_251_);
v___x_253_ = v_reuseFailAlloc_259_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; uint8_t v___x_258_; 
v___x_254_ = lean_nat_sub(v___x_251_, v_startInclusive_237_);
v___x_255_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v___x_253_, v___x_254_);
lean_dec_ref(v___x_253_);
v___x_256_ = lean_nat_add(v_startInclusive_237_, v___x_255_);
lean_dec(v___x_255_);
lean_dec(v_startInclusive_237_);
v___x_257_ = 0;
v___x_258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_246_, v___x_251_, v___x_256_, v_str_236_, v___x_243_, v___x_257_);
lean_dec_ref(v_str_236_);
lean_dec(v___x_256_);
lean_dec(v___x_251_);
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline___boxed(lean_object* v_s_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_264_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(uint8_t v___x_267_, lean_object* v___x_268_, lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v___x_271_, lean_object* v_inst_272_, lean_object* v_R_273_, lean_object* v_a_274_, uint8_t v_b_275_, lean_object* v_c_276_){
_start:
{
uint8_t v___x_277_; 
v___x_277_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_267_, v___x_268_, v___x_269_, v___x_271_, v_a_274_, v_b_275_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___boxed(lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v___x_282_, lean_object* v_inst_283_, lean_object* v_R_284_, lean_object* v_a_285_, lean_object* v_b_286_, lean_object* v_c_287_){
_start:
{
uint8_t v___x_1851__boxed_288_; uint8_t v_b_boxed_289_; uint8_t v_res_290_; lean_object* v_r_291_; 
v___x_1851__boxed_288_ = lean_unbox(v___x_278_);
v_b_boxed_289_ = lean_unbox(v_b_286_);
v_res_290_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(v___x_1851__boxed_288_, v___x_279_, v___x_280_, v___x_281_, v___x_282_, v_inst_283_, v_R_284_, v_a_285_, v_b_boxed_289_, v_c_287_);
lean_dec_ref(v___x_282_);
lean_dec_ref(v___x_281_);
lean_dec(v___x_280_);
lean_dec(v___x_279_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(lean_object* v_s_292_){
_start:
{
lean_object* v_str_293_; lean_object* v_startInclusive_294_; lean_object* v_endExclusive_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_str_293_ = lean_ctor_get(v_s_292_, 0);
lean_inc_ref(v_str_293_);
v_startInclusive_294_ = lean_ctor_get(v_s_292_, 1);
lean_inc(v_startInclusive_294_);
v_endExclusive_295_ = lean_ctor_get(v_s_292_, 2);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_sub(v_endExclusive_295_, v_startInclusive_294_);
v___x_298_ = lean_nat_dec_le(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec(v___x_297_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
lean_dec_ref(v_s_292_);
v___x_299_ = lean_unsigned_to_nat(0u);
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_300_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_nat_sub(v___x_297_, v___x_296_);
v___x_303_ = lean_nat_add(v_startInclusive_294_, v___x_302_);
lean_dec(v___x_302_);
v___x_304_ = lean_string_memcmp(v_str_293_, v___x_300_, v___x_303_, v___x_301_, v___x_296_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
lean_dec(v___x_297_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
lean_dec_ref(v_s_292_);
return v___x_301_;
}
else
{
uint8_t v___x_305_; 
lean_inc_ref(v_s_292_);
v___x_305_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_292_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_321_; 
v___x_306_ = l_String_Slice_Pos_prevn(v_s_292_, v___x_297_, v___x_296_);
v_isSharedCheck_321_ = !lean_is_exclusive(v_s_292_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; lean_object* v_unused_323_; lean_object* v_unused_324_; 
v_unused_322_ = lean_ctor_get(v_s_292_, 2);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_s_292_, 1);
lean_dec(v_unused_323_);
v_unused_324_ = lean_ctor_get(v_s_292_, 0);
lean_dec(v_unused_324_);
v___x_308_ = v_s_292_;
v_isShared_309_ = v_isSharedCheck_321_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_s_292_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_321_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_nat_add(v_startInclusive_294_, v___x_306_);
lean_dec(v___x_306_);
v___x_311_ = lean_nat_sub(v___x_310_, v_startInclusive_294_);
v___x_312_ = lean_nat_dec_le(v___x_296_, v___x_311_);
if (v___x_312_ == 0)
{
lean_dec(v___x_311_);
lean_dec(v___x_310_);
lean_del_object(v___x_308_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
return v___x_296_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_nat_sub(v___x_311_, v___x_296_);
lean_dec(v___x_311_);
v___x_314_ = lean_nat_add(v_startInclusive_294_, v___x_313_);
lean_dec(v___x_313_);
v___x_315_ = lean_string_memcmp(v_str_293_, v___x_300_, v___x_314_, v___x_301_, v___x_296_);
lean_dec(v___x_314_);
if (v___x_315_ == 0)
{
lean_dec(v___x_310_);
lean_del_object(v___x_308_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
return v___x_296_;
}
else
{
if (v___x_305_ == 0)
{
lean_object* v_s_317_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 2, v___x_310_);
v_s_317_ = v___x_308_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_str_293_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_startInclusive_294_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v___x_310_);
v_s_317_ = v_reuseFailAlloc_320_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
uint8_t v___x_318_; 
v___x_318_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_unsigned_to_nat(2u);
return v___x_319_;
}
else
{
return v___x_296_;
}
}
}
else
{
lean_dec(v___x_310_);
lean_del_object(v___x_308_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
return v___x_296_;
}
}
}
}
}
else
{
lean_dec(v___x_297_);
lean_dec(v_startInclusive_294_);
lean_dec_ref(v_str_293_);
lean_dec_ref(v_s_292_);
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_zero_327_; uint8_t v_isZero_328_; 
v_zero_327_ = lean_unsigned_to_nat(0u);
v_isZero_328_ = lean_nat_dec_eq(v_x_325_, v_zero_327_);
if (v_isZero_328_ == 1)
{
lean_dec(v_x_325_);
return v_x_326_;
}
else
{
uint32_t v___x_329_; lean_object* v_one_330_; lean_object* v_n_331_; lean_object* v___x_332_; 
v___x_329_ = 10;
v_one_330_ = lean_unsigned_to_nat(1u);
v_n_331_ = lean_nat_sub(v_x_325_, v_one_330_);
lean_dec(v_x_325_);
v___x_332_ = lean_string_push(v_x_326_, v___x_329_);
v_x_325_ = v_n_331_;
v_x_326_ = v___x_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(lean_object* v_a_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_335_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_336_ = lean_unsigned_to_nat(2u);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_string_utf8_byte_size(v_a_334_);
lean_inc_ref(v_a_334_);
v___x_339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_339_, 0, v_a_334_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
v___x_340_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(v___x_339_);
v___x_341_ = lean_nat_sub(v___x_336_, v___x_340_);
lean_dec(v___x_340_);
v___x_342_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_341_, v___x_335_);
v___x_343_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_342_, v_a_334_);
lean_dec_ref(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_a_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___boxed(lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(v_a_347_, v_a_348_);
lean_dec(v_a_347_);
return v_res_349_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(uint32_t v_a_350_){
_start:
{
uint32_t v___x_351_; uint8_t v___x_352_; 
v___x_351_ = 92;
v___x_352_ = lean_uint32_dec_eq(v_a_350_, v___x_351_);
if (v___x_352_ == 0)
{
uint32_t v___x_353_; uint8_t v___x_354_; 
v___x_353_ = 42;
v___x_354_ = lean_uint32_dec_eq(v_a_350_, v___x_353_);
if (v___x_354_ == 0)
{
uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 95;
v___x_356_ = lean_uint32_dec_eq(v_a_350_, v___x_355_);
if (v___x_356_ == 0)
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 91;
v___x_358_ = lean_uint32_dec_eq(v_a_350_, v___x_357_);
if (v___x_358_ == 0)
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 93;
v___x_360_ = lean_uint32_dec_eq(v_a_350_, v___x_359_);
if (v___x_360_ == 0)
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 123;
v___x_362_ = lean_uint32_dec_eq(v_a_350_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 125;
v___x_364_ = lean_uint32_dec_eq(v_a_350_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 96;
v___x_366_ = lean_uint32_dec_eq(v_a_350_, v___x_365_);
if (v___x_366_ == 0)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 33;
v___x_368_ = lean_uint32_dec_eq(v_a_350_, v___x_367_);
if (v___x_368_ == 0)
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 36;
v___x_370_ = lean_uint32_dec_eq(v_a_350_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 10;
v___x_372_ = lean_uint32_dec_eq(v_a_350_, v___x_371_);
return v___x_372_;
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
else
{
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial___boxed(lean_object* v_a_373_){
_start:
{
uint32_t v_a_242__boxed_374_; uint8_t v_res_375_; lean_object* v_r_376_; 
v_a_242__boxed_374_ = lean_unbox_uint32(v_a_373_);
lean_dec(v_a_373_);
v_res_375_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v_a_242__boxed_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(lean_object* v___x_377_, lean_object* v_value_378_, lean_object* v_a_379_, lean_object* v_b_380_){
_start:
{
uint8_t v_decide_381_; 
v_decide_381_ = lean_nat_dec_eq(v_a_379_, v___x_377_);
if (v_decide_381_ == 0)
{
uint32_t v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_382_ = lean_string_utf8_get_fast(v_value_378_, v_a_379_);
v___x_383_ = lean_string_utf8_next_fast(v_value_378_, v_a_379_);
lean_dec(v_a_379_);
v___x_384_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v___x_382_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_string_push(v_b_380_, v___x_382_);
v_a_379_ = v___x_383_;
v_b_380_ = v___x_385_;
goto _start;
}
else
{
uint32_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = 92;
v___x_388_ = lean_string_push(v_b_380_, v___x_387_);
v___x_389_ = lean_string_push(v___x_388_, v___x_382_);
v_a_379_ = v___x_383_;
v_b_380_ = v___x_389_;
goto _start;
}
}
else
{
lean_dec(v_a_379_);
return v_b_380_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg___boxed(lean_object* v___x_391_, lean_object* v_value_392_, lean_object* v_a_393_, lean_object* v_b_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_391_, v_value_392_, v_a_393_, v_b_394_);
lean_dec_ref(v_value_392_);
lean_dec(v___x_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(lean_object* v_value_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_397_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_398_ = lean_string_utf8_byte_size(v_value_396_);
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_398_, v_value_396_, v___x_399_, v___x_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped___boxed(lean_object* v_value_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_401_);
lean_dec_ref(v_value_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(lean_object* v___x_403_, lean_object* v___x_404_, lean_object* v_value_405_, lean_object* v_inst_406_, lean_object* v_R_407_, lean_object* v_a_408_, lean_object* v_b_409_, lean_object* v_c_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_404_, v_value_405_, v_a_408_, v_b_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___boxed(lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v_value_414_, lean_object* v_inst_415_, lean_object* v_R_416_, lean_object* v_a_417_, lean_object* v_b_418_, lean_object* v_c_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(v___x_412_, v___x_413_, v_value_414_, v_inst_415_, v_R_416_, v_a_417_, v_b_418_, v_c_419_);
lean_dec_ref(v_value_414_);
lean_dec(v___x_413_);
lean_dec_ref(v___x_412_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(lean_object* v_s_421_, lean_object* v_pos_422_){
_start:
{
lean_object* v_str_423_; lean_object* v_startInclusive_424_; lean_object* v_endExclusive_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v_decide_429_; 
v_str_423_ = lean_ctor_get(v_s_421_, 0);
v_startInclusive_424_ = lean_ctor_get(v_s_421_, 1);
v_endExclusive_425_ = lean_ctor_get(v_s_421_, 2);
v___x_426_ = lean_nat_add(v_startInclusive_424_, v_pos_422_);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = lean_nat_sub(v_endExclusive_425_, v___x_426_);
v_decide_429_ = lean_nat_dec_eq(v___x_427_, v___x_428_);
lean_dec(v___x_428_);
if (v_decide_429_ == 0)
{
uint32_t v___x_430_; uint32_t v___x_431_; uint8_t v___x_432_; 
v___x_430_ = lean_string_utf8_get_fast(v_str_423_, v___x_426_);
v___x_431_ = 48;
v___x_432_ = lean_uint32_dec_le(v___x_431_, v___x_430_);
if (v___x_432_ == 0)
{
lean_dec(v___x_426_);
return v_pos_422_;
}
else
{
uint32_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = 57;
v___x_434_ = lean_uint32_dec_le(v___x_430_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec(v___x_426_);
return v_pos_422_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_435_ = lean_string_utf8_next_fast(v_str_423_, v___x_426_);
v___x_436_ = lean_nat_sub(v___x_435_, v___x_426_);
lean_dec(v___x_426_);
v___x_437_ = lean_nat_add(v_pos_422_, v___x_436_);
lean_dec(v___x_436_);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_pos_422_, v___x_438_);
v___x_440_ = lean_nat_dec_le(v___x_439_, v___x_437_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
lean_dec(v___x_437_);
return v_pos_422_;
}
else
{
lean_dec(v_pos_422_);
v_pos_422_ = v___x_437_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_426_);
return v_pos_422_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0___boxed(lean_object* v_s_442_, lean_object* v_pos_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v_s_442_, v_pos_443_);
lean_dec_ref(v_s_442_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(lean_object* v_text_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v_afterDigits_463_; uint8_t v___y_465_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_string_utf8_byte_size(v_text_458_);
lean_inc_ref_n(v_text_458_, 2);
v___x_461_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_461_, 0, v_text_458_);
lean_ctor_set(v___x_461_, 1, v___x_459_);
lean_ctor_set(v___x_461_, 2, v___x_460_);
v___x_462_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v___x_461_, v___x_459_);
lean_inc(v___x_462_);
v_afterDigits_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_afterDigits_463_, 0, v_text_458_);
lean_ctor_set(v_afterDigits_463_, 1, v___x_462_);
lean_ctor_set(v_afterDigits_463_, 2, v___x_460_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_dec_le(v___x_540_, v___x_460_);
if (v___x_541_ == 0)
{
goto v___jp_535_;
}
else
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_543_ = lean_string_memcmp(v_text_458_, v___x_542_, v___x_459_, v___x_459_, v___x_540_);
if (v___x_543_ == 0)
{
goto v___jp_535_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_543_;
}
}
v___jp_464_:
{
if (v___y_465_ == 0)
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref(v_text_458_);
return v___y_465_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = l_String_Slice_Pos_nextn(v_afterDigits_463_, v___x_459_, v___x_466_);
lean_dec_ref_known(v_afterDigits_463_, 3);
v___x_468_ = lean_nat_add(v___x_462_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_462_);
v___x_469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_469_, 0, v_text_458_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
lean_ctor_set(v___x_469_, 2, v___x_460_);
v___x_470_ = l_String_Slice_Pos_get_x3f(v___x_469_, v___x_459_);
lean_dec_ref_known(v___x_469_, 3);
if (lean_obj_tag(v___x_470_) == 0)
{
return v___y_465_;
}
else
{
lean_object* v_val_471_; uint32_t v___x_472_; uint32_t v___x_473_; uint8_t v___x_474_; 
v_val_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = 32;
v___x_473_ = lean_unbox_uint32(v_val_471_);
lean_dec(v_val_471_);
v___x_474_ = lean_uint32_dec_eq(v___x_473_, v___x_472_);
return v___x_474_;
}
}
}
v___jp_475_:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_sub(v___x_460_, v___x_462_);
v___x_478_ = lean_nat_dec_le(v___x_476_, v___x_477_);
lean_dec(v___x_477_);
if (v___x_478_ == 0)
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref(v_text_458_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_480_ = lean_string_memcmp(v_text_458_, v___x_479_, v___x_462_, v___x_459_, v___x_476_);
v___y_465_ = v___x_480_;
goto v___jp_464_;
}
}
v___jp_481_:
{
lean_object* v___x_482_; 
v___x_482_ = l_String_Slice_Pos_get_x3f(v___x_461_, v___x_459_);
lean_dec_ref_known(v___x_461_, 3);
if (lean_obj_tag(v___x_482_) == 0)
{
uint8_t v___x_483_; 
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref(v_text_458_);
v___x_483_ = 0;
return v___x_483_;
}
else
{
lean_object* v_val_484_; uint32_t v___x_485_; uint32_t v___x_486_; uint8_t v___x_487_; 
v_val_484_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_val_484_);
lean_dec_ref_known(v___x_482_, 1);
v___x_485_ = 48;
v___x_486_ = lean_unbox_uint32(v_val_484_);
v___x_487_ = lean_uint32_dec_le(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_dec(v_val_484_);
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref(v_text_458_);
return v___x_487_;
}
else
{
uint32_t v___x_488_; uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_488_ = 57;
v___x_489_ = lean_unbox_uint32(v_val_484_);
lean_dec(v_val_484_);
v___x_490_ = lean_uint32_dec_le(v___x_489_, v___x_488_);
if (v___x_490_ == 0)
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref(v_text_458_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = lean_nat_sub(v___x_460_, v___x_462_);
v___x_493_ = lean_nat_dec_le(v___x_491_, v___x_492_);
lean_dec(v___x_492_);
if (v___x_493_ == 0)
{
goto v___jp_475_;
}
else
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1));
v___x_495_ = lean_string_memcmp(v_text_458_, v___x_494_, v___x_462_, v___x_459_, v___x_491_);
if (v___x_495_ == 0)
{
goto v___jp_475_;
}
else
{
v___y_465_ = v___x_495_;
goto v___jp_464_;
}
}
}
}
}
}
v___jp_496_:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(3u);
v___x_498_ = lean_nat_dec_le(v___x_497_, v___x_460_);
if (v___x_498_ == 0)
{
goto v___jp_481_;
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_500_ = lean_string_memcmp(v_text_458_, v___x_499_, v___x_459_, v___x_459_, v___x_497_);
if (v___x_500_ == 0)
{
goto v___jp_481_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_500_;
}
}
}
v___jp_501_:
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(3u);
v___x_503_ = lean_nat_dec_le(v___x_502_, v___x_460_);
if (v___x_503_ == 0)
{
goto v___jp_496_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3));
v___x_505_ = lean_string_memcmp(v_text_458_, v___x_504_, v___x_459_, v___x_459_, v___x_502_);
if (v___x_505_ == 0)
{
goto v___jp_496_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_505_;
}
}
}
v___jp_506_:
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(2u);
v___x_508_ = lean_nat_dec_le(v___x_507_, v___x_460_);
if (v___x_508_ == 0)
{
goto v___jp_501_;
}
else
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_510_ = lean_string_memcmp(v_text_458_, v___x_509_, v___x_459_, v___x_459_, v___x_507_);
if (v___x_510_ == 0)
{
goto v___jp_501_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_510_;
}
}
}
v___jp_511_:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___x_513_ = lean_string_dec_eq(v_text_458_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = lean_nat_dec_le(v___x_514_, v___x_460_);
if (v___x_515_ == 0)
{
goto v___jp_506_;
}
else
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_517_ = lean_string_memcmp(v_text_458_, v___x_516_, v___x_459_, v___x_459_, v___x_514_);
if (v___x_517_ == 0)
{
goto v___jp_506_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_517_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_513_;
}
}
v___jp_518_:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___x_520_ = lean_string_dec_eq(v_text_458_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(2u);
v___x_522_ = lean_nat_dec_le(v___x_521_, v___x_460_);
if (v___x_522_ == 0)
{
goto v___jp_511_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_524_ = lean_string_memcmp(v_text_458_, v___x_523_, v___x_459_, v___x_459_, v___x_521_);
if (v___x_524_ == 0)
{
goto v___jp_511_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_524_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_520_;
}
}
v___jp_525_:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_dec_le(v___x_526_, v___x_460_);
if (v___x_527_ == 0)
{
goto v___jp_518_;
}
else
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___x_529_ = lean_string_memcmp(v_text_458_, v___x_528_, v___x_459_, v___x_459_, v___x_526_);
if (v___x_529_ == 0)
{
goto v___jp_518_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_529_;
}
}
}
v___jp_530_:
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_dec_le(v___x_531_, v___x_460_);
if (v___x_532_ == 0)
{
goto v___jp_525_;
}
else
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_534_ = lean_string_memcmp(v_text_458_, v___x_533_, v___x_459_, v___x_459_, v___x_531_);
if (v___x_534_ == 0)
{
goto v___jp_525_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_534_;
}
}
}
v___jp_535_:
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_dec_le(v___x_536_, v___x_460_);
if (v___x_537_ == 0)
{
goto v___jp_530_;
}
else
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_539_ = lean_string_memcmp(v_text_458_, v___x_538_, v___x_459_, v___x_459_, v___x_536_);
if (v___x_539_ == 0)
{
goto v___jp_530_;
}
else
{
lean_dec_ref_known(v_afterDigits_463_, 3);
lean_dec(v___x_462_);
lean_dec_ref_known(v___x_461_, 3);
lean_dec_ref(v_text_458_);
return v___x_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object* v_text_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_text_544_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t v_atLineStart_548_, lean_object* v_value_549_){
_start:
{
lean_object* v_text_550_; 
v_text_550_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_549_);
if (v_atLineStart_548_ == 0)
{
lean_dec_ref(v_value_549_);
return v_text_550_;
}
else
{
uint8_t v___x_551_; 
v___x_551_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_value_549_);
if (v___x_551_ == 0)
{
return v_text_550_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_553_ = lean_string_append(v___x_552_, v_text_550_);
lean_dec_ref(v_text_550_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object* v_atLineStart_554_, lean_object* v_value_555_){
_start:
{
uint8_t v_atLineStart_boxed_556_; lean_object* v_res_557_; 
v_atLineStart_boxed_556_ = lean_unbox(v_atLineStart_554_);
v_res_557_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_boxed_556_, v_value_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object* v_s_558_, lean_object* v_pos_559_){
_start:
{
lean_object* v_str_560_; lean_object* v_startInclusive_561_; lean_object* v_endExclusive_562_; lean_object* v___x_563_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v_decide_574_; 
v_str_560_ = lean_ctor_get(v_s_558_, 0);
v_startInclusive_561_ = lean_ctor_get(v_s_558_, 1);
v_endExclusive_562_ = lean_ctor_get(v_s_558_, 2);
v___x_563_ = lean_nat_add(v_startInclusive_561_, v_pos_559_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_nat_sub(v_endExclusive_562_, v___x_563_);
v_decide_574_ = lean_nat_dec_eq(v___x_572_, v___x_573_);
lean_dec(v___x_573_);
if (v_decide_574_ == 0)
{
uint32_t v___x_575_; uint32_t v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_string_utf8_get_fast(v_str_560_, v___x_563_);
v___x_576_ = 32;
v___x_577_ = lean_uint32_dec_eq(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
uint32_t v___x_578_; uint8_t v___x_579_; 
v___x_578_ = 9;
v___x_579_ = lean_uint32_dec_eq(v___x_575_, v___x_578_);
if (v___x_579_ == 0)
{
uint32_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = 13;
v___x_581_ = lean_uint32_dec_eq(v___x_575_, v___x_580_);
if (v___x_581_ == 0)
{
uint32_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 10;
v___x_583_ = lean_uint32_dec_eq(v___x_575_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec(v___x_563_);
return v_pos_559_;
}
else
{
goto v___jp_564_;
}
}
else
{
goto v___jp_564_;
}
}
else
{
goto v___jp_564_;
}
}
else
{
goto v___jp_564_;
}
}
else
{
lean_dec(v___x_563_);
return v_pos_559_;
}
v___jp_564_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_565_ = lean_string_utf8_next_fast(v_str_560_, v___x_563_);
v___x_566_ = lean_nat_sub(v___x_565_, v___x_563_);
lean_dec(v___x_563_);
v___x_567_ = lean_nat_add(v_pos_559_, v___x_566_);
lean_dec(v___x_566_);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_pos_559_, v___x_568_);
v___x_570_ = lean_nat_dec_le(v___x_569_, v___x_567_);
lean_dec(v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v___x_567_);
return v_pos_559_;
}
else
{
lean_dec(v_pos_559_);
v_pos_559_ = v___x_567_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object* v_s_584_, lean_object* v_pos_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_584_, v_pos_585_);
lean_dec_ref(v_s_584_);
return v_res_586_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object* v_s_587_){
_start:
{
lean_object* v_startInclusive_588_; lean_object* v_endExclusive_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v_decide_593_; 
v_startInclusive_588_ = lean_ctor_get(v_s_587_, 1);
v_endExclusive_589_ = lean_ctor_get(v_s_587_, 2);
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_587_, v___x_590_);
v___x_592_ = lean_nat_sub(v_endExclusive_589_, v_startInclusive_588_);
v_decide_593_ = lean_nat_dec_eq(v___x_591_, v___x_592_);
lean_dec(v___x_592_);
lean_dec(v___x_591_);
return v_decide_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object* v_s_594_){
_start:
{
uint8_t v_res_595_; lean_object* v_r_596_; 
v_res_595_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v_s_594_);
lean_dec_ref(v_s_594_);
v_r_596_ = lean_box(v_res_595_);
return v_r_596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object* v_s_597_, lean_object* v_a_598_, lean_object* v_b_599_){
_start:
{
lean_object* v_str_600_; lean_object* v_startInclusive_601_; lean_object* v_endExclusive_602_; lean_object* v___x_603_; uint8_t v_decide_604_; 
v_str_600_ = lean_ctor_get(v_s_597_, 0);
v_startInclusive_601_ = lean_ctor_get(v_s_597_, 1);
v_endExclusive_602_ = lean_ctor_get(v_s_597_, 2);
v___x_603_ = lean_nat_sub(v_endExclusive_602_, v_startInclusive_601_);
v_decide_604_ = lean_nat_dec_eq(v_a_598_, v___x_603_);
lean_dec(v___x_603_);
if (v_decide_604_ == 0)
{
lean_object* v___x_605_; uint32_t v___x_606_; uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_605_ = lean_nat_add(v_startInclusive_601_, v_a_598_);
lean_dec(v_a_598_);
v___x_606_ = lean_string_utf8_get_fast(v_str_600_, v___x_605_);
v___x_607_ = 32;
v___x_608_ = lean_uint32_dec_eq(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v___x_605_);
return v_b_599_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_string_utf8_next_fast(v_str_600_, v___x_605_);
lean_dec(v___x_605_);
v___x_610_ = lean_nat_sub(v___x_609_, v_startInclusive_601_);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_b_599_, v___x_611_);
lean_dec(v_b_599_);
v_a_598_ = v___x_610_;
v_b_599_ = v___x_612_;
goto _start;
}
}
else
{
lean_dec(v_a_598_);
return v_b_599_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object* v_s_614_, lean_object* v_a_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_614_, v_a_615_, v_b_616_);
lean_dec_ref(v_s_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object* v_s_618_){
_start:
{
lean_object* v_n_619_; lean_object* v___x_620_; 
v_n_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_618_, v_n_619_, v_n_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object* v_s_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v_s_621_);
lean_dec_ref(v_s_621_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object* v_s_623_, lean_object* v_inst_624_, lean_object* v_R_625_, lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v_c_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_623_, v_a_626_, v_b_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object* v_s_630_, lean_object* v_inst_631_, lean_object* v_R_632_, lean_object* v_a_633_, lean_object* v_b_634_, lean_object* v_c_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(v_s_630_, v_inst_631_, v_R_632_, v_a_633_, v_b_634_, v_c_635_);
lean_dec_ref(v_s_630_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v_src_639_, lean_object* v___x_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v_it_644_; lean_object* v_out_645_; 
if (lean_obj_tag(v_a_641_) == 0)
{
lean_object* v_currPos_664_; lean_object* v_searcher_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_694_; 
v_currPos_664_ = lean_ctor_get(v_a_641_, 0);
v_searcher_665_ = lean_ctor_get(v_a_641_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_694_ == 0)
{
v___x_667_ = v_a_641_;
v_isShared_668_ = v_isSharedCheck_694_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_searcher_665_);
lean_inc(v_currPos_664_);
lean_dec(v_a_641_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_694_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_str_669_; lean_object* v_startInclusive_670_; lean_object* v_endExclusive_671_; lean_object* v___x_672_; uint8_t v_decide_673_; 
v_str_669_ = lean_ctor_get(v___x_637_, 0);
v_startInclusive_670_ = lean_ctor_get(v___x_637_, 1);
v_endExclusive_671_ = lean_ctor_get(v___x_637_, 2);
v___x_672_ = lean_nat_sub(v_endExclusive_671_, v_startInclusive_670_);
v_decide_673_ = lean_nat_dec_eq(v_searcher_665_, v___x_672_);
lean_dec(v___x_672_);
if (v_decide_673_ == 0)
{
uint32_t v___x_674_; lean_object* v___x_675_; uint32_t v___x_676_; uint8_t v___x_677_; 
v___x_674_ = 10;
v___x_675_ = lean_nat_add(v_startInclusive_670_, v_searcher_665_);
v___x_676_ = lean_string_utf8_get_fast(v_str_669_, v___x_675_);
v___x_677_ = lean_uint32_dec_eq(v___x_676_, v___x_674_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_dec(v_searcher_665_);
v___x_678_ = lean_string_utf8_next_fast(v_str_669_, v___x_675_);
lean_dec(v___x_675_);
v___x_679_ = lean_nat_sub(v___x_678_, v_startInclusive_670_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_679_);
v___x_681_ = v___x_667_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_currPos_664_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_683_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
v_a_641_ = v___x_681_;
goto _start;
}
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_slice_687_; lean_object* v_nextIt_689_; 
v___x_684_ = lean_string_utf8_next_fast(v_str_669_, v___x_675_);
v___x_685_ = lean_nat_sub(v___x_684_, v___x_675_);
lean_dec(v___x_675_);
v___x_686_ = lean_nat_add(v_searcher_665_, v___x_685_);
lean_dec(v___x_685_);
lean_dec(v_searcher_665_);
lean_inc_ref(v___x_637_);
v_slice_687_ = l_String_Slice_slice_x21(v___x_637_, v_currPos_664_, v___x_686_);
lean_dec(v_currPos_664_);
lean_inc(v___x_686_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 1, v___x_686_);
lean_ctor_set(v___x_667_, 0, v___x_686_);
v_nextIt_689_ = v___x_667_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_686_);
v_nextIt_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_it_644_ = v_nextIt_689_;
v_out_645_ = v_slice_687_;
goto v___jp_643_;
}
}
}
else
{
uint8_t v_decide_691_; 
lean_del_object(v___x_667_);
lean_dec(v_searcher_665_);
v_decide_691_ = lean_nat_dec_eq(v_currPos_664_, v___x_638_);
if (v_decide_691_ == 0)
{
lean_object* v_slice_692_; lean_object* v___x_693_; 
lean_inc(v___x_640_);
lean_inc_ref(v_src_639_);
v_slice_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_692_, 0, v_src_639_);
lean_ctor_set(v_slice_692_, 1, v_currPos_664_);
lean_ctor_set(v_slice_692_, 2, v___x_640_);
v___x_693_ = lean_box(1);
v_it_644_ = v___x_693_;
v_out_645_ = v_slice_692_;
goto v___jp_643_;
}
else
{
lean_dec(v_currPos_664_);
lean_dec(v___x_640_);
lean_dec_ref(v_src_639_);
lean_dec_ref(v___x_637_);
return v_b_642_;
}
}
}
}
else
{
lean_dec(v___x_640_);
lean_dec_ref(v_src_639_);
lean_dec_ref(v___x_637_);
return v_b_642_;
}
v___jp_643_:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = l_String_Slice_lines_lineMap(v_out_645_);
v___x_647_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_646_);
lean_dec_ref(v___x_646_);
if (lean_obj_tag(v_b_642_) == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
v_a_641_ = v_it_644_;
v_b_642_ = v___x_649_;
goto _start;
}
else
{
lean_object* v_val_651_; uint8_t v___x_652_; 
v_val_651_ = lean_ctor_get(v_b_642_, 0);
v___x_652_ = lean_nat_dec_le(v___x_648_, v_val_651_);
if (v___x_652_ == 0)
{
lean_dec(v___x_648_);
v_a_641_ = v_it_644_;
goto _start;
}
else
{
lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_isSharedCheck_661_ = !lean_is_exclusive(v_b_642_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_b_642_, 0);
lean_dec(v_unused_662_);
v___x_655_ = v_b_642_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_dec(v_b_642_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_648_);
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_648_);
v___x_658_ = v_reuseFailAlloc_660_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v_a_641_ = v_it_644_;
v_b_642_ = v___x_658_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_646_);
v_a_641_ = v_it_644_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v_src_697_, lean_object* v___x_698_, lean_object* v_a_699_, lean_object* v_b_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_695_, v___x_696_, v_src_697_, v___x_698_, v_a_699_, v_b_700_);
lean_dec(v___x_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v_src_704_, lean_object* v___x_705_, lean_object* v_a_706_, lean_object* v_b_707_){
_start:
{
lean_object* v_it_709_; lean_object* v_out_710_; 
if (lean_obj_tag(v_a_706_) == 0)
{
lean_object* v_currPos_729_; lean_object* v_searcher_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_759_; 
v_currPos_729_ = lean_ctor_get(v_a_706_, 0);
v_searcher_730_ = lean_ctor_get(v_a_706_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_759_ == 0)
{
v___x_732_ = v_a_706_;
v_isShared_733_ = v_isSharedCheck_759_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_searcher_730_);
lean_inc(v_currPos_729_);
lean_dec(v_a_706_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_759_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_str_734_; lean_object* v_startInclusive_735_; lean_object* v_endExclusive_736_; lean_object* v___x_737_; uint8_t v_decide_738_; 
v_str_734_ = lean_ctor_get(v___x_702_, 0);
v_startInclusive_735_ = lean_ctor_get(v___x_702_, 1);
v_endExclusive_736_ = lean_ctor_get(v___x_702_, 2);
v___x_737_ = lean_nat_sub(v_endExclusive_736_, v_startInclusive_735_);
v_decide_738_ = lean_nat_dec_eq(v_searcher_730_, v___x_737_);
lean_dec(v___x_737_);
if (v_decide_738_ == 0)
{
lean_object* v___x_739_; uint32_t v___x_740_; uint32_t v___x_741_; uint8_t v___x_742_; 
v___x_739_ = lean_nat_add(v_startInclusive_735_, v_searcher_730_);
v___x_740_ = lean_string_utf8_get_fast(v_str_734_, v___x_739_);
v___x_741_ = 10;
v___x_742_ = lean_uint32_dec_eq(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_searcher_730_);
v___x_743_ = lean_string_utf8_next_fast(v_str_734_, v___x_739_);
lean_dec(v___x_739_);
v___x_744_ = lean_nat_sub(v___x_743_, v_startInclusive_735_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_744_);
v___x_746_ = v___x_732_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_currPos_729_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_748_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
v___x_747_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_702_, v___x_703_, v_src_704_, v___x_705_, v___x_746_, v_b_707_);
return v___x_747_;
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_slice_752_; lean_object* v_nextIt_754_; 
v___x_749_ = lean_string_utf8_next_fast(v_str_734_, v___x_739_);
v___x_750_ = lean_nat_sub(v___x_749_, v___x_739_);
lean_dec(v___x_739_);
v___x_751_ = lean_nat_add(v_searcher_730_, v___x_750_);
lean_dec(v___x_750_);
lean_dec(v_searcher_730_);
lean_inc_ref(v___x_702_);
v_slice_752_ = l_String_Slice_slice_x21(v___x_702_, v_currPos_729_, v___x_751_);
lean_dec(v_currPos_729_);
lean_inc(v___x_751_);
if (v_isShared_733_ == 0)
{
lean_ctor_set(v___x_732_, 1, v___x_751_);
lean_ctor_set(v___x_732_, 0, v___x_751_);
v_nextIt_754_ = v___x_732_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_751_);
v_nextIt_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
v_it_709_ = v_nextIt_754_;
v_out_710_ = v_slice_752_;
goto v___jp_708_;
}
}
}
else
{
uint8_t v_decide_756_; 
lean_del_object(v___x_732_);
lean_dec(v_searcher_730_);
v_decide_756_ = lean_nat_dec_eq(v_currPos_729_, v___x_703_);
if (v_decide_756_ == 0)
{
lean_object* v_slice_757_; lean_object* v___x_758_; 
lean_inc(v___x_705_);
lean_inc_ref(v_src_704_);
v_slice_757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_757_, 0, v_src_704_);
lean_ctor_set(v_slice_757_, 1, v_currPos_729_);
lean_ctor_set(v_slice_757_, 2, v___x_705_);
v___x_758_ = lean_box(1);
v_it_709_ = v___x_758_;
v_out_710_ = v_slice_757_;
goto v___jp_708_;
}
else
{
lean_dec(v_currPos_729_);
lean_dec(v___x_705_);
lean_dec_ref(v_src_704_);
lean_dec_ref(v___x_702_);
return v_b_707_;
}
}
}
}
else
{
lean_dec(v___x_705_);
lean_dec_ref(v_src_704_);
lean_dec_ref(v___x_702_);
return v_b_707_;
}
v___jp_708_:
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = l_String_Slice_lines_lineMap(v_out_710_);
v___x_712_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
v___x_713_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_711_);
lean_dec_ref(v___x_711_);
if (lean_obj_tag(v_b_707_) == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_702_, v___x_703_, v_src_704_, v___x_705_, v_it_709_, v___x_714_);
return v___x_715_;
}
else
{
lean_object* v_val_716_; uint8_t v___x_717_; 
v_val_716_ = lean_ctor_get(v_b_707_, 0);
v___x_717_ = lean_nat_dec_le(v___x_713_, v_val_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v___x_713_);
v___x_718_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_702_, v___x_703_, v_src_704_, v___x_705_, v_it_709_, v_b_707_);
return v___x_718_;
}
else
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_isSharedCheck_726_ = !lean_is_exclusive(v_b_707_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_b_707_, 0);
lean_dec(v_unused_727_);
v___x_720_ = v_b_707_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_dec(v_b_707_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_713_);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_713_);
v___x_723_ = v_reuseFailAlloc_725_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; 
v___x_724_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_702_, v___x_703_, v_src_704_, v___x_705_, v_it_709_, v___x_723_);
return v___x_724_;
}
}
}
}
}
else
{
lean_object* v___x_728_; 
lean_dec_ref(v___x_711_);
v___x_728_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_702_, v___x_703_, v_src_704_, v___x_705_, v_it_709_, v_b_707_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object* v___x_760_, lean_object* v___x_761_, lean_object* v_src_762_, lean_object* v___x_763_, lean_object* v_a_764_, lean_object* v_b_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_760_, v___x_761_, v_src_762_, v___x_763_, v_a_764_, v_b_765_);
lean_dec(v___x_761_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object* v___x_767_, lean_object* v_i_768_, lean_object* v_out_769_, lean_object* v_pending_770_, lean_object* v___y_771_, lean_object* v_____r_772_, lean_object* v_out_773_){
_start:
{
lean_object* v_str_774_; lean_object* v_startInclusive_775_; lean_object* v_endExclusive_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_str_774_ = lean_ctor_get(v___x_767_, 0);
v_startInclusive_775_ = lean_ctor_get(v___x_767_, 1);
v_endExclusive_776_ = lean_ctor_get(v___x_767_, 2);
v___x_777_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_i_768_, v_out_769_);
v___x_778_ = lean_string_append(v_out_773_, v___x_777_);
lean_dec_ref(v___x_777_);
lean_inc(v_pending_770_);
v___x_779_ = l_String_Slice_Pos_nextn(v___x_767_, v_pending_770_, v___y_771_);
v___x_780_ = lean_nat_add(v_startInclusive_775_, v___x_779_);
lean_dec(v___x_779_);
v___x_781_ = lean_string_utf8_extract_fast(v_str_774_, v___x_780_, v_endExclusive_776_);
lean_dec(v___x_780_);
v___x_782_ = lean_string_append(v___x_778_, v___x_781_);
lean_dec_ref(v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_pending_770_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object* v___x_785_, lean_object* v_i_786_, lean_object* v_out_787_, lean_object* v_pending_788_, lean_object* v___y_789_, lean_object* v_____r_790_, lean_object* v_out_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_785_, v_i_786_, v_out_787_, v_pending_788_, v___y_789_, v_____r_790_, v_out_791_);
lean_dec_ref(v___x_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object* v_i_793_, lean_object* v___y_794_, lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v_src_797_, lean_object* v___x_798_, lean_object* v_a_799_, lean_object* v_b_800_){
_start:
{
lean_object* v___y_802_; lean_object* v_val_803_; 
if (lean_obj_tag(v_a_799_) == 0)
{
lean_object* v_currPos_807_; lean_object* v_searcher_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_871_; 
v_currPos_807_ = lean_ctor_get(v_a_799_, 0);
v_searcher_808_ = lean_ctor_get(v_a_799_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_a_799_);
if (v_isSharedCheck_871_ == 0)
{
v___x_810_ = v_a_799_;
v_isShared_811_ = v_isSharedCheck_871_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_searcher_808_);
lean_inc(v_currPos_807_);
lean_dec(v_a_799_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_871_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_str_812_; lean_object* v_startInclusive_813_; lean_object* v_endExclusive_814_; lean_object* v_out_815_; lean_object* v_pending_816_; lean_object* v_it_818_; lean_object* v_out_819_; lean_object* v___x_849_; uint8_t v_decide_850_; 
v_str_812_ = lean_ctor_get(v___x_795_, 0);
v_startInclusive_813_ = lean_ctor_get(v___x_795_, 1);
v_endExclusive_814_ = lean_ctor_get(v___x_795_, 2);
v_out_815_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_816_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_sub(v_endExclusive_814_, v_startInclusive_813_);
v_decide_850_ = lean_nat_dec_eq(v_searcher_808_, v___x_849_);
lean_dec(v___x_849_);
if (v_decide_850_ == 0)
{
uint32_t v___x_851_; lean_object* v___x_852_; uint32_t v___x_853_; uint8_t v___x_854_; 
v___x_851_ = 10;
v___x_852_ = lean_nat_add(v_startInclusive_813_, v_searcher_808_);
v___x_853_ = lean_string_utf8_get_fast(v_str_812_, v___x_852_);
v___x_854_ = lean_uint32_dec_eq(v___x_853_, v___x_851_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
lean_dec(v_searcher_808_);
v___x_855_ = lean_string_utf8_next_fast(v_str_812_, v___x_852_);
lean_dec(v___x_852_);
v___x_856_ = lean_nat_sub(v___x_855_, v_startInclusive_813_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v___x_856_);
v___x_858_ = v___x_810_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_currPos_807_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_856_);
v___x_858_ = v_reuseFailAlloc_860_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
v_a_799_ = v___x_858_;
goto _start;
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_slice_864_; lean_object* v_nextIt_866_; 
v___x_861_ = lean_string_utf8_next_fast(v_str_812_, v___x_852_);
v___x_862_ = lean_nat_sub(v___x_861_, v___x_852_);
lean_dec(v___x_852_);
v___x_863_ = lean_nat_add(v_searcher_808_, v___x_862_);
lean_dec(v___x_862_);
lean_dec(v_searcher_808_);
lean_inc_ref(v___x_795_);
v_slice_864_ = l_String_Slice_slice_x21(v___x_795_, v_currPos_807_, v___x_863_);
lean_dec(v_currPos_807_);
lean_inc(v___x_863_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v___x_863_);
lean_ctor_set(v___x_810_, 0, v___x_863_);
v_nextIt_866_ = v___x_810_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_863_);
v_nextIt_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
v_it_818_ = v_nextIt_866_;
v_out_819_ = v_slice_864_;
goto v___jp_817_;
}
}
}
else
{
uint8_t v_decide_868_; 
lean_del_object(v___x_810_);
lean_dec(v_searcher_808_);
v_decide_868_ = lean_nat_dec_eq(v_currPos_807_, v___x_796_);
if (v_decide_868_ == 0)
{
lean_object* v_slice_869_; lean_object* v___x_870_; 
lean_inc(v___x_798_);
lean_inc_ref(v_src_797_);
v_slice_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_869_, 0, v_src_797_);
lean_ctor_set(v_slice_869_, 1, v_currPos_807_);
lean_ctor_set(v_slice_869_, 2, v___x_798_);
v___x_870_ = lean_box(1);
v_it_818_ = v___x_870_;
v_out_819_ = v_slice_869_;
goto v___jp_817_;
}
else
{
lean_dec(v_currPos_807_);
lean_dec(v___x_798_);
lean_dec_ref(v_src_797_);
lean_dec_ref(v___x_795_);
lean_dec(v___y_794_);
lean_dec(v_i_793_);
return v_b_800_;
}
}
v___jp_817_:
{
lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_848_; 
v_fst_820_ = lean_ctor_get(v_b_800_, 0);
v_snd_821_ = lean_ctor_get(v_b_800_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_b_800_);
if (v_isSharedCheck_848_ == 0)
{
v___x_823_ = v_b_800_;
v_isShared_824_ = v_isSharedCheck_848_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_820_);
lean_dec(v_b_800_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_848_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = l_String_Slice_lines_lineMap(v_out_819_);
v___x_826_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; uint8_t v___x_828_; 
lean_del_object(v___x_823_);
v___x_827_ = lean_string_utf8_byte_size(v_fst_820_);
v___x_828_ = lean_nat_dec_eq(v___x_827_, v_pending_816_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = lean_nat_add(v_snd_821_, v___x_829_);
lean_dec(v_snd_821_);
v___x_831_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_830_, v_fst_820_);
v___x_832_ = lean_box(0);
lean_inc(v___y_794_);
lean_inc(v_i_793_);
v___x_833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_825_, v_i_793_, v_out_815_, v_pending_816_, v___y_794_, v___x_832_, v___x_831_);
lean_dec_ref(v___x_825_);
v___y_802_ = v_it_818_;
v_val_803_ = v___x_833_;
goto v___jp_801_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v_snd_821_);
v___x_834_ = lean_box(0);
lean_inc(v___y_794_);
lean_inc(v_i_793_);
v___x_835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_825_, v_i_793_, v_out_815_, v_pending_816_, v___y_794_, v___x_834_, v_fst_820_);
lean_dec_ref(v___x_825_);
v___y_802_ = v_it_818_;
v_val_803_ = v___x_835_;
goto v___jp_801_;
}
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; 
lean_dec_ref(v___x_825_);
v___x_836_ = lean_string_utf8_byte_size(v_fst_820_);
v___x_837_ = lean_nat_dec_eq(v___x_836_, v_pending_816_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = lean_unsigned_to_nat(1u);
v___x_839_ = lean_nat_add(v_snd_821_, v___x_838_);
lean_dec(v_snd_821_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_839_);
v___x_841_ = v___x_823_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_843_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
v_a_799_ = v_it_818_;
v_b_800_ = v___x_841_;
goto _start;
}
}
else
{
lean_object* v___x_845_; 
if (v_isShared_824_ == 0)
{
v___x_845_ = v___x_823_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_fst_820_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_snd_821_);
v___x_845_ = v_reuseFailAlloc_847_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v_a_799_ = v_it_818_;
v_b_800_ = v___x_845_;
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
lean_dec(v___x_798_);
lean_dec_ref(v_src_797_);
lean_dec_ref(v___x_795_);
lean_dec(v___y_794_);
lean_dec(v_i_793_);
return v_b_800_;
}
v___jp_801_:
{
if (lean_obj_tag(v_val_803_) == 0)
{
lean_object* v_a_804_; 
lean_dec(v___y_802_);
lean_dec(v___x_798_);
lean_dec_ref(v_src_797_);
lean_dec_ref(v___x_795_);
lean_dec(v___y_794_);
lean_dec(v_i_793_);
v_a_804_ = lean_ctor_get(v_val_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v_val_803_, 1);
return v_a_804_;
}
else
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v_val_803_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v_val_803_, 1);
v_a_799_ = v___y_802_;
v_b_800_ = v_a_805_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object* v_i_872_, lean_object* v___y_873_, lean_object* v___x_874_, lean_object* v___x_875_, lean_object* v_src_876_, lean_object* v___x_877_, lean_object* v_a_878_, lean_object* v_b_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_872_, v___y_873_, v___x_874_, v___x_875_, v_src_876_, v___x_877_, v_a_878_, v_b_879_);
lean_dec(v___x_875_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object* v_i_881_, lean_object* v___y_882_, lean_object* v___x_883_, lean_object* v___x_884_, lean_object* v_src_885_, lean_object* v___x_886_, lean_object* v_a_887_, lean_object* v_b_888_){
_start:
{
lean_object* v___y_890_; lean_object* v_val_891_; 
if (lean_obj_tag(v_a_887_) == 0)
{
lean_object* v_currPos_895_; lean_object* v_searcher_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_959_; 
v_currPos_895_ = lean_ctor_get(v_a_887_, 0);
v_searcher_896_ = lean_ctor_get(v_a_887_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_959_ == 0)
{
v___x_898_ = v_a_887_;
v_isShared_899_ = v_isSharedCheck_959_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_searcher_896_);
lean_inc(v_currPos_895_);
lean_dec(v_a_887_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_959_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_str_900_; lean_object* v_startInclusive_901_; lean_object* v_endExclusive_902_; lean_object* v_out_903_; lean_object* v_pending_904_; lean_object* v_it_906_; lean_object* v_out_907_; lean_object* v___x_937_; uint8_t v_decide_938_; 
v_str_900_ = lean_ctor_get(v___x_883_, 0);
v_startInclusive_901_ = lean_ctor_get(v___x_883_, 1);
v_endExclusive_902_ = lean_ctor_get(v___x_883_, 2);
v_out_903_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_pending_904_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_nat_sub(v_endExclusive_902_, v_startInclusive_901_);
v_decide_938_ = lean_nat_dec_eq(v_searcher_896_, v___x_937_);
lean_dec(v___x_937_);
if (v_decide_938_ == 0)
{
lean_object* v___x_939_; uint32_t v___x_940_; uint32_t v___x_941_; uint8_t v___x_942_; 
v___x_939_ = lean_nat_add(v_startInclusive_901_, v_searcher_896_);
v___x_940_ = lean_string_utf8_get_fast(v_str_900_, v___x_939_);
v___x_941_ = 10;
v___x_942_ = lean_uint32_dec_eq(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
lean_dec(v_searcher_896_);
v___x_943_ = lean_string_utf8_next_fast(v_str_900_, v___x_939_);
lean_dec(v___x_939_);
v___x_944_ = lean_nat_sub(v___x_943_, v_startInclusive_901_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_944_);
v___x_946_ = v___x_898_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_currPos_895_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_944_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_881_, v___y_882_, v___x_883_, v___x_884_, v_src_885_, v___x_886_, v___x_946_, v_b_888_);
return v___x_947_;
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_slice_952_; lean_object* v_nextIt_954_; 
v___x_949_ = lean_string_utf8_next_fast(v_str_900_, v___x_939_);
v___x_950_ = lean_nat_sub(v___x_949_, v___x_939_);
lean_dec(v___x_939_);
v___x_951_ = lean_nat_add(v_searcher_896_, v___x_950_);
lean_dec(v___x_950_);
lean_dec(v_searcher_896_);
lean_inc_ref(v___x_883_);
v_slice_952_ = l_String_Slice_slice_x21(v___x_883_, v_currPos_895_, v___x_951_);
lean_dec(v_currPos_895_);
lean_inc(v___x_951_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___x_951_);
lean_ctor_set(v___x_898_, 0, v___x_951_);
v_nextIt_954_ = v___x_898_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_951_);
v_nextIt_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_it_906_ = v_nextIt_954_;
v_out_907_ = v_slice_952_;
goto v___jp_905_;
}
}
}
else
{
uint8_t v_decide_956_; 
lean_del_object(v___x_898_);
lean_dec(v_searcher_896_);
v_decide_956_ = lean_nat_dec_eq(v_currPos_895_, v___x_884_);
if (v_decide_956_ == 0)
{
lean_object* v_slice_957_; lean_object* v___x_958_; 
lean_inc(v___x_886_);
lean_inc_ref(v_src_885_);
v_slice_957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_957_, 0, v_src_885_);
lean_ctor_set(v_slice_957_, 1, v_currPos_895_);
lean_ctor_set(v_slice_957_, 2, v___x_886_);
v___x_958_ = lean_box(1);
v_it_906_ = v___x_958_;
v_out_907_ = v_slice_957_;
goto v___jp_905_;
}
else
{
lean_dec(v_currPos_895_);
lean_dec(v___x_886_);
lean_dec_ref(v_src_885_);
lean_dec_ref(v___x_883_);
lean_dec(v___y_882_);
lean_dec(v_i_881_);
return v_b_888_;
}
}
v___jp_905_:
{
lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_936_; 
v_fst_908_ = lean_ctor_get(v_b_888_, 0);
v_snd_909_ = lean_ctor_get(v_b_888_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_b_888_);
if (v_isSharedCheck_936_ == 0)
{
v___x_911_ = v_b_888_;
v_isShared_912_ = v_isSharedCheck_936_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snd_909_);
lean_inc(v_fst_908_);
lean_dec(v_b_888_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_936_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = l_String_Slice_lines_lineMap(v_out_907_);
v___x_914_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; uint8_t v___x_916_; 
lean_del_object(v___x_911_);
v___x_915_ = lean_string_utf8_byte_size(v_fst_908_);
v___x_916_ = lean_nat_dec_eq(v___x_915_, v_pending_904_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_nat_add(v_snd_909_, v___x_917_);
lean_dec(v_snd_909_);
v___x_919_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_918_, v_fst_908_);
v___x_920_ = lean_box(0);
lean_inc(v___y_882_);
lean_inc(v_i_881_);
v___x_921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_913_, v_i_881_, v_out_903_, v_pending_904_, v___y_882_, v___x_920_, v___x_919_);
lean_dec_ref(v___x_913_);
v___y_890_ = v_it_906_;
v_val_891_ = v___x_921_;
goto v___jp_889_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v_snd_909_);
v___x_922_ = lean_box(0);
lean_inc(v___y_882_);
lean_inc(v_i_881_);
v___x_923_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_913_, v_i_881_, v_out_903_, v_pending_904_, v___y_882_, v___x_922_, v_fst_908_);
lean_dec_ref(v___x_913_);
v___y_890_ = v_it_906_;
v_val_891_ = v___x_923_;
goto v___jp_889_;
}
}
else
{
lean_object* v___x_924_; uint8_t v___x_925_; 
lean_dec_ref(v___x_913_);
v___x_924_ = lean_string_utf8_byte_size(v_fst_908_);
v___x_925_ = lean_nat_dec_eq(v___x_924_, v_pending_904_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_snd_909_, v___x_926_);
lean_dec(v_snd_909_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 1, v___x_927_);
v___x_929_ = v___x_911_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_fst_908_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v___x_927_);
v___x_929_ = v_reuseFailAlloc_931_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; 
v___x_930_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_881_, v___y_882_, v___x_883_, v___x_884_, v_src_885_, v___x_886_, v_it_906_, v___x_929_);
return v___x_930_;
}
}
else
{
lean_object* v___x_933_; 
if (v_isShared_912_ == 0)
{
v___x_933_ = v___x_911_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_fst_908_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_snd_909_);
v___x_933_ = v_reuseFailAlloc_935_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; 
v___x_934_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_881_, v___y_882_, v___x_883_, v___x_884_, v_src_885_, v___x_886_, v_it_906_, v___x_933_);
return v___x_934_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_886_);
lean_dec_ref(v_src_885_);
lean_dec_ref(v___x_883_);
lean_dec(v___y_882_);
lean_dec(v_i_881_);
return v_b_888_;
}
v___jp_889_:
{
if (lean_obj_tag(v_val_891_) == 0)
{
lean_object* v_a_892_; 
lean_dec(v___y_890_);
lean_dec(v___x_886_);
lean_dec_ref(v_src_885_);
lean_dec_ref(v___x_883_);
lean_dec(v___y_882_);
lean_dec(v_i_881_);
v_a_892_ = lean_ctor_get(v_val_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v_val_891_, 1);
return v_a_892_;
}
else
{
lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_893_ = lean_ctor_get(v_val_891_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v_val_891_, 1);
v___x_894_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_881_, v___y_882_, v___x_883_, v___x_884_, v_src_885_, v___x_886_, v___y_890_, v_a_893_);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object* v_i_960_, lean_object* v___y_961_, lean_object* v___x_962_, lean_object* v___x_963_, lean_object* v_src_964_, lean_object* v___x_965_, lean_object* v_a_966_, lean_object* v_b_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_960_, v___y_961_, v___x_962_, v___x_963_, v_src_964_, v___x_965_, v_a_966_, v_b_967_);
lean_dec(v___x_963_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object* v_i_972_, lean_object* v_src_973_){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___y_980_; lean_object* v___x_984_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_string_utf8_byte_size(v_src_973_);
lean_inc_ref_n(v_src_973_, 3);
v___x_976_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_976_, 0, v_src_973_);
lean_ctor_set(v___x_976_, 1, v___x_974_);
lean_ctor_set(v___x_976_, 2, v___x_975_);
v___x_977_ = lean_box(0);
v___x_978_ = l_String_lines(v_src_973_);
lean_inc(v___x_978_);
lean_inc_ref(v___x_976_);
v___x_984_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_976_, v___x_975_, v_src_973_, v___x_975_, v___x_978_, v___x_977_);
if (lean_obj_tag(v___x_984_) == 0)
{
v___y_980_ = v___x_974_;
goto v___jp_979_;
}
else
{
lean_object* v_val_985_; 
v_val_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref_known(v___x_984_, 1);
v___y_980_ = v_val_985_;
goto v___jp_979_;
}
v___jp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_fst_983_; 
v___x_981_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0));
v___x_982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_972_, v___y_980_, v___x_976_, v___x_975_, v_src_973_, v___x_975_, v___x_978_, v___x_981_);
v_fst_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_983_);
lean_dec_ref(v___x_982_);
return v_fst_983_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object* v_i_986_, lean_object* v___y_987_, lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v_src_990_, lean_object* v___x_991_, lean_object* v_inst_992_, lean_object* v_R_993_, lean_object* v_a_994_, lean_object* v_b_995_, lean_object* v_c_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_986_, v___y_987_, v___x_988_, v___x_989_, v_src_990_, v___x_991_, v_a_994_, v_b_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object* v_i_998_, lean_object* v___y_999_, lean_object* v___x_1000_, lean_object* v___x_1001_, lean_object* v_src_1002_, lean_object* v___x_1003_, lean_object* v_inst_1004_, lean_object* v_R_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_, lean_object* v_c_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(v_i_998_, v___y_999_, v___x_1000_, v___x_1001_, v_src_1002_, v___x_1003_, v_inst_1004_, v_R_1005_, v_a_1006_, v_b_1007_, v_c_1008_);
lean_dec(v___x_1001_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_src_1012_, lean_object* v___x_1013_, lean_object* v_inst_1014_, lean_object* v_R_1015_, lean_object* v_a_1016_, lean_object* v_b_1017_, lean_object* v_c_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1010_, v___x_1011_, v_src_1012_, v___x_1013_, v_a_1016_, v_b_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v_src_1022_, lean_object* v___x_1023_, lean_object* v_inst_1024_, lean_object* v_R_1025_, lean_object* v_a_1026_, lean_object* v_b_1027_, lean_object* v_c_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(v___x_1020_, v___x_1021_, v_src_1022_, v___x_1023_, v_inst_1024_, v_R_1025_, v_a_1026_, v_b_1027_, v_c_1028_);
lean_dec(v___x_1021_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object* v_i_1030_, lean_object* v___y_1031_, lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_src_1034_, lean_object* v___x_1035_, lean_object* v_inst_1036_, lean_object* v_R_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_, lean_object* v_c_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_1030_, v___y_1031_, v___x_1032_, v___x_1033_, v_src_1034_, v___x_1035_, v_a_1038_, v_b_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object* v_i_1042_, lean_object* v___y_1043_, lean_object* v___x_1044_, lean_object* v___x_1045_, lean_object* v_src_1046_, lean_object* v___x_1047_, lean_object* v_inst_1048_, lean_object* v_R_1049_, lean_object* v_a_1050_, lean_object* v_b_1051_, lean_object* v_c_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(v_i_1042_, v___y_1043_, v___x_1044_, v___x_1045_, v_src_1046_, v___x_1047_, v_inst_1048_, v_R_1049_, v_a_1050_, v_b_1051_, v_c_1052_);
lean_dec(v___x_1045_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object* v___x_1054_, lean_object* v___x_1055_, lean_object* v_src_1056_, lean_object* v___x_1057_, lean_object* v_inst_1058_, lean_object* v_R_1059_, lean_object* v_a_1060_, lean_object* v_b_1061_, lean_object* v_c_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_1054_, v___x_1055_, v_src_1056_, v___x_1057_, v_a_1060_, v_b_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v_src_1066_, lean_object* v___x_1067_, lean_object* v_inst_1068_, lean_object* v_R_1069_, lean_object* v_a_1070_, lean_object* v_b_1071_, lean_object* v_c_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(v___x_1064_, v___x_1065_, v_src_1066_, v___x_1067_, v_inst_1068_, v_R_1069_, v_a_1070_, v_b_1071_, v_c_1072_);
lean_dec(v___x_1065_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v_zero_1076_; uint8_t v_isZero_1077_; 
v_zero_1076_ = lean_unsigned_to_nat(0u);
v_isZero_1077_ = lean_nat_dec_eq(v_x_1074_, v_zero_1076_);
if (v_isZero_1077_ == 1)
{
lean_dec(v_x_1074_);
return v_x_1075_;
}
else
{
uint32_t v___x_1078_; lean_object* v_one_1079_; lean_object* v_n_1080_; lean_object* v___x_1081_; 
v___x_1078_ = 96;
v_one_1079_ = lean_unsigned_to_nat(1u);
v_n_1080_ = lean_nat_sub(v_x_1074_, v_one_1079_);
lean_dec(v_x_1074_);
v___x_1081_ = lean_string_push(v_x_1075_, v___x_1078_);
v_x_1074_ = v_n_1080_;
v_x_1075_ = v___x_1081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object* v_value_1084_){
_start:
{
lean_object* v___y_1086_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1108_; 
v___x_1100_ = lean_string_utf8_byte_size(v_value_1084_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1108_ = lean_nat_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = lean_unsigned_to_nat(1u);
v___x_1110_ = lean_nat_dec_le(v___x_1109_, v___x_1100_);
if (v___x_1110_ == 0)
{
goto v___jp_1102_;
}
else
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1112_ = lean_string_memcmp(v_value_1084_, v___x_1111_, v___x_1101_, v___x_1101_, v___x_1109_);
if (v___x_1112_ == 0)
{
goto v___jp_1102_;
}
else
{
goto v___jp_1094_;
}
}
}
else
{
lean_object* v___x_1113_; 
lean_dec_ref(v_value_1084_);
v___x_1113_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___y_1086_ = v___x_1113_;
goto v___jp_1085_;
}
v___jp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_delim_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1087_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_1088_ = l_Lean_Doc_longestBacktickRun(v___y_1086_);
v___x_1089_ = lean_unsigned_to_nat(1u);
v___x_1090_ = lean_nat_add(v___x_1088_, v___x_1089_);
lean_dec(v___x_1088_);
v_delim_1091_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___x_1090_, v___x_1087_);
lean_inc_ref(v_delim_1091_);
v___x_1092_ = lean_string_append(v_delim_1091_, v___y_1086_);
lean_dec_ref(v___y_1086_);
v___x_1093_ = lean_string_append(v___x_1092_, v_delim_1091_);
lean_dec_ref(v_delim_1091_);
return v___x_1093_;
}
v___jp_1094_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1096_ = lean_string_append(v___x_1095_, v_value_1084_);
lean_dec_ref(v_value_1084_);
v___x_1097_ = lean_string_append(v___x_1096_, v___x_1095_);
v___y_1086_ = v___x_1097_;
goto v___jp_1085_;
}
v___jp_1098_:
{
uint8_t v___x_1099_; 
lean_inc_ref(v_value_1084_);
v___x_1099_ = l_Lean_Doc_versoCodeBoundarySpaces(v_value_1084_);
if (v___x_1099_ == 0)
{
v___y_1086_ = v_value_1084_;
goto v___jp_1085_;
}
else
{
goto v___jp_1094_;
}
}
v___jp_1102_:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1103_ = lean_unsigned_to_nat(1u);
v___x_1104_ = lean_nat_dec_le(v___x_1103_, v___x_1100_);
if (v___x_1104_ == 0)
{
goto v___jp_1098_;
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1105_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1106_ = lean_nat_sub(v___x_1100_, v___x_1103_);
v___x_1107_ = lean_string_memcmp(v_value_1084_, v___x_1105_, v___x_1106_, v___x_1101_, v___x_1103_);
lean_dec(v___x_1106_);
if (v___x_1107_ == 0)
{
goto v___jp_1098_;
}
else
{
goto v___jp_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t v_char_1114_, lean_object* v_as_1115_, size_t v_i_1116_, size_t v_stop_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v___y_1120_; uint8_t v___x_1124_; 
v___x_1124_ = lean_usize_dec_eq(v_i_1116_, v_stop_1117_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_array_uget_borrowed(v_as_1115_, v_i_1116_);
lean_inc(v___x_1125_);
v___x_1126_ = l_Lean_Doc_InlineView_of(v___x_1125_);
if (lean_obj_tag(v___x_1126_) == 1)
{
lean_object* v_val_1127_; 
v_val_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_val_1127_);
lean_dec_ref_known(v___x_1126_, 1);
switch(lean_obj_tag(v_val_1127_))
{
case 1:
{
lean_object* v_view_1128_; lean_object* v___y_1130_; uint32_t v___x_1135_; uint8_t v___x_1136_; 
v_view_1128_ = lean_ctor_get(v_val_1127_, 0);
lean_inc_ref(v_view_1128_);
lean_dec_ref_known(v_val_1127_, 1);
v___x_1135_ = 95;
v___x_1136_ = lean_uint32_dec_eq(v_char_1114_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_unsigned_to_nat(0u);
v___y_1130_ = v___x_1137_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_unsigned_to_nat(1u);
v___y_1130_ = v___x_1138_;
goto v___jp_1129_;
}
v___jp_1129_:
{
lean_object* v_content_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_content_1131_ = lean_ctor_get(v_view_1128_, 2);
lean_inc_ref(v_content_1131_);
lean_dec_ref(v_view_1128_);
v___x_1132_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1114_, v_content_1131_);
lean_dec_ref(v_content_1131_);
v___x_1133_ = lean_nat_add(v___y_1130_, v___x_1132_);
lean_dec(v___x_1132_);
v___x_1134_ = lean_nat_dec_le(v_b_1118_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec(v___x_1133_);
v___y_1120_ = v_b_1118_;
goto v___jp_1119_;
}
else
{
lean_dec(v_b_1118_);
v___y_1120_ = v___x_1133_;
goto v___jp_1119_;
}
}
}
case 2:
{
lean_object* v_view_1139_; lean_object* v___y_1141_; uint32_t v___x_1146_; uint8_t v___x_1147_; 
v_view_1139_ = lean_ctor_get(v_val_1127_, 0);
lean_inc_ref(v_view_1139_);
lean_dec_ref_known(v_val_1127_, 1);
v___x_1146_ = 42;
v___x_1147_ = lean_uint32_dec_eq(v_char_1114_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___y_1141_ = v___x_1148_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_unsigned_to_nat(1u);
v___y_1141_ = v___x_1149_;
goto v___jp_1140_;
}
v___jp_1140_:
{
lean_object* v_content_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_content_1142_ = lean_ctor_get(v_view_1139_, 2);
lean_inc_ref(v_content_1142_);
lean_dec_ref(v_view_1139_);
v___x_1143_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1114_, v_content_1142_);
lean_dec_ref(v_content_1142_);
v___x_1144_ = lean_nat_add(v___y_1141_, v___x_1143_);
lean_dec(v___x_1143_);
v___x_1145_ = lean_nat_dec_le(v_b_1118_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec(v___x_1144_);
v___y_1120_ = v_b_1118_;
goto v___jp_1119_;
}
else
{
lean_dec(v_b_1118_);
v___y_1120_ = v___x_1144_;
goto v___jp_1119_;
}
}
}
case 5:
{
lean_object* v_view_1150_; lean_object* v_content_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_view_1150_ = lean_ctor_get(v_val_1127_, 0);
lean_inc_ref(v_view_1150_);
lean_dec_ref_known(v_val_1127_, 1);
v_content_1151_ = lean_ctor_get(v_view_1150_, 2);
lean_inc_ref(v_content_1151_);
lean_dec_ref(v_view_1150_);
v___x_1152_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1114_, v_content_1151_);
lean_dec_ref(v_content_1151_);
v___x_1153_ = lean_nat_dec_le(v_b_1118_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_dec(v___x_1152_);
v___y_1120_ = v_b_1118_;
goto v___jp_1119_;
}
else
{
lean_dec(v_b_1118_);
v___y_1120_ = v___x_1152_;
goto v___jp_1119_;
}
}
case 9:
{
lean_object* v_view_1154_; lean_object* v_content_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_view_1154_ = lean_ctor_get(v_val_1127_, 0);
lean_inc_ref(v_view_1154_);
lean_dec_ref_known(v_val_1127_, 1);
v_content_1155_ = lean_ctor_get(v_view_1154_, 6);
lean_inc_ref(v_content_1155_);
lean_dec_ref(v_view_1154_);
v___x_1156_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1114_, v_content_1155_);
lean_dec_ref(v_content_1155_);
v___x_1157_ = lean_nat_dec_le(v_b_1118_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec(v___x_1156_);
v___y_1120_ = v_b_1118_;
goto v___jp_1119_;
}
else
{
lean_dec(v_b_1118_);
v___y_1120_ = v___x_1156_;
goto v___jp_1119_;
}
}
default: 
{
lean_dec(v_val_1127_);
v___y_1120_ = v_b_1118_;
goto v___jp_1119_;
}
}
}
else
{
lean_dec(v___x_1126_);
v___y_1120_ = v_b_1118_;
goto v___jp_1119_;
}
}
else
{
return v_b_1118_;
}
v___jp_1119_:
{
size_t v___x_1121_; size_t v___x_1122_; 
v___x_1121_ = ((size_t)1ULL);
v___x_1122_ = lean_usize_add(v_i_1116_, v___x_1121_);
v_i_1116_ = v___x_1122_;
v_b_1118_ = v___y_1120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t v_char_1158_, lean_object* v_inls_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1160_ = lean_unsigned_to_nat(0u);
v___x_1161_ = lean_array_get_size(v_inls_1159_);
v___x_1162_ = lean_nat_dec_lt(v___x_1160_, v___x_1161_);
if (v___x_1162_ == 0)
{
return v___x_1160_;
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_nat_dec_le(v___x_1161_, v___x_1161_);
if (v___x_1163_ == 0)
{
if (v___x_1162_ == 0)
{
return v___x_1160_;
}
else
{
size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = ((size_t)0ULL);
v___x_1165_ = lean_usize_of_nat(v___x_1161_);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1158_, v_inls_1159_, v___x_1164_, v___x_1165_, v___x_1160_);
return v___x_1166_;
}
}
else
{
size_t v___x_1167_; size_t v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = lean_usize_of_nat(v___x_1161_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1158_, v_inls_1159_, v___x_1167_, v___x_1168_, v___x_1160_);
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object* v_char_1170_, lean_object* v_inls_1171_){
_start:
{
uint32_t v_char_boxed_1172_; lean_object* v_res_1173_; 
v_char_boxed_1172_ = lean_unbox_uint32(v_char_1170_);
lean_dec(v_char_1170_);
v_res_1173_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_boxed_1172_, v_inls_1171_);
lean_dec_ref(v_inls_1171_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object* v_char_1174_, lean_object* v_as_1175_, lean_object* v_i_1176_, lean_object* v_stop_1177_, lean_object* v_b_1178_){
_start:
{
uint32_t v_char_boxed_1179_; size_t v_i_boxed_1180_; size_t v_stop_boxed_1181_; lean_object* v_res_1182_; 
v_char_boxed_1179_ = lean_unbox_uint32(v_char_1174_);
lean_dec(v_char_1174_);
v_i_boxed_1180_ = lean_unbox_usize(v_i_1176_);
lean_dec(v_i_1176_);
v_stop_boxed_1181_ = lean_unbox_usize(v_stop_1177_);
lean_dec(v_stop_1177_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_boxed_1179_, v_as_1175_, v_i_boxed_1180_, v_stop_boxed_1181_, v_b_1178_);
lean_dec_ref(v_as_1175_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t v_char_1183_, lean_object* v_inls_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1186_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1183_, v_inls_1184_);
v___x_1187_ = lean_nat_add(v___x_1185_, v___x_1186_);
lean_dec(v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object* v_char_1188_, lean_object* v_inls_1189_){
_start:
{
uint32_t v_char_boxed_1190_; lean_object* v_res_1191_; 
v_char_boxed_1190_ = lean_unbox_uint32(v_char_1188_);
lean_dec(v_char_1188_);
v_res_1191_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_boxed_1190_, v_inls_1189_);
lean_dec_ref(v_inls_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object* v_as_1192_, size_t v_i_1193_, size_t v_stop_1194_, lean_object* v_b_1195_){
_start:
{
lean_object* v___y_1197_; uint8_t v___x_1201_; 
v___x_1201_ = lean_usize_dec_eq(v_i_1193_, v_stop_1194_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; lean_object* v_contents_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1202_ = lean_array_uget_borrowed(v_as_1192_, v_i_1193_);
v_contents_1203_ = lean_ctor_get(v___x_1202_, 2);
v___x_1204_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1203_);
v___x_1205_ = lean_nat_dec_le(v_b_1195_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_dec(v___x_1204_);
v___y_1197_ = v_b_1195_;
goto v___jp_1196_;
}
else
{
lean_dec(v_b_1195_);
v___y_1197_ = v___x_1204_;
goto v___jp_1196_;
}
}
else
{
return v_b_1195_;
}
v___jp_1196_:
{
size_t v___x_1198_; size_t v___x_1199_; 
v___x_1198_ = ((size_t)1ULL);
v___x_1199_ = lean_usize_add(v_i_1193_, v___x_1198_);
v_i_1193_ = v___x_1199_;
v_b_1195_ = v___y_1197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object* v_as_1206_, size_t v_i_1207_, size_t v_stop_1208_, lean_object* v_b_1209_){
_start:
{
lean_object* v___y_1211_; uint8_t v___x_1215_; 
v___x_1215_ = lean_usize_dec_eq(v_i_1207_, v_stop_1208_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v_desc_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1216_ = lean_array_uget_borrowed(v_as_1206_, v_i_1207_);
v_desc_1217_ = lean_ctor_get(v___x_1216_, 3);
v___x_1218_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_desc_1217_);
v___x_1219_ = lean_nat_dec_le(v_b_1209_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_dec(v___x_1218_);
v___y_1211_ = v_b_1209_;
goto v___jp_1210_;
}
else
{
lean_dec(v_b_1209_);
v___y_1211_ = v___x_1218_;
goto v___jp_1210_;
}
}
else
{
return v_b_1209_;
}
v___jp_1210_:
{
size_t v___x_1212_; size_t v___x_1213_; 
v___x_1212_ = ((size_t)1ULL);
v___x_1213_ = lean_usize_add(v_i_1207_, v___x_1212_);
v_i_1207_ = v___x_1213_;
v_b_1209_ = v___y_1211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object* v_as_1220_, size_t v_i_1221_, size_t v_stop_1222_, lean_object* v_b_1223_){
_start:
{
lean_object* v___y_1225_; lean_object* v___y_1230_; uint8_t v___x_1234_; 
v___x_1234_ = lean_usize_dec_eq(v_i_1221_, v_stop_1222_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = lean_array_uget_borrowed(v_as_1220_, v_i_1221_);
lean_inc(v___x_1235_);
v___x_1236_ = l_Lean_Doc_BlockView_of(v___x_1235_);
if (lean_obj_tag(v___x_1236_) == 1)
{
lean_object* v_val_1237_; 
v_val_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v___x_1236_, 1);
switch(lean_obj_tag(v_val_1237_))
{
case 6:
{
lean_object* v_view_1238_; lean_object* v_content_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_view_1238_ = lean_ctor_get(v_val_1237_, 0);
lean_inc_ref(v_view_1238_);
lean_dec_ref_known(v_val_1237_, 1);
v_content_1239_ = lean_ctor_get(v_view_1238_, 4);
lean_inc_ref(v_content_1239_);
lean_dec_ref(v_view_1238_);
v___x_1240_ = lean_unsigned_to_nat(3u);
v___x_1241_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1239_);
lean_dec_ref(v_content_1239_);
v___x_1242_ = lean_nat_dec_le(v___x_1240_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec(v___x_1241_);
v___y_1230_ = v___x_1240_;
goto v___jp_1229_;
}
else
{
v___y_1230_ = v___x_1241_;
goto v___jp_1229_;
}
}
case 4:
{
lean_object* v_view_1243_; lean_object* v_content_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_view_1243_ = lean_ctor_get(v_val_1237_, 0);
lean_inc_ref(v_view_1243_);
lean_dec_ref_known(v_val_1237_, 1);
v_content_1244_ = lean_ctor_get(v_view_1243_, 2);
lean_inc_ref(v_content_1244_);
lean_dec_ref(v_view_1243_);
v___x_1245_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1244_);
lean_dec_ref(v_content_1244_);
v___x_1246_ = lean_nat_dec_le(v_b_1223_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_dec(v___x_1245_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
lean_dec(v_b_1223_);
v___y_1225_ = v___x_1245_;
goto v___jp_1224_;
}
}
case 1:
{
lean_object* v_view_1247_; lean_object* v_items_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_view_1247_ = lean_ctor_get(v_val_1237_, 0);
lean_inc_ref(v_view_1247_);
lean_dec_ref_known(v_val_1237_, 1);
v_items_1248_ = lean_ctor_get(v_view_1247_, 1);
lean_inc_ref(v_items_1248_);
lean_dec_ref(v_view_1247_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_array_get_size(v_items_1248_);
v___x_1251_ = lean_nat_dec_lt(v___x_1249_, v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec_ref(v_items_1248_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_nat_dec_le(v___x_1250_, v___x_1250_);
if (v___x_1252_ == 0)
{
if (v___x_1251_ == 0)
{
lean_dec_ref(v_items_1248_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
size_t v___x_1253_; size_t v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = lean_usize_of_nat(v___x_1250_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1248_, v___x_1253_, v___x_1254_, v_b_1223_);
lean_dec_ref(v_items_1248_);
v___y_1225_ = v___x_1255_;
goto v___jp_1224_;
}
}
else
{
size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((size_t)0ULL);
v___x_1257_ = lean_usize_of_nat(v___x_1250_);
v___x_1258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1248_, v___x_1256_, v___x_1257_, v_b_1223_);
lean_dec_ref(v_items_1248_);
v___y_1225_ = v___x_1258_;
goto v___jp_1224_;
}
}
}
case 2:
{
lean_object* v_view_1259_; lean_object* v_items_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_view_1259_ = lean_ctor_get(v_val_1237_, 0);
lean_inc_ref(v_view_1259_);
lean_dec_ref_known(v_val_1237_, 1);
v_items_1260_ = lean_ctor_get(v_view_1259_, 2);
lean_inc_ref(v_items_1260_);
lean_dec_ref(v_view_1259_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_array_get_size(v_items_1260_);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec_ref(v_items_1260_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_nat_dec_le(v___x_1262_, v___x_1262_);
if (v___x_1264_ == 0)
{
if (v___x_1263_ == 0)
{
lean_dec_ref(v_items_1260_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((size_t)0ULL);
v___x_1266_ = lean_usize_of_nat(v___x_1262_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1260_, v___x_1265_, v___x_1266_, v_b_1223_);
lean_dec_ref(v_items_1260_);
v___y_1225_ = v___x_1267_;
goto v___jp_1224_;
}
}
else
{
size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = ((size_t)0ULL);
v___x_1269_ = lean_usize_of_nat(v___x_1262_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1260_, v___x_1268_, v___x_1269_, v_b_1223_);
lean_dec_ref(v_items_1260_);
v___y_1225_ = v___x_1270_;
goto v___jp_1224_;
}
}
}
case 3:
{
lean_object* v_view_1271_; lean_object* v_items_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_view_1271_ = lean_ctor_get(v_val_1237_, 0);
lean_inc_ref(v_view_1271_);
lean_dec_ref_known(v_val_1237_, 1);
v_items_1272_ = lean_ctor_get(v_view_1271_, 1);
lean_inc_ref(v_items_1272_);
lean_dec_ref(v_view_1271_);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_array_get_size(v_items_1272_);
v___x_1275_ = lean_nat_dec_lt(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v_items_1272_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_nat_dec_le(v___x_1274_, v___x_1274_);
if (v___x_1276_ == 0)
{
if (v___x_1275_ == 0)
{
lean_dec_ref(v_items_1272_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
size_t v___x_1277_; size_t v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = ((size_t)0ULL);
v___x_1278_ = lean_usize_of_nat(v___x_1274_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1272_, v___x_1277_, v___x_1278_, v_b_1223_);
lean_dec_ref(v_items_1272_);
v___y_1225_ = v___x_1279_;
goto v___jp_1224_;
}
}
else
{
size_t v___x_1280_; size_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = lean_usize_of_nat(v___x_1274_);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1272_, v___x_1280_, v___x_1281_, v_b_1223_);
lean_dec_ref(v_items_1272_);
v___y_1225_ = v___x_1282_;
goto v___jp_1224_;
}
}
}
default: 
{
lean_dec(v_val_1237_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
}
}
else
{
lean_dec(v___x_1236_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
}
else
{
return v_b_1223_;
}
v___jp_1224_:
{
size_t v___x_1226_; size_t v___x_1227_; 
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1221_, v___x_1226_);
v_i_1221_ = v___x_1227_;
v_b_1223_ = v___y_1225_;
goto _start;
}
v___jp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v___y_1230_, v___x_1231_);
lean_dec(v___y_1230_);
v___x_1233_ = lean_nat_dec_le(v_b_1223_, v___x_1232_);
if (v___x_1233_ == 0)
{
lean_dec(v___x_1232_);
v___y_1225_ = v_b_1223_;
goto v___jp_1224_;
}
else
{
lean_dec(v_b_1223_);
v___y_1225_ = v___x_1232_;
goto v___jp_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object* v_blks_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_array_get_size(v_blks_1283_);
v___x_1286_ = lean_nat_dec_lt(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
return v___x_1284_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_le(v___x_1285_, v___x_1285_);
if (v___x_1287_ == 0)
{
if (v___x_1286_ == 0)
{
return v___x_1284_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1285_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1283_, v___x_1288_, v___x_1289_, v___x_1284_);
return v___x_1290_;
}
}
else
{
size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = lean_usize_of_nat(v___x_1285_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1283_, v___x_1291_, v___x_1292_, v___x_1284_);
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object* v_as_1294_, size_t v_i_1295_, size_t v_stop_1296_, lean_object* v_b_1297_){
_start:
{
lean_object* v___y_1299_; uint8_t v___x_1303_; 
v___x_1303_ = lean_usize_dec_eq(v_i_1295_, v_stop_1296_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v_contents_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1304_ = lean_array_uget_borrowed(v_as_1294_, v_i_1295_);
v_contents_1305_ = lean_ctor_get(v___x_1304_, 2);
v___x_1306_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1305_);
v___x_1307_ = lean_nat_dec_le(v_b_1297_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v___x_1306_);
v___y_1299_ = v_b_1297_;
goto v___jp_1298_;
}
else
{
lean_dec(v_b_1297_);
v___y_1299_ = v___x_1306_;
goto v___jp_1298_;
}
}
else
{
return v_b_1297_;
}
v___jp_1298_:
{
size_t v___x_1300_; size_t v___x_1301_; 
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_add(v_i_1295_, v___x_1300_);
v_i_1295_ = v___x_1301_;
v_b_1297_ = v___y_1299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object* v_as_1308_, lean_object* v_i_1309_, lean_object* v_stop_1310_, lean_object* v_b_1311_){
_start:
{
size_t v_i_boxed_1312_; size_t v_stop_boxed_1313_; lean_object* v_res_1314_; 
v_i_boxed_1312_ = lean_unbox_usize(v_i_1309_);
lean_dec(v_i_1309_);
v_stop_boxed_1313_ = lean_unbox_usize(v_stop_1310_);
lean_dec(v_stop_1310_);
v_res_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_as_1308_, v_i_boxed_1312_, v_stop_boxed_1313_, v_b_1311_);
lean_dec_ref(v_as_1308_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object* v_as_1315_, lean_object* v_i_1316_, lean_object* v_stop_1317_, lean_object* v_b_1318_){
_start:
{
size_t v_i_boxed_1319_; size_t v_stop_boxed_1320_; lean_object* v_res_1321_; 
v_i_boxed_1319_ = lean_unbox_usize(v_i_1316_);
lean_dec(v_i_1316_);
v_stop_boxed_1320_ = lean_unbox_usize(v_stop_1317_);
lean_dec(v_stop_1317_);
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_as_1315_, v_i_boxed_1319_, v_stop_boxed_1320_, v_b_1318_);
lean_dec_ref(v_as_1315_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object* v_as_1322_, lean_object* v_i_1323_, lean_object* v_stop_1324_, lean_object* v_b_1325_){
_start:
{
size_t v_i_boxed_1326_; size_t v_stop_boxed_1327_; lean_object* v_res_1328_; 
v_i_boxed_1326_ = lean_unbox_usize(v_i_1323_);
lean_dec(v_i_1323_);
v_stop_boxed_1327_ = lean_unbox_usize(v_stop_1324_);
lean_dec(v_stop_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_as_1322_, v_i_boxed_1326_, v_stop_boxed_1327_, v_b_1325_);
lean_dec_ref(v_as_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object* v_blks_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1329_);
lean_dec_ref(v_blks_1329_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object* v_as_1331_, lean_object* v_i_1332_, lean_object* v_stop_1333_, lean_object* v_b_1334_){
_start:
{
size_t v_i_boxed_1335_; size_t v_stop_boxed_1336_; lean_object* v_res_1337_; 
v_i_boxed_1335_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_stop_boxed_1336_ = lean_unbox_usize(v_stop_1333_);
lean_dec(v_stop_1333_);
v_res_1337_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_as_1331_, v_i_boxed_1335_, v_stop_boxed_1336_, v_b_1334_);
lean_dec_ref(v_as_1331_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object* v_blks_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = lean_unsigned_to_nat(3u);
v___x_1340_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1338_);
v___x_1341_ = lean_nat_dec_le(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec(v___x_1340_);
return v___x_1339_;
}
else
{
return v___x_1340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object* v_blks_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_blks_1342_);
lean_dec_ref(v_blks_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object* v_inl_1344_){
_start:
{
lean_object* v___x_1345_; 
lean_inc(v_inl_1344_);
v___x_1345_ = l_Lean_Doc_LinebreakView_of(v_inl_1344_);
if (lean_obj_tag(v___x_1345_) == 1)
{
uint8_t v___x_1346_; 
lean_dec_ref_known(v___x_1345_, 1);
lean_dec(v_inl_1344_);
v___x_1346_ = 1;
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
lean_dec(v___x_1345_);
v___x_1347_ = l_Lean_Doc_TextView_of(v_inl_1344_);
if (lean_obj_tag(v___x_1347_) == 1)
{
lean_object* v_val_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v_decide_1356_; 
v_val_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = 1;
v___x_1350_ = l_Lean_Doc_TextView_getVersoText(v_val_1348_);
lean_dec(v_val_1348_);
v___x_1351_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v___x_1349_, v___x_1350_);
v___x_1352_ = lean_unsigned_to_nat(0u);
v___x_1353_ = lean_string_utf8_byte_size(v___x_1351_);
v___x_1354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1351_);
lean_ctor_set(v___x_1354_, 1, v___x_1352_);
lean_ctor_set(v___x_1354_, 2, v___x_1353_);
v___x_1355_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1354_, v___x_1352_);
lean_dec_ref_known(v___x_1354_, 3);
v_decide_1356_ = lean_nat_dec_eq(v___x_1355_, v___x_1353_);
lean_dec(v___x_1355_);
return v_decide_1356_;
}
else
{
uint8_t v___x_1357_; 
lean_dec(v___x_1347_);
v___x_1357_ = 0;
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object* v_inl_1358_){
_start:
{
uint8_t v_res_1359_; lean_object* v_r_1360_; 
v_res_1359_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v_inl_1358_);
v_r_1360_ = lean_box(v_res_1359_);
return v_r_1360_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object* v_stx_1361_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Doc_BlockView_of(v_stx_1361_);
if (lean_obj_tag(v___x_1362_) == 1)
{
lean_object* v_val_1363_; 
v_val_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v___x_1362_, 1);
switch(lean_obj_tag(v_val_1363_))
{
case 8:
{
uint8_t v___x_1364_; 
lean_dec_ref_known(v_val_1363_, 1);
v___x_1364_ = 1;
return v___x_1364_;
}
case 9:
{
uint8_t v___x_1365_; 
lean_dec_ref_known(v_val_1363_, 1);
v___x_1365_ = 1;
return v___x_1365_;
}
case 10:
{
uint8_t v___x_1366_; 
lean_dec_ref_known(v_val_1363_, 1);
v___x_1366_ = 1;
return v___x_1366_;
}
case 11:
{
uint8_t v___x_1367_; 
lean_dec_ref_known(v_val_1363_, 1);
v___x_1367_ = 1;
return v___x_1367_;
}
default: 
{
uint8_t v___x_1368_; 
lean_dec(v_val_1363_);
v___x_1368_ = 0;
return v___x_1368_;
}
}
}
else
{
uint8_t v___x_1369_; 
lean_dec(v___x_1362_);
v___x_1369_ = 0;
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object* v_stx_1370_){
_start:
{
uint8_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v_stx_1370_);
v_r_1372_ = lean_box(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object* v_inl_1373_){
_start:
{
lean_object* v___x_1374_; 
lean_inc(v_inl_1373_);
v___x_1374_ = l_Lean_Doc_LinebreakView_of(v_inl_1373_);
if (lean_obj_tag(v___x_1374_) == 1)
{
uint8_t v___x_1375_; 
lean_dec_ref_known(v___x_1374_, 1);
lean_dec(v_inl_1373_);
v___x_1375_ = 1;
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; 
lean_dec(v___x_1374_);
v___x_1376_ = l_Lean_Doc_TextView_of(v_inl_1373_);
if (lean_obj_tag(v___x_1376_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v_decide_1383_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_val_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = l_Lean_Doc_TextView_getVersoTextSource(v_val_1377_);
lean_dec(v_val_1377_);
v___x_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = lean_string_utf8_byte_size(v___x_1378_);
v___x_1381_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1378_);
lean_ctor_set(v___x_1381_, 1, v___x_1379_);
lean_ctor_set(v___x_1381_, 2, v___x_1380_);
v___x_1382_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1381_, v___x_1379_);
lean_dec_ref_known(v___x_1381_, 3);
v_decide_1383_ = lean_nat_dec_eq(v___x_1382_, v___x_1380_);
lean_dec(v___x_1382_);
return v_decide_1383_;
}
else
{
uint8_t v___x_1384_; 
lean_dec(v___x_1376_);
v___x_1384_ = 0;
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object* v_inl_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v_inl_1385_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object* v_as_1388_, size_t v_i_1389_, size_t v_stop_1390_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_usize_dec_eq(v_i_1389_, v_stop_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_array_uget_borrowed(v_as_1388_, v_i_1389_);
lean_inc(v___x_1392_);
v___x_1393_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1392_);
if (v___x_1393_ == 0)
{
uint8_t v___x_1394_; 
v___x_1394_ = 1;
return v___x_1394_;
}
else
{
size_t v___x_1395_; size_t v___x_1396_; 
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1389_, v___x_1395_);
v_i_1389_ = v___x_1396_;
goto _start;
}
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = 0;
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object* v_as_1399_, lean_object* v_i_1400_, lean_object* v_stop_1401_){
_start:
{
size_t v_i_boxed_1402_; size_t v_stop_boxed_1403_; uint8_t v_res_1404_; lean_object* v_r_1405_; 
v_i_boxed_1402_ = lean_unbox_usize(v_i_1400_);
lean_dec(v_i_1400_);
v_stop_boxed_1403_ = lean_unbox_usize(v_stop_1401_);
lean_dec(v_stop_1401_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_as_1399_, v_i_boxed_1402_, v_stop_boxed_1403_);
lean_dec_ref(v_as_1399_);
v_r_1405_ = lean_box(v_res_1404_);
return v_r_1405_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object* v_stx_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_Doc_ParaView_of(v_stx_1406_);
if (lean_obj_tag(v___x_1407_) == 1)
{
lean_object* v_val_1408_; lean_object* v_content_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_val_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v_content_1409_ = lean_ctor_get(v_val_1408_, 1);
lean_inc_ref(v_content_1409_);
lean_dec(v_val_1408_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v___x_1411_ = lean_array_get_size(v_content_1409_);
v___x_1412_ = lean_nat_dec_lt(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
uint8_t v___x_1413_; 
lean_dec_ref(v_content_1409_);
v___x_1413_ = 1;
return v___x_1413_;
}
else
{
if (v___x_1412_ == 0)
{
lean_dec_ref(v_content_1409_);
return v___x_1412_;
}
else
{
size_t v___x_1414_; size_t v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1411_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_content_1409_, v___x_1414_, v___x_1415_);
lean_dec_ref(v_content_1409_);
if (v___x_1416_ == 0)
{
return v___x_1412_;
}
else
{
uint8_t v___x_1417_; 
v___x_1417_ = 0;
return v___x_1417_;
}
}
}
}
else
{
uint8_t v___x_1418_; 
lean_dec(v___x_1407_);
v___x_1418_ = 0;
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object* v_stx_1419_){
_start:
{
uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_res_1420_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_stx_1419_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object* v_stx_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Doc_LinebreakView_of(v_stx_1422_);
if (lean_obj_tag(v___x_1423_) == 1)
{
uint8_t v___x_1424_; 
lean_dec_ref_known(v___x_1423_, 1);
v___x_1424_ = 1;
return v___x_1424_;
}
else
{
uint8_t v___x_1425_; 
lean_dec(v___x_1423_);
v___x_1425_ = 0;
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object* v_stx_1426_){
_start:
{
uint8_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v_stx_1426_);
v_r_1428_ = lean_box(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object* v_inls_1429_){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1430_ = lean_array_get_size(v_inls_1429_);
v___x_1431_ = lean_unsigned_to_nat(1u);
v___x_1432_ = lean_nat_dec_eq(v___x_1430_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_box(0);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v_inl_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v_inl_1435_ = lean_array_fget_borrowed(v_inls_1429_, v___x_1434_);
lean_inc(v_inl_1435_);
v___x_1436_ = l_Lean_Doc_InlineView_of(v_inl_1435_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_box(0);
return v___x_1437_;
}
else
{
lean_object* v_val_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1461_; 
v_val_1438_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1440_ = v___x_1436_;
v_isShared_1441_ = v_isSharedCheck_1461_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_val_1438_);
lean_dec(v___x_1436_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1461_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
switch(lean_obj_tag(v_val_1438_))
{
case 1:
{
lean_object* v___x_1443_; 
lean_dec_ref_known(v_val_1438_, 1);
lean_inc(v_inl_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_inl_1435_);
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_inl_1435_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
case 2:
{
lean_object* v___x_1446_; 
lean_dec_ref_known(v_val_1438_, 1);
lean_inc(v_inl_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_inl_1435_);
v___x_1446_ = v___x_1440_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_inl_1435_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
case 3:
{
lean_object* v___x_1449_; 
lean_dec_ref_known(v_val_1438_, 1);
lean_inc(v_inl_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_inl_1435_);
v___x_1449_ = v___x_1440_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_inl_1435_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
case 4:
{
lean_object* v___x_1452_; 
lean_dec_ref_known(v_val_1438_, 1);
lean_inc(v_inl_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_inl_1435_);
v___x_1452_ = v___x_1440_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_inl_1435_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
case 6:
{
lean_object* v___x_1455_; 
lean_dec_ref_known(v_val_1438_, 1);
lean_inc(v_inl_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_inl_1435_);
v___x_1455_ = v___x_1440_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_inl_1435_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
case 9:
{
lean_object* v___x_1458_; 
lean_dec_ref_known(v_val_1438_, 1);
lean_inc(v_inl_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_inl_1435_);
v___x_1458_ = v___x_1440_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_inl_1435_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
default: 
{
lean_object* v___x_1460_; 
lean_del_object(v___x_1440_);
lean_dec(v_val_1438_);
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object* v_inls_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_inls_1462_);
lean_dec_ref(v_inls_1462_);
return v_res_1463_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = 41;
v___x_1465_ = lean_box_uint32(v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
v___x_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = 93;
v___x_1469_ = lean_box_uint32(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
v___x_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object* v_a_1472_){
_start:
{
if (lean_obj_tag(v_a_1472_) == 0)
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0);
return v___x_1473_;
}
else
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object* v_a_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_a_1475_);
lean_dec_ref(v_a_1475_);
return v_res_1476_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = 95;
v___x_1478_ = lean_box_uint32(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
return v___x_1480_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = 42;
v___x_1482_ = lean_box_uint32(v___x_1481_);
return v___x_1482_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = 96;
v___x_1486_ = lean_box_uint32(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
v___x_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object* v_inl_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Doc_InlineView_of(v_inl_1489_);
if (lean_obj_tag(v___x_1490_) == 1)
{
lean_object* v_val_1491_; 
v_val_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v___x_1490_, 1);
switch(lean_obj_tag(v_val_1491_))
{
case 1:
{
lean_object* v___x_1492_; 
lean_dec_ref_known(v_val_1491_, 1);
v___x_1492_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1492_;
}
case 2:
{
lean_object* v___x_1493_; 
lean_dec_ref_known(v_val_1491_, 1);
v___x_1493_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1493_;
}
case 3:
{
lean_object* v___x_1494_; 
lean_dec_ref_known(v_val_1491_, 1);
v___x_1494_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1494_;
}
case 4:
{
lean_object* v___x_1495_; 
lean_dec_ref_known(v_val_1491_, 1);
v___x_1495_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1495_;
}
case 5:
{
lean_object* v_view_1496_; lean_object* v_target_1497_; lean_object* v___x_1498_; 
v_view_1496_ = lean_ctor_get(v_val_1491_, 0);
lean_inc_ref(v_view_1496_);
lean_dec_ref_known(v_val_1491_, 1);
v_target_1497_ = lean_ctor_get(v_view_1496_, 4);
lean_inc_ref(v_target_1497_);
lean_dec_ref(v_view_1496_);
v___x_1498_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1497_);
lean_dec_ref(v_target_1497_);
return v___x_1498_;
}
case 6:
{
lean_object* v_view_1499_; lean_object* v_target_1500_; lean_object* v___x_1501_; 
v_view_1499_ = lean_ctor_get(v_val_1491_, 0);
lean_inc_ref(v_view_1499_);
lean_dec_ref_known(v_val_1491_, 1);
v_target_1500_ = lean_ctor_get(v_view_1499_, 4);
lean_inc_ref(v_target_1500_);
lean_dec_ref(v_view_1499_);
v___x_1501_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1500_);
lean_dec_ref(v_target_1500_);
return v___x_1501_;
}
case 7:
{
lean_object* v___x_1502_; 
lean_dec_ref_known(v_val_1491_, 1);
v___x_1502_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1502_;
}
case 9:
{
lean_object* v_view_1503_; lean_object* v_content_1504_; lean_object* v___x_1505_; 
v_view_1503_ = lean_ctor_get(v_val_1491_, 0);
lean_inc_ref(v_view_1503_);
lean_dec_ref_known(v_val_1491_, 1);
v_content_1504_ = lean_ctor_get(v_view_1503_, 6);
lean_inc_ref(v_content_1504_);
lean_dec_ref(v_view_1503_);
v___x_1505_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_1504_);
lean_dec_ref(v_content_1504_);
if (lean_obj_tag(v___x_1505_) == 1)
{
lean_object* v_val_1506_; 
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v_inl_1489_ = v_val_1506_;
goto _start;
}
else
{
lean_object* v___x_1508_; 
lean_dec(v___x_1505_);
v___x_1508_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1508_;
}
}
default: 
{
lean_object* v___x_1509_; 
lean_dec(v_val_1491_);
v___x_1509_ = lean_box(0);
return v___x_1509_;
}
}
}
else
{
lean_object* v___x_1510_; 
lean_dec(v___x_1490_);
v___x_1510_ = lean_box(0);
return v___x_1510_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = 36;
v___x_1512_ = lean_box_uint32(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object* v_stx_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Doc_InlineView_of(v_stx_1515_);
if (lean_obj_tag(v___x_1516_) == 1)
{
lean_object* v_val_1517_; 
v_val_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v___x_1516_, 1);
switch(lean_obj_tag(v_val_1517_))
{
case 1:
{
lean_object* v___x_1518_; 
lean_dec_ref_known(v_val_1517_, 1);
v___x_1518_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1518_;
}
case 2:
{
lean_object* v___x_1519_; 
lean_dec_ref_known(v_val_1517_, 1);
v___x_1519_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1519_;
}
case 3:
{
lean_object* v___x_1520_; 
lean_dec_ref_known(v_val_1517_, 1);
v___x_1520_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1520_;
}
case 4:
{
lean_object* v___x_1521_; 
lean_dec_ref_known(v_val_1517_, 1);
v___x_1521_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0);
return v___x_1521_;
}
default: 
{
lean_object* v___x_1522_; 
lean_dec(v_val_1517_);
v___x_1522_ = lean_box(0);
return v___x_1522_;
}
}
}
else
{
lean_object* v___x_1523_; 
lean_dec(v___x_1516_);
v___x_1523_ = lean_box(0);
return v___x_1523_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object* v_inl_1524_, lean_object* v_next_x3f_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1524_);
if (lean_obj_tag(v___x_1526_) == 1)
{
if (lean_obj_tag(v_next_x3f_1525_) == 0)
{
uint8_t v___x_1527_; 
lean_dec_ref_known(v___x_1526_, 1);
v___x_1527_ = 0;
return v___x_1527_;
}
else
{
lean_object* v_val_1528_; lean_object* v_val_1529_; lean_object* v___x_1530_; 
v_val_1528_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1528_);
lean_dec_ref_known(v___x_1526_, 1);
v_val_1529_ = lean_ctor_get(v_next_x3f_1525_, 0);
lean_inc(v_val_1529_);
lean_dec_ref_known(v_next_x3f_1525_, 1);
v___x_1530_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1529_);
if (lean_obj_tag(v___x_1530_) == 1)
{
lean_object* v_val_1531_; uint32_t v___x_1532_; uint32_t v___x_1533_; uint8_t v___x_1534_; 
v_val_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = lean_unbox_uint32(v_val_1528_);
lean_dec(v_val_1528_);
v___x_1533_ = lean_unbox_uint32(v_val_1531_);
lean_dec(v_val_1531_);
v___x_1534_ = lean_uint32_dec_eq(v___x_1532_, v___x_1533_);
return v___x_1534_;
}
else
{
uint8_t v___x_1535_; 
lean_dec(v___x_1530_);
lean_dec(v_val_1528_);
v___x_1535_ = 0;
return v___x_1535_;
}
}
}
else
{
uint8_t v___x_1536_; 
lean_dec(v___x_1526_);
lean_dec(v_next_x3f_1525_);
v___x_1536_ = 0;
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object* v_inl_1537_, lean_object* v_next_x3f_1538_){
_start:
{
uint8_t v_res_1539_; lean_object* v_r_1540_; 
v_res_1539_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_inl_1537_, v_next_x3f_1538_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object* v_inl_1541_, lean_object* v_next_x3f_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1541_);
if (lean_obj_tag(v___x_1543_) == 1)
{
lean_object* v_val_1544_; uint32_t v___x_1545_; uint32_t v___x_1546_; uint8_t v___x_1547_; 
v_val_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_val_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = 96;
v___x_1546_ = lean_unbox_uint32(v_val_1544_);
lean_dec(v_val_1544_);
v___x_1547_ = lean_uint32_dec_eq(v___x_1546_, v___x_1545_);
if (v___x_1547_ == 0)
{
lean_dec(v_next_x3f_1542_);
return v___x_1547_;
}
else
{
if (lean_obj_tag(v_next_x3f_1542_) == 0)
{
uint8_t v___x_1548_; 
v___x_1548_ = 0;
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1550_; 
v_val_1549_ = lean_ctor_get(v_next_x3f_1542_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_next_x3f_1542_, 1);
v___x_1550_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1549_);
if (lean_obj_tag(v___x_1550_) == 1)
{
lean_object* v_val_1551_; uint32_t v___x_1552_; uint8_t v___x_1553_; 
v_val_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = lean_unbox_uint32(v_val_1551_);
lean_dec(v_val_1551_);
v___x_1553_ = lean_uint32_dec_eq(v___x_1552_, v___x_1545_);
return v___x_1553_;
}
else
{
uint8_t v___x_1554_; 
lean_dec(v___x_1550_);
v___x_1554_ = 0;
return v___x_1554_;
}
}
}
}
else
{
uint8_t v___x_1555_; 
lean_dec(v___x_1543_);
lean_dec(v_next_x3f_1542_);
v___x_1555_ = 0;
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object* v_inl_1556_, lean_object* v_next_x3f_1557_){
_start:
{
uint8_t v_res_1558_; lean_object* v_r_1559_; 
v_res_1558_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v_inl_1556_, v_next_x3f_1557_);
v_r_1559_ = lean_box(v_res_1558_);
return v_r_1559_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object* v_inls_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = lean_array_get_size(v_inls_1560_);
v___x_1563_ = lean_nat_dec_lt(v___x_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_array_fget_borrowed(v_inls_1560_, v___x_1561_);
lean_inc(v___x_1564_);
v___x_1565_ = l_Lean_Doc_TextView_of(v___x_1564_);
if (lean_obj_tag(v___x_1565_) == 1)
{
lean_object* v_val_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_val_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = l_Lean_Doc_TextView_getVersoText(v_val_1566_);
lean_dec(v_val_1566_);
v___x_1568_ = lean_string_utf8_byte_size(v___x_1567_);
v___x_1569_ = lean_unsigned_to_nat(1u);
v___x_1570_ = lean_nat_dec_le(v___x_1569_, v___x_1568_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v___x_1567_);
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_1572_ = lean_string_memcmp(v___x_1567_, v___x_1571_, v___x_1561_, v___x_1561_, v___x_1569_);
lean_dec_ref(v___x_1567_);
return v___x_1572_;
}
}
else
{
uint8_t v___x_1573_; 
lean_dec(v___x_1565_);
v___x_1573_ = 0;
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object* v_inls_1574_){
_start:
{
uint8_t v_res_1575_; lean_object* v_r_1576_; 
v_res_1575_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_inls_1574_);
lean_dec_ref(v_inls_1574_);
v_r_1576_ = lean_box(v_res_1575_);
return v_r_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object* v_x_1580_, lean_object* v_a_1581_){
_start:
{
if (lean_obj_tag(v_x_1580_) == 0)
{
lean_object* v_url_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v_snd_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_snd_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_url_1582_ = lean_ctor_get(v_x_1580_, 2);
v___x_1583_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_1584_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1583_, v_a_1581_);
v_snd_1585_ = lean_ctor_get(v___x_1584_, 1);
lean_inc(v_snd_1585_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = l_Lean_TSyntax_getVersoLinkUrl(v_url_1582_);
v___x_1587_ = l_Lean_Doc_escapeVersoLinkUrl(v___x_1586_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1587_, v_snd_1585_);
lean_dec_ref(v___x_1587_);
v_snd_1589_ = lean_ctor_get(v___x_1588_, 1);
lean_inc(v_snd_1589_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_1591_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1590_, v_snd_1589_);
return v___x_1591_;
}
else
{
lean_object* v_name_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v_snd_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_snd_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_name_1592_ = lean_ctor_get(v_x_1580_, 2);
v___x_1593_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_1594_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1593_, v_a_1581_);
v_snd_1595_ = lean_ctor_get(v___x_1594_, 1);
lean_inc(v_snd_1595_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = l_Lean_TSyntax_getVersoRefName(v_name_1592_);
v___x_1597_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1596_, v_snd_1595_);
lean_dec_ref(v___x_1596_);
v_snd_1598_ = lean_ctor_get(v___x_1597_, 1);
lean_inc(v_snd_1598_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_1600_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1599_, v_snd_1598_);
return v___x_1600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object* v_x_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1601_, v_a_1602_);
lean_dec_ref(v_x_1601_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object* v_x_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1604_, v_a_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object* v_x_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(v_x_1608_, v_a_1609_, v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_x_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object* v_s_1612_, lean_object* v_pos_1613_){
_start:
{
lean_object* v_str_1614_; lean_object* v_startInclusive_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v_decide_1619_; 
v_str_1614_ = lean_ctor_get(v_s_1612_, 0);
v_startInclusive_1615_ = lean_ctor_get(v_s_1612_, 1);
v___x_1616_ = lean_nat_add(v_startInclusive_1615_, v_pos_1613_);
v___x_1617_ = lean_nat_sub(v___x_1616_, v_startInclusive_1615_);
v___x_1618_ = lean_unsigned_to_nat(0u);
v_decide_1619_ = lean_nat_dec_eq(v___x_1617_, v___x_1618_);
if (v_decide_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint32_t v___x_1625_; uint32_t v___x_1626_; uint8_t v___x_1627_; 
lean_inc(v_startInclusive_1615_);
lean_inc_ref(v_str_1614_);
v___x_1620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1620_, 0, v_str_1614_);
lean_ctor_set(v___x_1620_, 1, v_startInclusive_1615_);
lean_ctor_set(v___x_1620_, 2, v___x_1616_);
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = lean_nat_sub(v___x_1617_, v___x_1621_);
lean_dec(v___x_1617_);
v___x_1623_ = l_String_Slice_posLE(v___x_1620_, v___x_1622_);
lean_dec_ref_known(v___x_1620_, 3);
v___x_1624_ = lean_nat_add(v_startInclusive_1615_, v___x_1623_);
v___x_1625_ = lean_string_utf8_get_fast(v_str_1614_, v___x_1624_);
lean_dec(v___x_1624_);
v___x_1626_ = 32;
v___x_1627_ = lean_uint32_dec_eq(v___x_1625_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_dec(v___x_1623_);
return v_pos_1613_;
}
else
{
lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = lean_nat_add(v___x_1623_, v___x_1621_);
v___x_1629_ = lean_nat_dec_le(v___x_1628_, v_pos_1613_);
lean_dec(v___x_1628_);
if (v___x_1629_ == 0)
{
lean_dec(v___x_1623_);
return v_pos_1613_;
}
else
{
lean_dec(v_pos_1613_);
v_pos_1613_ = v___x_1623_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1617_);
lean_dec(v___x_1616_);
return v_pos_1613_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object* v_s_1631_, lean_object* v_pos_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v_s_1631_, v_pos_1632_);
lean_dec_ref(v_s_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object* v_marker_1634_, lean_object* v_contents_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_alone_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_string_utf8_byte_size(v_marker_1634_);
lean_inc_ref(v_marker_1634_);
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v_marker_1634_);
lean_ctor_set(v___x_1639_, 1, v___x_1637_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
v___x_1640_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v___x_1639_, v___x_1638_);
lean_dec_ref_known(v___x_1639_, 3);
v_alone_1641_ = lean_string_utf8_extract_fast(v_marker_1634_, v___x_1637_, v___x_1640_);
lean_dec(v___x_1640_);
v___x_1642_ = lean_array_get_size(v_contents_1635_);
v___x_1643_ = lean_nat_dec_lt(v___x_1637_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
lean_dec_ref(v_marker_1634_);
v___x_1644_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_alone_1641_, v_a_1636_);
lean_dec_ref(v_alone_1641_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = lean_array_fget_borrowed(v_contents_1635_, v___x_1637_);
lean_inc(v___x_1645_);
v___x_1646_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v___x_1645_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v_alone_1641_);
v___x_1647_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_marker_1634_, v_a_1636_);
lean_dec_ref(v_marker_1634_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v_marker_1634_);
v___x_1648_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_1649_ = lean_string_append(v_alone_1641_, v___x_1648_);
v___x_1650_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1649_, v_a_1636_);
lean_dec_ref(v___x_1649_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object* v_marker_1651_, lean_object* v_contents_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1651_, v_contents_1652_, v_a_1653_);
lean_dec_ref(v_contents_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object* v_marker_1655_, lean_object* v_contents_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1655_, v_contents_1656_, v_a_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object* v_marker_1660_, lean_object* v_contents_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(v_marker_1660_, v_contents_1661_, v_a_1662_, v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_contents_1661_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object* v_as_1665_, size_t v_i_1666_, size_t v_stop_1667_, lean_object* v_b_1668_){
_start:
{
lean_object* v___y_1670_; uint8_t v___x_1674_; 
v___x_1674_ = lean_usize_dec_eq(v_i_1666_, v_stop_1667_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = lean_array_uget_borrowed(v_as_1665_, v_i_1666_);
lean_inc(v___x_1675_);
v___x_1676_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_inc(v___x_1675_);
v___x_1677_ = lean_array_push(v_b_1668_, v___x_1675_);
v___y_1670_ = v___x_1677_;
goto v___jp_1669_;
}
else
{
v___y_1670_ = v_b_1668_;
goto v___jp_1669_;
}
}
else
{
return v_b_1668_;
}
v___jp_1669_:
{
size_t v___x_1671_; size_t v___x_1672_; 
v___x_1671_ = ((size_t)1ULL);
v___x_1672_ = lean_usize_add(v_i_1666_, v___x_1671_);
v_i_1666_ = v___x_1672_;
v_b_1668_ = v___y_1670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object* v_as_1678_, lean_object* v_i_1679_, lean_object* v_stop_1680_, lean_object* v_b_1681_){
_start:
{
size_t v_i_boxed_1682_; size_t v_stop_boxed_1683_; lean_object* v_res_1684_; 
v_i_boxed_1682_ = lean_unbox_usize(v_i_1679_);
lean_dec(v_i_1679_);
v_stop_boxed_1683_ = lean_unbox_usize(v_stop_1680_);
lean_dec(v_stop_1680_);
v_res_1684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_as_1678_, v_i_boxed_1682_, v_stop_boxed_1683_, v_b_1681_);
lean_dec_ref(v_as_1678_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t v_sz_1685_, size_t v_i_1686_, lean_object* v_bs_1687_){
_start:
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_lt(v_i_1686_, v_sz_1685_);
if (v___x_1688_ == 0)
{
return v_bs_1687_;
}
else
{
lean_object* v_v_1689_; lean_object* v___x_1690_; lean_object* v_bs_x27_1691_; size_t v___x_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v_v_1689_ = lean_array_uget(v_bs_1687_, v_i_1686_);
v___x_1690_ = lean_unsigned_to_nat(0u);
v_bs_x27_1691_ = lean_array_uset(v_bs_1687_, v_i_1686_, v___x_1690_);
v___x_1692_ = ((size_t)1ULL);
v___x_1693_ = lean_usize_add(v_i_1686_, v___x_1692_);
v___x_1694_ = lean_array_uset(v_bs_x27_1691_, v_i_1686_, v_v_1689_);
v_i_1686_ = v___x_1693_;
v_bs_1687_ = v___x_1694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_bs_1698_){
_start:
{
size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_boxed_1699_, v_i_boxed_1700_, v_bs_1698_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v_zero_1704_; uint8_t v_isZero_1705_; 
v_zero_1704_ = lean_unsigned_to_nat(0u);
v_isZero_1705_ = lean_nat_dec_eq(v_x_1702_, v_zero_1704_);
if (v_isZero_1705_ == 1)
{
lean_dec(v_x_1702_);
return v_x_1703_;
}
else
{
uint32_t v___x_1706_; lean_object* v_one_1707_; lean_object* v_n_1708_; lean_object* v___x_1709_; 
v___x_1706_ = 35;
v_one_1707_ = lean_unsigned_to_nat(1u);
v_n_1708_ = lean_nat_sub(v_x_1702_, v_one_1707_);
lean_dec(v_x_1702_);
v___x_1709_ = lean_string_push(v_x_1703_, v___x_1706_);
v_x_1702_ = v_n_1708_;
v_x_1703_ = v___x_1709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object* v_x_1711_, lean_object* v_x_1712_){
_start:
{
lean_object* v_zero_1713_; uint8_t v_isZero_1714_; 
v_zero_1713_ = lean_unsigned_to_nat(0u);
v_isZero_1714_ = lean_nat_dec_eq(v_x_1711_, v_zero_1713_);
if (v_isZero_1714_ == 1)
{
lean_dec(v_x_1711_);
return v_x_1712_;
}
else
{
uint32_t v___x_1715_; lean_object* v_one_1716_; lean_object* v_n_1717_; lean_object* v___x_1718_; 
v___x_1715_ = 58;
v_one_1716_ = lean_unsigned_to_nat(1u);
v_n_1717_ = lean_nat_sub(v_x_1711_, v_one_1716_);
lean_dec(v_x_1711_);
v___x_1718_ = lean_string_push(v_x_1712_, v___x_1715_);
v_x_1711_ = v_n_1717_;
v_x_1712_ = v___x_1718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t v_char_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v_zero_1723_; uint8_t v_isZero_1724_; 
v_zero_1723_ = lean_unsigned_to_nat(0u);
v_isZero_1724_ = lean_nat_dec_eq(v_x_1721_, v_zero_1723_);
if (v_isZero_1724_ == 1)
{
lean_dec(v_x_1721_);
return v_x_1722_;
}
else
{
lean_object* v_one_1725_; lean_object* v_n_1726_; lean_object* v___x_1727_; 
v_one_1725_ = lean_unsigned_to_nat(1u);
v_n_1726_ = lean_nat_sub(v_x_1721_, v_one_1725_);
lean_dec(v_x_1721_);
v___x_1727_ = lean_string_push(v_x_1722_, v_char_1720_);
v_x_1721_ = v_n_1726_;
v_x_1722_ = v___x_1727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object* v_char_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
uint32_t v_char_boxed_1732_; lean_object* v_res_1733_; 
v_char_boxed_1732_ = lean_unbox_uint32(v_char_1729_);
lean_dec(v_char_1729_);
v_res_1733_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_boxed_1732_, v_x_1730_, v_x_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 0)
{
if (lean_obj_tag(v_x_1735_) == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = 1;
return v___x_1736_;
}
else
{
uint8_t v___x_1737_; 
v___x_1737_ = 0;
return v___x_1737_;
}
}
else
{
if (lean_obj_tag(v_x_1735_) == 0)
{
uint8_t v___x_1738_; 
v___x_1738_ = 0;
return v___x_1738_;
}
else
{
lean_object* v_val_1739_; lean_object* v_val_1740_; uint32_t v___x_1741_; uint32_t v___x_1742_; uint8_t v___x_1743_; 
v_val_1739_ = lean_ctor_get(v_x_1734_, 0);
v_val_1740_ = lean_ctor_get(v_x_1735_, 0);
v___x_1741_ = lean_unbox_uint32(v_val_1739_);
v___x_1742_ = lean_unbox_uint32(v_val_1740_);
v___x_1743_ = lean_uint32_dec_eq(v___x_1741_, v___x_1742_);
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
uint8_t v_res_1746_; lean_object* v_r_1747_; 
v_res_1746_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v_x_1744_, v_x_1745_);
lean_dec(v_x_1745_);
lean_dec(v_x_1744_);
v_r_1747_ = lean_box(v_res_1746_);
return v_r_1747_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg(){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0));
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___boxed(lean_object* v___dummy_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v_res_1753_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t v___x_1754_, lean_object* v_as_1755_, size_t v_i_1756_, size_t v_stop_1757_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_eq(v_i_1756_, v_stop_1757_);
if (v___x_1758_ == 0)
{
uint8_t v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = 1;
v___x_1760_ = lean_array_uget_borrowed(v_as_1755_, v_i_1756_);
lean_inc(v___x_1760_);
v___x_1761_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1760_);
if (v___x_1761_ == 0)
{
return v___x_1759_;
}
else
{
if (v___x_1754_ == 0)
{
size_t v___x_1762_; size_t v___x_1763_; 
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1756_, v___x_1762_);
v_i_1756_ = v___x_1763_;
goto _start;
}
else
{
return v___x_1759_;
}
}
}
else
{
uint8_t v___x_1765_; 
v___x_1765_ = 0;
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v___x_1766_, lean_object* v_as_1767_, lean_object* v_i_1768_, lean_object* v_stop_1769_){
_start:
{
uint8_t v___x_61874__boxed_1770_; size_t v_i_boxed_1771_; size_t v_stop_boxed_1772_; uint8_t v_res_1773_; lean_object* v_r_1774_; 
v___x_61874__boxed_1770_ = lean_unbox(v___x_1766_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_stop_boxed_1772_ = lean_unbox_usize(v_stop_1769_);
lean_dec(v_stop_1769_);
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_61874__boxed_1770_, v_as_1767_, v_i_boxed_1771_, v_stop_boxed_1772_);
lean_dec_ref(v_as_1767_);
v_r_1774_ = lean_box(v_res_1773_);
return v_r_1774_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t v___x_1775_, uint8_t v___x_1776_, lean_object* v_as_1777_, size_t v_i_1778_, size_t v_stop_1779_){
_start:
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_usize_dec_eq(v_i_1778_, v_stop_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; uint8_t v___y_1783_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1781_ = 1;
v___x_1787_ = lean_array_uget_borrowed(v_as_1777_, v_i_1778_);
lean_inc(v___x_1787_);
v___x_1788_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v___x_1787_);
if (v___x_1788_ == 0)
{
v___y_1783_ = v___x_1775_;
goto v___jp_1782_;
}
else
{
v___y_1783_ = v___x_1776_;
goto v___jp_1782_;
}
v___jp_1782_:
{
if (v___y_1783_ == 0)
{
size_t v___x_1784_; size_t v___x_1785_; 
v___x_1784_ = ((size_t)1ULL);
v___x_1785_ = lean_usize_add(v_i_1778_, v___x_1784_);
v_i_1778_ = v___x_1785_;
goto _start;
}
else
{
return v___x_1781_;
}
}
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = 0;
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v___x_1790_, lean_object* v___x_1791_, lean_object* v_as_1792_, lean_object* v_i_1793_, lean_object* v_stop_1794_){
_start:
{
uint8_t v___x_61893__boxed_1795_; uint8_t v___x_61894__boxed_1796_; size_t v_i_boxed_1797_; size_t v_stop_boxed_1798_; uint8_t v_res_1799_; lean_object* v_r_1800_; 
v___x_61893__boxed_1795_ = lean_unbox(v___x_1790_);
v___x_61894__boxed_1796_ = lean_unbox(v___x_1791_);
v_i_boxed_1797_ = lean_unbox_usize(v_i_1793_);
lean_dec(v_i_1793_);
v_stop_boxed_1798_ = lean_unbox_usize(v_stop_1794_);
lean_dec(v_stop_1794_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_61893__boxed_1795_, v___x_61894__boxed_1796_, v_as_1792_, v_i_boxed_1797_, v_stop_boxed_1798_);
lean_dec_ref(v_as_1792_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v_a_1805_, lean_object* v_b_1806_){
_start:
{
if (lean_obj_tag(v_a_1805_) == 0)
{
lean_object* v_currPos_1807_; lean_object* v_searcher_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1841_; 
v_currPos_1807_ = lean_ctor_get(v_a_1805_, 0);
v_searcher_1808_ = lean_ctor_get(v_a_1805_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_a_1805_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1810_ = v_a_1805_;
v_isShared_1811_ = v_isSharedCheck_1841_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_searcher_1808_);
lean_inc(v_currPos_1807_);
lean_dec(v_a_1805_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1841_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v_it_1814_; lean_object* v_startInclusive_1815_; lean_object* v_endExclusive_1816_; uint8_t v_decide_1822_; 
v___x_1812_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v_decide_1822_ = lean_nat_dec_eq(v_searcher_1808_, v___x_1804_);
if (v_decide_1822_ == 0)
{
uint32_t v___x_1823_; uint32_t v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = 10;
v___x_1824_ = lean_string_utf8_get_fast(v___y_1802_, v_searcher_1808_);
v___x_1825_ = lean_uint32_dec_eq(v___x_1824_, v___x_1823_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_string_utf8_next_fast(v___y_1802_, v_searcher_1808_);
lean_dec(v_searcher_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1826_);
v___x_1828_ = v___x_1810_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_currPos_1807_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
v_a_1805_ = v___x_1828_;
goto _start;
}
}
else
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_slice_1834_; lean_object* v_nextIt_1836_; 
v___x_1831_ = lean_string_utf8_next_fast(v___y_1802_, v_searcher_1808_);
v___x_1832_ = lean_nat_sub(v___x_1831_, v_searcher_1808_);
v___x_1833_ = lean_nat_add(v_searcher_1808_, v___x_1832_);
lean_dec(v___x_1832_);
v_slice_1834_ = l_String_Slice_subslice_x21(v___x_1803_, v_currPos_1807_, v_searcher_1808_);
lean_inc(v___x_1833_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1833_);
lean_ctor_set(v___x_1810_, 0, v___x_1833_);
v_nextIt_1836_ = v___x_1810_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1833_);
v_nextIt_1836_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v_startInclusive_1837_; lean_object* v_endExclusive_1838_; 
v_startInclusive_1837_ = lean_ctor_get(v_slice_1834_, 0);
lean_inc(v_startInclusive_1837_);
v_endExclusive_1838_ = lean_ctor_get(v_slice_1834_, 1);
lean_inc(v_endExclusive_1838_);
lean_dec_ref(v_slice_1834_);
v_it_1814_ = v_nextIt_1836_;
v_startInclusive_1815_ = v_startInclusive_1837_;
v_endExclusive_1816_ = v_endExclusive_1838_;
goto v___jp_1813_;
}
}
}
else
{
lean_object* v___x_1840_; 
lean_del_object(v___x_1810_);
lean_dec(v_searcher_1808_);
v___x_1840_ = lean_box(1);
lean_inc(v___x_1804_);
v_it_1814_ = v___x_1840_;
v_startInclusive_1815_ = v_currPos_1807_;
v_endExclusive_1816_ = v___x_1804_;
goto v___jp_1813_;
}
v___jp_1813_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_inc(v___y_1801_);
v___x_1817_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v___y_1801_, v___x_1812_);
v___x_1818_ = lean_string_utf8_extract_fast(v___y_1802_, v_startInclusive_1815_, v_endExclusive_1816_);
lean_dec(v_endExclusive_1816_);
lean_dec(v_startInclusive_1815_);
v___x_1819_ = lean_string_append(v___x_1817_, v___x_1818_);
lean_dec_ref(v___x_1818_);
v___x_1820_ = lean_array_push(v_b_1806_, v___x_1819_);
v_a_1805_ = v_it_1814_;
v_b_1806_ = v___x_1820_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1804_);
return v_b_1806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___x_1844_, lean_object* v___x_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_1842_, v___y_1843_, v___x_1844_, v___x_1845_, v_a_1846_, v_b_1847_);
lean_dec_ref(v___x_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object* v___x_1849_, lean_object* v___x_1850_, lean_object* v_____r_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1854_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v___x_1849_);
v___x_1855_ = lean_box(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1850_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___y_1853_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object* v___x_1859_, lean_object* v___x_1860_, lean_object* v_____r_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1859_, v___x_1860_, v_____r_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1862_);
return v_res_1864_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0(void){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object* v_upperBound_1872_, lean_object* v___y_1873_, lean_object* v_a_1874_, lean_object* v_b_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___y_1879_; uint8_t v___x_1896_; 
v___x_1896_ = lean_nat_dec_lt(v_a_1874_, v_upperBound_1872_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; 
lean_dec(v_a_1874_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v_b_1875_);
lean_ctor_set(v___x_1897_, 1, v___y_1877_);
return v___x_1897_;
}
else
{
lean_object* v_fst_1898_; lean_object* v_snd_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___y_1903_; lean_object* v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1923_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_fst_1898_ = lean_ctor_get(v_b_1875_, 0);
lean_inc(v_fst_1898_);
v_snd_1899_ = lean_ctor_get(v_b_1875_, 1);
lean_inc(v_snd_1899_);
lean_dec_ref(v_b_1875_);
v___x_1900_ = lean_array_fget_borrowed(v___y_1873_, v_a_1874_);
lean_inc(v___x_1900_);
v___x_1901_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_snd_1899_, v___x_1900_);
lean_dec(v_snd_1899_);
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_add(v_a_1874_, v___x_1927_);
v___x_1929_ = lean_array_get_size(v___y_1873_);
v___x_1930_ = lean_nat_dec_lt(v___x_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v___y_1923_ = v___x_1931_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_array_fget_borrowed(v___y_1873_, v___x_1928_);
lean_dec(v___x_1928_);
lean_inc(v___x_1932_);
v___x_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
v___y_1923_ = v___x_1933_;
goto v___jp_1922_;
}
v___jp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_box(0);
lean_inc(v___x_1900_);
v___x_1905_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1900_, v___x_1901_, v___x_1904_, v___y_1876_, v___y_1903_);
v___y_1879_ = v___x_1905_;
goto v___jp_1878_;
}
v___jp_1906_:
{
uint8_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_unbox(v_fst_1898_);
lean_dec(v_fst_1898_);
lean_inc(v___y_1907_);
lean_inc(v___x_1900_);
v___x_1910_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1900_, v___y_1907_, v___x_1909_, v___y_1908_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___y_1907_) == 1)
{
lean_object* v_snd_1911_; lean_object* v___x_1912_; 
v_snd_1911_ = lean_ctor_get(v___x_1910_, 1);
lean_inc(v_snd_1911_);
lean_dec_ref(v___x_1910_);
lean_inc(v___x_1900_);
v___x_1912_ = l_Lean_Doc_RoleView_of(v___x_1900_);
if (lean_obj_tag(v___x_1912_) == 1)
{
lean_dec_ref_known(v___x_1912_, 1);
lean_dec_ref_known(v___y_1907_, 1);
v___y_1903_ = v_snd_1911_;
goto v___jp_1902_;
}
else
{
uint8_t v___x_1913_; 
lean_dec(v___x_1912_);
lean_inc(v___x_1900_);
v___x_1913_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v___x_1900_, v___y_1907_);
if (v___x_1913_ == 0)
{
v___y_1903_ = v_snd_1911_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v_fst_1916_; lean_object* v_snd_1917_; lean_object* v___x_1918_; 
v___x_1914_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1915_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1914_, v_snd_1911_);
v_fst_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_fst_1916_);
v_snd_1917_ = lean_ctor_get(v___x_1915_, 1);
lean_inc(v_snd_1917_);
lean_dec_ref(v___x_1915_);
lean_inc(v___x_1900_);
v___x_1918_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1900_, v___x_1901_, v_fst_1916_, v___y_1876_, v_snd_1917_);
v___y_1879_ = v___x_1918_;
goto v___jp_1878_;
}
}
}
else
{
lean_object* v_snd_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___y_1907_);
v_snd_1919_ = lean_ctor_get(v___x_1910_, 1);
lean_inc(v_snd_1919_);
lean_dec_ref(v___x_1910_);
v___x_1920_ = lean_box(0);
lean_inc(v___x_1900_);
v___x_1921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1900_, v___x_1901_, v___x_1920_, v___y_1876_, v_snd_1919_);
v___y_1879_ = v___x_1921_;
goto v___jp_1878_;
}
}
v___jp_1922_:
{
if (lean_obj_tag(v___x_1901_) == 0)
{
uint8_t v___x_1924_; 
v___x_1924_ = 0;
v___y_1907_ = v___y_1923_;
v___y_1908_ = v___x_1924_;
goto v___jp_1906_;
}
else
{
lean_object* v_val_1925_; uint8_t v_alternate_1926_; 
v_val_1925_ = lean_ctor_get(v___x_1901_, 0);
v_alternate_1926_ = lean_ctor_get_uint8(v_val_1925_, 1);
v___y_1907_ = v___y_1923_;
v___y_1908_ = v_alternate_1926_;
goto v___jp_1906_;
}
}
}
v___jp_1878_:
{
lean_object* v_fst_1880_; 
v_fst_1880_ = lean_ctor_get(v___y_1879_, 0);
lean_inc(v_fst_1880_);
if (lean_obj_tag(v_fst_1880_) == 0)
{
lean_object* v_snd_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_a_1874_);
v_snd_1881_ = lean_ctor_get(v___y_1879_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___y_1879_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___y_1879_, 0);
lean_dec(v_unused_1890_);
v___x_1883_ = v___y_1879_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_snd_1881_);
lean_dec(v___y_1879_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v_a_1885_; lean_object* v___x_1887_; 
v_a_1885_ = lean_ctor_get(v_fst_1880_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v_fst_1880_, 1);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v_a_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1885_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_snd_1881_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
else
{
lean_object* v_snd_1891_; lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_snd_1891_ = lean_ctor_get(v___y_1879_, 1);
lean_inc(v_snd_1891_);
lean_dec_ref(v___y_1879_);
v_a_1892_ = lean_ctor_get(v_fst_1880_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v_fst_1880_, 1);
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_add(v_a_1874_, v___x_1893_);
lean_dec(v_a_1874_);
v_a_1874_ = v___x_1894_;
v_b_1875_ = v_a_1892_;
v___y_1877_ = v_snd_1891_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object* v_stxs_1936_, uint8_t v_lineStart_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___y_1942_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1940_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_array_get_size(v_stxs_1936_);
v___x_1959_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0));
v___x_1960_ = lean_nat_dec_lt(v___x_1940_, v___x_1958_);
if (v___x_1960_ == 0)
{
v___y_1942_ = v___x_1959_;
goto v___jp_1941_;
}
else
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_nat_dec_le(v___x_1958_, v___x_1958_);
if (v___x_1961_ == 0)
{
if (v___x_1960_ == 0)
{
v___y_1942_ = v___x_1959_;
goto v___jp_1941_;
}
else
{
size_t v___x_1962_; size_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = ((size_t)0ULL);
v___x_1963_ = lean_usize_of_nat(v___x_1958_);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1936_, v___x_1962_, v___x_1963_, v___x_1959_);
v___y_1942_ = v___x_1964_;
goto v___jp_1941_;
}
}
else
{
size_t v___x_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = ((size_t)0ULL);
v___x_1966_ = lean_usize_of_nat(v___x_1958_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1936_, v___x_1965_, v___x_1966_, v___x_1959_);
v___y_1942_ = v___x_1967_;
goto v___jp_1941_;
}
}
v___jp_1941_:
{
lean_object* v___x_1943_; lean_object* v_prev_x3f_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v_snd_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v___x_1943_ = lean_array_get_size(v___y_1942_);
v_prev_x3f_1944_ = lean_box(0);
v___x_1945_ = lean_box(v_lineStart_1937_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
lean_ctor_set(v___x_1946_, 1, v_prev_x3f_1944_);
v___x_1947_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v___x_1943_, v___y_1942_, v___x_1940_, v___x_1946_, v_a_1938_, v_a_1939_);
lean_dec_ref(v___y_1942_);
v_snd_1948_ = lean_ctor_get(v___x_1947_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1947_, 0);
lean_dec(v_unused_1957_);
v___x_1950_ = v___x_1947_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_snd_1948_);
lean_dec(v___x_1947_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = lean_box(0);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_snd_1948_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t v_char_1968_, lean_object* v_inls_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_delim_1974_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___x_1985_; lean_object* v_snd_1986_; lean_object* v___y_1988_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_1973_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_1968_, v_inls_1969_);
v_delim_1974_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_1968_, v___x_1973_, v___x_1972_);
v___x_1985_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1974_, v_a_1971_);
v_snd_1986_ = lean_ctor_get(v___x_1985_, 1);
lean_inc(v_snd_1986_);
lean_dec_ref(v___x_1985_);
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_array_get_size(v_inls_1969_);
v___x_1997_ = lean_nat_dec_lt(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_box(0);
v___y_1988_ = v___x_1998_;
goto v___jp_1987_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_array_fget_borrowed(v_inls_1969_, v___x_1995_);
lean_inc(v___x_1999_);
v___x_2000_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v___x_1999_);
v___y_1988_ = v___x_2000_;
goto v___jp_1987_;
}
v___jp_1975_:
{
size_t v_sz_1978_; size_t v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; lean_object* v_snd_1983_; lean_object* v___x_1984_; 
v_sz_1978_ = lean_array_size(v_inls_1969_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_1978_, v___x_1979_, v_inls_1969_);
v___x_1981_ = 0;
v___x_1982_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_1980_, v___x_1981_, v___y_1976_, v___y_1977_);
lean_dec_ref(v___x_1980_);
v_snd_1983_ = lean_ctor_get(v___x_1982_, 1);
lean_inc(v_snd_1983_);
lean_dec_ref(v___x_1982_);
v___x_1984_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1974_, v_snd_1983_);
lean_dec_ref(v_delim_1974_);
return v___x_1984_;
}
v___jp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1989_ = lean_box_uint32(v_char_1968_);
v___x_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
v___x_1991_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v___y_1988_, v___x_1990_);
lean_dec_ref_known(v___x_1990_, 1);
lean_dec(v___y_1988_);
if (v___x_1991_ == 0)
{
v___y_1976_ = v_a_1970_;
v___y_1977_ = v_snd_1986_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_snd_1994_; 
v___x_1992_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1993_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1992_, v_snd_1986_);
v_snd_1994_ = lean_ctor_get(v___x_1993_, 1);
lean_inc(v_snd_1994_);
lean_dec_ref(v___x_1993_);
v___y_1976_ = v_a_1970_;
v___y_1977_ = v_snd_1994_;
goto v___jp_1975_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v___y_2007_, uint8_t v___x_2008_, lean_object* v_as_2009_, size_t v_sz_2010_, size_t v_i_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_usize_dec_lt(v_i_2011_, v_sz_2010_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref(v___y_2007_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v_b_2012_);
lean_ctor_set(v___x_2016_, 1, v___y_2014_);
return v___x_2016_;
}
else
{
lean_object* v___x_2017_; lean_object* v_snd_2018_; lean_object* v_a_2019_; lean_object* v_contents_2020_; lean_object* v___x_2021_; lean_object* v_snd_2022_; size_t v_sz_2023_; size_t v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v_snd_2029_; lean_object* v___x_2030_; lean_object* v_snd_2031_; lean_object* v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; 
v___x_2017_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2013_, v___y_2014_);
v_snd_2018_ = lean_ctor_get(v___x_2017_, 1);
lean_inc(v_snd_2018_);
lean_dec_ref(v___x_2017_);
v_a_2019_ = lean_array_uget_borrowed(v_as_2009_, v_i_2011_);
v_contents_2020_ = lean_ctor_get(v_a_2019_, 2);
lean_inc_ref(v___y_2007_);
v___x_2021_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2007_, v_contents_2020_, v_snd_2018_);
v_snd_2022_ = lean_ctor_get(v___x_2021_, 1);
lean_inc(v_snd_2022_);
lean_dec_ref(v___x_2021_);
v_sz_2023_ = lean_array_size(v_contents_2020_);
v___x_2024_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2020_);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2023_, v___x_2024_, v_contents_2020_);
v___x_2026_ = lean_string_length(v___y_2007_);
v___x_2027_ = lean_nat_add(v___y_2013_, v___x_2026_);
v___x_2028_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2025_, v___x_2008_, v___x_2027_, v_snd_2022_);
lean_dec(v___x_2027_);
lean_dec_ref(v___x_2025_);
v_snd_2029_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_snd_2029_);
lean_dec_ref(v___x_2028_);
v___x_2030_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2029_);
v_snd_2031_ = lean_ctor_get(v___x_2030_, 1);
lean_inc(v_snd_2031_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = lean_box(0);
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_add(v_i_2011_, v___x_2033_);
v_i_2011_ = v___x_2034_;
v_b_2012_ = v___x_2032_;
v___y_2014_ = v_snd_2031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t v___x_2039_, uint8_t v_alternate_2040_, lean_object* v_as_2041_, size_t v_sz_2042_, size_t v_i_2043_, lean_object* v_b_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
uint8_t v___x_2047_; 
v___x_2047_ = lean_usize_dec_lt(v_i_2043_, v_sz_2042_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_b_2044_);
lean_ctor_set(v___x_2048_, 1, v___y_2046_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; lean_object* v_snd_2050_; lean_object* v_a_2051_; lean_object* v___y_2053_; 
v___x_2049_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2045_, v___y_2046_);
v_snd_2050_ = lean_ctor_get(v___x_2049_, 1);
lean_inc(v_snd_2050_);
lean_dec_ref(v___x_2049_);
v_a_2051_ = lean_array_uget_borrowed(v_as_2041_, v_i_2043_);
if (v_alternate_2040_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_inc(v_b_2044_);
v___x_2071_ = l_Nat_reprFast(v_b_2044_);
v___x_2072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0));
v___x_2073_ = lean_string_append(v___x_2071_, v___x_2072_);
v___y_2053_ = v___x_2073_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_inc(v_b_2044_);
v___x_2074_ = l_Nat_reprFast(v_b_2044_);
v___x_2075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1));
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
v___y_2053_ = v___x_2076_;
goto v___jp_2052_;
}
v___jp_2052_:
{
lean_object* v_contents_2054_; lean_object* v___x_2055_; lean_object* v_snd_2056_; size_t v_sz_2057_; size_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v_snd_2063_; lean_object* v___x_2064_; lean_object* v_snd_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; size_t v___x_2068_; size_t v___x_2069_; 
v_contents_2054_ = lean_ctor_get(v_a_2051_, 2);
lean_inc_ref(v___y_2053_);
v___x_2055_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2053_, v_contents_2054_, v_snd_2050_);
v_snd_2056_ = lean_ctor_get(v___x_2055_, 1);
lean_inc(v_snd_2056_);
lean_dec_ref(v___x_2055_);
v_sz_2057_ = lean_array_size(v_contents_2054_);
v___x_2058_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2054_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2057_, v___x_2058_, v_contents_2054_);
v___x_2060_ = lean_string_length(v___y_2053_);
lean_dec_ref(v___y_2053_);
v___x_2061_ = lean_nat_add(v___y_2045_, v___x_2060_);
v___x_2062_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2059_, v___x_2039_, v___x_2061_, v_snd_2056_);
lean_dec(v___x_2061_);
lean_dec_ref(v___x_2059_);
v_snd_2063_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_snd_2063_);
lean_dec_ref(v___x_2062_);
v___x_2064_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2063_);
v_snd_2065_ = lean_ctor_get(v___x_2064_, 1);
lean_inc(v_snd_2065_);
lean_dec_ref(v___x_2064_);
v___x_2066_ = lean_unsigned_to_nat(1u);
v___x_2067_ = lean_nat_add(v_b_2044_, v___x_2066_);
lean_dec(v_b_2044_);
v___x_2068_ = ((size_t)1ULL);
v___x_2069_ = lean_usize_add(v_i_2043_, v___x_2068_);
v_i_2043_ = v___x_2069_;
v_b_2044_ = v___x_2067_;
v___y_2046_ = v_snd_2065_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t v___x_2077_, lean_object* v_as_2078_, size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v_b_2081_);
lean_ctor_set(v___x_2085_, 1, v___y_2083_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v_snd_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_snd_2090_; lean_object* v_a_2091_; lean_object* v_term_2092_; lean_object* v___x_2093_; lean_object* v___y_2095_; lean_object* v___y_2096_; uint8_t v___x_2117_; 
v___x_2086_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2082_, v___y_2083_);
v_snd_2087_ = lean_ctor_get(v___x_2086_, 1);
lean_inc(v_snd_2087_);
lean_dec_ref(v___x_2086_);
v___x_2088_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_2089_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2088_, v_snd_2087_);
v_snd_2090_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_snd_2090_);
lean_dec_ref(v___x_2089_);
v_a_2091_ = lean_array_uget_borrowed(v_as_2078_, v_i_2080_);
v_term_2092_ = lean_ctor_get(v_a_2091_, 2);
v___x_2093_ = lean_box(0);
v___x_2117_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_term_2092_);
if (v___x_2117_ == 0)
{
v___y_2095_ = v___y_2082_;
v___y_2096_ = v_snd_2090_;
goto v___jp_2094_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v_snd_2120_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2119_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2118_, v_snd_2090_);
v_snd_2120_ = lean_ctor_get(v___x_2119_, 1);
lean_inc(v_snd_2120_);
lean_dec_ref(v___x_2119_);
v___y_2095_ = v___y_2082_;
v___y_2096_ = v_snd_2120_;
goto v___jp_2094_;
}
v___jp_2094_:
{
lean_object* v_term_2097_; lean_object* v_desc_2098_; size_t v_sz_2099_; size_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v_snd_2103_; lean_object* v___x_2104_; lean_object* v_snd_2105_; size_t v_sz_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v_snd_2113_; size_t v___x_2114_; size_t v___x_2115_; 
v_term_2097_ = lean_ctor_get(v_a_2091_, 2);
v_desc_2098_ = lean_ctor_get(v_a_2091_, 3);
v_sz_2099_ = lean_array_size(v_term_2097_);
v___x_2100_ = ((size_t)0ULL);
lean_inc_ref(v_term_2097_);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2099_, v___x_2100_, v_term_2097_);
v___x_2102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2101_, v___x_2077_, v___y_2095_, v___y_2096_);
lean_dec_ref(v___x_2101_);
v_snd_2103_ = lean_ctor_get(v___x_2102_, 1);
lean_inc(v_snd_2103_);
lean_dec_ref(v___x_2102_);
v___x_2104_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2103_);
v_snd_2105_ = lean_ctor_get(v___x_2104_, 1);
lean_inc(v_snd_2105_);
lean_dec_ref(v___x_2104_);
v_sz_2106_ = lean_array_size(v_desc_2098_);
lean_inc_ref(v_desc_2098_);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2106_, v___x_2100_, v_desc_2098_);
v___x_2108_ = lean_unsigned_to_nat(2u);
v___x_2109_ = lean_nat_add(v___y_2095_, v___x_2108_);
v___x_2110_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2107_, v___x_2077_, v___x_2109_, v_snd_2105_);
lean_dec(v___x_2109_);
lean_dec_ref(v___x_2107_);
v_snd_2111_ = lean_ctor_get(v___x_2110_, 1);
lean_inc(v_snd_2111_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2111_);
v_snd_2113_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_snd_2113_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2080_, v___x_2114_);
v_i_2080_ = v___x_2115_;
v_b_2081_ = v___x_2093_;
v___y_2083_ = v_snd_2113_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_2124_, lean_object* v_next_x3f_2125_, uint8_t v_atLineStart_2126_, uint8_t v_alternate_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v___y_2131_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
lean_inc(v_stx_2124_);
v___x_2161_ = l_Lean_Syntax_getKind(v_stx_2124_);
v___x_2162_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3));
v___x_2163_ = lean_name_eq(v___x_2161_, v___x_2162_);
lean_dec(v___x_2161_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_inc(v_stx_2124_);
v___x_2164_ = l_Lean_Doc_ArgValView_of(v_stx_2124_);
if (lean_obj_tag(v___x_2164_) == 1)
{
lean_object* v_val_2165_; 
lean_dec(v_next_x3f_2125_);
lean_dec(v_stx_2124_);
v_val_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_val_2165_);
lean_dec_ref_known(v___x_2164_, 1);
if (lean_obj_tag(v_val_2165_) == 1)
{
lean_object* v_x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_x_2166_ = lean_ctor_get(v_val_2165_, 0);
lean_inc(v_x_2166_);
lean_dec_ref_known(v_val_2165_, 1);
v___x_2167_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_x_2166_);
v___x_2168_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2167_, v_a_2129_);
lean_dec_ref(v___x_2167_);
return v___x_2168_;
}
else
{
lean_object* v_lit_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_lit_2169_ = lean_ctor_get(v_val_2165_, 0);
lean_inc(v_lit_2169_);
lean_dec(v_val_2165_);
v___x_2170_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_lit_2169_);
v___x_2171_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2170_, v_a_2129_);
lean_dec_ref(v___x_2170_);
return v___x_2171_;
}
}
else
{
lean_object* v___x_2172_; 
lean_dec(v___x_2164_);
lean_inc(v_stx_2124_);
v___x_2172_ = l_Lean_Doc_ArgView_of(v_stx_2124_);
if (lean_obj_tag(v___x_2172_) == 1)
{
lean_object* v_val_2173_; 
lean_dec(v_next_x3f_2125_);
lean_dec(v_stx_2124_);
v_val_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_val_2173_);
lean_dec_ref_known(v___x_2172_, 1);
switch(lean_obj_tag(v_val_2173_))
{
case 0:
{
lean_object* v_val_2174_; lean_object* v___x_2175_; 
v_val_2174_ = lean_ctor_get(v_val_2173_, 1);
lean_inc(v_val_2174_);
lean_dec_ref_known(v_val_2173_, 2);
v___x_2175_ = lean_box(0);
v_stx_2124_ = v_val_2174_;
v_next_x3f_2125_ = v___x_2175_;
v_atLineStart_2126_ = v___x_2163_;
v_alternate_2127_ = v___x_2163_;
goto _start;
}
case 1:
{
lean_object* v_name_2177_; lean_object* v_val_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_snd_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v_snd_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v_snd_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v_snd_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_name_2177_ = lean_ctor_get(v_val_2173_, 2);
lean_inc(v_name_2177_);
v_val_2178_ = lean_ctor_get(v_val_2173_, 4);
lean_inc(v_val_2178_);
lean_dec_ref_known(v_val_2173_, 5);
v___x_2179_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_2180_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2179_, v_a_2129_);
v_snd_2181_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_snd_2181_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2177_);
v___x_2183_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2182_, v_snd_2181_);
lean_dec_ref(v___x_2182_);
v_snd_2184_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_snd_2184_);
lean_dec_ref(v___x_2183_);
v___x_2185_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
v___x_2186_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2185_, v_snd_2184_);
v_snd_2187_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_snd_2187_);
lean_dec_ref(v___x_2186_);
v___x_2188_ = lean_box(0);
v___x_2189_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_val_2178_, v___x_2188_, v___x_2163_, v___x_2163_, v_a_2128_, v_snd_2187_);
v_snd_2190_ = lean_ctor_get(v___x_2189_, 1);
lean_inc(v_snd_2190_);
lean_dec_ref(v___x_2189_);
v___x_2191_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_2192_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2191_, v_snd_2190_);
return v___x_2192_;
}
default: 
{
lean_object* v_name_2193_; uint8_t v_isOn_2194_; lean_object* v___y_2196_; 
v_name_2193_ = lean_ctor_get(v_val_2173_, 2);
lean_inc(v_name_2193_);
v_isOn_2194_ = lean_ctor_get_uint8(v_val_2173_, sizeof(void*)*3);
lean_dec_ref_known(v_val_2173_, 3);
if (v_isOn_2194_ == 0)
{
lean_object* v___x_2201_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7));
v___y_2196_ = v___x_2201_;
goto v___jp_2195_;
}
else
{
lean_object* v___x_2202_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5));
v___y_2196_ = v___x_2202_;
goto v___jp_2195_;
}
v___jp_2195_:
{
lean_object* v___x_2197_; lean_object* v_snd_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2197_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2196_, v_a_2129_);
v_snd_2198_ = lean_ctor_get(v___x_2197_, 1);
lean_inc(v_snd_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2193_);
v___x_2200_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2199_, v_snd_2198_);
lean_dec_ref(v___x_2199_);
return v___x_2200_;
}
}
}
}
else
{
lean_object* v___x_2203_; 
lean_dec(v___x_2172_);
lean_inc(v_stx_2124_);
v___x_2203_ = l_Lean_Doc_LinkTargetView_of(v_stx_2124_);
if (lean_obj_tag(v___x_2203_) == 1)
{
lean_object* v_val_2204_; lean_object* v___x_2205_; 
lean_dec(v_next_x3f_2125_);
lean_dec(v_stx_2124_);
v_val_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_val_2204_, v_a_2129_);
lean_dec(v_val_2204_);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; 
lean_dec(v___x_2203_);
lean_inc(v_stx_2124_);
v___x_2206_ = l_Lean_Doc_InlineView_of(v_stx_2124_);
if (lean_obj_tag(v___x_2206_) == 1)
{
lean_object* v_val_2207_; 
lean_dec(v_stx_2124_);
v_val_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_val_2207_);
lean_dec_ref_known(v___x_2206_, 1);
switch(lean_obj_tag(v_val_2207_))
{
case 0:
{
lean_object* v_view_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_next_x3f_2125_);
v_view_2208_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2208_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2209_ = l_Lean_Doc_TextView_getVersoText(v_view_2208_);
lean_dec_ref(v_view_2208_);
v___x_2210_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_2126_, v___x_2209_);
v___x_2211_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2210_, v_a_2129_);
lean_dec_ref(v___x_2210_);
return v___x_2211_;
}
case 1:
{
lean_object* v_view_2212_; lean_object* v_content_2213_; uint32_t v___x_2214_; lean_object* v___x_2215_; 
lean_dec(v_next_x3f_2125_);
v_view_2212_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2212_);
lean_dec_ref_known(v_val_2207_, 1);
v_content_2213_ = lean_ctor_get(v_view_2212_, 2);
lean_inc_ref(v_content_2213_);
lean_dec_ref(v_view_2212_);
v___x_2214_ = 95;
v___x_2215_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2214_, v_content_2213_, v_a_2128_, v_a_2129_);
return v___x_2215_;
}
case 2:
{
lean_object* v_view_2216_; lean_object* v_content_2217_; uint32_t v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v_next_x3f_2125_);
v_view_2216_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2216_);
lean_dec_ref_known(v_val_2207_, 1);
v_content_2217_ = lean_ctor_get(v_view_2216_, 2);
lean_inc_ref(v_content_2217_);
lean_dec_ref(v_view_2216_);
v___x_2218_ = 42;
v___x_2219_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2218_, v_content_2217_, v_a_2128_, v_a_2129_);
return v___x_2219_;
}
case 3:
{
lean_object* v_view_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec(v_next_x3f_2125_);
v_view_2220_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2220_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2221_ = l_Lean_Doc_CodeView_getVersoCode(v_view_2220_);
lean_dec_ref(v_view_2220_);
v___x_2222_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2221_);
v___x_2223_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2222_, v_a_2129_);
lean_dec_ref(v___x_2222_);
return v___x_2223_;
}
case 4:
{
lean_object* v_view_2224_; lean_object* v___y_2226_; uint8_t v_mode_2232_; 
lean_dec(v_next_x3f_2125_);
v_view_2224_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2224_);
lean_dec_ref_known(v_val_2207_, 1);
v_mode_2232_ = lean_ctor_get_uint8(v_view_2224_, sizeof(void*)*3);
if (v_mode_2232_ == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5));
v___y_2226_ = v___x_2233_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
v___y_2226_ = v___x_2234_;
goto v___jp_2225_;
}
v___jp_2225_:
{
lean_object* v___x_2227_; lean_object* v_snd_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2227_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2226_, v_a_2129_);
v_snd_2228_ = lean_ctor_get(v___x_2227_, 1);
lean_inc(v_snd_2228_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = l_Lean_Doc_MathView_getVersoCode(v_view_2224_);
lean_dec_ref(v_view_2224_);
v___x_2230_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2229_);
v___x_2231_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2230_, v_snd_2228_);
lean_dec_ref(v___x_2230_);
return v___x_2231_;
}
}
case 5:
{
lean_object* v_view_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v_snd_2238_; lean_object* v_content_2239_; lean_object* v_target_2240_; size_t v_sz_2241_; size_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_snd_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_snd_2248_; lean_object* v___x_2249_; 
lean_dec(v_next_x3f_2125_);
v_view_2235_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2235_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2236_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2237_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2236_, v_a_2129_);
v_snd_2238_ = lean_ctor_get(v___x_2237_, 1);
lean_inc(v_snd_2238_);
lean_dec_ref(v___x_2237_);
v_content_2239_ = lean_ctor_get(v_view_2235_, 2);
lean_inc_ref(v_content_2239_);
v_target_2240_ = lean_ctor_get(v_view_2235_, 4);
lean_inc_ref(v_target_2240_);
lean_dec_ref(v_view_2235_);
v_sz_2241_ = lean_array_size(v_content_2239_);
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2241_, v___x_2242_, v_content_2239_);
v___x_2244_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2243_, v___x_2163_, v_a_2128_, v_snd_2238_);
lean_dec_ref(v___x_2243_);
v_snd_2245_ = lean_ctor_get(v___x_2244_, 1);
lean_inc(v_snd_2245_);
lean_dec_ref(v___x_2244_);
v___x_2246_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2247_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2246_, v_snd_2245_);
v_snd_2248_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_snd_2248_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2240_, v_snd_2248_);
lean_dec_ref(v_target_2240_);
return v___x_2249_;
}
case 6:
{
lean_object* v_view_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_snd_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_snd_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v_snd_2260_; lean_object* v_target_2261_; lean_object* v___x_2262_; 
lean_dec(v_next_x3f_2125_);
v_view_2250_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2250_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2251_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7));
v___x_2252_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2251_, v_a_2129_);
v_snd_2253_ = lean_ctor_get(v___x_2252_, 1);
lean_inc(v_snd_2253_);
lean_dec_ref(v___x_2252_);
v___x_2254_ = l_Lean_Doc_ImageView_getAlt(v_view_2250_);
v___x_2255_ = l_Lean_Doc_escapeVersoImageAlt(v___x_2254_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2255_, v_snd_2253_);
lean_dec_ref(v___x_2255_);
v_snd_2257_ = lean_ctor_get(v___x_2256_, 1);
lean_inc(v_snd_2257_);
lean_dec_ref(v___x_2256_);
v___x_2258_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2259_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2258_, v_snd_2257_);
v_snd_2260_ = lean_ctor_get(v___x_2259_, 1);
lean_inc(v_snd_2260_);
lean_dec_ref(v___x_2259_);
v_target_2261_ = lean_ctor_get(v_view_2250_, 4);
lean_inc_ref(v_target_2261_);
lean_dec_ref(v_view_2250_);
v___x_2262_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2261_, v_snd_2260_);
lean_dec_ref(v_target_2261_);
return v___x_2262_;
}
case 7:
{
lean_object* v_view_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v_snd_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_snd_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_next_x3f_2125_);
v_view_2263_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2263_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2264_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2265_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2264_, v_a_2129_);
v_snd_2266_ = lean_ctor_get(v___x_2265_, 1);
lean_inc(v_snd_2266_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = l_Lean_Doc_FootnoteView_getName(v_view_2263_);
lean_dec_ref(v_view_2263_);
v___x_2268_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2267_, v_snd_2266_);
lean_dec_ref(v___x_2267_);
v_snd_2269_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_snd_2269_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2271_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2270_, v_snd_2269_);
return v___x_2271_;
}
case 8:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref_known(v_val_2207_, 1);
lean_dec(v_next_x3f_2125_);
v___x_2272_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2273_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2272_, v_a_2129_);
return v___x_2273_;
}
default: 
{
lean_object* v_view_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v_snd_2277_; lean_object* v_name_2278_; lean_object* v_args_2279_; lean_object* v_content_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v_snd_2283_; lean_object* v___x_2284_; size_t v_sz_2285_; size_t v___x_2286_; lean_object* v___x_2287_; lean_object* v_snd_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v_snd_2291_; lean_object* v___x_2302_; 
v_view_2274_ = lean_ctor_get(v_val_2207_, 0);
lean_inc_ref(v_view_2274_);
lean_dec_ref_known(v_val_2207_, 1);
v___x_2275_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2276_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2275_, v_a_2129_);
v_snd_2277_ = lean_ctor_get(v___x_2276_, 1);
lean_inc(v_snd_2277_);
lean_dec_ref(v___x_2276_);
v_name_2278_ = lean_ctor_get(v_view_2274_, 2);
lean_inc(v_name_2278_);
v_args_2279_ = lean_ctor_get(v_view_2274_, 3);
lean_inc_ref(v_args_2279_);
v_content_2280_ = lean_ctor_get(v_view_2274_, 6);
lean_inc_ref(v_content_2280_);
lean_dec_ref(v_view_2274_);
v___x_2281_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2278_);
v___x_2282_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2281_, v_snd_2277_);
lean_dec_ref(v___x_2281_);
v_snd_2283_ = lean_ctor_get(v___x_2282_, 1);
lean_inc(v_snd_2283_);
lean_dec_ref(v___x_2282_);
v___x_2284_ = lean_box(0);
v_sz_2285_ = lean_array_size(v_args_2279_);
v___x_2286_ = ((size_t)0ULL);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2163_, v_args_2279_, v_sz_2285_, v___x_2286_, v___x_2284_, v_a_2128_, v_snd_2283_);
lean_dec_ref(v_args_2279_);
v_snd_2288_ = lean_ctor_get(v___x_2287_, 1);
lean_inc(v_snd_2288_);
lean_dec_ref(v___x_2287_);
v___x_2289_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2290_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2289_, v_snd_2288_);
v_snd_2291_ = lean_ctor_get(v___x_2290_, 1);
lean_inc(v_snd_2291_);
lean_dec_ref(v___x_2290_);
v___x_2302_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_2280_);
if (lean_obj_tag(v___x_2302_) == 1)
{
lean_object* v_val_2303_; uint8_t v___x_2304_; 
v_val_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_val_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_val_2303_, v_next_x3f_2125_);
if (v___x_2304_ == 0)
{
size_t v_sz_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_sz_2305_ = lean_array_size(v_content_2280_);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2305_, v___x_2286_, v_content_2280_);
v___x_2307_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2306_, v___x_2304_, v_a_2128_, v_snd_2291_);
lean_dec_ref(v___x_2306_);
return v___x_2307_;
}
else
{
goto v___jp_2292_;
}
}
else
{
lean_dec(v___x_2302_);
lean_dec(v_next_x3f_2125_);
goto v___jp_2292_;
}
v___jp_2292_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_snd_2295_; size_t v_sz_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_snd_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2294_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2293_, v_snd_2291_);
v_snd_2295_ = lean_ctor_get(v___x_2294_, 1);
lean_inc(v_snd_2295_);
lean_dec_ref(v___x_2294_);
v_sz_2296_ = lean_array_size(v_content_2280_);
v___x_2297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2296_, v___x_2286_, v_content_2280_);
v___x_2298_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2297_, v___x_2163_, v_a_2128_, v_snd_2295_);
lean_dec_ref(v___x_2297_);
v_snd_2299_ = lean_ctor_get(v___x_2298_, 1);
lean_inc(v_snd_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2301_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2300_, v_snd_2299_);
return v___x_2301_;
}
}
}
}
else
{
lean_object* v___x_2308_; 
lean_dec(v___x_2206_);
lean_dec(v_next_x3f_2125_);
lean_inc(v_stx_2124_);
v___x_2308_ = l_Lean_Doc_BlockView_of(v_stx_2124_);
if (lean_obj_tag(v___x_2308_) == 1)
{
lean_object* v_val_2309_; 
v_val_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_val_2309_);
lean_dec_ref_known(v___x_2308_, 1);
switch(lean_obj_tag(v_val_2309_))
{
case 0:
{
lean_object* v_view_2310_; lean_object* v_content_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
lean_dec(v_stx_2124_);
v_view_2310_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2310_);
lean_dec_ref_known(v_val_2309_, 1);
v_content_2311_ = lean_ctor_get(v_view_2310_, 1);
lean_inc_ref(v_content_2311_);
lean_dec_ref(v_view_2310_);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_array_get_size(v_content_2311_);
v___x_2314_ = lean_nat_dec_lt(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec_ref(v_content_2311_);
goto v___jp_2158_;
}
else
{
if (v___x_2314_ == 0)
{
lean_dec_ref(v_content_2311_);
goto v___jp_2158_;
}
else
{
size_t v___x_2315_; size_t v___x_2316_; uint8_t v___x_2317_; lean_object* v___y_2319_; lean_object* v___y_2320_; 
v___x_2315_ = ((size_t)0ULL);
v___x_2316_ = lean_usize_of_nat(v___x_2313_);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_2163_, v_content_2311_, v___x_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v_content_2311_);
goto v___jp_2158_;
}
else
{
if (v___x_2163_ == 0)
{
lean_object* v___x_2326_; lean_object* v_snd_2327_; 
v___x_2326_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2327_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_snd_2327_);
lean_dec_ref(v___x_2326_);
if (v___x_2314_ == 0)
{
goto v___jp_2328_;
}
else
{
if (v___x_2314_ == 0)
{
goto v___jp_2328_;
}
else
{
uint8_t v___x_2332_; 
v___x_2332_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_2317_, v___x_2163_, v_content_2311_, v___x_2315_, v___x_2316_);
if (v___x_2332_ == 0)
{
goto v___jp_2328_;
}
else
{
v___y_2319_ = v_a_2128_;
v___y_2320_ = v_snd_2327_;
goto v___jp_2318_;
}
}
}
v___jp_2328_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v_snd_2331_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2330_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2329_, v_snd_2327_);
v_snd_2331_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_snd_2331_);
lean_dec_ref(v___x_2330_);
v___y_2319_ = v_a_2128_;
v___y_2320_ = v_snd_2331_;
goto v___jp_2318_;
}
}
else
{
lean_dec_ref(v_content_2311_);
goto v___jp_2158_;
}
}
v___jp_2318_:
{
size_t v_sz_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_snd_2324_; lean_object* v___x_2325_; 
v_sz_2321_ = lean_array_size(v_content_2311_);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2321_, v___x_2315_, v_content_2311_);
v___x_2323_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2322_, v___x_2317_, v___y_2319_, v___y_2320_);
lean_dec_ref(v___x_2322_);
v_snd_2324_ = lean_ctor_get(v___x_2323_, 1);
lean_inc(v_snd_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2324_);
return v___x_2325_;
}
}
}
}
case 1:
{
lean_object* v_view_2333_; lean_object* v___y_2335_; 
lean_dec(v_stx_2124_);
v_view_2333_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2333_);
lean_dec_ref_known(v_val_2309_, 1);
if (v_alternate_2127_ == 0)
{
lean_object* v___x_2343_; 
v___x_2343_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11));
v___y_2335_ = v___x_2343_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2344_; 
v___x_2344_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___y_2335_ = v___x_2344_;
goto v___jp_2334_;
}
v___jp_2334_:
{
lean_object* v_items_2336_; lean_object* v___x_2337_; size_t v_sz_2338_; size_t v___x_2339_; lean_object* v___x_2340_; lean_object* v_snd_2341_; lean_object* v___x_2342_; 
v_items_2336_ = lean_ctor_get(v_view_2333_, 1);
lean_inc_ref(v_items_2336_);
lean_dec_ref(v_view_2333_);
v___x_2337_ = lean_box(0);
v_sz_2338_ = lean_array_size(v_items_2336_);
v___x_2339_ = ((size_t)0ULL);
lean_inc_ref(v___y_2335_);
v___x_2340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2335_, v___x_2163_, v_items_2336_, v_sz_2338_, v___x_2339_, v___x_2337_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_items_2336_);
v_snd_2341_ = lean_ctor_get(v___x_2340_, 1);
lean_inc(v_snd_2341_);
lean_dec_ref(v___x_2340_);
v___x_2342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2341_);
return v___x_2342_;
}
}
case 2:
{
lean_object* v_view_2345_; lean_object* v_start_2346_; lean_object* v_items_2347_; size_t v_sz_2348_; size_t v___x_2349_; lean_object* v___x_2350_; lean_object* v_snd_2351_; lean_object* v___x_2352_; 
lean_dec(v_stx_2124_);
v_view_2345_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2345_);
lean_dec_ref_known(v_val_2309_, 1);
v_start_2346_ = lean_ctor_get(v_view_2345_, 1);
lean_inc(v_start_2346_);
v_items_2347_ = lean_ctor_get(v_view_2345_, 2);
lean_inc_ref(v_items_2347_);
lean_dec_ref(v_view_2345_);
v_sz_2348_ = lean_array_size(v_items_2347_);
v___x_2349_ = ((size_t)0ULL);
v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_2163_, v_alternate_2127_, v_items_2347_, v_sz_2348_, v___x_2349_, v_start_2346_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_items_2347_);
v_snd_2351_ = lean_ctor_get(v___x_2350_, 1);
lean_inc(v_snd_2351_);
lean_dec_ref(v___x_2350_);
v___x_2352_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2351_);
return v___x_2352_;
}
case 3:
{
lean_object* v_view_2353_; lean_object* v_items_2354_; lean_object* v___x_2355_; size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; lean_object* v_snd_2359_; lean_object* v___x_2360_; 
lean_dec(v_stx_2124_);
v_view_2353_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2353_);
lean_dec_ref_known(v_val_2309_, 1);
v_items_2354_ = lean_ctor_get(v_view_2353_, 1);
lean_inc_ref(v_items_2354_);
lean_dec_ref(v_view_2353_);
v___x_2355_ = lean_box(0);
v_sz_2356_ = lean_array_size(v_items_2354_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_2163_, v_items_2354_, v_sz_2356_, v___x_2357_, v___x_2355_, v_a_2128_, v_a_2129_);
lean_dec_ref(v_items_2354_);
v_snd_2359_ = lean_ctor_get(v___x_2358_, 1);
lean_inc(v_snd_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2359_);
return v___x_2360_;
}
case 4:
{
lean_object* v_view_2361_; lean_object* v___x_2362_; lean_object* v_snd_2363_; lean_object* v_content_2364_; lean_object* v___y_2366_; lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
lean_dec(v_stx_2124_);
v_view_2361_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2361_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2362_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2363_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_snd_2363_);
lean_dec_ref(v___x_2362_);
v_content_2364_ = lean_ctor_get(v_view_2361_, 2);
lean_inc_ref(v_content_2364_);
lean_dec_ref(v_view_2361_);
v___x_2377_ = lean_array_get_size(v_content_2364_);
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = lean_nat_dec_eq(v___x_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
v___x_2380_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
v___y_2366_ = v___x_2380_;
goto v___jp_2365_;
}
else
{
lean_object* v___x_2381_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9));
v___y_2366_ = v___x_2381_;
goto v___jp_2365_;
}
v___jp_2365_:
{
lean_object* v___x_2367_; lean_object* v_snd_2368_; size_t v_sz_2369_; size_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_snd_2375_; lean_object* v___x_2376_; 
v___x_2367_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2366_, v_snd_2363_);
v_snd_2368_ = lean_ctor_get(v___x_2367_, 1);
lean_inc(v_snd_2368_);
lean_dec_ref(v___x_2367_);
v_sz_2369_ = lean_array_size(v_content_2364_);
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2369_, v___x_2370_, v_content_2364_);
v___x_2372_ = lean_unsigned_to_nat(2u);
v___x_2373_ = lean_nat_add(v_a_2128_, v___x_2372_);
v___x_2374_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2371_, v___x_2163_, v___x_2373_, v_snd_2368_);
lean_dec(v___x_2373_);
lean_dec_ref(v___x_2371_);
v_snd_2375_ = lean_ctor_get(v___x_2374_, 1);
lean_inc(v_snd_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2375_);
return v___x_2376_;
}
}
case 5:
{
lean_object* v_view_2382_; lean_object* v___x_2383_; lean_object* v_snd_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2409_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
lean_dec(v_stx_2124_);
v_view_2382_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2382_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2383_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2384_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_snd_2384_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2386_ = lean_unsigned_to_nat(3u);
v___x_2387_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_view_2382_);
v___x_2425_ = l_Lean_Doc_longestBacktickRun(v___x_2387_);
v___x_2426_ = lean_unsigned_to_nat(1u);
v___x_2427_ = lean_nat_add(v___x_2425_, v___x_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_nat_dec_le(v___x_2386_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_dec(v___x_2427_);
v___y_2409_ = v___x_2386_;
goto v___jp_2408_;
}
else
{
v___y_2409_ = v___x_2427_;
goto v___jp_2408_;
}
v___jp_2388_:
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_string_append(v___x_2387_, v___y_2390_);
v___y_2140_ = v___y_2389_;
v___y_2141_ = v___y_2390_;
v___y_2142_ = v___y_2391_;
v___y_2143_ = v___y_2392_;
v___y_2144_ = v___x_2393_;
goto v___jp_2139_;
}
v___jp_2394_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v_snd_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2399_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2398_, v___y_2397_);
v_snd_2400_ = lean_ctor_get(v___x_2399_, 1);
lean_inc(v_snd_2400_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = lean_string_utf8_byte_size(v___x_2387_);
v___x_2402_ = lean_unsigned_to_nat(0u);
v___x_2403_ = lean_nat_dec_eq(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_nat_dec_le(v___x_2404_, v___x_2401_);
if (v___x_2405_ == 0)
{
v___y_2389_ = v___y_2395_;
v___y_2390_ = v___x_2398_;
v___y_2391_ = v_snd_2400_;
v___y_2392_ = v___y_2396_;
goto v___jp_2388_;
}
else
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = lean_nat_sub(v___x_2401_, v___x_2404_);
v___x_2407_ = lean_string_memcmp(v___x_2387_, v___x_2398_, v___x_2406_, v___x_2402_, v___x_2404_);
lean_dec(v___x_2406_);
if (v___x_2407_ == 0)
{
v___y_2389_ = v___y_2395_;
v___y_2390_ = v___x_2398_;
v___y_2391_ = v_snd_2400_;
v___y_2392_ = v___y_2396_;
goto v___jp_2388_;
}
else
{
v___y_2140_ = v___y_2395_;
v___y_2141_ = v___x_2398_;
v___y_2142_ = v_snd_2400_;
v___y_2143_ = v___y_2396_;
v___y_2144_ = v___x_2387_;
goto v___jp_2139_;
}
}
}
else
{
v___y_2140_ = v___y_2395_;
v___y_2141_ = v___x_2398_;
v___y_2142_ = v_snd_2400_;
v___y_2143_ = v___y_2396_;
v___y_2144_ = v___x_2387_;
goto v___jp_2139_;
}
}
v___jp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v_name_x3f_2412_; 
v___x_2410_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___y_2409_, v___x_2385_);
v___x_2411_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2410_, v_snd_2384_);
v_name_x3f_2412_ = lean_ctor_get(v_view_2382_, 2);
lean_inc(v_name_x3f_2412_);
if (lean_obj_tag(v_name_x3f_2412_) == 1)
{
lean_object* v_snd_2413_; lean_object* v_args_2414_; lean_object* v_val_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_snd_2418_; lean_object* v___x_2419_; size_t v_sz_2420_; size_t v___x_2421_; lean_object* v___x_2422_; lean_object* v_snd_2423_; 
v_snd_2413_ = lean_ctor_get(v___x_2411_, 1);
lean_inc(v_snd_2413_);
lean_dec_ref(v___x_2411_);
v_args_2414_ = lean_ctor_get(v_view_2382_, 3);
lean_inc_ref(v_args_2414_);
lean_dec_ref(v_view_2382_);
v_val_2415_ = lean_ctor_get(v_name_x3f_2412_, 0);
lean_inc(v_val_2415_);
lean_dec_ref_known(v_name_x3f_2412_, 1);
v___x_2416_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_val_2415_);
v___x_2417_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2416_, v_snd_2413_);
lean_dec_ref(v___x_2416_);
v_snd_2418_ = lean_ctor_get(v___x_2417_, 1);
lean_inc(v_snd_2418_);
lean_dec_ref(v___x_2417_);
v___x_2419_ = lean_box(0);
v_sz_2420_ = lean_array_size(v_args_2414_);
v___x_2421_ = ((size_t)0ULL);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2163_, v_args_2414_, v_sz_2420_, v___x_2421_, v___x_2419_, v_a_2128_, v_snd_2418_);
lean_dec_ref(v_args_2414_);
v_snd_2423_ = lean_ctor_get(v___x_2422_, 1);
lean_inc(v_snd_2423_);
lean_dec_ref(v___x_2422_);
v___y_2395_ = v___x_2410_;
v___y_2396_ = v_a_2128_;
v___y_2397_ = v_snd_2423_;
goto v___jp_2394_;
}
else
{
lean_object* v_snd_2424_; 
lean_dec(v_name_x3f_2412_);
lean_dec_ref(v_view_2382_);
v_snd_2424_ = lean_ctor_get(v___x_2411_, 1);
lean_inc(v_snd_2424_);
lean_dec_ref(v___x_2411_);
v___y_2395_ = v___x_2410_;
v___y_2396_ = v_a_2128_;
v___y_2397_ = v_snd_2424_;
goto v___jp_2394_;
}
}
}
case 6:
{
lean_object* v_view_2429_; lean_object* v___x_2430_; lean_object* v_snd_2431_; lean_object* v_name_2432_; lean_object* v_args_2433_; lean_object* v_content_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v_snd_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v_snd_2442_; lean_object* v___x_2443_; size_t v_sz_2444_; size_t v___x_2445_; lean_object* v___x_2446_; lean_object* v_snd_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v_snd_2450_; size_t v_sz_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_snd_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; lean_object* v_snd_2459_; lean_object* v___x_2460_; 
lean_dec(v_stx_2124_);
v_view_2429_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2429_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2430_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2431_ = lean_ctor_get(v___x_2430_, 1);
lean_inc(v_snd_2431_);
lean_dec_ref(v___x_2430_);
v_name_2432_ = lean_ctor_get(v_view_2429_, 2);
lean_inc(v_name_2432_);
v_args_2433_ = lean_ctor_get(v_view_2429_, 3);
lean_inc_ref(v_args_2433_);
v_content_2434_ = lean_ctor_get(v_view_2429_, 4);
lean_inc_ref(v_content_2434_);
lean_dec_ref(v_view_2429_);
v___x_2435_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2436_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_content_2434_);
v___x_2437_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(v___x_2436_, v___x_2435_);
v___x_2438_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2437_, v_snd_2431_);
v_snd_2439_ = lean_ctor_get(v___x_2438_, 1);
lean_inc(v_snd_2439_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2432_);
v___x_2441_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2440_, v_snd_2439_);
lean_dec_ref(v___x_2440_);
v_snd_2442_ = lean_ctor_get(v___x_2441_, 1);
lean_inc(v_snd_2442_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = lean_box(0);
v_sz_2444_ = lean_array_size(v_args_2433_);
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2163_, v_args_2433_, v_sz_2444_, v___x_2445_, v___x_2443_, v_a_2128_, v_snd_2442_);
lean_dec_ref(v_args_2433_);
v_snd_2447_ = lean_ctor_get(v___x_2446_, 1);
lean_inc(v_snd_2447_);
lean_dec_ref(v___x_2446_);
v___x_2448_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2449_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2448_, v_snd_2447_);
v_snd_2450_ = lean_ctor_get(v___x_2449_, 1);
lean_inc(v_snd_2450_);
lean_dec_ref(v___x_2449_);
v_sz_2451_ = lean_array_size(v_content_2434_);
v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2451_, v___x_2445_, v_content_2434_);
v___x_2453_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2452_, v___x_2163_, v_a_2128_, v_snd_2450_);
lean_dec_ref(v___x_2452_);
v_snd_2454_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_snd_2454_);
lean_dec_ref(v___x_2453_);
lean_inc(v_a_2128_);
v___x_2455_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2128_, v___x_2435_);
v___x_2456_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2455_, v_snd_2454_);
lean_dec_ref(v___x_2455_);
v_snd_2457_ = lean_ctor_get(v___x_2456_, 1);
lean_inc(v_snd_2457_);
lean_dec_ref(v___x_2456_);
v___x_2458_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2437_, v_snd_2457_);
lean_dec_ref(v___x_2437_);
v_snd_2459_ = lean_ctor_get(v___x_2458_, 1);
lean_inc(v_snd_2459_);
lean_dec_ref(v___x_2458_);
v___x_2460_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2459_);
return v___x_2460_;
}
case 7:
{
lean_object* v_view_2461_; lean_object* v___x_2462_; lean_object* v_snd_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v_snd_2466_; lean_object* v_name_2467_; lean_object* v_args_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_snd_2471_; lean_object* v___x_2472_; size_t v_sz_2473_; size_t v___x_2474_; lean_object* v___x_2475_; lean_object* v_snd_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_snd_2479_; lean_object* v___x_2480_; 
lean_dec(v_stx_2124_);
v_view_2461_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2461_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2462_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2463_ = lean_ctor_get(v___x_2462_, 1);
lean_inc(v_snd_2463_);
lean_dec_ref(v___x_2462_);
v___x_2464_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2465_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2464_, v_snd_2463_);
v_snd_2466_ = lean_ctor_get(v___x_2465_, 1);
lean_inc(v_snd_2466_);
lean_dec_ref(v___x_2465_);
v_name_2467_ = lean_ctor_get(v_view_2461_, 2);
lean_inc(v_name_2467_);
v_args_2468_ = lean_ctor_get(v_view_2461_, 3);
lean_inc_ref(v_args_2468_);
lean_dec_ref(v_view_2461_);
v___x_2469_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2467_);
v___x_2470_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2469_, v_snd_2466_);
lean_dec_ref(v___x_2469_);
v_snd_2471_ = lean_ctor_get(v___x_2470_, 1);
lean_inc(v_snd_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = lean_box(0);
v_sz_2473_ = lean_array_size(v_args_2468_);
v___x_2474_ = ((size_t)0ULL);
v___x_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2163_, v_args_2468_, v_sz_2473_, v___x_2474_, v___x_2472_, v_a_2128_, v_snd_2471_);
lean_dec_ref(v_args_2468_);
v_snd_2476_ = lean_ctor_get(v___x_2475_, 1);
lean_inc(v_snd_2476_);
lean_dec_ref(v___x_2475_);
v___x_2477_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2478_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2477_, v_snd_2476_);
v_snd_2479_ = lean_ctor_get(v___x_2478_, 1);
lean_inc(v_snd_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2479_);
return v___x_2480_;
}
case 8:
{
lean_object* v_view_2481_; lean_object* v___x_2482_; lean_object* v_snd_2483_; lean_object* v_level_2484_; lean_object* v_content_2485_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v_snd_2500_; uint8_t v___x_2501_; 
lean_dec(v_stx_2124_);
v_view_2481_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2481_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2482_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2483_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_snd_2483_);
lean_dec_ref(v___x_2482_);
v_level_2484_ = lean_ctor_get(v_view_2481_, 2);
lean_inc(v_level_2484_);
v_content_2485_ = lean_ctor_get(v_view_2481_, 3);
lean_inc_ref(v_content_2485_);
lean_dec_ref(v_view_2481_);
v___x_2495_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_2496_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(v_level_2484_, v___x_2495_);
v___x_2497_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2498_ = lean_string_append(v___x_2496_, v___x_2497_);
v___x_2499_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2498_, v_snd_2483_);
lean_dec_ref(v___x_2498_);
v_snd_2500_ = lean_ctor_get(v___x_2499_, 1);
lean_inc(v_snd_2500_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2485_);
if (v___x_2501_ == 0)
{
v___y_2487_ = v_a_2128_;
v___y_2488_ = v_snd_2500_;
goto v___jp_2486_;
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v_snd_2504_; 
v___x_2502_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2503_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2502_, v_snd_2500_);
v_snd_2504_ = lean_ctor_get(v___x_2503_, 1);
lean_inc(v_snd_2504_);
lean_dec_ref(v___x_2503_);
v___y_2487_ = v_a_2128_;
v___y_2488_ = v_snd_2504_;
goto v___jp_2486_;
}
v___jp_2486_:
{
size_t v_sz_2489_; size_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v_snd_2493_; lean_object* v___x_2494_; 
v_sz_2489_ = lean_array_size(v_content_2485_);
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2489_, v___x_2490_, v_content_2485_);
v___x_2492_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2491_, v___x_2163_, v___y_2487_, v___y_2488_);
lean_dec_ref(v___x_2491_);
v_snd_2493_ = lean_ctor_get(v___x_2492_, 1);
lean_inc(v_snd_2493_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2493_);
return v___x_2494_;
}
}
case 9:
{
lean_object* v_view_2505_; lean_object* v___x_2506_; lean_object* v_snd_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v_snd_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_snd_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_snd_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_snd_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_snd_2522_; lean_object* v___x_2523_; 
lean_dec(v_stx_2124_);
v_view_2505_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2505_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2506_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2507_ = lean_ctor_get(v___x_2506_, 1);
lean_inc(v_snd_2507_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2509_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2508_, v_snd_2507_);
v_snd_2510_ = lean_ctor_get(v___x_2509_, 1);
lean_inc(v_snd_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = l_Lean_Doc_LinkRefView_getName(v_view_2505_);
v___x_2512_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2511_, v_snd_2510_);
lean_dec_ref(v___x_2511_);
v_snd_2513_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_snd_2513_);
lean_dec_ref(v___x_2512_);
v___x_2514_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2515_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2514_, v_snd_2513_);
v_snd_2516_ = lean_ctor_get(v___x_2515_, 1);
lean_inc(v_snd_2516_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2518_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2517_, v_snd_2516_);
v_snd_2519_ = lean_ctor_get(v___x_2518_, 1);
lean_inc(v_snd_2519_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = l_Lean_Doc_LinkRefView_getUrl(v_view_2505_);
lean_dec_ref(v_view_2505_);
v___x_2521_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2520_, v_snd_2519_);
lean_dec_ref(v___x_2520_);
v_snd_2522_ = lean_ctor_get(v___x_2521_, 1);
lean_inc(v_snd_2522_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2522_);
return v___x_2523_;
}
case 10:
{
lean_object* v_view_2524_; lean_object* v___x_2525_; lean_object* v_snd_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_snd_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_snd_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_snd_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_snd_2538_; lean_object* v_content_2539_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___x_2549_; 
lean_dec(v_stx_2124_);
v_view_2524_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2524_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2525_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2526_ = lean_ctor_get(v___x_2525_, 1);
lean_inc(v_snd_2526_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2528_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2527_, v_snd_2526_);
v_snd_2529_ = lean_ctor_get(v___x_2528_, 1);
lean_inc(v_snd_2529_);
lean_dec_ref(v___x_2528_);
v___x_2530_ = l_Lean_Doc_FootnoteRefView_getName(v_view_2524_);
v___x_2531_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2530_, v_snd_2529_);
lean_dec_ref(v___x_2530_);
v_snd_2532_ = lean_ctor_get(v___x_2531_, 1);
lean_inc(v_snd_2532_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2534_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2533_, v_snd_2532_);
v_snd_2535_ = lean_ctor_get(v___x_2534_, 1);
lean_inc(v_snd_2535_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2537_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2536_, v_snd_2535_);
v_snd_2538_ = lean_ctor_get(v___x_2537_, 1);
lean_inc(v_snd_2538_);
lean_dec_ref(v___x_2537_);
v_content_2539_ = lean_ctor_get(v_view_2524_, 4);
lean_inc_ref(v_content_2539_);
lean_dec_ref(v_view_2524_);
v___x_2549_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2539_);
if (v___x_2549_ == 0)
{
v___y_2541_ = v_a_2128_;
v___y_2542_ = v_snd_2538_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_snd_2552_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2551_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2550_, v_snd_2538_);
v_snd_2552_ = lean_ctor_get(v___x_2551_, 1);
lean_inc(v_snd_2552_);
lean_dec_ref(v___x_2551_);
v___y_2541_ = v_a_2128_;
v___y_2542_ = v_snd_2552_;
goto v___jp_2540_;
}
v___jp_2540_:
{
size_t v_sz_2543_; size_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v_snd_2547_; lean_object* v___x_2548_; 
v_sz_2543_ = lean_array_size(v_content_2539_);
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2543_, v___x_2544_, v_content_2539_);
v___x_2546_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2545_, v___x_2163_, v___y_2541_, v___y_2542_);
lean_dec_ref(v___x_2545_);
v_snd_2547_ = lean_ctor_get(v___x_2546_, 1);
lean_inc(v_snd_2547_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2547_);
return v___x_2548_;
}
}
default: 
{
lean_object* v_view_2553_; lean_object* v___x_2554_; lean_object* v_snd_2555_; lean_object* v___y_2557_; lean_object* v___x_2570_; 
v_view_2553_ = lean_ctor_get(v_val_2309_, 0);
lean_inc_ref(v_view_2553_);
lean_dec_ref_known(v_val_2309_, 1);
v___x_2554_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2128_, v_a_2129_);
v_snd_2555_ = lean_ctor_get(v___x_2554_, 1);
lean_inc(v_snd_2555_);
lean_dec_ref(v___x_2554_);
v___x_2570_ = l_Lean_Syntax_getSubstring_x3f(v_stx_2124_, v___x_2163_, v___x_2163_);
lean_dec(v_stx_2124_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_contents_2571_; lean_object* v___x_2572_; 
v_contents_2571_ = lean_ctor_get(v_view_2553_, 2);
lean_inc(v_contents_2571_);
lean_dec_ref(v_view_2553_);
v___x_2572_ = l_Lean_Syntax_reprint(v_contents_2571_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___y_2557_ = v___x_2573_;
goto v___jp_2556_;
}
else
{
lean_object* v_val_2574_; 
v_val_2574_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_val_2574_);
lean_dec_ref_known(v___x_2572_, 1);
v___y_2557_ = v_val_2574_;
goto v___jp_2556_;
}
}
else
{
lean_object* v_val_2575_; lean_object* v_str_2576_; lean_object* v_startPos_2577_; lean_object* v_stopPos_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_snd_2582_; lean_object* v___x_2583_; 
lean_dec_ref(v_view_2553_);
v_val_2575_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_val_2575_);
lean_dec_ref_known(v___x_2570_, 1);
v_str_2576_ = lean_ctor_get(v_val_2575_, 0);
lean_inc_ref(v_str_2576_);
v_startPos_2577_ = lean_ctor_get(v_val_2575_, 1);
lean_inc(v_startPos_2577_);
v_stopPos_2578_ = lean_ctor_get(v_val_2575_, 2);
lean_inc(v_stopPos_2578_);
lean_dec(v_val_2575_);
v___x_2579_ = lean_string_utf8_extract(v_str_2576_, v_startPos_2577_, v_stopPos_2578_);
lean_dec(v_stopPos_2578_);
lean_dec(v_startPos_2577_);
lean_dec_ref(v_str_2576_);
lean_inc(v_a_2128_);
v___x_2580_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2128_, v___x_2579_);
v___x_2581_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2580_, v_snd_2555_);
lean_dec_ref(v___x_2580_);
v_snd_2582_ = lean_ctor_get(v___x_2581_, 1);
lean_inc(v_snd_2582_);
lean_dec_ref(v___x_2581_);
v___x_2583_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2582_);
return v___x_2583_;
}
v___jp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2558_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
v___x_2559_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2558_, v_snd_2555_);
v_snd_2560_ = lean_ctor_get(v___x_2559_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v___x_2559_);
lean_inc(v_a_2128_);
v___x_2561_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2128_, v___y_2557_);
v___x_2562_ = lean_string_utf8_byte_size(v___x_2561_);
v___x_2563_ = lean_unsigned_to_nat(0u);
v___x_2564_ = lean_nat_dec_eq(v___x_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v_snd_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_snd_2569_; 
v___x_2565_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2561_, v_snd_2560_);
lean_dec_ref(v___x_2561_);
v_snd_2566_ = lean_ctor_get(v___x_2565_, 1);
lean_inc(v_snd_2566_);
lean_dec_ref(v___x_2565_);
v___x_2567_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2568_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2567_, v_snd_2566_);
v_snd_2569_ = lean_ctor_get(v___x_2568_, 1);
lean_inc(v_snd_2569_);
lean_dec_ref(v___x_2568_);
v___y_2131_ = v_snd_2569_;
goto v___jp_2130_;
}
else
{
lean_dec_ref(v___x_2561_);
v___y_2131_ = v_snd_2560_;
goto v___jp_2130_;
}
}
}
}
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec(v___x_2308_);
v___x_2584_ = lean_box(0);
v___x_2585_ = l_Lean_Syntax_formatStx(v_stx_2124_, v___x_2584_, v___x_2163_);
v___x_2586_ = l_Std_Format_defWidth;
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = l_Std_Format_pretty(v___x_2585_, v___x_2586_, v___x_2587_, v___x_2587_);
v___x_2589_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2588_, v_a_2129_);
lean_dec_ref(v___x_2588_);
return v___x_2589_;
}
}
}
}
}
}
else
{
lean_object* v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_next_x3f_2125_);
v___x_2590_ = l_Lean_Syntax_getArgs(v_stx_2124_);
lean_dec(v_stx_2124_);
v___x_2591_ = 0;
v___x_2592_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2590_, v___x_2591_, v_a_2128_, v_a_2129_);
lean_dec_ref(v___x_2590_);
return v___x_2592_;
}
v___jp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_snd_2137_; lean_object* v___x_2138_; 
v___x_2132_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
lean_inc(v_a_2128_);
v___x_2133_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2128_, v___x_2132_);
v___x_2134_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_2135_ = lean_string_append(v___x_2133_, v___x_2134_);
v___x_2136_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2135_, v___y_2131_);
lean_dec_ref(v___x_2135_);
v_snd_2137_ = lean_ctor_get(v___x_2136_, 1);
lean_inc(v_snd_2137_);
lean_dec_ref(v___x_2136_);
v___x_2138_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2137_);
return v___x_2138_;
}
v___jp_2139_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_snd_2154_; lean_object* v___x_2155_; lean_object* v_snd_2156_; lean_object* v___x_2157_; 
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_string_utf8_byte_size(v___y_2144_);
lean_inc_ref(v___y_2144_);
v___x_2147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2147_, 0, v___y_2144_);
lean_ctor_set(v___x_2147_, 1, v___x_2145_);
lean_ctor_set(v___x_2147_, 2, v___x_2146_);
v___x_2148_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
v___x_2149_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2150_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2143_, v___y_2144_, v___x_2147_, v___x_2146_, v___x_2148_, v___x_2149_);
lean_dec_ref_known(v___x_2147_, 3);
lean_dec_ref(v___y_2144_);
v___x_2151_ = lean_array_to_list(v___x_2150_);
v___x_2152_ = l_String_intercalate(v___y_2141_, v___x_2151_);
v___x_2153_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2152_, v___y_2142_);
lean_dec_ref(v___x_2152_);
v_snd_2154_ = lean_ctor_get(v___x_2153_, 1);
lean_inc(v_snd_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2140_, v_snd_2154_);
lean_dec_ref(v___y_2140_);
v_snd_2156_ = lean_ctor_get(v___x_2155_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2156_);
return v___x_2157_;
}
v___jp_2158_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v_a_2129_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t v___x_2593_, lean_object* v_as_2594_, size_t v_sz_2595_, size_t v_i_2596_, lean_object* v_b_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_usize_dec_lt(v_i_2596_, v_sz_2595_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v_b_2597_);
lean_ctor_set(v___x_2601_, 1, v___y_2599_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v_snd_2604_; lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_snd_2608_; lean_object* v___x_2609_; size_t v___x_2610_; size_t v___x_2611_; 
v___x_2602_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12));
v___x_2603_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2602_, v___y_2599_);
v_snd_2604_ = lean_ctor_get(v___x_2603_, 1);
lean_inc(v_snd_2604_);
lean_dec_ref(v___x_2603_);
v_a_2605_ = lean_array_uget_borrowed(v_as_2594_, v_i_2596_);
v___x_2606_ = lean_box(0);
lean_inc(v_a_2605_);
v___x_2607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2605_, v___x_2606_, v___x_2593_, v___x_2593_, v___y_2598_, v_snd_2604_);
v_snd_2608_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_snd_2608_);
lean_dec_ref(v___x_2607_);
v___x_2609_ = lean_box(0);
v___x_2610_ = ((size_t)1ULL);
v___x_2611_ = lean_usize_add(v_i_2596_, v___x_2610_);
v_i_2596_ = v___x_2611_;
v_b_2597_ = v___x_2609_;
v___y_2599_ = v_snd_2608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v___x_2613_, lean_object* v_as_2614_, lean_object* v_sz_2615_, lean_object* v_i_2616_, lean_object* v_b_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v___x_62075__boxed_2620_; size_t v_sz_boxed_2621_; size_t v_i_boxed_2622_; lean_object* v_res_2623_; 
v___x_62075__boxed_2620_ = lean_unbox(v___x_2613_);
v_sz_boxed_2621_ = lean_unbox_usize(v_sz_2615_);
lean_dec(v_sz_2615_);
v_i_boxed_2622_ = lean_unbox_usize(v_i_2616_);
lean_dec(v_i_2616_);
v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_62075__boxed_2620_, v_as_2614_, v_sz_boxed_2621_, v_i_boxed_2622_, v_b_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v_as_2614_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object* v___y_2624_, lean_object* v___x_2625_, lean_object* v_as_2626_, lean_object* v_sz_2627_, lean_object* v_i_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v___x_62093__boxed_2632_; size_t v_sz_boxed_2633_; size_t v_i_boxed_2634_; lean_object* v_res_2635_; 
v___x_62093__boxed_2632_ = lean_unbox(v___x_2625_);
v_sz_boxed_2633_ = lean_unbox_usize(v_sz_2627_);
lean_dec(v_sz_2627_);
v_i_boxed_2634_ = lean_unbox_usize(v_i_2628_);
lean_dec(v_i_2628_);
v_res_2635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2624_, v___x_62093__boxed_2632_, v_as_2626_, v_sz_boxed_2633_, v_i_boxed_2634_, v_b_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v_as_2626_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object* v_stxs_2636_, lean_object* v_lineStart_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
uint8_t v_lineStart_boxed_2640_; lean_object* v_res_2641_; 
v_lineStart_boxed_2640_ = lean_unbox(v_lineStart_2637_);
v_res_2641_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v_stxs_2636_, v_lineStart_boxed_2640_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_stxs_2636_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object* v_char_2642_, lean_object* v_inls_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_){
_start:
{
uint32_t v_char_boxed_2646_; lean_object* v_res_2647_; 
v_char_boxed_2646_ = lean_unbox_uint32(v_char_2642_);
lean_dec(v_char_2642_);
v_res_2647_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v_char_boxed_2646_, v_inls_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2644_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object* v___x_2648_, lean_object* v_alternate_2649_, lean_object* v_as_2650_, lean_object* v_sz_2651_, lean_object* v_i_2652_, lean_object* v_b_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v___x_62173__boxed_2656_; uint8_t v_alternate_boxed_2657_; size_t v_sz_boxed_2658_; size_t v_i_boxed_2659_; lean_object* v_res_2660_; 
v___x_62173__boxed_2656_ = lean_unbox(v___x_2648_);
v_alternate_boxed_2657_ = lean_unbox(v_alternate_2649_);
v_sz_boxed_2658_ = lean_unbox_usize(v_sz_2651_);
lean_dec(v_sz_2651_);
v_i_boxed_2659_ = lean_unbox_usize(v_i_2652_);
lean_dec(v_i_2652_);
v_res_2660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_62173__boxed_2656_, v_alternate_boxed_2657_, v_as_2650_, v_sz_boxed_2658_, v_i_boxed_2659_, v_b_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v_as_2650_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object* v___x_2661_, lean_object* v_as_2662_, lean_object* v_sz_2663_, lean_object* v_i_2664_, lean_object* v_b_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
uint8_t v___x_62207__boxed_2668_; size_t v_sz_boxed_2669_; size_t v_i_boxed_2670_; lean_object* v_res_2671_; 
v___x_62207__boxed_2668_ = lean_unbox(v___x_2661_);
v_sz_boxed_2669_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2670_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_62207__boxed_2668_, v_as_2662_, v_sz_boxed_2669_, v_i_boxed_2670_, v_b_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v_as_2662_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object* v_upperBound_2672_, lean_object* v___y_2673_, lean_object* v_a_2674_, lean_object* v_b_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2672_, v___y_2673_, v_a_2674_, v_b_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2673_);
lean_dec(v_upperBound_2672_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object* v_stx_2679_, lean_object* v_next_x3f_2680_, lean_object* v_atLineStart_2681_, lean_object* v_alternate_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
uint8_t v_atLineStart_boxed_2685_; uint8_t v_alternate_boxed_2686_; lean_object* v_res_2687_; 
v_atLineStart_boxed_2685_ = lean_unbox(v_atLineStart_2681_);
v_alternate_boxed_2686_ = lean_unbox(v_alternate_2682_);
v_res_2687_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2679_, v_next_x3f_2680_, v_atLineStart_boxed_2685_, v_alternate_boxed_2686_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2683_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object* v_s_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object* v_s_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(v_s_2690_);
lean_dec_ref(v_s_2690_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object* v_upperBound_2692_, lean_object* v___y_2693_, lean_object* v_inst_2694_, lean_object* v_R_2695_, lean_object* v_a_2696_, lean_object* v_b_2697_, lean_object* v_c_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2692_, v___y_2693_, v_a_2696_, v_b_2697_, v___y_2699_, v___y_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object* v_upperBound_2702_, lean_object* v___y_2703_, lean_object* v_inst_2704_, lean_object* v_R_2705_, lean_object* v_a_2706_, lean_object* v_b_2707_, lean_object* v_c_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(v_upperBound_2702_, v___y_2703_, v_inst_2704_, v_R_2705_, v_a_2706_, v_b_2707_, v_c_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2703_);
lean_dec(v_upperBound_2702_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___x_2714_, lean_object* v___x_2715_, lean_object* v_inst_2716_, lean_object* v_R_2717_, lean_object* v_a_2718_, lean_object* v_b_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2712_, v___y_2713_, v___x_2714_, v___x_2715_, v_a_2718_, v_b_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___x_2723_, lean_object* v___x_2724_, lean_object* v_inst_2725_, lean_object* v_R_2726_, lean_object* v_a_2727_, lean_object* v_b_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(v___y_2721_, v___y_2722_, v___x_2723_, v___x_2724_, v_inst_2725_, v_R_2726_, v_a_2727_, v_b_2728_);
lean_dec_ref(v___x_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object* v_s_2730_, lean_object* v_pos_2731_){
_start:
{
lean_object* v_str_2732_; lean_object* v_startInclusive_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v_decide_2737_; 
v_str_2732_ = lean_ctor_get(v_s_2730_, 0);
v_startInclusive_2733_ = lean_ctor_get(v_s_2730_, 1);
v___x_2734_ = lean_nat_add(v_startInclusive_2733_, v_pos_2731_);
v___x_2735_ = lean_nat_sub(v___x_2734_, v_startInclusive_2733_);
v___x_2736_ = lean_unsigned_to_nat(0u);
v_decide_2737_ = lean_nat_dec_eq(v___x_2735_, v___x_2736_);
if (v_decide_2737_ == 0)
{
uint32_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; uint32_t v___x_2744_; uint8_t v___x_2745_; 
v___x_2738_ = 10;
lean_inc(v_startInclusive_2733_);
lean_inc_ref(v_str_2732_);
v___x_2739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2739_, 0, v_str_2732_);
lean_ctor_set(v___x_2739_, 1, v_startInclusive_2733_);
lean_ctor_set(v___x_2739_, 2, v___x_2734_);
v___x_2740_ = lean_unsigned_to_nat(1u);
v___x_2741_ = lean_nat_sub(v___x_2735_, v___x_2740_);
lean_dec(v___x_2735_);
v___x_2742_ = l_String_Slice_posLE(v___x_2739_, v___x_2741_);
lean_dec_ref_known(v___x_2739_, 3);
v___x_2743_ = lean_nat_add(v_startInclusive_2733_, v___x_2742_);
v___x_2744_ = lean_string_utf8_get_fast(v_str_2732_, v___x_2743_);
lean_dec(v___x_2743_);
v___x_2745_ = lean_uint32_dec_eq(v___x_2744_, v___x_2738_);
if (v___x_2745_ == 0)
{
lean_dec(v___x_2742_);
return v_pos_2731_;
}
else
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2746_ = lean_nat_add(v___x_2742_, v___x_2740_);
v___x_2747_ = lean_nat_dec_le(v___x_2746_, v_pos_2731_);
lean_dec(v___x_2746_);
if (v___x_2747_ == 0)
{
lean_dec(v___x_2742_);
return v_pos_2731_;
}
else
{
lean_dec(v_pos_2731_);
v_pos_2731_ = v___x_2742_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2735_);
lean_dec(v___x_2734_);
return v_pos_2731_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object* v_s_2749_, lean_object* v_pos_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v_s_2749_, v_pos_2750_);
lean_dec_ref(v_s_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object* v_s_2752_){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2753_ = lean_string_utf8_byte_size(v_s_2752_);
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_nat_dec_le(v___x_2754_, v___x_2753_);
if (v___x_2755_ == 0)
{
return v_s_2752_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2757_ = lean_unsigned_to_nat(0u);
v___x_2758_ = lean_nat_sub(v___x_2753_, v___x_2754_);
v___x_2759_ = lean_string_memcmp(v_s_2752_, v___x_2756_, v___x_2758_, v___x_2757_, v___x_2754_);
lean_dec(v___x_2758_);
if (v___x_2759_ == 0)
{
return v_s_2752_;
}
else
{
uint32_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2760_ = 10;
lean_inc_ref(v_s_2752_);
v___x_2761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2761_, 0, v_s_2752_);
lean_ctor_set(v___x_2761_, 1, v___x_2757_);
lean_ctor_set(v___x_2761_, 2, v___x_2753_);
v___x_2762_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v___x_2761_, v___x_2753_);
lean_dec_ref_known(v___x_2761_, 3);
v___x_2763_ = lean_string_utf8_extract_fast(v_s_2752_, v___x_2757_, v___x_2762_);
lean_dec(v___x_2762_);
lean_dec_ref(v_s_2752_);
v___x_2764_ = lean_string_push(v___x_2763_, v___x_2760_);
return v___x_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object* v_stx_2765_, uint8_t v_alternate_2766_){
_start:
{
lean_object* v___x_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_snd_2772_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = 0;
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2771_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2765_, v___x_2767_, v___x_2768_, v_alternate_2766_, v___x_2769_, v___x_2770_);
v_snd_2772_ = lean_ctor_get(v___x_2771_, 1);
lean_inc(v_snd_2772_);
lean_dec_ref(v___x_2771_);
return v_snd_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object* v_stx_2773_, lean_object* v_alternate_2774_){
_start:
{
uint8_t v_alternate_boxed_2775_; lean_object* v_res_2776_; 
v_alternate_boxed_2775_ = lean_unbox(v_alternate_2774_);
v_res_2776_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2773_, v_alternate_boxed_2775_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_2777_, uint8_t v_alternate_2778_){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2777_, v_alternate_2778_);
v___x_2780_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object* v_stx_2781_, lean_object* v_alternate_2782_){
_start:
{
uint8_t v_alternate_boxed_2783_; lean_object* v_res_2784_; 
v_alternate_boxed_2783_ = lean_unbox(v_alternate_2782_);
v_res_2784_ = l_Lean_Doc_Parser_versoSyntaxToString(v_stx_2781_, v_alternate_boxed_2783_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object* v_b_2785_, lean_object* v___y_2786_){
_start:
{
uint8_t v___x_2787_; 
lean_inc(v_b_2785_);
v___x_2787_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_b_2785_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; uint8_t v___y_2790_; 
lean_inc(v_b_2785_);
v___x_2788_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v___y_2786_, v_b_2785_);
lean_dec(v___y_2786_);
if (lean_obj_tag(v___x_2788_) == 0)
{
v___y_2790_ = v___x_2787_;
goto v___jp_2789_;
}
else
{
lean_object* v_val_2793_; uint8_t v_alternate_2794_; 
v_val_2793_ = lean_ctor_get(v___x_2788_, 0);
v_alternate_2794_ = lean_ctor_get_uint8(v_val_2793_, 1);
v___y_2790_ = v_alternate_2794_;
goto v___jp_2789_;
}
v___jp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_b_2785_, v___y_2790_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v___x_2788_);
return v___x_2792_;
}
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_dec(v_b_2785_);
v___x_2795_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___y_2786_);
return v___x_2796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object* v_n_2797_, lean_object* v_f_2798_, lean_object* v_xs_2799_, lean_object* v_k_2800_, lean_object* v_acc_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = lean_nat_dec_lt(v_k_2800_, v_n_2797_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
lean_dec(v_k_2800_);
lean_dec_ref(v_f_2798_);
v___x_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2804_, 0, v_acc_2801_);
lean_ctor_set(v___x_2804_, 1, v___y_2802_);
return v___x_2804_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v_fst_2807_; lean_object* v_snd_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2805_ = lean_array_fget_borrowed(v_xs_2799_, v_k_2800_);
lean_inc_ref(v_f_2798_);
lean_inc(v___x_2805_);
v___x_2806_ = lean_apply_2(v_f_2798_, v___x_2805_, v___y_2802_);
v_fst_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_fst_2807_);
v_snd_2808_ = lean_ctor_get(v___x_2806_, 1);
lean_inc(v_snd_2808_);
lean_dec_ref(v___x_2806_);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_nat_add(v_k_2800_, v___x_2809_);
lean_dec(v_k_2800_);
v___x_2811_ = lean_array_push(v_acc_2801_, v_fst_2807_);
v_k_2800_ = v___x_2810_;
v_acc_2801_ = v___x_2811_;
v___y_2802_ = v_snd_2808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object* v_n_2813_, lean_object* v_f_2814_, lean_object* v_xs_2815_, lean_object* v_k_2816_, lean_object* v_acc_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2813_, v_f_2814_, v_xs_2815_, v_k_2816_, v_acc_2817_, v___y_2818_);
lean_dec_ref(v_xs_2815_);
lean_dec(v_n_2813_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object* v_blocks_2821_){
_start:
{
lean_object* v___f_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v_fst_2828_; 
v___f_2822_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0));
v___x_2823_ = lean_array_get_size(v_blocks_2821_);
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2826_ = lean_box(0);
v___x_2827_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v___x_2823_, v___f_2822_, v_blocks_2821_, v___x_2824_, v___x_2825_, v___x_2826_);
v_fst_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_fst_2828_);
lean_dec_ref(v___x_2827_);
return v_fst_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object* v_blocks_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2829_);
lean_dec_ref(v_blocks_2829_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object* v_00_u03b1_2831_, lean_object* v_00_u03b2_2832_, lean_object* v_n_2833_, lean_object* v_f_2834_, lean_object* v_xs_2835_, lean_object* v_k_2836_, lean_object* v_h_2837_, lean_object* v_acc_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2833_, v_f_2834_, v_xs_2835_, v_k_2836_, v_acc_2838_, v___y_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object* v_00_u03b1_2841_, lean_object* v_00_u03b2_2842_, lean_object* v_n_2843_, lean_object* v_f_2844_, lean_object* v_xs_2845_, lean_object* v_k_2846_, lean_object* v_h_2847_, lean_object* v_acc_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(v_00_u03b1_2841_, v_00_u03b2_2842_, v_n_2843_, v_f_2844_, v_xs_2845_, v_k_2846_, v_h_2847_, v_acc_2848_, v___y_2849_);
lean_dec_ref(v_xs_2845_);
lean_dec(v_n_2843_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object* v_as_2851_, size_t v_i_2852_, size_t v_stop_2853_, lean_object* v_b_2854_){
_start:
{
uint8_t v___x_2855_; 
v___x_2855_ = lean_usize_dec_eq(v_i_2852_, v_stop_2853_);
if (v___x_2855_ == 0)
{
lean_object* v___x_2856_; lean_object* v___x_2857_; size_t v___x_2858_; size_t v___x_2859_; 
v___x_2856_ = lean_array_uget_borrowed(v_as_2851_, v_i_2852_);
v___x_2857_ = lean_string_append(v_b_2854_, v___x_2856_);
v___x_2858_ = ((size_t)1ULL);
v___x_2859_ = lean_usize_add(v_i_2852_, v___x_2858_);
v_i_2852_ = v___x_2859_;
v_b_2854_ = v___x_2857_;
goto _start;
}
else
{
return v_b_2854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object* v_as_2861_, lean_object* v_i_2862_, lean_object* v_stop_2863_, lean_object* v_b_2864_){
_start:
{
size_t v_i_boxed_2865_; size_t v_stop_boxed_2866_; lean_object* v_res_2867_; 
v_i_boxed_2865_ = lean_unbox_usize(v_i_2862_);
lean_dec(v_i_2862_);
v_stop_boxed_2866_ = lean_unbox_usize(v_stop_2863_);
lean_dec(v_stop_2863_);
v_res_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v_as_2861_, v_i_boxed_2865_, v_stop_boxed_2866_, v_b_2864_);
lean_dec_ref(v_as_2861_);
return v_res_2867_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0(void){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2869_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object* v_blocks_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2871_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1));
v___x_2872_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2870_);
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = lean_array_get_size(v___x_2872_);
v___x_2875_ = lean_nat_dec_lt(v___x_2873_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; 
lean_dec_ref(v___x_2872_);
v___x_2876_ = lean_obj_once(&l_Lean_Doc_Parser_versoDocumentToString___closed__0, &l_Lean_Doc_Parser_versoDocumentToString___closed__0_once, _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0);
return v___x_2876_;
}
else
{
size_t v___x_2877_; size_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2877_ = ((size_t)0ULL);
v___x_2878_ = lean_usize_of_nat(v___x_2874_);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v___x_2872_, v___x_2877_, v___x_2878_, v___x_2871_);
lean_dec_ref(v___x_2872_);
v___x_2880_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2879_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object* v_blocks_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Doc_Parser_versoDocumentToString(v_blocks_2881_);
lean_dec_ref(v_blocks_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; lean_object* v_stxTrav_2886_; lean_object* v_cur_2887_; lean_object* v___x_2888_; 
v___x_2885_ = lean_st_ref_get(v___y_2883_);
v_stxTrav_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc_ref(v_stxTrav_2886_);
lean_dec(v___x_2885_);
v_cur_2887_ = lean_ctor_get(v_stxTrav_2886_, 0);
lean_inc(v_cur_2887_);
lean_dec_ref(v_stxTrav_2886_);
v___x_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_cur_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2889_);
lean_dec(v___y_2889_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2893_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; lean_object* v_stxTrav_2907_; lean_object* v_leadWord_2908_; uint8_t v_leadWordIdent_2909_; uint8_t v_isUngrouped_2910_; uint8_t v_mustBeGrouped_2911_; lean_object* v_stack_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2923_; 
v___x_2906_ = lean_st_ref_take(v___y_2904_);
v_stxTrav_2907_ = lean_ctor_get(v___x_2906_, 0);
v_leadWord_2908_ = lean_ctor_get(v___x_2906_, 1);
v_leadWordIdent_2909_ = lean_ctor_get_uint8(v___x_2906_, sizeof(void*)*3);
v_isUngrouped_2910_ = lean_ctor_get_uint8(v___x_2906_, sizeof(void*)*3 + 1);
v_mustBeGrouped_2911_ = lean_ctor_get_uint8(v___x_2906_, sizeof(void*)*3 + 2);
v_stack_2912_ = lean_ctor_get(v___x_2906_, 2);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2914_ = v___x_2906_;
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_stack_2912_);
lean_inc(v_leadWord_2908_);
lean_inc(v_stxTrav_2907_);
lean_dec(v___x_2906_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2923_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2919_; 
v___x_2916_ = lean_box(0);
v___x_2917_ = l_Lean_Syntax_Traverser_left(v_stxTrav_2907_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2917_);
v___x_2919_ = v___x_2914_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_leadWord_2908_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v_stack_2912_);
lean_ctor_set_uint8(v_reuseFailAlloc_2922_, sizeof(void*)*3, v_leadWordIdent_2909_);
lean_ctor_set_uint8(v_reuseFailAlloc_2922_, sizeof(void*)*3 + 1, v_isUngrouped_2910_);
lean_ctor_set_uint8(v_reuseFailAlloc_2922_, sizeof(void*)*3 + 2, v_mustBeGrouped_2911_);
v___x_2919_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_st_ref_put(v___y_2904_, v___x_2919_);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2916_);
return v___x_2921_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2924_);
lean_dec(v___y_2924_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2928_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object* v_upperBound_2939_, lean_object* v___x_2940_, lean_object* v_rendered_2941_, lean_object* v_a_2942_, lean_object* v_b_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
uint8_t v___x_2949_; 
v___x_2949_ = lean_nat_dec_lt(v_a_2942_, v_upperBound_2939_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; 
lean_dec(v_a_2942_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v_b_2943_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; lean_object* v___y_2953_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v___x_2951_ = lean_box(0);
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = lean_unsigned_to_nat(1u);
v___x_2961_ = lean_nat_sub(v___x_2940_, v___x_2960_);
v___x_2962_ = lean_nat_sub(v___x_2961_, v_a_2942_);
lean_dec(v___x_2961_);
v___x_2963_ = lean_array_fget_borrowed(v_rendered_2941_, v___x_2962_);
lean_dec(v___x_2962_);
v___x_2964_ = lean_nat_dec_eq(v_a_2942_, v___x_2959_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; 
lean_inc(v___x_2963_);
v___x_2965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
v___y_2953_ = v___x_2965_;
goto v___jp_2952_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_inc(v___x_2963_);
v___x_2966_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2963_);
v___x_2967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
v___y_2953_ = v___x_2967_;
goto v___jp_2952_;
}
v___jp_2952_:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___y_2953_, v___y_2945_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2955_; 
lean_dec_ref_known(v___x_2954_, 1);
v___x_2955_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2945_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec_ref_known(v___x_2955_, 1);
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = lean_nat_add(v_a_2942_, v___x_2956_);
lean_dec(v_a_2942_);
v_a_2942_ = v___x_2957_;
v_b_2943_ = v___x_2951_;
goto _start;
}
else
{
lean_dec(v_a_2942_);
return v___x_2955_;
}
}
else
{
lean_dec(v_a_2942_);
return v___x_2954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object* v_upperBound_2968_, lean_object* v___x_2969_, lean_object* v_rendered_2970_, lean_object* v_a_2971_, lean_object* v_b_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_2968_, v___x_2969_, v_rendered_2970_, v_a_2971_, v_b_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v_rendered_2970_);
lean_dec(v___x_2969_);
lean_dec(v_upperBound_2968_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_2979_, lean_object* v_rendered_2980_, lean_object* v___x_2981_, lean_object* v___x_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v___x_2979_, v___x_2979_, v_rendered_2980_, v___x_2981_, v___x_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_2995_ == 0)
{
lean_object* v_unused_2996_; 
v_unused_2996_ = lean_ctor_get(v___x_2988_, 0);
lean_dec(v_unused_2996_);
v___x_2990_ = v___x_2988_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_dec(v___x_2988_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2982_);
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2982_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
return v___x_2988_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_2997_, lean_object* v_rendered_2998_, lean_object* v___x_2999_, lean_object* v___x_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_2997_, v_rendered_2998_, v___x_2999_, v___x_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec_ref(v_rendered_2998_);
lean_dec(v___x_2997_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v___x_3012_; lean_object* v_a_3013_; lean_object* v_blocks_3014_; lean_object* v_rendered_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3012_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_3008_);
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
v_blocks_3014_ = l_Lean_TSyntax_getVersoBlocks(v_a_3013_);
lean_dec(v_a_3013_);
v_rendered_3015_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_3014_);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_array_get_size(v_blocks_3014_);
lean_dec_ref(v_blocks_3014_);
v___x_3018_ = lean_box(0);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3019_, 0, v___x_3017_);
lean_closure_set(v___f_3019_, 1, v_rendered_3015_);
lean_closure_set(v___f_3019_, 2, v___x_3016_);
lean_closure_set(v___f_3019_, 3, v___x_3018_);
v___x_3020_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs___boxed), 6, 1);
lean_closure_set(v___x_3020_, 0, v___f_3019_);
v___x_3021_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3020_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___f_3034_; lean_object* v___x_3035_; 
v___f_3034_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_3035_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_3034_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Lean_Doc_Parser_document_formatter(v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object* v_upperBound_3042_, lean_object* v___x_3043_, lean_object* v_rendered_3044_, lean_object* v_inst_3045_, lean_object* v_R_3046_, lean_object* v_a_3047_, lean_object* v_b_3048_, lean_object* v_c_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_3042_, v___x_3043_, v_rendered_3044_, v_a_3047_, v_b_3048_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object* v_upperBound_3056_, lean_object* v___x_3057_, lean_object* v_rendered_3058_, lean_object* v_inst_3059_, lean_object* v_R_3060_, lean_object* v_a_3061_, lean_object* v_b_3062_, lean_object* v_c_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(v_upperBound_3056_, v___x_3057_, v_rendered_3058_, v_inst_3059_, v_R_3060_, v_a_3061_, v_b_3062_, v_c_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec_ref(v_rendered_3058_);
lean_dec(v___x_3057_);
lean_dec(v_upperBound_3056_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1(){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3087_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3088_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4));
v___x_3089_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6));
v___x_3090_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___boxed), 5, 0);
v___x_3091_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3087_, v___x_3088_, v___x_3089_, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object* v_a_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
return v_res_3093_;
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
