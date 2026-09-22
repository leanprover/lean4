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
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2_value;
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
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "%%%"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ":::"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "+ "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "- "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\t"};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21;
static const lean_string_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22 = (const lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22_value;
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23;
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
static const lean_ctor_object l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static lean_once_cell_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1;
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
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_172_ = lean_string_utf8_byte_size(v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_179_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_180_ = lean_string_utf8_byte_size(v_a_175_);
v___x_181_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_182_ = lean_nat_dec_le(v___x_181_, v___x_180_);
if (v___x_182_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_nat_sub(v___x_180_, v___x_181_);
v___x_185_ = lean_string_memcmp(v_a_175_, v___x_179_, v___x_184_, v___x_183_, v___x_181_);
lean_dec(v___x_184_);
if (v___x_185_ == 0)
{
goto v___jp_176_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
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
uint8_t v___x_1741__boxed_211_; uint8_t v_b_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v___x_1741__boxed_211_ = lean_unbox(v___x_205_);
v_b_boxed_212_ = lean_unbox(v_b_210_);
v_res_213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_1741__boxed_211_, v___x_206_, v___x_207_, v___x_208_, v_a_209_, v_b_boxed_212_);
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
lean_object* v_str_238_; lean_object* v_startInclusive_239_; lean_object* v_endExclusive_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_str_238_ = lean_ctor_get(v_s_237_, 0);
lean_inc_ref(v_str_238_);
v_startInclusive_239_ = lean_ctor_get(v_s_237_, 1);
lean_inc(v_startInclusive_239_);
v_endExclusive_240_ = lean_ctor_get(v_s_237_, 2);
v___x_241_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_242_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_243_ = lean_nat_sub(v_endExclusive_240_, v_startInclusive_239_);
v___x_244_ = lean_nat_dec_le(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v___x_243_);
lean_dec(v_startInclusive_239_);
lean_dec_ref(v_str_238_);
lean_dec_ref(v_s_237_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_nat_sub(v___x_243_, v___x_242_);
v___x_247_ = lean_nat_add(v_startInclusive_239_, v___x_246_);
lean_dec(v___x_246_);
v___x_248_ = lean_string_memcmp(v_str_238_, v___x_241_, v___x_247_, v___x_245_, v___x_242_);
lean_dec(v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v___x_243_);
lean_dec(v_startInclusive_239_);
lean_dec_ref(v_str_238_);
lean_dec_ref(v_s_237_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_263_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = l_String_Slice_Pos_prevn(v_s_237_, v___x_243_, v___x_249_);
v_isSharedCheck_263_ = !lean_is_exclusive(v_s_237_);
if (v_isSharedCheck_263_ == 0)
{
lean_object* v_unused_264_; lean_object* v_unused_265_; lean_object* v_unused_266_; 
v_unused_264_ = lean_ctor_get(v_s_237_, 2);
lean_dec(v_unused_264_);
v_unused_265_ = lean_ctor_get(v_s_237_, 1);
lean_dec(v_unused_265_);
v_unused_266_ = lean_ctor_get(v_s_237_, 0);
lean_dec(v_unused_266_);
v___x_252_ = v_s_237_;
v_isShared_253_ = v_isSharedCheck_263_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_s_237_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_263_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_nat_add(v_startInclusive_239_, v___x_250_);
lean_dec(v___x_250_);
lean_inc(v___x_254_);
lean_inc(v_startInclusive_239_);
lean_inc_ref(v_str_238_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 2, v___x_254_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_str_238_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_startInclusive_239_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v___x_254_);
v___x_256_ = v_reuseFailAlloc_262_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; uint8_t v___x_261_; 
v___x_257_ = lean_nat_sub(v___x_254_, v_startInclusive_239_);
v___x_258_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__0(v___x_256_, v___x_257_);
lean_dec_ref(v___x_256_);
v___x_259_ = lean_nat_add(v_startInclusive_239_, v___x_258_);
lean_dec(v___x_258_);
lean_dec(v_startInclusive_239_);
v___x_260_ = 0;
v___x_261_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_248_, v___x_254_, v___x_259_, v_str_238_, v___x_245_, v___x_260_);
lean_dec_ref(v_str_238_);
lean_dec(v___x_259_);
lean_dec(v___x_254_);
return v___x_261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline___boxed(lean_object* v_s_267_){
_start:
{
uint8_t v_res_268_; lean_object* v_r_269_; 
v_res_268_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(uint8_t v___x_270_, lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v_inst_275_, lean_object* v_R_276_, lean_object* v_a_277_, uint8_t v_b_278_, lean_object* v_c_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___redArg(v___x_270_, v___x_271_, v___x_272_, v___x_274_, v_a_277_, v_b_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1___boxed(lean_object* v___x_281_, lean_object* v___x_282_, lean_object* v___x_283_, lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v_inst_286_, lean_object* v_R_287_, lean_object* v_a_288_, lean_object* v_b_289_, lean_object* v_c_290_){
_start:
{
uint8_t v___x_1852__boxed_291_; uint8_t v_b_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v___x_1852__boxed_291_ = lean_unbox(v___x_281_);
v_b_boxed_292_ = lean_unbox(v_b_289_);
v_res_293_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline_spec__1(v___x_1852__boxed_291_, v___x_282_, v___x_283_, v___x_284_, v___x_285_, v_inst_286_, v_R_287_, v_a_288_, v_b_boxed_292_, v_c_290_);
lean_dec_ref(v___x_285_);
lean_dec_ref(v___x_284_);
lean_dec(v___x_283_);
lean_dec(v___x_282_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(lean_object* v_s_295_){
_start:
{
lean_object* v_str_296_; lean_object* v_startInclusive_297_; lean_object* v_endExclusive_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_str_296_ = lean_ctor_get(v_s_295_, 0);
lean_inc_ref(v_str_296_);
v_startInclusive_297_ = lean_ctor_get(v_s_295_, 1);
lean_inc(v_startInclusive_297_);
v_endExclusive_298_ = lean_ctor_get(v_s_295_, 2);
v___x_299_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_300_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_301_ = lean_nat_sub(v_endExclusive_298_, v_startInclusive_297_);
v___x_302_ = lean_nat_dec_le(v___x_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec(v___x_301_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
lean_dec_ref(v_s_295_);
v___x_303_ = lean_unsigned_to_nat(0u);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_sub(v___x_301_, v___x_300_);
v___x_306_ = lean_nat_add(v_startInclusive_297_, v___x_305_);
lean_dec(v___x_305_);
v___x_307_ = lean_string_memcmp(v_str_296_, v___x_299_, v___x_306_, v___x_304_, v___x_300_);
lean_dec(v___x_306_);
if (v___x_307_ == 0)
{
lean_dec(v___x_301_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
lean_dec_ref(v_s_295_);
return v___x_304_;
}
else
{
uint8_t v___x_308_; 
lean_inc_ref(v_s_295_);
v___x_308_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_295_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_325_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = l_String_Slice_Pos_prevn(v_s_295_, v___x_301_, v___x_309_);
v_isSharedCheck_325_ = !lean_is_exclusive(v_s_295_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; lean_object* v_unused_327_; lean_object* v_unused_328_; 
v_unused_326_ = lean_ctor_get(v_s_295_, 2);
lean_dec(v_unused_326_);
v_unused_327_ = lean_ctor_get(v_s_295_, 1);
lean_dec(v_unused_327_);
v_unused_328_ = lean_ctor_get(v_s_295_, 0);
lean_dec(v_unused_328_);
v___x_312_ = v_s_295_;
v_isShared_313_ = v_isSharedCheck_325_;
goto v_resetjp_311_;
}
else
{
lean_dec(v_s_295_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_325_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_nat_add(v_startInclusive_297_, v___x_310_);
lean_dec(v___x_310_);
v___x_315_ = lean_nat_sub(v___x_314_, v_startInclusive_297_);
v___x_316_ = lean_nat_dec_le(v___x_300_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v___x_315_);
lean_dec(v___x_314_);
lean_del_object(v___x_312_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
return v___x_309_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_nat_sub(v___x_315_, v___x_300_);
lean_dec(v___x_315_);
v___x_318_ = lean_nat_add(v_startInclusive_297_, v___x_317_);
lean_dec(v___x_317_);
v___x_319_ = lean_string_memcmp(v_str_296_, v___x_299_, v___x_318_, v___x_304_, v___x_300_);
lean_dec(v___x_318_);
if (v___x_319_ == 0)
{
lean_dec(v___x_314_);
lean_del_object(v___x_312_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
return v___x_309_;
}
else
{
if (v___x_308_ == 0)
{
lean_object* v_s_321_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 2, v___x_314_);
v_s_321_ = v___x_312_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_str_296_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_startInclusive_297_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v___x_314_);
v_s_321_ = v_reuseFailAlloc_324_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
uint8_t v___x_322_; 
v___x_322_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endsWithEscapedNewline(v_s_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(2u);
return v___x_323_;
}
else
{
return v___x_309_;
}
}
}
else
{
lean_dec(v___x_314_);
lean_del_object(v___x_312_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
return v___x_309_;
}
}
}
}
}
else
{
lean_dec(v___x_301_);
lean_dec(v_startInclusive_297_);
lean_dec_ref(v_str_296_);
lean_dec_ref(v_s_295_);
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v_zero_331_; uint8_t v_isZero_332_; 
v_zero_331_ = lean_unsigned_to_nat(0u);
v_isZero_332_ = lean_nat_dec_eq(v_x_329_, v_zero_331_);
if (v_isZero_332_ == 1)
{
lean_dec(v_x_329_);
return v_x_330_;
}
else
{
uint32_t v___x_333_; lean_object* v_one_334_; lean_object* v_n_335_; lean_object* v___x_336_; 
v___x_333_ = 10;
v_one_334_ = lean_unsigned_to_nat(1u);
v_n_335_ = lean_nat_sub(v_x_329_, v_one_334_);
lean_dec(v_x_329_);
v___x_336_ = lean_string_push(v_x_330_, v___x_333_);
v_x_329_ = v_n_335_;
v_x_330_ = v___x_336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(lean_object* v_a_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_339_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_340_ = lean_unsigned_to_nat(2u);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_string_utf8_byte_size(v_a_338_);
lean_inc_ref(v_a_338_);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v_a_338_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
v___x_344_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_trailingLineEndings(v___x_343_);
v___x_345_ = lean_nat_sub(v___x_340_, v___x_344_);
lean_dec(v___x_344_);
v___x_346_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_345_, v___x_339_);
v___x_347_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_346_, v_a_338_);
lean_dec_ref(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_a_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___boxed(lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock(v_a_351_, v_a_352_);
lean_dec(v_a_351_);
return v_res_353_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(uint32_t v_a_354_){
_start:
{
uint32_t v___x_355_; uint8_t v___x_356_; 
v___x_355_ = 92;
v___x_356_ = lean_uint32_dec_eq(v_a_354_, v___x_355_);
if (v___x_356_ == 0)
{
uint32_t v___x_357_; uint8_t v___x_358_; 
v___x_357_ = 42;
v___x_358_ = lean_uint32_dec_eq(v_a_354_, v___x_357_);
if (v___x_358_ == 0)
{
uint32_t v___x_359_; uint8_t v___x_360_; 
v___x_359_ = 95;
v___x_360_ = lean_uint32_dec_eq(v_a_354_, v___x_359_);
if (v___x_360_ == 0)
{
uint32_t v___x_361_; uint8_t v___x_362_; 
v___x_361_ = 91;
v___x_362_ = lean_uint32_dec_eq(v_a_354_, v___x_361_);
if (v___x_362_ == 0)
{
uint32_t v___x_363_; uint8_t v___x_364_; 
v___x_363_ = 93;
v___x_364_ = lean_uint32_dec_eq(v_a_354_, v___x_363_);
if (v___x_364_ == 0)
{
uint32_t v___x_365_; uint8_t v___x_366_; 
v___x_365_ = 123;
v___x_366_ = lean_uint32_dec_eq(v_a_354_, v___x_365_);
if (v___x_366_ == 0)
{
uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_367_ = 125;
v___x_368_ = lean_uint32_dec_eq(v_a_354_, v___x_367_);
if (v___x_368_ == 0)
{
uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_369_ = 96;
v___x_370_ = lean_uint32_dec_eq(v_a_354_, v___x_369_);
if (v___x_370_ == 0)
{
uint32_t v___x_371_; uint8_t v___x_372_; 
v___x_371_ = 33;
v___x_372_ = lean_uint32_dec_eq(v_a_354_, v___x_371_);
if (v___x_372_ == 0)
{
uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_373_ = 36;
v___x_374_ = lean_uint32_dec_eq(v_a_354_, v___x_373_);
if (v___x_374_ == 0)
{
uint32_t v___x_375_; uint8_t v___x_376_; 
v___x_375_ = 10;
v___x_376_ = lean_uint32_dec_eq(v_a_354_, v___x_375_);
return v___x_376_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial___boxed(lean_object* v_a_377_){
_start:
{
uint32_t v_a_242__boxed_378_; uint8_t v_res_379_; lean_object* v_r_380_; 
v_a_242__boxed_378_ = lean_unbox_uint32(v_a_377_);
lean_dec(v_a_377_);
v_res_379_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v_a_242__boxed_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(lean_object* v___x_381_, lean_object* v_value_382_, lean_object* v_a_383_, lean_object* v_b_384_){
_start:
{
uint8_t v_decide_385_; 
v_decide_385_ = lean_nat_dec_eq(v_a_383_, v___x_381_);
if (v_decide_385_ == 0)
{
uint32_t v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = lean_string_utf8_get_fast(v_value_382_, v_a_383_);
v___x_387_ = lean_string_utf8_next_fast(v_value_382_, v_a_383_);
lean_dec(v_a_383_);
v___x_388_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_isSpecial(v___x_386_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_string_push(v_b_384_, v___x_386_);
v_a_383_ = v___x_387_;
v_b_384_ = v___x_389_;
goto _start;
}
else
{
uint32_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = 92;
v___x_392_ = lean_string_push(v_b_384_, v___x_391_);
v___x_393_ = lean_string_push(v___x_392_, v___x_386_);
v_a_383_ = v___x_387_;
v_b_384_ = v___x_393_;
goto _start;
}
}
else
{
lean_dec(v_a_383_);
return v_b_384_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg___boxed(lean_object* v___x_395_, lean_object* v_value_396_, lean_object* v_a_397_, lean_object* v_b_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_395_, v_value_396_, v_a_397_, v_b_398_);
lean_dec_ref(v_value_396_);
lean_dec(v___x_395_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(lean_object* v_value_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_402_ = lean_string_utf8_byte_size(v_value_400_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_402_, v_value_400_, v___x_403_, v___x_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped___boxed(lean_object* v_value_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_405_);
lean_dec_ref(v_value_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(lean_object* v___x_407_, lean_object* v___x_408_, lean_object* v_value_409_, lean_object* v_inst_410_, lean_object* v_R_411_, lean_object* v_a_412_, lean_object* v_b_413_, lean_object* v_c_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___redArg(v___x_408_, v_value_409_, v_a_412_, v_b_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0___boxed(lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v_value_418_, lean_object* v_inst_419_, lean_object* v_R_420_, lean_object* v_a_421_, lean_object* v_b_422_, lean_object* v_c_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped_spec__0(v___x_416_, v___x_417_, v_value_418_, v_inst_419_, v_R_420_, v_a_421_, v_b_422_, v_c_423_);
lean_dec_ref(v_value_418_);
lean_dec(v___x_417_);
lean_dec_ref(v___x_416_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(lean_object* v_s_425_, lean_object* v_pos_426_){
_start:
{
lean_object* v_str_427_; lean_object* v_startInclusive_428_; lean_object* v_endExclusive_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v_decide_433_; 
v_str_427_ = lean_ctor_get(v_s_425_, 0);
v_startInclusive_428_ = lean_ctor_get(v_s_425_, 1);
v_endExclusive_429_ = lean_ctor_get(v_s_425_, 2);
v___x_430_ = lean_nat_add(v_startInclusive_428_, v_pos_426_);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_nat_sub(v_endExclusive_429_, v___x_430_);
v_decide_433_ = lean_nat_dec_eq(v___x_431_, v___x_432_);
lean_dec(v___x_432_);
if (v_decide_433_ == 0)
{
uint32_t v___x_434_; uint32_t v___x_435_; uint8_t v___x_436_; 
v___x_434_ = lean_string_utf8_get_fast(v_str_427_, v___x_430_);
v___x_435_ = 48;
v___x_436_ = lean_uint32_dec_le(v___x_435_, v___x_434_);
if (v___x_436_ == 0)
{
lean_dec(v___x_430_);
return v_pos_426_;
}
else
{
uint32_t v___x_437_; uint8_t v___x_438_; 
v___x_437_ = 57;
v___x_438_ = lean_uint32_dec_le(v___x_434_, v___x_437_);
if (v___x_438_ == 0)
{
lean_dec(v___x_430_);
return v_pos_426_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_439_ = lean_string_utf8_next_fast(v_str_427_, v___x_430_);
v___x_440_ = lean_nat_sub(v___x_439_, v___x_430_);
lean_dec(v___x_430_);
v___x_441_ = lean_nat_add(v_pos_426_, v___x_440_);
lean_dec(v___x_440_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_pos_426_, v___x_442_);
v___x_444_ = lean_nat_dec_le(v___x_443_, v___x_441_);
lean_dec(v___x_443_);
if (v___x_444_ == 0)
{
lean_dec(v___x_441_);
return v_pos_426_;
}
else
{
lean_dec(v_pos_426_);
v_pos_426_ = v___x_441_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_430_);
return v_pos_426_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0___boxed(lean_object* v_s_446_, lean_object* v_pos_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v_s_446_, v_pos_447_);
lean_dec_ref(v_s_446_);
return v_res_448_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_451_ = lean_string_utf8_byte_size(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_454_ = lean_string_utf8_byte_size(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_457_ = lean_string_utf8_byte_size(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_460_ = lean_string_utf8_byte_size(v___x_459_);
return v___x_460_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_463_ = lean_string_utf8_byte_size(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_467_ = lean_string_utf8_byte_size(v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14));
v___x_471_ = lean_string_utf8_byte_size(v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16));
v___x_474_ = lean_string_utf8_byte_size(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18));
v___x_477_ = lean_string_utf8_byte_size(v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20));
v___x_480_ = lean_string_utf8_byte_size(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_483_ = lean_string_utf8_byte_size(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(lean_object* v_text_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_afterDigits_489_; uint8_t v___y_491_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_string_utf8_byte_size(v_text_484_);
lean_inc_ref_n(v_text_484_, 2);
v___x_487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_487_, 0, v_text_484_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_486_);
v___x_488_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape_spec__0(v___x_487_, v___x_485_);
lean_inc(v___x_488_);
v_afterDigits_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_afterDigits_489_, 0, v_text_484_);
lean_ctor_set(v_afterDigits_489_, 1, v___x_488_);
lean_ctor_set(v_afterDigits_489_, 2, v___x_486_);
v___x_566_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_567_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23);
v___x_568_ = lean_nat_dec_le(v___x_567_, v___x_486_);
if (v___x_568_ == 0)
{
goto v___jp_561_;
}
else
{
uint8_t v___x_569_; 
v___x_569_ = lean_string_memcmp(v_text_484_, v___x_566_, v___x_485_, v___x_485_, v___x_567_);
if (v___x_569_ == 0)
{
goto v___jp_561_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_569_;
}
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref(v_text_484_);
return v___y_491_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = l_String_Slice_Pos_nextn(v_afterDigits_489_, v___x_485_, v___x_492_);
lean_dec_ref_known(v_afterDigits_489_, 3);
v___x_494_ = lean_nat_add(v___x_488_, v___x_493_);
lean_dec(v___x_493_);
lean_dec(v___x_488_);
v___x_495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_495_, 0, v_text_484_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_ctor_set(v___x_495_, 2, v___x_486_);
v___x_496_ = l_String_Slice_Pos_get_x3f(v___x_495_, v___x_485_);
lean_dec_ref_known(v___x_495_, 3);
if (lean_obj_tag(v___x_496_) == 0)
{
return v___y_491_;
}
else
{
lean_object* v_val_497_; uint32_t v___x_498_; uint32_t v___x_499_; uint8_t v___x_500_; 
v_val_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = 32;
v___x_499_ = lean_unbox_uint32(v_val_497_);
lean_dec(v_val_497_);
v___x_500_ = lean_uint32_dec_eq(v___x_499_, v___x_498_);
return v___x_500_;
}
}
}
v___jp_501_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_502_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_503_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__1);
v___x_504_ = lean_nat_sub(v___x_486_, v___x_488_);
v___x_505_ = lean_nat_dec_le(v___x_503_, v___x_504_);
lean_dec(v___x_504_);
if (v___x_505_ == 0)
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref(v_text_484_);
return v___x_505_;
}
else
{
uint8_t v___x_506_; 
v___x_506_ = lean_string_memcmp(v_text_484_, v___x_502_, v___x_488_, v___x_485_, v___x_503_);
v___y_491_ = v___x_506_;
goto v___jp_490_;
}
}
v___jp_507_:
{
lean_object* v___x_508_; 
v___x_508_ = l_String_Slice_Pos_get_x3f(v___x_487_, v___x_485_);
lean_dec_ref_known(v___x_487_, 3);
if (lean_obj_tag(v___x_508_) == 0)
{
uint8_t v___x_509_; 
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref(v_text_484_);
v___x_509_ = 0;
return v___x_509_;
}
else
{
lean_object* v_val_510_; uint32_t v___x_511_; uint32_t v___x_512_; uint8_t v___x_513_; 
v_val_510_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_508_, 1);
v___x_511_ = 48;
v___x_512_ = lean_unbox_uint32(v_val_510_);
v___x_513_ = lean_uint32_dec_le(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v_val_510_);
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref(v_text_484_);
return v___x_513_;
}
else
{
uint32_t v___x_514_; uint32_t v___x_515_; uint8_t v___x_516_; 
v___x_514_ = 57;
v___x_515_ = lean_unbox_uint32(v_val_510_);
lean_dec(v_val_510_);
v___x_516_ = lean_uint32_dec_le(v___x_515_, v___x_514_);
if (v___x_516_ == 0)
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref(v_text_484_);
return v___x_516_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_517_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__2));
v___x_518_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__3);
v___x_519_ = lean_nat_sub(v___x_486_, v___x_488_);
v___x_520_ = lean_nat_dec_le(v___x_518_, v___x_519_);
lean_dec(v___x_519_);
if (v___x_520_ == 0)
{
goto v___jp_501_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = lean_string_memcmp(v_text_484_, v___x_517_, v___x_488_, v___x_485_, v___x_518_);
if (v___x_521_ == 0)
{
goto v___jp_501_;
}
else
{
v___y_491_ = v___x_521_;
goto v___jp_490_;
}
}
}
}
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_524_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__5);
v___x_525_ = lean_nat_dec_le(v___x_524_, v___x_486_);
if (v___x_525_ == 0)
{
goto v___jp_507_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = lean_string_memcmp(v_text_484_, v___x_523_, v___x_485_, v___x_485_, v___x_524_);
if (v___x_526_ == 0)
{
goto v___jp_507_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_526_;
}
}
}
v___jp_527_:
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_528_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__6));
v___x_529_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__7);
v___x_530_ = lean_nat_dec_le(v___x_529_, v___x_486_);
if (v___x_530_ == 0)
{
goto v___jp_522_;
}
else
{
uint8_t v___x_531_; 
v___x_531_ = lean_string_memcmp(v_text_484_, v___x_528_, v___x_485_, v___x_485_, v___x_529_);
if (v___x_531_ == 0)
{
goto v___jp_522_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_531_;
}
}
}
v___jp_532_:
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_534_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__9);
v___x_535_ = lean_nat_dec_le(v___x_534_, v___x_486_);
if (v___x_535_ == 0)
{
goto v___jp_527_;
}
else
{
uint8_t v___x_536_; 
v___x_536_ = lean_string_memcmp(v_text_484_, v___x_533_, v___x_485_, v___x_485_, v___x_534_);
if (v___x_536_ == 0)
{
goto v___jp_527_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_536_;
}
}
}
v___jp_537_:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___x_539_ = lean_string_dec_eq(v_text_484_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__11));
v___x_541_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__12);
v___x_542_ = lean_nat_dec_le(v___x_541_, v___x_486_);
if (v___x_542_ == 0)
{
goto v___jp_532_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = lean_string_memcmp(v_text_484_, v___x_540_, v___x_485_, v___x_485_, v___x_541_);
if (v___x_543_ == 0)
{
goto v___jp_532_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_543_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_539_;
}
}
v___jp_544_:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13));
v___x_546_ = lean_string_dec_eq(v_text_484_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14));
v___x_548_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__15);
v___x_549_ = lean_nat_dec_le(v___x_548_, v___x_486_);
if (v___x_549_ == 0)
{
goto v___jp_537_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = lean_string_memcmp(v_text_484_, v___x_547_, v___x_485_, v___x_485_, v___x_548_);
if (v___x_550_ == 0)
{
goto v___jp_537_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_550_;
}
}
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_546_;
}
}
v___jp_551_:
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16));
v___x_553_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__17);
v___x_554_ = lean_nat_dec_le(v___x_553_, v___x_486_);
if (v___x_554_ == 0)
{
goto v___jp_544_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = lean_string_memcmp(v_text_484_, v___x_552_, v___x_485_, v___x_485_, v___x_553_);
if (v___x_555_ == 0)
{
goto v___jp_544_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_555_;
}
}
}
v___jp_556_:
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18));
v___x_558_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__19);
v___x_559_ = lean_nat_dec_le(v___x_558_, v___x_486_);
if (v___x_559_ == 0)
{
goto v___jp_551_;
}
else
{
uint8_t v___x_560_; 
v___x_560_ = lean_string_memcmp(v_text_484_, v___x_557_, v___x_485_, v___x_485_, v___x_558_);
if (v___x_560_ == 0)
{
goto v___jp_551_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_560_;
}
}
}
v___jp_561_:
{
lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__20));
v___x_563_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__21);
v___x_564_ = lean_nat_dec_le(v___x_563_, v___x_486_);
if (v___x_564_ == 0)
{
goto v___jp_556_;
}
else
{
uint8_t v___x_565_; 
v___x_565_ = lean_string_memcmp(v_text_484_, v___x_562_, v___x_485_, v___x_485_, v___x_563_);
if (v___x_565_ == 0)
{
goto v___jp_556_;
}
else
{
lean_dec_ref_known(v_afterDigits_489_, 3);
lean_dec(v___x_488_);
lean_dec_ref_known(v___x_487_, 3);
lean_dec_ref(v_text_484_);
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___boxed(lean_object* v_text_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_text_570_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(uint8_t v_atLineStart_574_, lean_object* v_value_575_){
_start:
{
lean_object* v_text_576_; 
v_text_576_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_escaped(v_value_575_);
if (v_atLineStart_574_ == 0)
{
lean_dec_ref(v_value_575_);
return v_text_576_;
}
else
{
uint8_t v___x_577_; 
v___x_577_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape(v_value_575_);
if (v___x_577_ == 0)
{
return v_text_576_;
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_579_ = lean_string_append(v___x_578_, v_text_576_);
lean_dec_ref(v_text_576_);
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___boxed(lean_object* v_atLineStart_580_, lean_object* v_value_581_){
_start:
{
uint8_t v_atLineStart_boxed_582_; lean_object* v_res_583_; 
v_atLineStart_boxed_582_ = lean_unbox(v_atLineStart_580_);
v_res_583_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_boxed_582_, v_value_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(lean_object* v_s_584_, lean_object* v_pos_585_){
_start:
{
lean_object* v_str_586_; lean_object* v_startInclusive_587_; lean_object* v_endExclusive_588_; lean_object* v___x_589_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v_decide_600_; 
v_str_586_ = lean_ctor_get(v_s_584_, 0);
v_startInclusive_587_ = lean_ctor_get(v_s_584_, 1);
v_endExclusive_588_ = lean_ctor_get(v_s_584_, 2);
v___x_589_ = lean_nat_add(v_startInclusive_587_, v_pos_585_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_nat_sub(v_endExclusive_588_, v___x_589_);
v_decide_600_ = lean_nat_dec_eq(v___x_598_, v___x_599_);
lean_dec(v___x_599_);
if (v_decide_600_ == 0)
{
uint32_t v___x_601_; uint32_t v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_string_utf8_get_fast(v_str_586_, v___x_589_);
v___x_602_ = 32;
v___x_603_ = lean_uint32_dec_eq(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
uint32_t v___x_604_; uint8_t v___x_605_; 
v___x_604_ = 9;
v___x_605_ = lean_uint32_dec_eq(v___x_601_, v___x_604_);
if (v___x_605_ == 0)
{
uint32_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 13;
v___x_607_ = lean_uint32_dec_eq(v___x_601_, v___x_606_);
if (v___x_607_ == 0)
{
uint32_t v___x_608_; uint8_t v___x_609_; 
v___x_608_ = 10;
v___x_609_ = lean_uint32_dec_eq(v___x_601_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v___x_589_);
return v_pos_585_;
}
else
{
goto v___jp_590_;
}
}
else
{
goto v___jp_590_;
}
}
else
{
goto v___jp_590_;
}
}
else
{
goto v___jp_590_;
}
}
else
{
lean_dec(v___x_589_);
return v_pos_585_;
}
v___jp_590_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_591_ = lean_string_utf8_next_fast(v_str_586_, v___x_589_);
v___x_592_ = lean_nat_sub(v___x_591_, v___x_589_);
lean_dec(v___x_589_);
v___x_593_ = lean_nat_add(v_pos_585_, v___x_592_);
lean_dec(v___x_592_);
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_pos_585_, v___x_594_);
v___x_596_ = lean_nat_dec_le(v___x_595_, v___x_593_);
lean_dec(v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v___x_593_);
return v_pos_585_;
}
else
{
lean_dec(v_pos_585_);
v_pos_585_ = v___x_593_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0___boxed(lean_object* v_s_610_, lean_object* v_pos_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_610_, v_pos_611_);
lean_dec_ref(v_s_610_);
return v_res_612_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(lean_object* v_s_613_){
_start:
{
lean_object* v_startInclusive_614_; lean_object* v_endExclusive_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v_decide_619_; 
v_startInclusive_614_ = lean_ctor_get(v_s_613_, 1);
v_endExclusive_615_ = lean_ctor_get(v_s_613_, 2);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v_s_613_, v___x_616_);
v___x_618_ = lean_nat_sub(v_endExclusive_615_, v_startInclusive_614_);
v_decide_619_ = lean_nat_dec_eq(v___x_617_, v___x_618_);
lean_dec(v___x_618_);
lean_dec(v___x_617_);
return v_decide_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank___boxed(lean_object* v_s_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v_s_620_);
lean_dec_ref(v_s_620_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(lean_object* v_s_623_, lean_object* v_a_624_, lean_object* v_b_625_){
_start:
{
lean_object* v_str_626_; lean_object* v_startInclusive_627_; lean_object* v_endExclusive_628_; lean_object* v___x_629_; uint8_t v_decide_630_; 
v_str_626_ = lean_ctor_get(v_s_623_, 0);
v_startInclusive_627_ = lean_ctor_get(v_s_623_, 1);
v_endExclusive_628_ = lean_ctor_get(v_s_623_, 2);
v___x_629_ = lean_nat_sub(v_endExclusive_628_, v_startInclusive_627_);
v_decide_630_ = lean_nat_dec_eq(v_a_624_, v___x_629_);
lean_dec(v___x_629_);
if (v_decide_630_ == 0)
{
lean_object* v___x_631_; uint32_t v___x_632_; uint32_t v___x_633_; uint8_t v___x_634_; 
v___x_631_ = lean_nat_add(v_startInclusive_627_, v_a_624_);
lean_dec(v_a_624_);
v___x_632_ = lean_string_utf8_get_fast(v_str_626_, v___x_631_);
v___x_633_ = 32;
v___x_634_ = lean_uint32_dec_eq(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_dec(v___x_631_);
return v_b_625_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_string_utf8_next_fast(v_str_626_, v___x_631_);
lean_dec(v___x_631_);
v___x_636_ = lean_nat_sub(v___x_635_, v_startInclusive_627_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v_b_625_, v___x_637_);
lean_dec(v_b_625_);
v_a_624_ = v___x_636_;
v_b_625_ = v___x_638_;
goto _start;
}
}
else
{
lean_dec(v_a_624_);
return v_b_625_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg___boxed(lean_object* v_s_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_640_, v_a_641_, v_b_642_);
lean_dec_ref(v_s_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(lean_object* v_s_644_){
_start:
{
lean_object* v_n_645_; lean_object* v___x_646_; 
v_n_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_644_, v_n_645_, v_n_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation___boxed(lean_object* v_s_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v_s_647_);
lean_dec_ref(v_s_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(lean_object* v_s_649_, lean_object* v_inst_650_, lean_object* v_R_651_, lean_object* v_a_652_, lean_object* v_b_653_, lean_object* v_c_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___redArg(v_s_649_, v_a_652_, v_b_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0___boxed(lean_object* v_s_656_, lean_object* v_inst_657_, lean_object* v_R_658_, lean_object* v_a_659_, lean_object* v_b_660_, lean_object* v_c_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation_spec__0(v_s_656_, v_inst_657_, v_R_658_, v_a_659_, v_b_660_, v_c_661_);
lean_dec_ref(v_s_656_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v_src_665_, lean_object* v___x_666_, lean_object* v_a_667_, lean_object* v_b_668_){
_start:
{
lean_object* v_it_670_; lean_object* v_out_671_; 
if (lean_obj_tag(v_a_667_) == 0)
{
lean_object* v_currPos_690_; lean_object* v_searcher_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_720_; 
v_currPos_690_ = lean_ctor_get(v_a_667_, 0);
v_searcher_691_ = lean_ctor_get(v_a_667_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_667_);
if (v_isSharedCheck_720_ == 0)
{
v___x_693_ = v_a_667_;
v_isShared_694_ = v_isSharedCheck_720_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_searcher_691_);
lean_inc(v_currPos_690_);
lean_dec(v_a_667_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_720_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_str_695_; lean_object* v_startInclusive_696_; lean_object* v_endExclusive_697_; lean_object* v___x_698_; uint8_t v_decide_699_; 
v_str_695_ = lean_ctor_get(v___x_663_, 0);
v_startInclusive_696_ = lean_ctor_get(v___x_663_, 1);
v_endExclusive_697_ = lean_ctor_get(v___x_663_, 2);
v___x_698_ = lean_nat_sub(v_endExclusive_697_, v_startInclusive_696_);
v_decide_699_ = lean_nat_dec_eq(v_searcher_691_, v___x_698_);
lean_dec(v___x_698_);
if (v_decide_699_ == 0)
{
uint32_t v___x_700_; lean_object* v___x_701_; uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_700_ = 10;
v___x_701_ = lean_nat_add(v_startInclusive_696_, v_searcher_691_);
v___x_702_ = lean_string_utf8_get_fast(v_str_695_, v___x_701_);
v___x_703_ = lean_uint32_dec_eq(v___x_702_, v___x_700_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
lean_dec(v_searcher_691_);
v___x_704_ = lean_string_utf8_next_fast(v_str_695_, v___x_701_);
lean_dec(v___x_701_);
v___x_705_ = lean_nat_sub(v___x_704_, v_startInclusive_696_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_705_);
v___x_707_ = v___x_693_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_currPos_690_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_709_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
v_a_667_ = v___x_707_;
goto _start;
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_slice_713_; lean_object* v_nextIt_715_; 
v___x_710_ = lean_string_utf8_next_fast(v_str_695_, v___x_701_);
v___x_711_ = lean_nat_sub(v___x_710_, v___x_701_);
lean_dec(v___x_701_);
v___x_712_ = lean_nat_add(v_searcher_691_, v___x_711_);
lean_dec(v___x_711_);
lean_dec(v_searcher_691_);
lean_inc_ref(v___x_663_);
v_slice_713_ = l_String_Slice_slice_x21(v___x_663_, v_currPos_690_, v___x_712_);
lean_dec(v_currPos_690_);
lean_inc(v___x_712_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_712_);
lean_ctor_set(v___x_693_, 0, v___x_712_);
v_nextIt_715_ = v___x_693_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v___x_712_);
v_nextIt_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
v_it_670_ = v_nextIt_715_;
v_out_671_ = v_slice_713_;
goto v___jp_669_;
}
}
}
else
{
uint8_t v_decide_717_; 
lean_del_object(v___x_693_);
lean_dec(v_searcher_691_);
v_decide_717_ = lean_nat_dec_eq(v_currPos_690_, v___x_664_);
if (v_decide_717_ == 0)
{
lean_object* v_slice_718_; lean_object* v___x_719_; 
lean_inc(v___x_666_);
lean_inc_ref(v_src_665_);
v_slice_718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_718_, 0, v_src_665_);
lean_ctor_set(v_slice_718_, 1, v_currPos_690_);
lean_ctor_set(v_slice_718_, 2, v___x_666_);
v___x_719_ = lean_box(1);
v_it_670_ = v___x_719_;
v_out_671_ = v_slice_718_;
goto v___jp_669_;
}
else
{
lean_dec(v_currPos_690_);
lean_dec(v___x_666_);
lean_dec_ref(v_src_665_);
lean_dec_ref(v___x_663_);
return v_b_668_;
}
}
}
}
else
{
lean_dec(v___x_666_);
lean_dec_ref(v_src_665_);
lean_dec_ref(v___x_663_);
return v_b_668_;
}
v___jp_669_:
{
lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_672_ = l_String_Slice_lines_lineMap(v_out_671_);
v___x_673_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_672_);
lean_dec_ref(v___x_672_);
if (lean_obj_tag(v_b_668_) == 0)
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
v_a_667_ = v_it_670_;
v_b_668_ = v___x_675_;
goto _start;
}
else
{
lean_object* v_val_677_; uint8_t v___x_678_; 
v_val_677_ = lean_ctor_get(v_b_668_, 0);
v___x_678_ = lean_nat_dec_le(v___x_674_, v_val_677_);
if (v___x_678_ == 0)
{
lean_dec(v___x_674_);
v_a_667_ = v_it_670_;
goto _start;
}
else
{
lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_687_; 
v_isSharedCheck_687_ = !lean_is_exclusive(v_b_668_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_b_668_, 0);
lean_dec(v_unused_688_);
v___x_681_ = v_b_668_;
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
else
{
lean_dec(v_b_668_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_674_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_674_);
v___x_684_ = v_reuseFailAlloc_686_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v_a_667_ = v_it_670_;
v_b_668_ = v___x_684_;
goto _start;
}
}
}
}
}
else
{
lean_dec_ref(v___x_672_);
v_a_667_ = v_it_670_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg___boxed(lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_src_723_, lean_object* v___x_724_, lean_object* v_a_725_, lean_object* v_b_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_721_, v___x_722_, v_src_723_, v___x_724_, v_a_725_, v_b_726_);
lean_dec(v___x_722_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v_src_730_, lean_object* v___x_731_, lean_object* v_a_732_, lean_object* v_b_733_){
_start:
{
lean_object* v_it_735_; lean_object* v_out_736_; 
if (lean_obj_tag(v_a_732_) == 0)
{
lean_object* v_currPos_755_; lean_object* v_searcher_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_785_; 
v_currPos_755_ = lean_ctor_get(v_a_732_, 0);
v_searcher_756_ = lean_ctor_get(v_a_732_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_a_732_);
if (v_isSharedCheck_785_ == 0)
{
v___x_758_ = v_a_732_;
v_isShared_759_ = v_isSharedCheck_785_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_searcher_756_);
lean_inc(v_currPos_755_);
lean_dec(v_a_732_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_785_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_str_760_; lean_object* v_startInclusive_761_; lean_object* v_endExclusive_762_; lean_object* v___x_763_; uint8_t v_decide_764_; 
v_str_760_ = lean_ctor_get(v___x_728_, 0);
v_startInclusive_761_ = lean_ctor_get(v___x_728_, 1);
v_endExclusive_762_ = lean_ctor_get(v___x_728_, 2);
v___x_763_ = lean_nat_sub(v_endExclusive_762_, v_startInclusive_761_);
v_decide_764_ = lean_nat_dec_eq(v_searcher_756_, v___x_763_);
lean_dec(v___x_763_);
if (v_decide_764_ == 0)
{
lean_object* v___x_765_; uint32_t v___x_766_; uint32_t v___x_767_; uint8_t v___x_768_; 
v___x_765_ = lean_nat_add(v_startInclusive_761_, v_searcher_756_);
v___x_766_ = lean_string_utf8_get_fast(v_str_760_, v___x_765_);
v___x_767_ = 10;
v___x_768_ = lean_uint32_dec_eq(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec(v_searcher_756_);
v___x_769_ = lean_string_utf8_next_fast(v_str_760_, v___x_765_);
lean_dec(v___x_765_);
v___x_770_ = lean_nat_sub(v___x_769_, v_startInclusive_761_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_770_);
v___x_772_ = v___x_758_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_currPos_755_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_774_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; 
v___x_773_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_728_, v___x_729_, v_src_730_, v___x_731_, v___x_772_, v_b_733_);
return v___x_773_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_slice_778_; lean_object* v_nextIt_780_; 
v___x_775_ = lean_string_utf8_next_fast(v_str_760_, v___x_765_);
v___x_776_ = lean_nat_sub(v___x_775_, v___x_765_);
lean_dec(v___x_765_);
v___x_777_ = lean_nat_add(v_searcher_756_, v___x_776_);
lean_dec(v___x_776_);
lean_dec(v_searcher_756_);
lean_inc_ref(v___x_728_);
v_slice_778_ = l_String_Slice_slice_x21(v___x_728_, v_currPos_755_, v___x_777_);
lean_dec(v_currPos_755_);
lean_inc(v___x_777_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_777_);
lean_ctor_set(v___x_758_, 0, v___x_777_);
v_nextIt_780_ = v___x_758_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_777_);
v_nextIt_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
v_it_735_ = v_nextIt_780_;
v_out_736_ = v_slice_778_;
goto v___jp_734_;
}
}
}
else
{
uint8_t v_decide_782_; 
lean_del_object(v___x_758_);
lean_dec(v_searcher_756_);
v_decide_782_ = lean_nat_dec_eq(v_currPos_755_, v___x_729_);
if (v_decide_782_ == 0)
{
lean_object* v_slice_783_; lean_object* v___x_784_; 
lean_inc(v___x_731_);
lean_inc_ref(v_src_730_);
v_slice_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_783_, 0, v_src_730_);
lean_ctor_set(v_slice_783_, 1, v_currPos_755_);
lean_ctor_set(v_slice_783_, 2, v___x_731_);
v___x_784_ = lean_box(1);
v_it_735_ = v___x_784_;
v_out_736_ = v_slice_783_;
goto v___jp_734_;
}
else
{
lean_dec(v_currPos_755_);
lean_dec(v___x_731_);
lean_dec_ref(v_src_730_);
lean_dec_ref(v___x_728_);
return v_b_733_;
}
}
}
}
else
{
lean_dec(v___x_731_);
lean_dec_ref(v_src_730_);
lean_dec_ref(v___x_728_);
return v_b_733_;
}
v___jp_734_:
{
lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_737_ = l_String_Slice_lines_lineMap(v_out_736_);
v___x_738_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_indentation(v___x_737_);
lean_dec_ref(v___x_737_);
if (lean_obj_tag(v_b_733_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
v___x_741_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_728_, v___x_729_, v_src_730_, v___x_731_, v_it_735_, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v_val_742_; uint8_t v___x_743_; 
v_val_742_ = lean_ctor_get(v_b_733_, 0);
v___x_743_ = lean_nat_dec_le(v___x_739_, v_val_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v___x_739_);
v___x_744_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_728_, v___x_729_, v_src_730_, v___x_731_, v_it_735_, v_b_733_);
return v___x_744_;
}
else
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_isSharedCheck_752_ = !lean_is_exclusive(v_b_733_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_b_733_, 0);
lean_dec(v_unused_753_);
v___x_746_ = v_b_733_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_dec(v_b_733_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_739_);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_739_);
v___x_749_ = v_reuseFailAlloc_751_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; 
v___x_750_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_728_, v___x_729_, v_src_730_, v___x_731_, v_it_735_, v___x_749_);
return v___x_750_;
}
}
}
}
}
else
{
lean_object* v___x_754_; 
lean_dec_ref(v___x_737_);
v___x_754_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_728_, v___x_729_, v_src_730_, v___x_731_, v_it_735_, v_b_733_);
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg___boxed(lean_object* v___x_786_, lean_object* v___x_787_, lean_object* v_src_788_, lean_object* v___x_789_, lean_object* v_a_790_, lean_object* v_b_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_786_, v___x_787_, v_src_788_, v___x_789_, v_a_790_, v_b_791_);
lean_dec(v___x_787_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(lean_object* v___x_793_, lean_object* v_i_794_, lean_object* v_out_795_, lean_object* v_pending_796_, lean_object* v___y_797_, lean_object* v_____r_798_, lean_object* v_out_799_){
_start:
{
lean_object* v_str_800_; lean_object* v_startInclusive_801_; lean_object* v_endExclusive_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v_str_800_ = lean_ctor_get(v___x_793_, 0);
v_startInclusive_801_ = lean_ctor_get(v___x_793_, 1);
v_endExclusive_802_ = lean_ctor_get(v___x_793_, 2);
v___x_803_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_i_794_, v_out_795_);
v___x_804_ = lean_string_append(v_out_799_, v___x_803_);
lean_dec_ref(v___x_803_);
lean_inc(v_pending_796_);
v___x_805_ = l_String_Slice_Pos_nextn(v___x_793_, v_pending_796_, v___y_797_);
v___x_806_ = lean_nat_add(v_startInclusive_801_, v___x_805_);
lean_dec(v___x_805_);
v___x_807_ = lean_string_utf8_extract_fast(v_str_800_, v___x_806_, v_endExclusive_802_);
lean_dec(v___x_806_);
v___x_808_ = lean_string_append(v___x_804_, v___x_807_);
lean_dec_ref(v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_pending_796_);
v___x_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0___boxed(lean_object* v___x_811_, lean_object* v_i_812_, lean_object* v_out_813_, lean_object* v_pending_814_, lean_object* v___y_815_, lean_object* v_____r_816_, lean_object* v_out_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_811_, v_i_812_, v_out_813_, v_pending_814_, v___y_815_, v_____r_816_, v_out_817_);
lean_dec_ref(v___x_811_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(lean_object* v_i_819_, lean_object* v___y_820_, lean_object* v___x_821_, lean_object* v___x_822_, lean_object* v_src_823_, lean_object* v___x_824_, lean_object* v_a_825_, lean_object* v_b_826_){
_start:
{
lean_object* v___y_828_; lean_object* v_val_829_; 
if (lean_obj_tag(v_a_825_) == 0)
{
lean_object* v_currPos_833_; lean_object* v_searcher_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_897_; 
v_currPos_833_ = lean_ctor_get(v_a_825_, 0);
v_searcher_834_ = lean_ctor_get(v_a_825_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_897_ == 0)
{
v___x_836_ = v_a_825_;
v_isShared_837_ = v_isSharedCheck_897_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_searcher_834_);
lean_inc(v_currPos_833_);
lean_dec(v_a_825_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_897_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_str_838_; lean_object* v_startInclusive_839_; lean_object* v_endExclusive_840_; lean_object* v_out_841_; lean_object* v_pending_842_; lean_object* v_it_844_; lean_object* v_out_845_; lean_object* v___x_875_; uint8_t v_decide_876_; 
v_str_838_ = lean_ctor_get(v___x_821_, 0);
v_startInclusive_839_ = lean_ctor_get(v___x_821_, 1);
v_endExclusive_840_ = lean_ctor_get(v___x_821_, 2);
v_out_841_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v_pending_842_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_nat_sub(v_endExclusive_840_, v_startInclusive_839_);
v_decide_876_ = lean_nat_dec_eq(v_searcher_834_, v___x_875_);
lean_dec(v___x_875_);
if (v_decide_876_ == 0)
{
uint32_t v___x_877_; lean_object* v___x_878_; uint32_t v___x_879_; uint8_t v___x_880_; 
v___x_877_ = 10;
v___x_878_ = lean_nat_add(v_startInclusive_839_, v_searcher_834_);
v___x_879_ = lean_string_utf8_get_fast(v_str_838_, v___x_878_);
v___x_880_ = lean_uint32_dec_eq(v___x_879_, v___x_877_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v_searcher_834_);
v___x_881_ = lean_string_utf8_next_fast(v_str_838_, v___x_878_);
lean_dec(v___x_878_);
v___x_882_ = lean_nat_sub(v___x_881_, v_startInclusive_839_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_882_);
v___x_884_ = v___x_836_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_currPos_833_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_886_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v_a_825_ = v___x_884_;
goto _start;
}
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_slice_890_; lean_object* v_nextIt_892_; 
v___x_887_ = lean_string_utf8_next_fast(v_str_838_, v___x_878_);
v___x_888_ = lean_nat_sub(v___x_887_, v___x_878_);
lean_dec(v___x_878_);
v___x_889_ = lean_nat_add(v_searcher_834_, v___x_888_);
lean_dec(v___x_888_);
lean_dec(v_searcher_834_);
lean_inc_ref(v___x_821_);
v_slice_890_ = l_String_Slice_slice_x21(v___x_821_, v_currPos_833_, v___x_889_);
lean_dec(v_currPos_833_);
lean_inc(v___x_889_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_889_);
lean_ctor_set(v___x_836_, 0, v___x_889_);
v_nextIt_892_ = v___x_836_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_889_);
v_nextIt_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
v_it_844_ = v_nextIt_892_;
v_out_845_ = v_slice_890_;
goto v___jp_843_;
}
}
}
else
{
uint8_t v_decide_894_; 
lean_del_object(v___x_836_);
lean_dec(v_searcher_834_);
v_decide_894_ = lean_nat_dec_eq(v_currPos_833_, v___x_822_);
if (v_decide_894_ == 0)
{
lean_object* v_slice_895_; lean_object* v___x_896_; 
lean_inc(v___x_824_);
lean_inc_ref(v_src_823_);
v_slice_895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_895_, 0, v_src_823_);
lean_ctor_set(v_slice_895_, 1, v_currPos_833_);
lean_ctor_set(v_slice_895_, 2, v___x_824_);
v___x_896_ = lean_box(1);
v_it_844_ = v___x_896_;
v_out_845_ = v_slice_895_;
goto v___jp_843_;
}
else
{
lean_dec(v_currPos_833_);
lean_dec(v___x_824_);
lean_dec_ref(v_src_823_);
lean_dec_ref(v___x_821_);
lean_dec(v___y_820_);
lean_dec(v_i_819_);
return v_b_826_;
}
}
v___jp_843_:
{
lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_874_; 
v_fst_846_ = lean_ctor_get(v_b_826_, 0);
v_snd_847_ = lean_ctor_get(v_b_826_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_b_826_);
if (v_isSharedCheck_874_ == 0)
{
v___x_849_ = v_b_826_;
v_isShared_850_ = v_isSharedCheck_874_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_847_);
lean_inc(v_fst_846_);
lean_dec(v_b_826_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_874_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = l_String_Slice_lines_lineMap(v_out_845_);
v___x_852_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; uint8_t v___x_854_; 
lean_del_object(v___x_849_);
v___x_853_ = lean_string_utf8_byte_size(v_fst_846_);
v___x_854_ = lean_nat_dec_eq(v___x_853_, v_pending_842_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = lean_nat_add(v_snd_847_, v___x_855_);
lean_dec(v_snd_847_);
v___x_857_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_856_, v_fst_846_);
v___x_858_ = lean_box(0);
lean_inc(v___y_820_);
lean_inc(v_i_819_);
v___x_859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_851_, v_i_819_, v_out_841_, v_pending_842_, v___y_820_, v___x_858_, v___x_857_);
lean_dec_ref(v___x_851_);
v___y_828_ = v_it_844_;
v_val_829_ = v___x_859_;
goto v___jp_827_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v_snd_847_);
v___x_860_ = lean_box(0);
lean_inc(v___y_820_);
lean_inc(v_i_819_);
v___x_861_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_851_, v_i_819_, v_out_841_, v_pending_842_, v___y_820_, v___x_860_, v_fst_846_);
lean_dec_ref(v___x_851_);
v___y_828_ = v_it_844_;
v_val_829_ = v___x_861_;
goto v___jp_827_;
}
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
lean_dec_ref(v___x_851_);
v___x_862_ = lean_string_utf8_byte_size(v_fst_846_);
v___x_863_ = lean_nat_dec_eq(v___x_862_, v_pending_842_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_add(v_snd_847_, v___x_864_);
lean_dec(v_snd_847_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_865_);
v___x_867_ = v___x_849_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_865_);
v___x_867_ = v_reuseFailAlloc_869_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
v_a_825_ = v_it_844_;
v_b_826_ = v___x_867_;
goto _start;
}
}
else
{
lean_object* v___x_871_; 
if (v_isShared_850_ == 0)
{
v___x_871_ = v___x_849_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_snd_847_);
v___x_871_ = v_reuseFailAlloc_873_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
v_a_825_ = v_it_844_;
v_b_826_ = v___x_871_;
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
lean_dec(v___x_824_);
lean_dec_ref(v_src_823_);
lean_dec_ref(v___x_821_);
lean_dec(v___y_820_);
lean_dec(v_i_819_);
return v_b_826_;
}
v___jp_827_:
{
if (lean_obj_tag(v_val_829_) == 0)
{
lean_object* v_a_830_; 
lean_dec(v___y_828_);
lean_dec(v___x_824_);
lean_dec_ref(v_src_823_);
lean_dec_ref(v___x_821_);
lean_dec(v___y_820_);
lean_dec(v_i_819_);
v_a_830_ = lean_ctor_get(v_val_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v_val_829_, 1);
return v_a_830_;
}
else
{
lean_object* v_a_831_; 
v_a_831_ = lean_ctor_get(v_val_829_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v_val_829_, 1);
v_a_825_ = v___y_828_;
v_b_826_ = v_a_831_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg___boxed(lean_object* v_i_898_, lean_object* v___y_899_, lean_object* v___x_900_, lean_object* v___x_901_, lean_object* v_src_902_, lean_object* v___x_903_, lean_object* v_a_904_, lean_object* v_b_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_898_, v___y_899_, v___x_900_, v___x_901_, v_src_902_, v___x_903_, v_a_904_, v_b_905_);
lean_dec(v___x_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(lean_object* v_i_907_, lean_object* v___y_908_, lean_object* v___x_909_, lean_object* v___x_910_, lean_object* v_src_911_, lean_object* v___x_912_, lean_object* v_a_913_, lean_object* v_b_914_){
_start:
{
lean_object* v___y_916_; lean_object* v_val_917_; 
if (lean_obj_tag(v_a_913_) == 0)
{
lean_object* v_currPos_921_; lean_object* v_searcher_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_985_; 
v_currPos_921_ = lean_ctor_get(v_a_913_, 0);
v_searcher_922_ = lean_ctor_get(v_a_913_, 1);
v_isSharedCheck_985_ = !lean_is_exclusive(v_a_913_);
if (v_isSharedCheck_985_ == 0)
{
v___x_924_ = v_a_913_;
v_isShared_925_ = v_isSharedCheck_985_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_searcher_922_);
lean_inc(v_currPos_921_);
lean_dec(v_a_913_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_985_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_str_926_; lean_object* v_startInclusive_927_; lean_object* v_endExclusive_928_; lean_object* v_out_929_; lean_object* v_pending_930_; lean_object* v_it_932_; lean_object* v_out_933_; lean_object* v___x_963_; uint8_t v_decide_964_; 
v_str_926_ = lean_ctor_get(v___x_909_, 0);
v_startInclusive_927_ = lean_ctor_get(v___x_909_, 1);
v_endExclusive_928_ = lean_ctor_get(v___x_909_, 2);
v_out_929_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v_pending_930_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_nat_sub(v_endExclusive_928_, v_startInclusive_927_);
v_decide_964_ = lean_nat_dec_eq(v_searcher_922_, v___x_963_);
lean_dec(v___x_963_);
if (v_decide_964_ == 0)
{
lean_object* v___x_965_; uint32_t v___x_966_; uint32_t v___x_967_; uint8_t v___x_968_; 
v___x_965_ = lean_nat_add(v_startInclusive_927_, v_searcher_922_);
v___x_966_ = lean_string_utf8_get_fast(v_str_926_, v___x_965_);
v___x_967_ = 10;
v___x_968_ = lean_uint32_dec_eq(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
lean_dec(v_searcher_922_);
v___x_969_ = lean_string_utf8_next_fast(v_str_926_, v___x_965_);
lean_dec(v___x_965_);
v___x_970_ = lean_nat_sub(v___x_969_, v_startInclusive_927_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_970_);
v___x_972_ = v___x_924_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_currPos_921_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___x_970_);
v___x_972_ = v_reuseFailAlloc_974_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; 
v___x_973_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_907_, v___y_908_, v___x_909_, v___x_910_, v_src_911_, v___x_912_, v___x_972_, v_b_914_);
return v___x_973_;
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_slice_978_; lean_object* v_nextIt_980_; 
v___x_975_ = lean_string_utf8_next_fast(v_str_926_, v___x_965_);
v___x_976_ = lean_nat_sub(v___x_975_, v___x_965_);
lean_dec(v___x_965_);
v___x_977_ = lean_nat_add(v_searcher_922_, v___x_976_);
lean_dec(v___x_976_);
lean_dec(v_searcher_922_);
lean_inc_ref(v___x_909_);
v_slice_978_ = l_String_Slice_slice_x21(v___x_909_, v_currPos_921_, v___x_977_);
lean_dec(v_currPos_921_);
lean_inc(v___x_977_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_977_);
lean_ctor_set(v___x_924_, 0, v___x_977_);
v_nextIt_980_ = v___x_924_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_977_);
v_nextIt_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
v_it_932_ = v_nextIt_980_;
v_out_933_ = v_slice_978_;
goto v___jp_931_;
}
}
}
else
{
uint8_t v_decide_982_; 
lean_del_object(v___x_924_);
lean_dec(v_searcher_922_);
v_decide_982_ = lean_nat_dec_eq(v_currPos_921_, v___x_910_);
if (v_decide_982_ == 0)
{
lean_object* v_slice_983_; lean_object* v___x_984_; 
lean_inc(v___x_912_);
lean_inc_ref(v_src_911_);
v_slice_983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_slice_983_, 0, v_src_911_);
lean_ctor_set(v_slice_983_, 1, v_currPos_921_);
lean_ctor_set(v_slice_983_, 2, v___x_912_);
v___x_984_ = lean_box(1);
v_it_932_ = v___x_984_;
v_out_933_ = v_slice_983_;
goto v___jp_931_;
}
else
{
lean_dec(v_currPos_921_);
lean_dec(v___x_912_);
lean_dec_ref(v_src_911_);
lean_dec_ref(v___x_909_);
lean_dec(v___y_908_);
lean_dec(v_i_907_);
return v_b_914_;
}
}
v___jp_931_:
{
lean_object* v_fst_934_; lean_object* v_snd_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_962_; 
v_fst_934_ = lean_ctor_get(v_b_914_, 0);
v_snd_935_ = lean_ctor_get(v_b_914_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_b_914_);
if (v_isSharedCheck_962_ == 0)
{
v___x_937_ = v_b_914_;
v_isShared_938_ = v_isSharedCheck_962_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snd_935_);
lean_inc(v_fst_934_);
lean_dec(v_b_914_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_962_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = l_String_Slice_lines_lineMap(v_out_933_);
v___x_940_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank(v___x_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; uint8_t v___x_942_; 
lean_del_object(v___x_937_);
v___x_941_ = lean_string_utf8_byte_size(v_fst_934_);
v___x_942_ = lean_nat_dec_eq(v___x_941_, v_pending_930_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_nat_add(v_snd_935_, v___x_943_);
lean_dec(v_snd_935_);
v___x_945_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock_spec__0(v___x_944_, v_fst_934_);
v___x_946_ = lean_box(0);
lean_inc(v___y_908_);
lean_inc(v_i_907_);
v___x_947_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_939_, v_i_907_, v_out_929_, v_pending_930_, v___y_908_, v___x_946_, v___x_945_);
lean_dec_ref(v___x_939_);
v___y_916_ = v_it_932_;
v_val_917_ = v___x_947_;
goto v___jp_915_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_snd_935_);
v___x_948_ = lean_box(0);
lean_inc(v___y_908_);
lean_inc(v_i_907_);
v___x_949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___lam__0(v___x_939_, v_i_907_, v_out_929_, v_pending_930_, v___y_908_, v___x_948_, v_fst_934_);
lean_dec_ref(v___x_939_);
v___y_916_ = v_it_932_;
v_val_917_ = v___x_949_;
goto v___jp_915_;
}
}
else
{
lean_object* v___x_950_; uint8_t v___x_951_; 
lean_dec_ref(v___x_939_);
v___x_950_ = lean_string_utf8_byte_size(v_fst_934_);
v___x_951_ = lean_nat_dec_eq(v___x_950_, v_pending_930_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v_snd_935_, v___x_952_);
lean_dec(v_snd_935_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 1, v___x_953_);
v___x_955_ = v___x_937_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_fst_934_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_907_, v___y_908_, v___x_909_, v___x_910_, v_src_911_, v___x_912_, v_it_932_, v___x_955_);
return v___x_956_;
}
}
else
{
lean_object* v___x_959_; 
if (v_isShared_938_ == 0)
{
v___x_959_ = v___x_937_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_fst_934_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_snd_935_);
v___x_959_ = v_reuseFailAlloc_961_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_960_; 
v___x_960_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_907_, v___y_908_, v___x_909_, v___x_910_, v_src_911_, v___x_912_, v_it_932_, v___x_959_);
return v___x_960_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_912_);
lean_dec_ref(v_src_911_);
lean_dec_ref(v___x_909_);
lean_dec(v___y_908_);
lean_dec(v_i_907_);
return v_b_914_;
}
v___jp_915_:
{
if (lean_obj_tag(v_val_917_) == 0)
{
lean_object* v_a_918_; 
lean_dec(v___y_916_);
lean_dec(v___x_912_);
lean_dec_ref(v_src_911_);
lean_dec_ref(v___x_909_);
lean_dec(v___y_908_);
lean_dec(v_i_907_);
v_a_918_ = lean_ctor_get(v_val_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v_val_917_, 1);
return v_a_918_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_920_; 
v_a_919_ = lean_ctor_get(v_val_917_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v_val_917_, 1);
v___x_920_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_907_, v___y_908_, v___x_909_, v___x_910_, v_src_911_, v___x_912_, v___y_916_, v_a_919_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg___boxed(lean_object* v_i_986_, lean_object* v___y_987_, lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v_src_990_, lean_object* v___x_991_, lean_object* v_a_992_, lean_object* v_b_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_986_, v___y_987_, v___x_988_, v___x_989_, v_src_990_, v___x_991_, v_a_992_, v_b_993_);
lean_dec(v___x_989_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(lean_object* v_i_998_, lean_object* v_src_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___y_1006_; lean_object* v___x_1010_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_string_utf8_byte_size(v_src_999_);
lean_inc_ref_n(v_src_999_, 3);
v___x_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1002_, 0, v_src_999_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
v___x_1003_ = lean_box(0);
v___x_1004_ = l_String_lines(v_src_999_);
lean_inc(v___x_1004_);
lean_inc_ref(v___x_1002_);
v___x_1010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1002_, v___x_1001_, v_src_999_, v___x_1001_, v___x_1004_, v___x_1003_);
if (lean_obj_tag(v___x_1010_) == 0)
{
v___y_1006_ = v___x_1000_;
goto v___jp_1005_;
}
else
{
lean_object* v_val_1011_; 
v_val_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___y_1006_ = v_val_1011_;
goto v___jp_1005_;
}
v___jp_1005_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_fst_1009_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented___closed__0));
v___x_1008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_998_, v___y_1006_, v___x_1002_, v___x_1001_, v_src_999_, v___x_1001_, v___x_1004_, v___x_1007_);
v_fst_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_fst_1009_);
lean_dec_ref(v___x_1008_);
return v_fst_1009_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(lean_object* v_i_1012_, lean_object* v___y_1013_, lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v_src_1016_, lean_object* v___x_1017_, lean_object* v_inst_1018_, lean_object* v_R_1019_, lean_object* v_a_1020_, lean_object* v_b_1021_, lean_object* v_c_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___redArg(v_i_1012_, v___y_1013_, v___x_1014_, v___x_1015_, v_src_1016_, v___x_1017_, v_a_1020_, v_b_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0___boxed(lean_object* v_i_1024_, lean_object* v___y_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v_src_1028_, lean_object* v___x_1029_, lean_object* v_inst_1030_, lean_object* v_R_1031_, lean_object* v_a_1032_, lean_object* v_b_1033_, lean_object* v_c_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0(v_i_1024_, v___y_1025_, v___x_1026_, v___x_1027_, v_src_1028_, v___x_1029_, v_inst_1030_, v_R_1031_, v_a_1032_, v_b_1033_, v_c_1034_);
lean_dec(v___x_1027_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_src_1038_, lean_object* v___x_1039_, lean_object* v_inst_1040_, lean_object* v_R_1041_, lean_object* v_a_1042_, lean_object* v_b_1043_, lean_object* v_c_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___redArg(v___x_1036_, v___x_1037_, v_src_1038_, v___x_1039_, v_a_1042_, v_b_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1___boxed(lean_object* v___x_1046_, lean_object* v___x_1047_, lean_object* v_src_1048_, lean_object* v___x_1049_, lean_object* v_inst_1050_, lean_object* v_R_1051_, lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v_c_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1(v___x_1046_, v___x_1047_, v_src_1048_, v___x_1049_, v_inst_1050_, v_R_1051_, v_a_1052_, v_b_1053_, v_c_1054_);
lean_dec(v___x_1047_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(lean_object* v_i_1056_, lean_object* v___y_1057_, lean_object* v___x_1058_, lean_object* v___x_1059_, lean_object* v_src_1060_, lean_object* v___x_1061_, lean_object* v_inst_1062_, lean_object* v_R_1063_, lean_object* v_a_1064_, lean_object* v_b_1065_, lean_object* v_c_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___redArg(v_i_1056_, v___y_1057_, v___x_1058_, v___x_1059_, v_src_1060_, v___x_1061_, v_a_1064_, v_b_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0___boxed(lean_object* v_i_1068_, lean_object* v___y_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v_src_1072_, lean_object* v___x_1073_, lean_object* v_inst_1074_, lean_object* v_R_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v_c_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__0_spec__0(v_i_1068_, v___y_1069_, v___x_1070_, v___x_1071_, v_src_1072_, v___x_1073_, v_inst_1074_, v_R_1075_, v_a_1076_, v_b_1077_, v_c_1078_);
lean_dec(v___x_1071_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v_src_1082_, lean_object* v___x_1083_, lean_object* v_inst_1084_, lean_object* v_R_1085_, lean_object* v_a_1086_, lean_object* v_b_1087_, lean_object* v_c_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___redArg(v___x_1080_, v___x_1081_, v_src_1082_, v___x_1083_, v_a_1086_, v_b_1087_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2___boxed(lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v_src_1092_, lean_object* v___x_1093_, lean_object* v_inst_1094_, lean_object* v_R_1095_, lean_object* v_a_1096_, lean_object* v_b_1097_, lean_object* v_c_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented_spec__1_spec__2(v___x_1090_, v___x_1091_, v_src_1092_, v___x_1093_, v_inst_1094_, v_R_1095_, v_a_1096_, v_b_1097_, v_c_1098_);
lean_dec(v___x_1091_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v_zero_1102_; uint8_t v_isZero_1103_; 
v_zero_1102_ = lean_unsigned_to_nat(0u);
v_isZero_1103_ = lean_nat_dec_eq(v_x_1100_, v_zero_1102_);
if (v_isZero_1103_ == 1)
{
lean_dec(v_x_1100_);
return v_x_1101_;
}
else
{
uint32_t v___x_1104_; lean_object* v_one_1105_; lean_object* v_n_1106_; lean_object* v___x_1107_; 
v___x_1104_ = 96;
v_one_1105_ = lean_unsigned_to_nat(1u);
v_n_1106_ = lean_nat_sub(v_x_1100_, v_one_1105_);
lean_dec(v_x_1100_);
v___x_1107_ = lean_string_push(v_x_1101_, v___x_1104_);
v_x_1100_ = v_n_1106_;
v_x_1101_ = v___x_1107_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1111_ = lean_string_utf8_byte_size(v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(lean_object* v_value_1112_){
_start:
{
lean_object* v___y_1114_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1136_; 
v___x_1128_ = lean_string_utf8_byte_size(v_value_1112_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_nat_dec_eq(v___x_1128_, v___x_1129_);
if (v___x_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1138_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1);
v___x_1139_ = lean_nat_dec_le(v___x_1138_, v___x_1128_);
if (v___x_1139_ == 0)
{
goto v___jp_1130_;
}
else
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_string_memcmp(v_value_1112_, v___x_1137_, v___x_1129_, v___x_1129_, v___x_1138_);
if (v___x_1140_ == 0)
{
goto v___jp_1130_;
}
else
{
goto v___jp_1122_;
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v_value_1112_);
v___x_1141_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___y_1114_ = v___x_1141_;
goto v___jp_1113_;
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_delim_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1115_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_1116_ = l_Lean_Doc_longestBacktickRun(v___y_1114_);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v___x_1116_, v___x_1117_);
lean_dec(v___x_1116_);
v_delim_1119_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___x_1118_, v___x_1115_);
lean_inc_ref(v_delim_1119_);
v___x_1120_ = lean_string_append(v_delim_1119_, v___y_1114_);
lean_dec_ref(v___y_1114_);
v___x_1121_ = lean_string_append(v___x_1120_, v_delim_1119_);
lean_dec_ref(v_delim_1119_);
return v___x_1121_;
}
v___jp_1122_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_1124_ = lean_string_append(v___x_1123_, v_value_1112_);
lean_dec_ref(v_value_1112_);
v___x_1125_ = lean_string_append(v___x_1124_, v___x_1123_);
v___y_1114_ = v___x_1125_;
goto v___jp_1113_;
}
v___jp_1126_:
{
uint8_t v___x_1127_; 
lean_inc_ref(v_value_1112_);
v___x_1127_ = l_Lean_Doc_versoCodeBoundarySpaces(v_value_1112_);
if (v___x_1127_ == 0)
{
v___y_1114_ = v_value_1112_;
goto v___jp_1113_;
}
else
{
goto v___jp_1122_;
}
}
v___jp_1130_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__0));
v___x_1132_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString___closed__1);
v___x_1133_ = lean_nat_dec_le(v___x_1132_, v___x_1128_);
if (v___x_1133_ == 0)
{
goto v___jp_1126_;
}
else
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = lean_nat_sub(v___x_1128_, v___x_1132_);
v___x_1135_ = lean_string_memcmp(v_value_1112_, v___x_1131_, v___x_1134_, v___x_1129_, v___x_1132_);
lean_dec(v___x_1134_);
if (v___x_1135_ == 0)
{
goto v___jp_1126_;
}
else
{
goto v___jp_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(uint32_t v_char_1142_, lean_object* v_as_1143_, size_t v_i_1144_, size_t v_stop_1145_, lean_object* v_b_1146_){
_start:
{
lean_object* v___y_1148_; uint8_t v___x_1152_; 
v___x_1152_ = lean_usize_dec_eq(v_i_1144_, v_stop_1145_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = lean_array_uget_borrowed(v_as_1143_, v_i_1144_);
lean_inc(v___x_1153_);
v___x_1154_ = l_Lean_Doc_InlineView_of(v___x_1153_);
if (lean_obj_tag(v___x_1154_) == 1)
{
lean_object* v_val_1155_; 
v_val_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_val_1155_);
lean_dec_ref_known(v___x_1154_, 1);
switch(lean_obj_tag(v_val_1155_))
{
case 1:
{
lean_object* v_view_1156_; lean_object* v___y_1158_; uint32_t v___x_1163_; uint8_t v___x_1164_; 
v_view_1156_ = lean_ctor_get(v_val_1155_, 0);
lean_inc_ref(v_view_1156_);
lean_dec_ref_known(v_val_1155_, 1);
v___x_1163_ = 95;
v___x_1164_ = lean_uint32_dec_eq(v_char_1142_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___y_1158_ = v___x_1165_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_unsigned_to_nat(1u);
v___y_1158_ = v___x_1166_;
goto v___jp_1157_;
}
v___jp_1157_:
{
lean_object* v_content_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_content_1159_ = lean_ctor_get(v_view_1156_, 2);
lean_inc_ref(v_content_1159_);
lean_dec_ref(v_view_1156_);
v___x_1160_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1142_, v_content_1159_);
lean_dec_ref(v_content_1159_);
v___x_1161_ = lean_nat_add(v___y_1158_, v___x_1160_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_nat_dec_le(v_b_1146_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_dec(v___x_1161_);
v___y_1148_ = v_b_1146_;
goto v___jp_1147_;
}
else
{
lean_dec(v_b_1146_);
v___y_1148_ = v___x_1161_;
goto v___jp_1147_;
}
}
}
case 2:
{
lean_object* v_view_1167_; lean_object* v___y_1169_; uint32_t v___x_1174_; uint8_t v___x_1175_; 
v_view_1167_ = lean_ctor_get(v_val_1155_, 0);
lean_inc_ref(v_view_1167_);
lean_dec_ref_known(v_val_1155_, 1);
v___x_1174_ = 42;
v___x_1175_ = lean_uint32_dec_eq(v_char_1142_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_unsigned_to_nat(0u);
v___y_1169_ = v___x_1176_;
goto v___jp_1168_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_unsigned_to_nat(1u);
v___y_1169_ = v___x_1177_;
goto v___jp_1168_;
}
v___jp_1168_:
{
lean_object* v_content_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_content_1170_ = lean_ctor_get(v_view_1167_, 2);
lean_inc_ref(v_content_1170_);
lean_dec_ref(v_view_1167_);
v___x_1171_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1142_, v_content_1170_);
lean_dec_ref(v_content_1170_);
v___x_1172_ = lean_nat_add(v___y_1169_, v___x_1171_);
lean_dec(v___x_1171_);
v___x_1173_ = lean_nat_dec_le(v_b_1146_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v___x_1172_);
v___y_1148_ = v_b_1146_;
goto v___jp_1147_;
}
else
{
lean_dec(v_b_1146_);
v___y_1148_ = v___x_1172_;
goto v___jp_1147_;
}
}
}
case 5:
{
lean_object* v_view_1178_; lean_object* v_content_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_view_1178_ = lean_ctor_get(v_val_1155_, 0);
lean_inc_ref(v_view_1178_);
lean_dec_ref_known(v_val_1155_, 1);
v_content_1179_ = lean_ctor_get(v_view_1178_, 2);
lean_inc_ref(v_content_1179_);
lean_dec_ref(v_view_1178_);
v___x_1180_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1142_, v_content_1179_);
lean_dec_ref(v_content_1179_);
v___x_1181_ = lean_nat_dec_le(v_b_1146_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v___x_1180_);
v___y_1148_ = v_b_1146_;
goto v___jp_1147_;
}
else
{
lean_dec(v_b_1146_);
v___y_1148_ = v___x_1180_;
goto v___jp_1147_;
}
}
case 9:
{
lean_object* v_view_1182_; lean_object* v_content_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_view_1182_ = lean_ctor_get(v_val_1155_, 0);
lean_inc_ref(v_view_1182_);
lean_dec_ref_known(v_val_1155_, 1);
v_content_1183_ = lean_ctor_get(v_view_1182_, 6);
lean_inc_ref(v_content_1183_);
lean_dec_ref(v_view_1182_);
v___x_1184_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1142_, v_content_1183_);
lean_dec_ref(v_content_1183_);
v___x_1185_ = lean_nat_dec_le(v_b_1146_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_dec(v___x_1184_);
v___y_1148_ = v_b_1146_;
goto v___jp_1147_;
}
else
{
lean_dec(v_b_1146_);
v___y_1148_ = v___x_1184_;
goto v___jp_1147_;
}
}
default: 
{
lean_dec(v_val_1155_);
v___y_1148_ = v_b_1146_;
goto v___jp_1147_;
}
}
}
else
{
lean_dec(v___x_1154_);
v___y_1148_ = v_b_1146_;
goto v___jp_1147_;
}
}
else
{
return v_b_1146_;
}
v___jp_1147_:
{
size_t v___x_1149_; size_t v___x_1150_; 
v___x_1149_ = ((size_t)1ULL);
v___x_1150_ = lean_usize_add(v_i_1144_, v___x_1149_);
v_i_1144_ = v___x_1150_;
v_b_1146_ = v___y_1148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(uint32_t v_char_1186_, lean_object* v_inls_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = lean_array_get_size(v_inls_1187_);
v___x_1190_ = lean_nat_dec_lt(v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
return v___x_1188_;
}
else
{
uint8_t v___x_1191_; 
v___x_1191_ = lean_nat_dec_le(v___x_1189_, v___x_1189_);
if (v___x_1191_ == 0)
{
if (v___x_1190_ == 0)
{
return v___x_1188_;
}
else
{
size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = lean_usize_of_nat(v___x_1189_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1186_, v_inls_1187_, v___x_1192_, v___x_1193_, v___x_1188_);
return v___x_1194_;
}
}
else
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = lean_usize_of_nat(v___x_1189_);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_1186_, v_inls_1187_, v___x_1195_, v___x_1196_, v___x_1188_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth___boxed(lean_object* v_char_1198_, lean_object* v_inls_1199_){
_start:
{
uint32_t v_char_boxed_1200_; lean_object* v_res_1201_; 
v_char_boxed_1200_ = lean_unbox_uint32(v_char_1198_);
lean_dec(v_char_1198_);
v_res_1201_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_boxed_1200_, v_inls_1199_);
lean_dec_ref(v_inls_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0___boxed(lean_object* v_char_1202_, lean_object* v_as_1203_, lean_object* v_i_1204_, lean_object* v_stop_1205_, lean_object* v_b_1206_){
_start:
{
uint32_t v_char_boxed_1207_; size_t v_i_boxed_1208_; size_t v_stop_boxed_1209_; lean_object* v_res_1210_; 
v_char_boxed_1207_ = lean_unbox_uint32(v_char_1202_);
lean_dec(v_char_1202_);
v_i_boxed_1208_ = lean_unbox_usize(v_i_1204_);
lean_dec(v_i_1204_);
v_stop_boxed_1209_ = lean_unbox_usize(v_stop_1205_);
lean_dec(v_stop_1205_);
v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth_spec__0(v_char_boxed_1207_, v_as_1203_, v_i_boxed_1208_, v_stop_boxed_1209_, v_b_1206_);
lean_dec_ref(v_as_1203_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(uint32_t v_char_1211_, lean_object* v_inls_1212_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun_depth(v_char_1211_, v_inls_1212_);
v___x_1215_ = lean_nat_add(v___x_1213_, v___x_1214_);
lean_dec(v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun___boxed(lean_object* v_char_1216_, lean_object* v_inls_1217_){
_start:
{
uint32_t v_char_boxed_1218_; lean_object* v_res_1219_; 
v_char_boxed_1218_ = lean_unbox_uint32(v_char_1216_);
lean_dec(v_char_1216_);
v_res_1219_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_boxed_1218_, v_inls_1217_);
lean_dec_ref(v_inls_1217_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(lean_object* v_as_1220_, size_t v_i_1221_, size_t v_stop_1222_, lean_object* v_b_1223_){
_start:
{
lean_object* v___y_1225_; uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_eq(v_i_1221_, v_stop_1222_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; lean_object* v_contents_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1230_ = lean_array_uget_borrowed(v_as_1220_, v_i_1221_);
v_contents_1231_ = lean_ctor_get(v___x_1230_, 2);
v___x_1232_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1231_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(lean_object* v_as_1234_, size_t v_i_1235_, size_t v_stop_1236_, lean_object* v_b_1237_){
_start:
{
lean_object* v___y_1239_; uint8_t v___x_1243_; 
v___x_1243_ = lean_usize_dec_eq(v_i_1235_, v_stop_1236_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v_desc_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1244_ = lean_array_uget_borrowed(v_as_1234_, v_i_1235_);
v_desc_1245_ = lean_ctor_get(v___x_1244_, 3);
v___x_1246_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_desc_1245_);
v___x_1247_ = lean_nat_dec_le(v_b_1237_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_dec(v___x_1246_);
v___y_1239_ = v_b_1237_;
goto v___jp_1238_;
}
else
{
lean_dec(v_b_1237_);
v___y_1239_ = v___x_1246_;
goto v___jp_1238_;
}
}
else
{
return v_b_1237_;
}
v___jp_1238_:
{
size_t v___x_1240_; size_t v___x_1241_; 
v___x_1240_ = ((size_t)1ULL);
v___x_1241_ = lean_usize_add(v_i_1235_, v___x_1240_);
v_i_1235_ = v___x_1241_;
v_b_1237_ = v___y_1239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(lean_object* v_as_1248_, size_t v_i_1249_, size_t v_stop_1250_, lean_object* v_b_1251_){
_start:
{
lean_object* v___y_1253_; lean_object* v___y_1258_; uint8_t v___x_1262_; 
v___x_1262_ = lean_usize_dec_eq(v_i_1249_, v_stop_1250_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_array_uget_borrowed(v_as_1248_, v_i_1249_);
lean_inc(v___x_1263_);
v___x_1264_ = l_Lean_Doc_BlockView_of(v___x_1263_);
if (lean_obj_tag(v___x_1264_) == 1)
{
lean_object* v_val_1265_; 
v_val_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v___x_1264_, 1);
switch(lean_obj_tag(v_val_1265_))
{
case 6:
{
lean_object* v_view_1266_; lean_object* v_content_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_view_1266_ = lean_ctor_get(v_val_1265_, 0);
lean_inc_ref(v_view_1266_);
lean_dec_ref_known(v_val_1265_, 1);
v_content_1267_ = lean_ctor_get(v_view_1266_, 4);
lean_inc_ref(v_content_1267_);
lean_dec_ref(v_view_1266_);
v___x_1268_ = lean_unsigned_to_nat(3u);
v___x_1269_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1267_);
lean_dec_ref(v_content_1267_);
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_dec(v___x_1269_);
v___y_1258_ = v___x_1268_;
goto v___jp_1257_;
}
else
{
v___y_1258_ = v___x_1269_;
goto v___jp_1257_;
}
}
case 4:
{
lean_object* v_view_1271_; lean_object* v_content_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v_view_1271_ = lean_ctor_get(v_val_1265_, 0);
lean_inc_ref(v_view_1271_);
lean_dec_ref_known(v_val_1265_, 1);
v_content_1272_ = lean_ctor_get(v_view_1271_, 2);
lean_inc_ref(v_content_1272_);
lean_dec_ref(v_view_1271_);
v___x_1273_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_content_1272_);
lean_dec_ref(v_content_1272_);
v___x_1274_ = lean_nat_dec_le(v_b_1251_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_dec(v___x_1273_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
lean_dec(v_b_1251_);
v___y_1253_ = v___x_1273_;
goto v___jp_1252_;
}
}
case 1:
{
lean_object* v_view_1275_; lean_object* v_items_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v_view_1275_ = lean_ctor_get(v_val_1265_, 0);
lean_inc_ref(v_view_1275_);
lean_dec_ref_known(v_val_1265_, 1);
v_items_1276_ = lean_ctor_get(v_view_1275_, 1);
lean_inc_ref(v_items_1276_);
lean_dec_ref(v_view_1275_);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_array_get_size(v_items_1276_);
v___x_1279_ = lean_nat_dec_lt(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v_items_1276_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_nat_dec_le(v___x_1278_, v___x_1278_);
if (v___x_1280_ == 0)
{
if (v___x_1279_ == 0)
{
lean_dec_ref(v_items_1276_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1278_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1276_, v___x_1281_, v___x_1282_, v_b_1251_);
lean_dec_ref(v_items_1276_);
v___y_1253_ = v___x_1283_;
goto v___jp_1252_;
}
}
else
{
size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = lean_usize_of_nat(v___x_1278_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_items_1276_, v___x_1284_, v___x_1285_, v_b_1251_);
lean_dec_ref(v_items_1276_);
v___y_1253_ = v___x_1286_;
goto v___jp_1252_;
}
}
}
case 2:
{
lean_object* v_view_1287_; lean_object* v_items_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_view_1287_ = lean_ctor_get(v_val_1265_, 0);
lean_inc_ref(v_view_1287_);
lean_dec_ref_known(v_val_1265_, 1);
v_items_1288_ = lean_ctor_get(v_view_1287_, 2);
lean_inc_ref(v_items_1288_);
lean_dec_ref(v_view_1287_);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_array_get_size(v_items_1288_);
v___x_1291_ = lean_nat_dec_lt(v___x_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v_items_1288_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_nat_dec_le(v___x_1290_, v___x_1290_);
if (v___x_1292_ == 0)
{
if (v___x_1291_ == 0)
{
lean_dec_ref(v_items_1288_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((size_t)0ULL);
v___x_1294_ = lean_usize_of_nat(v___x_1290_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1288_, v___x_1293_, v___x_1294_, v_b_1251_);
lean_dec_ref(v_items_1288_);
v___y_1253_ = v___x_1295_;
goto v___jp_1252_;
}
}
else
{
size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1290_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_items_1288_, v___x_1296_, v___x_1297_, v_b_1251_);
lean_dec_ref(v_items_1288_);
v___y_1253_ = v___x_1298_;
goto v___jp_1252_;
}
}
}
case 3:
{
lean_object* v_view_1299_; lean_object* v_items_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_view_1299_ = lean_ctor_get(v_val_1265_, 0);
lean_inc_ref(v_view_1299_);
lean_dec_ref_known(v_val_1265_, 1);
v_items_1300_ = lean_ctor_get(v_view_1299_, 1);
lean_inc_ref(v_items_1300_);
lean_dec_ref(v_view_1299_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_get_size(v_items_1300_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec_ref(v_items_1300_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_nat_dec_le(v___x_1302_, v___x_1302_);
if (v___x_1304_ == 0)
{
if (v___x_1303_ == 0)
{
lean_dec_ref(v_items_1300_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = lean_usize_of_nat(v___x_1302_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1300_, v___x_1305_, v___x_1306_, v_b_1251_);
lean_dec_ref(v_items_1300_);
v___y_1253_ = v___x_1307_;
goto v___jp_1252_;
}
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1302_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_items_1300_, v___x_1308_, v___x_1309_, v_b_1251_);
lean_dec_ref(v_items_1300_);
v___y_1253_ = v___x_1310_;
goto v___jp_1252_;
}
}
}
default: 
{
lean_dec(v_val_1265_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
}
}
else
{
lean_dec(v___x_1264_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
}
else
{
return v_b_1251_;
}
v___jp_1252_:
{
size_t v___x_1254_; size_t v___x_1255_; 
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_add(v_i_1249_, v___x_1254_);
v_i_1249_ = v___x_1255_;
v_b_1251_ = v___y_1253_;
goto _start;
}
v___jp_1257_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_add(v___y_1258_, v___x_1259_);
lean_dec(v___y_1258_);
v___x_1261_ = lean_nat_dec_le(v_b_1251_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_dec(v___x_1260_);
v___y_1253_ = v_b_1251_;
goto v___jp_1252_;
}
else
{
lean_dec(v_b_1251_);
v___y_1253_ = v___x_1260_;
goto v___jp_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(lean_object* v_blks_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = lean_array_get_size(v_blks_1311_);
v___x_1314_ = lean_nat_dec_lt(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
return v___x_1312_;
}
else
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_le(v___x_1313_, v___x_1313_);
if (v___x_1315_ == 0)
{
if (v___x_1314_ == 0)
{
return v___x_1312_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = lean_usize_of_nat(v___x_1313_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1311_, v___x_1316_, v___x_1317_, v___x_1312_);
return v___x_1318_;
}
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1313_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_blks_1311_, v___x_1319_, v___x_1320_, v___x_1312_);
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(lean_object* v_as_1322_, size_t v_i_1323_, size_t v_stop_1324_, lean_object* v_b_1325_){
_start:
{
lean_object* v___y_1327_; uint8_t v___x_1331_; 
v___x_1331_ = lean_usize_dec_eq(v_i_1323_, v_stop_1324_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; lean_object* v_contents_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1332_ = lean_array_uget_borrowed(v_as_1322_, v_i_1323_);
v_contents_1333_ = lean_ctor_get(v___x_1332_, 2);
v___x_1334_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_contents_1333_);
v___x_1335_ = lean_nat_dec_le(v_b_1325_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec(v___x_1334_);
v___y_1327_ = v_b_1325_;
goto v___jp_1326_;
}
else
{
lean_dec(v_b_1325_);
v___y_1327_ = v___x_1334_;
goto v___jp_1326_;
}
}
else
{
return v_b_1325_;
}
v___jp_1326_:
{
size_t v___x_1328_; size_t v___x_1329_; 
v___x_1328_ = ((size_t)1ULL);
v___x_1329_ = lean_usize_add(v_i_1323_, v___x_1328_);
v_i_1323_ = v___x_1329_;
v_b_1325_ = v___y_1327_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0___boxed(lean_object* v_as_1336_, lean_object* v_i_1337_, lean_object* v_stop_1338_, lean_object* v_b_1339_){
_start:
{
size_t v_i_boxed_1340_; size_t v_stop_boxed_1341_; lean_object* v_res_1342_; 
v_i_boxed_1340_ = lean_unbox_usize(v_i_1337_);
lean_dec(v_i_1337_);
v_stop_boxed_1341_ = lean_unbox_usize(v_stop_1338_);
lean_dec(v_stop_1338_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__0(v_as_1336_, v_i_boxed_1340_, v_stop_boxed_1341_, v_b_1339_);
lean_dec_ref(v_as_1336_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1___boxed(lean_object* v_as_1343_, lean_object* v_i_1344_, lean_object* v_stop_1345_, lean_object* v_b_1346_){
_start:
{
size_t v_i_boxed_1347_; size_t v_stop_boxed_1348_; lean_object* v_res_1349_; 
v_i_boxed_1347_ = lean_unbox_usize(v_i_1344_);
lean_dec(v_i_1344_);
v_stop_boxed_1348_ = lean_unbox_usize(v_stop_1345_);
lean_dec(v_stop_1345_);
v_res_1349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__1(v_as_1343_, v_i_boxed_1347_, v_stop_boxed_1348_, v_b_1346_);
lean_dec_ref(v_as_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2___boxed(lean_object* v_as_1350_, lean_object* v_i_1351_, lean_object* v_stop_1352_, lean_object* v_b_1353_){
_start:
{
size_t v_i_boxed_1354_; size_t v_stop_boxed_1355_; lean_object* v_res_1356_; 
v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_stop_boxed_1355_ = lean_unbox_usize(v_stop_1352_);
lean_dec(v_stop_1352_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__2(v_as_1350_, v_i_boxed_1354_, v_stop_boxed_1355_, v_b_1353_);
lean_dec_ref(v_as_1350_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest___boxed(lean_object* v_blks_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1357_);
lean_dec_ref(v_blks_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3___boxed(lean_object* v_as_1359_, lean_object* v_i_1360_, lean_object* v_stop_1361_, lean_object* v_b_1362_){
_start:
{
size_t v_i_boxed_1363_; size_t v_stop_boxed_1364_; lean_object* v_res_1365_; 
v_i_boxed_1363_ = lean_unbox_usize(v_i_1360_);
lean_dec(v_i_1360_);
v_stop_boxed_1364_ = lean_unbox_usize(v_stop_1361_);
lean_dec(v_stop_1361_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest_spec__3(v_as_1359_, v_i_boxed_1363_, v_stop_boxed_1364_, v_b_1362_);
lean_dec_ref(v_as_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(lean_object* v_blks_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1367_ = lean_unsigned_to_nat(3u);
v___x_1368_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun_deepest(v_blks_1366_);
v___x_1369_ = lean_nat_dec_le(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_dec(v___x_1368_);
return v___x_1367_;
}
else
{
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun___boxed(lean_object* v_blks_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_blks_1370_);
lean_dec_ref(v_blks_1370_);
return v_res_1371_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(lean_object* v_inl_1372_){
_start:
{
lean_object* v___x_1373_; 
lean_inc(v_inl_1372_);
v___x_1373_ = l_Lean_Doc_LinebreakView_of(v_inl_1372_);
if (lean_obj_tag(v___x_1373_) == 1)
{
uint8_t v___x_1374_; 
lean_dec_ref_known(v___x_1373_, 1);
lean_dec(v_inl_1372_);
v___x_1374_ = 1;
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; 
lean_dec(v___x_1373_);
v___x_1375_ = l_Lean_Doc_TextView_of(v_inl_1372_);
if (lean_obj_tag(v___x_1375_) == 1)
{
lean_object* v_val_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v_decide_1384_; 
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = 1;
v___x_1378_ = l_Lean_Doc_TextView_getVersoText(v_val_1376_);
lean_dec(v_val_1376_);
v___x_1379_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v___x_1377_, v___x_1378_);
v___x_1380_ = lean_unsigned_to_nat(0u);
v___x_1381_ = lean_string_utf8_byte_size(v___x_1379_);
v___x_1382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1379_);
lean_ctor_set(v___x_1382_, 1, v___x_1380_);
lean_ctor_set(v___x_1382_, 2, v___x_1381_);
v___x_1383_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1382_, v___x_1380_);
lean_dec_ref_known(v___x_1382_, 3);
v_decide_1384_ = lean_nat_dec_eq(v___x_1383_, v___x_1381_);
lean_dec(v___x_1383_);
return v_decide_1384_;
}
else
{
uint8_t v___x_1385_; 
lean_dec(v___x_1375_);
v___x_1385_ = 0;
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank___boxed(lean_object* v_inl_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v_inl_1386_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(lean_object* v_stx_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Doc_BlockView_of(v_stx_1389_);
if (lean_obj_tag(v___x_1390_) == 1)
{
lean_object* v_val_1391_; 
v_val_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v___x_1390_, 1);
switch(lean_obj_tag(v_val_1391_))
{
case 8:
{
uint8_t v___x_1392_; 
lean_dec_ref_known(v_val_1391_, 1);
v___x_1392_ = 1;
return v___x_1392_;
}
case 9:
{
uint8_t v___x_1393_; 
lean_dec_ref_known(v_val_1391_, 1);
v___x_1393_ = 1;
return v___x_1393_;
}
case 10:
{
uint8_t v___x_1394_; 
lean_dec_ref_known(v_val_1391_, 1);
v___x_1394_ = 1;
return v___x_1394_;
}
case 11:
{
uint8_t v___x_1395_; 
lean_dec_ref_known(v_val_1391_, 1);
v___x_1395_ = 1;
return v___x_1395_;
}
default: 
{
uint8_t v___x_1396_; 
lean_dec(v_val_1391_);
v___x_1396_ = 0;
return v___x_1396_;
}
}
}
else
{
uint8_t v___x_1397_; 
lean_dec(v___x_1390_);
v___x_1397_ = 0;
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart___boxed(lean_object* v_stx_1398_){
_start:
{
uint8_t v_res_1399_; lean_object* v_r_1400_; 
v_res_1399_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v_stx_1398_);
v_r_1400_ = lean_box(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(lean_object* v_inl_1401_){
_start:
{
lean_object* v___x_1402_; 
lean_inc(v_inl_1401_);
v___x_1402_ = l_Lean_Doc_LinebreakView_of(v_inl_1401_);
if (lean_obj_tag(v___x_1402_) == 1)
{
uint8_t v___x_1403_; 
lean_dec_ref_known(v___x_1402_, 1);
lean_dec(v_inl_1401_);
v___x_1403_ = 1;
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; 
lean_dec(v___x_1402_);
v___x_1404_ = l_Lean_Doc_TextView_of(v_inl_1401_);
if (lean_obj_tag(v___x_1404_) == 1)
{
lean_object* v_val_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v_decide_1411_; 
v_val_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_val_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v___x_1406_ = l_Lean_Doc_TextView_getVersoTextSource(v_val_1405_);
lean_dec(v_val_1405_);
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_string_utf8_byte_size(v___x_1406_);
v___x_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1406_);
lean_ctor_set(v___x_1409_, 1, v___x_1407_);
lean_ctor_set(v___x_1409_, 2, v___x_1408_);
v___x_1410_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blank_spec__0(v___x_1409_, v___x_1407_);
lean_dec_ref_known(v___x_1409_, 3);
v_decide_1411_ = lean_nat_dec_eq(v___x_1410_, v___x_1408_);
lean_dec(v___x_1410_);
return v_decide_1411_;
}
else
{
uint8_t v___x_1412_; 
lean_dec(v___x_1404_);
v___x_1412_ = 0;
return v___x_1412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline___boxed(lean_object* v_inl_1413_){
_start:
{
uint8_t v_res_1414_; lean_object* v_r_1415_; 
v_res_1414_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v_inl_1413_);
v_r_1415_ = lean_box(v_res_1414_);
return v_r_1415_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(lean_object* v_as_1416_, size_t v_i_1417_, size_t v_stop_1418_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_usize_dec_eq(v_i_1417_, v_stop_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1420_ = lean_array_uget_borrowed(v_as_1416_, v_i_1417_);
lean_inc(v___x_1420_);
v___x_1421_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1420_);
if (v___x_1421_ == 0)
{
uint8_t v___x_1422_; 
v___x_1422_ = 1;
return v___x_1422_;
}
else
{
size_t v___x_1423_; size_t v___x_1424_; 
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_add(v_i_1417_, v___x_1423_);
v_i_1417_ = v___x_1424_;
goto _start;
}
}
else
{
uint8_t v___x_1426_; 
v___x_1426_ = 0;
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0___boxed(lean_object* v_as_1427_, lean_object* v_i_1428_, lean_object* v_stop_1429_){
_start:
{
size_t v_i_boxed_1430_; size_t v_stop_boxed_1431_; uint8_t v_res_1432_; lean_object* v_r_1433_; 
v_i_boxed_1430_ = lean_unbox_usize(v_i_1428_);
lean_dec(v_i_1428_);
v_stop_boxed_1431_ = lean_unbox_usize(v_stop_1429_);
lean_dec(v_stop_1429_);
v_res_1432_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_as_1427_, v_i_boxed_1430_, v_stop_boxed_1431_);
lean_dec_ref(v_as_1427_);
v_r_1433_ = lean_box(v_res_1432_);
return v_r_1433_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(lean_object* v_stx_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Doc_ParaView_of(v_stx_1434_);
if (lean_obj_tag(v___x_1435_) == 1)
{
lean_object* v_val_1436_; lean_object* v_content_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; uint8_t v___x_1440_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v_content_1437_ = lean_ctor_get(v_val_1436_, 1);
lean_inc_ref(v_content_1437_);
lean_dec(v_val_1436_);
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = lean_array_get_size(v_content_1437_);
v___x_1440_ = lean_nat_dec_lt(v___x_1438_, v___x_1439_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; 
lean_dec_ref(v_content_1437_);
v___x_1441_ = 1;
return v___x_1441_;
}
else
{
if (v___x_1440_ == 0)
{
lean_dec_ref(v_content_1437_);
return v___x_1440_;
}
else
{
size_t v___x_1442_; size_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = ((size_t)0ULL);
v___x_1443_ = lean_usize_of_nat(v___x_1439_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph_spec__0(v_content_1437_, v___x_1442_, v___x_1443_);
lean_dec_ref(v_content_1437_);
if (v___x_1444_ == 0)
{
return v___x_1440_;
}
else
{
uint8_t v___x_1445_; 
v___x_1445_ = 0;
return v___x_1445_;
}
}
}
}
else
{
uint8_t v___x_1446_; 
lean_dec(v___x_1435_);
v___x_1446_ = 0;
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph___boxed(lean_object* v_stx_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_stx_1447_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(lean_object* v_stx_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Doc_LinebreakView_of(v_stx_1450_);
if (lean_obj_tag(v___x_1451_) == 1)
{
uint8_t v___x_1452_; 
lean_dec_ref_known(v___x_1451_, 1);
v___x_1452_ = 1;
return v___x_1452_;
}
else
{
uint8_t v___x_1453_; 
lean_dec(v___x_1451_);
v___x_1453_ = 0;
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak___boxed(lean_object* v_stx_1454_){
_start:
{
uint8_t v_res_1455_; lean_object* v_r_1456_; 
v_res_1455_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v_stx_1454_);
v_r_1456_ = lean_box(v_res_1455_);
return v_r_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(lean_object* v_inls_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = lean_array_get_size(v_inls_1457_);
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_dec_eq(v___x_1458_, v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_box(0);
return v___x_1461_;
}
else
{
lean_object* v___x_1462_; lean_object* v_inl_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_unsigned_to_nat(0u);
v_inl_1463_ = lean_array_fget_borrowed(v_inls_1457_, v___x_1462_);
lean_inc(v_inl_1463_);
v___x_1464_ = l_Lean_Doc_InlineView_of(v_inl_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_box(0);
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1477_; 
v_val_1466_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_val_1466_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1477_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
switch(lean_obj_tag(v_val_1466_))
{
case 0:
{
lean_object* v___x_1470_; 
lean_dec_ref_known(v_val_1466_, 1);
lean_del_object(v___x_1468_);
v___x_1470_ = lean_box(0);
return v___x_1470_;
}
case 5:
{
lean_object* v___x_1471_; 
lean_dec_ref_known(v_val_1466_, 1);
lean_del_object(v___x_1468_);
v___x_1471_ = lean_box(0);
return v___x_1471_;
}
case 7:
{
lean_object* v___x_1472_; 
lean_dec_ref_known(v_val_1466_, 1);
lean_del_object(v___x_1468_);
v___x_1472_ = lean_box(0);
return v___x_1472_;
}
case 8:
{
lean_object* v___x_1473_; 
lean_dec_ref_known(v_val_1466_, 1);
lean_del_object(v___x_1468_);
v___x_1473_ = lean_box(0);
return v___x_1473_;
}
default: 
{
lean_object* v___x_1475_; 
lean_dec(v_val_1466_);
lean_inc(v_inl_1463_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v_inl_1463_);
v___x_1475_ = v___x_1468_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_inl_1463_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f___boxed(lean_object* v_inls_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_inls_1478_);
lean_dec_ref(v_inls_1478_);
return v_res_1479_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = 41;
v___x_1481_ = lean_box_uint32(v___x_1480_);
return v___x_1481_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0___boxed__const__1;
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = 93;
v___x_1485_ = lean_box_uint32(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1___boxed__const__1;
v___x_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(lean_object* v_a_1488_){
_start:
{
if (lean_obj_tag(v_a_1488_) == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__0);
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___boxed(lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_a_1491_);
lean_dec_ref(v_a_1491_);
return v_res_1492_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = 95;
v___x_1494_ = lean_box_uint32(v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0___boxed__const__1;
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = 42;
v___x_1498_ = lean_box_uint32(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1___boxed__const__1;
v___x_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = 96;
v___x_1502_ = lean_box_uint32(v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2___boxed__const__1;
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(lean_object* v_inl_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Doc_InlineView_of(v_inl_1505_);
if (lean_obj_tag(v___x_1506_) == 1)
{
lean_object* v_val_1507_; 
v_val_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1507_);
lean_dec_ref_known(v___x_1506_, 1);
switch(lean_obj_tag(v_val_1507_))
{
case 1:
{
lean_object* v___x_1508_; 
lean_dec_ref_known(v_val_1507_, 1);
v___x_1508_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1508_;
}
case 2:
{
lean_object* v___x_1509_; 
lean_dec_ref_known(v_val_1507_, 1);
v___x_1509_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1509_;
}
case 3:
{
lean_object* v___x_1510_; 
lean_dec_ref_known(v_val_1507_, 1);
v___x_1510_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1510_;
}
case 4:
{
lean_object* v___x_1511_; 
lean_dec_ref_known(v_val_1507_, 1);
v___x_1511_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1511_;
}
case 5:
{
lean_object* v_view_1512_; lean_object* v_target_1513_; lean_object* v___x_1514_; 
v_view_1512_ = lean_ctor_get(v_val_1507_, 0);
lean_inc_ref(v_view_1512_);
lean_dec_ref_known(v_val_1507_, 1);
v_target_1513_ = lean_ctor_get(v_view_1512_, 4);
lean_inc_ref(v_target_1513_);
lean_dec_ref(v_view_1512_);
v___x_1514_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1513_);
lean_dec_ref(v_target_1513_);
return v___x_1514_;
}
case 6:
{
lean_object* v_view_1515_; lean_object* v_target_1516_; lean_object* v___x_1517_; 
v_view_1515_ = lean_ctor_get(v_val_1507_, 0);
lean_inc_ref(v_view_1515_);
lean_dec_ref_known(v_val_1507_, 1);
v_target_1516_ = lean_ctor_get(v_view_1515_, 4);
lean_inc_ref(v_target_1516_);
lean_dec_ref(v_view_1515_);
v___x_1517_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser(v_target_1516_);
lean_dec_ref(v_target_1516_);
return v___x_1517_;
}
case 7:
{
lean_object* v___x_1518_; 
lean_dec_ref_known(v_val_1507_, 1);
v___x_1518_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1518_;
}
case 9:
{
lean_object* v_view_1519_; lean_object* v_content_1520_; lean_object* v___x_1521_; 
v_view_1519_ = lean_ctor_get(v_val_1507_, 0);
lean_inc_ref(v_view_1519_);
lean_dec_ref_known(v_val_1507_, 1);
v_content_1520_ = lean_ctor_get(v_view_1519_, 6);
lean_inc_ref(v_content_1520_);
lean_dec_ref(v_view_1519_);
v___x_1521_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_1520_);
lean_dec_ref(v_content_1520_);
if (lean_obj_tag(v___x_1521_) == 1)
{
lean_object* v_val_1522_; 
v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v_inl_1505_ = v_val_1522_;
goto _start;
}
else
{
lean_object* v___x_1524_; 
lean_dec(v___x_1521_);
v___x_1524_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar_targetCloser___closed__1);
return v___x_1524_;
}
}
default: 
{
lean_object* v___x_1525_; 
lean_dec(v_val_1507_);
v___x_1525_ = lean_box(0);
return v___x_1525_;
}
}
}
else
{
lean_object* v___x_1526_; 
lean_dec(v___x_1506_);
v___x_1526_ = lean_box(0);
return v___x_1526_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = 36;
v___x_1528_ = lean_box_uint32(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0___boxed__const__1;
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(lean_object* v_stx_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Doc_InlineView_of(v_stx_1531_);
if (lean_obj_tag(v___x_1532_) == 1)
{
lean_object* v_val_1533_; 
v_val_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v___x_1532_, 1);
switch(lean_obj_tag(v_val_1533_))
{
case 1:
{
lean_object* v___x_1534_; 
lean_dec_ref_known(v_val_1533_, 1);
v___x_1534_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__0);
return v___x_1534_;
}
case 2:
{
lean_object* v___x_1535_; 
lean_dec_ref_known(v_val_1533_, 1);
v___x_1535_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__1);
return v___x_1535_;
}
case 3:
{
lean_object* v___x_1536_; 
lean_dec_ref_known(v_val_1533_, 1);
v___x_1536_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar___closed__2);
return v___x_1536_;
}
case 4:
{
lean_object* v___x_1537_; 
lean_dec_ref_known(v_val_1533_, 1);
v___x_1537_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar___closed__0);
return v___x_1537_;
}
default: 
{
lean_object* v___x_1538_; 
lean_dec(v_val_1533_);
v___x_1538_ = lean_box(0);
return v___x_1538_;
}
}
}
else
{
lean_object* v___x_1539_; 
lean_dec(v___x_1532_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(lean_object* v_inl_1540_, lean_object* v_next_x3f_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1540_);
if (lean_obj_tag(v___x_1542_) == 1)
{
if (lean_obj_tag(v_next_x3f_1541_) == 0)
{
uint8_t v___x_1543_; 
lean_dec_ref_known(v___x_1542_, 1);
v___x_1543_ = 0;
return v___x_1543_;
}
else
{
lean_object* v_val_1544_; lean_object* v_val_1545_; lean_object* v___x_1546_; 
v_val_1544_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_val_1544_);
lean_dec_ref_known(v___x_1542_, 1);
v_val_1545_ = lean_ctor_get(v_next_x3f_1541_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v_next_x3f_1541_, 1);
v___x_1546_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1545_);
if (lean_obj_tag(v___x_1546_) == 1)
{
lean_object* v_val_1547_; uint32_t v___x_1548_; uint32_t v___x_1549_; uint8_t v___x_1550_; 
v_val_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_val_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = lean_unbox_uint32(v_val_1544_);
lean_dec(v_val_1544_);
v___x_1549_ = lean_unbox_uint32(v_val_1547_);
lean_dec(v_val_1547_);
v___x_1550_ = lean_uint32_dec_eq(v___x_1548_, v___x_1549_);
return v___x_1550_;
}
else
{
uint8_t v___x_1551_; 
lean_dec(v___x_1546_);
lean_dec(v_val_1544_);
v___x_1551_ = 0;
return v___x_1551_;
}
}
}
else
{
uint8_t v___x_1552_; 
lean_dec(v___x_1542_);
lean_dec(v_next_x3f_1541_);
v___x_1552_ = 0;
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto___boxed(lean_object* v_inl_1553_, lean_object* v_next_x3f_1554_){
_start:
{
uint8_t v_res_1555_; lean_object* v_r_1556_; 
v_res_1555_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_inl_1553_, v_next_x3f_1554_);
v_r_1556_ = lean_box(v_res_1555_);
return v_r_1556_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(lean_object* v_inl_1557_, lean_object* v_next_x3f_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_closerChar(v_inl_1557_);
if (lean_obj_tag(v___x_1559_) == 1)
{
lean_object* v_val_1560_; uint32_t v___x_1561_; uint32_t v___x_1562_; uint8_t v___x_1563_; 
v_val_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_val_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1561_ = 96;
v___x_1562_ = lean_unbox_uint32(v_val_1560_);
lean_dec(v_val_1560_);
v___x_1563_ = lean_uint32_dec_eq(v___x_1562_, v___x_1561_);
if (v___x_1563_ == 0)
{
lean_dec(v_next_x3f_1558_);
return v___x_1563_;
}
else
{
if (lean_obj_tag(v_next_x3f_1558_) == 0)
{
uint8_t v___x_1564_; 
v___x_1564_ = 0;
return v___x_1564_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1566_; 
v_val_1565_ = lean_ctor_get(v_next_x3f_1558_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v_next_x3f_1558_, 1);
v___x_1566_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v_val_1565_);
if (lean_obj_tag(v___x_1566_) == 1)
{
lean_object* v_val_1567_; uint32_t v___x_1568_; uint8_t v___x_1569_; 
v_val_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = lean_unbox_uint32(v_val_1567_);
lean_dec(v_val_1567_);
v___x_1569_ = lean_uint32_dec_eq(v___x_1568_, v___x_1561_);
return v___x_1569_;
}
else
{
uint8_t v___x_1570_; 
lean_dec(v___x_1566_);
v___x_1570_ = 0;
return v___x_1570_;
}
}
}
}
else
{
uint8_t v___x_1571_; 
lean_dec(v___x_1559_);
lean_dec(v_next_x3f_1558_);
v___x_1571_ = 0;
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto___boxed(lean_object* v_inl_1572_, lean_object* v_next_x3f_1573_){
_start:
{
uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_res_1574_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v_inl_1572_, v_next_x3f_1573_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(lean_object* v_inls_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_array_get_size(v_inls_1576_);
v___x_1579_ = lean_nat_dec_lt(v___x_1577_, v___x_1578_);
if (v___x_1579_ == 0)
{
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_array_fget_borrowed(v_inls_1576_, v___x_1577_);
lean_inc(v___x_1580_);
v___x_1581_ = l_Lean_Doc_TextView_of(v___x_1580_);
if (lean_obj_tag(v___x_1581_) == 1)
{
lean_object* v_val_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_val_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_Doc_TextView_getVersoText(v_val_1582_);
lean_dec(v_val_1582_);
v___x_1584_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_1585_ = lean_string_utf8_byte_size(v___x_1583_);
v___x_1586_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__23);
v___x_1587_ = lean_nat_dec_le(v___x_1586_, v___x_1585_);
if (v___x_1587_ == 0)
{
lean_dec_ref(v___x_1583_);
return v___x_1587_;
}
else
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_string_memcmp(v___x_1583_, v___x_1584_, v___x_1577_, v___x_1577_, v___x_1586_);
lean_dec_ref(v___x_1583_);
return v___x_1588_;
}
}
else
{
uint8_t v___x_1589_; 
lean_dec(v___x_1581_);
v___x_1589_ = 0;
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace___boxed(lean_object* v_inls_1590_){
_start:
{
uint8_t v_res_1591_; lean_object* v_r_1592_; 
v_res_1591_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_inls_1590_);
lean_dec_ref(v_inls_1590_);
v_r_1592_ = lean_box(v_res_1591_);
return v_r_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(lean_object* v_x_1596_, lean_object* v_a_1597_){
_start:
{
if (lean_obj_tag(v_x_1596_) == 0)
{
lean_object* v_url_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_snd_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_snd_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_url_1598_ = lean_ctor_get(v_x_1596_, 2);
v___x_1599_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_1600_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1599_, v_a_1597_);
v_snd_1601_ = lean_ctor_get(v___x_1600_, 1);
lean_inc(v_snd_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = l_Lean_TSyntax_getVersoLinkUrl(v_url_1598_);
v___x_1603_ = l_Lean_Doc_escapeVersoLinkUrl(v___x_1602_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1603_, v_snd_1601_);
lean_dec_ref(v___x_1603_);
v_snd_1605_ = lean_ctor_get(v___x_1604_, 1);
lean_inc(v_snd_1605_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_1607_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1606_, v_snd_1605_);
return v___x_1607_;
}
else
{
lean_object* v_name_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_snd_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v_snd_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_name_1608_ = lean_ctor_get(v_x_1596_, 2);
v___x_1609_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_1610_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1609_, v_a_1597_);
v_snd_1611_ = lean_ctor_get(v___x_1610_, 1);
lean_inc(v_snd_1611_);
lean_dec_ref(v___x_1610_);
v___x_1612_ = l_Lean_TSyntax_getVersoRefName(v_name_1608_);
v___x_1613_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1612_, v_snd_1611_);
lean_dec_ref(v___x_1612_);
v_snd_1614_ = lean_ctor_get(v___x_1613_, 1);
lean_inc(v_snd_1614_);
lean_dec_ref(v___x_1613_);
v___x_1615_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_1616_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1615_, v_snd_1614_);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___boxed(lean_object* v_x_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1617_, v_a_1618_);
lean_dec_ref(v_x_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(lean_object* v_x_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_x_1620_, v_a_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___boxed(lean_object* v_x_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString(v_x_1624_, v_a_1625_, v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_x_1624_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(lean_object* v_s_1628_, lean_object* v_pos_1629_){
_start:
{
lean_object* v_str_1630_; lean_object* v_startInclusive_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v_decide_1635_; 
v_str_1630_ = lean_ctor_get(v_s_1628_, 0);
v_startInclusive_1631_ = lean_ctor_get(v_s_1628_, 1);
v___x_1632_ = lean_nat_add(v_startInclusive_1631_, v_pos_1629_);
v___x_1633_ = lean_nat_sub(v___x_1632_, v_startInclusive_1631_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v_decide_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
if (v_decide_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint32_t v___x_1641_; uint32_t v___x_1642_; uint8_t v___x_1643_; 
lean_inc(v_startInclusive_1631_);
lean_inc_ref(v_str_1630_);
v___x_1636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1636_, 0, v_str_1630_);
lean_ctor_set(v___x_1636_, 1, v_startInclusive_1631_);
lean_ctor_set(v___x_1636_, 2, v___x_1632_);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_sub(v___x_1633_, v___x_1637_);
lean_dec(v___x_1633_);
v___x_1639_ = l_String_Slice_posLE(v___x_1636_, v___x_1638_);
lean_dec_ref_known(v___x_1636_, 3);
v___x_1640_ = lean_nat_add(v_startInclusive_1631_, v___x_1639_);
v___x_1641_ = lean_string_utf8_get_fast(v_str_1630_, v___x_1640_);
lean_dec(v___x_1640_);
v___x_1642_ = 32;
v___x_1643_ = lean_uint32_dec_eq(v___x_1641_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_dec(v___x_1639_);
return v_pos_1629_;
}
else
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = lean_nat_add(v___x_1639_, v___x_1637_);
v___x_1645_ = lean_nat_dec_le(v___x_1644_, v_pos_1629_);
lean_dec(v___x_1644_);
if (v___x_1645_ == 0)
{
lean_dec(v___x_1639_);
return v_pos_1629_;
}
else
{
lean_dec(v_pos_1629_);
v_pos_1629_ = v___x_1639_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1633_);
lean_dec(v___x_1632_);
return v_pos_1629_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0___boxed(lean_object* v_s_1647_, lean_object* v_pos_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v_s_1647_, v_pos_1648_);
lean_dec_ref(v_s_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(lean_object* v_marker_1650_, lean_object* v_contents_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v_alone_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = lean_string_utf8_byte_size(v_marker_1650_);
lean_inc_ref(v_marker_1650_);
v___x_1655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1655_, 0, v_marker_1650_);
lean_ctor_set(v___x_1655_, 1, v___x_1653_);
lean_ctor_set(v___x_1655_, 2, v___x_1654_);
v___x_1656_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart_spec__0(v___x_1655_, v___x_1654_);
lean_dec_ref_known(v___x_1655_, 3);
v_alone_1657_ = lean_string_utf8_extract_fast(v_marker_1650_, v___x_1653_, v___x_1656_);
lean_dec(v___x_1656_);
v___x_1658_ = lean_array_get_size(v_contents_1651_);
v___x_1659_ = lean_nat_dec_lt(v___x_1653_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v_marker_1650_);
v___x_1660_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_alone_1657_, v_a_1652_);
lean_dec_ref(v_alone_1657_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = lean_array_fget_borrowed(v_contents_1651_, v___x_1653_);
lean_inc(v___x_1661_);
v___x_1662_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_needsLineStart(v___x_1661_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref(v_alone_1657_);
v___x_1663_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_marker_1650_, v_a_1652_);
lean_dec_ref(v_marker_1650_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec_ref(v_marker_1650_);
v___x_1664_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_1665_ = lean_string_append(v_alone_1657_, v___x_1664_);
v___x_1666_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1665_, v_a_1652_);
lean_dec_ref(v___x_1665_);
return v___x_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg___boxed(lean_object* v_marker_1667_, lean_object* v_contents_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1667_, v_contents_1668_, v_a_1669_);
lean_dec_ref(v_contents_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(lean_object* v_marker_1671_, lean_object* v_contents_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v_marker_1671_, v_contents_1672_, v_a_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___boxed(lean_object* v_marker_1676_, lean_object* v_contents_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart(v_marker_1676_, v_contents_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_contents_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(lean_object* v_as_1681_, size_t v_i_1682_, size_t v_stop_1683_, lean_object* v_b_1684_){
_start:
{
lean_object* v___y_1686_; uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_eq(v_i_1682_, v_stop_1683_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1691_ = lean_array_uget_borrowed(v_as_1681_, v_i_1682_);
lean_inc(v___x_1691_);
v___x_1692_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
lean_inc(v___x_1691_);
v___x_1693_ = lean_array_push(v_b_1684_, v___x_1691_);
v___y_1686_ = v___x_1693_;
goto v___jp_1685_;
}
else
{
v___y_1686_ = v_b_1684_;
goto v___jp_1685_;
}
}
else
{
return v_b_1684_;
}
v___jp_1685_:
{
size_t v___x_1687_; size_t v___x_1688_; 
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_add(v_i_1682_, v___x_1687_);
v_i_1682_ = v___x_1688_;
v_b_1684_ = v___y_1686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1___boxed(lean_object* v_as_1694_, lean_object* v_i_1695_, lean_object* v_stop_1696_, lean_object* v_b_1697_){
_start:
{
size_t v_i_boxed_1698_; size_t v_stop_boxed_1699_; lean_object* v_res_1700_; 
v_i_boxed_1698_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_stop_boxed_1699_ = lean_unbox_usize(v_stop_1696_);
lean_dec(v_stop_1696_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_as_1694_, v_i_boxed_1698_, v_stop_boxed_1699_, v_b_1697_);
lean_dec_ref(v_as_1694_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(size_t v_sz_1701_, size_t v_i_1702_, lean_object* v_bs_1703_){
_start:
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_usize_dec_lt(v_i_1702_, v_sz_1701_);
if (v___x_1704_ == 0)
{
return v_bs_1703_;
}
else
{
lean_object* v_v_1705_; lean_object* v___x_1706_; lean_object* v_bs_x27_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v_v_1705_ = lean_array_uget(v_bs_1703_, v_i_1702_);
v___x_1706_ = lean_unsigned_to_nat(0u);
v_bs_x27_1707_ = lean_array_uset(v_bs_1703_, v_i_1702_, v___x_1706_);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_i_1702_, v___x_1708_);
v___x_1710_ = lean_array_uset(v_bs_x27_1707_, v_i_1702_, v_v_1705_);
v_i_1702_ = v___x_1709_;
v_bs_1703_ = v___x_1710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3___boxed(lean_object* v_sz_1712_, lean_object* v_i_1713_, lean_object* v_bs_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1712_);
lean_dec(v_sz_1712_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v_zero_1720_; uint8_t v_isZero_1721_; 
v_zero_1720_ = lean_unsigned_to_nat(0u);
v_isZero_1721_ = lean_nat_dec_eq(v_x_1718_, v_zero_1720_);
if (v_isZero_1721_ == 1)
{
lean_dec(v_x_1718_);
return v_x_1719_;
}
else
{
uint32_t v___x_1722_; lean_object* v_one_1723_; lean_object* v_n_1724_; lean_object* v___x_1725_; 
v___x_1722_ = 35;
v_one_1723_ = lean_unsigned_to_nat(1u);
v_n_1724_ = lean_nat_sub(v_x_1718_, v_one_1723_);
lean_dec(v_x_1718_);
v___x_1725_ = lean_string_push(v_x_1719_, v___x_1722_);
v_x_1718_ = v_n_1724_;
v_x_1719_ = v___x_1725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v_zero_1729_; uint8_t v_isZero_1730_; 
v_zero_1729_ = lean_unsigned_to_nat(0u);
v_isZero_1730_ = lean_nat_dec_eq(v_x_1727_, v_zero_1729_);
if (v_isZero_1730_ == 1)
{
lean_dec(v_x_1727_);
return v_x_1728_;
}
else
{
uint32_t v___x_1731_; lean_object* v_one_1732_; lean_object* v_n_1733_; lean_object* v___x_1734_; 
v___x_1731_ = 58;
v_one_1732_ = lean_unsigned_to_nat(1u);
v_n_1733_ = lean_nat_sub(v_x_1727_, v_one_1732_);
lean_dec(v_x_1727_);
v___x_1734_ = lean_string_push(v_x_1728_, v___x_1731_);
v_x_1727_ = v_n_1733_;
v_x_1728_ = v___x_1734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(uint32_t v_char_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
lean_object* v_zero_1739_; uint8_t v_isZero_1740_; 
v_zero_1739_ = lean_unsigned_to_nat(0u);
v_isZero_1740_ = lean_nat_dec_eq(v_x_1737_, v_zero_1739_);
if (v_isZero_1740_ == 1)
{
lean_dec(v_x_1737_);
return v_x_1738_;
}
else
{
lean_object* v_one_1741_; lean_object* v_n_1742_; lean_object* v___x_1743_; 
v_one_1741_ = lean_unsigned_to_nat(1u);
v_n_1742_ = lean_nat_sub(v_x_1737_, v_one_1741_);
lean_dec(v_x_1737_);
v___x_1743_ = lean_string_push(v_x_1738_, v_char_1736_);
v_x_1737_ = v_n_1742_;
v_x_1738_ = v___x_1743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15___boxed(lean_object* v_char_1745_, lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
uint32_t v_char_boxed_1748_; lean_object* v_res_1749_; 
v_char_boxed_1748_ = lean_unbox_uint32(v_char_1745_);
lean_dec(v_char_1745_);
v_res_1749_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_boxed_1748_, v_x_1746_, v_x_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
if (lean_obj_tag(v_x_1751_) == 0)
{
uint8_t v___x_1752_; 
v___x_1752_ = 1;
return v___x_1752_;
}
else
{
uint8_t v___x_1753_; 
v___x_1753_ = 0;
return v___x_1753_;
}
}
else
{
if (lean_obj_tag(v_x_1751_) == 0)
{
uint8_t v___x_1754_; 
v___x_1754_ = 0;
return v___x_1754_;
}
else
{
lean_object* v_val_1755_; lean_object* v_val_1756_; uint32_t v___x_1757_; uint32_t v___x_1758_; uint8_t v___x_1759_; 
v_val_1755_ = lean_ctor_get(v_x_1750_, 0);
v_val_1756_ = lean_ctor_get(v_x_1751_, 0);
v___x_1757_ = lean_unbox_uint32(v_val_1755_);
v___x_1758_ = lean_unbox_uint32(v_val_1756_);
v___x_1759_ = lean_uint32_dec_eq(v___x_1757_, v___x_1758_);
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16___boxed(lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
uint8_t v_res_1762_; lean_object* v_r_1763_; 
v_res_1762_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v_x_1760_, v_x_1761_);
lean_dec(v_x_1761_);
lean_dec(v_x_1760_);
v_r_1763_ = lean_box(v_res_1762_);
return v_r_1763_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg(){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___closed__0));
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg___boxed(lean_object* v___dummy_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v_res_1769_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(uint8_t v___x_1770_, lean_object* v_as_1771_, size_t v_i_1772_, size_t v_stop_1773_){
_start:
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_usize_dec_eq(v_i_1772_, v_stop_1773_);
if (v___x_1774_ == 0)
{
uint8_t v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = 1;
v___x_1776_ = lean_array_uget_borrowed(v_as_1771_, v_i_1772_);
lean_inc(v___x_1776_);
v___x_1777_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankInline(v___x_1776_);
if (v___x_1777_ == 0)
{
return v___x_1775_;
}
else
{
if (v___x_1770_ == 0)
{
size_t v___x_1778_; size_t v___x_1779_; 
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_add(v_i_1772_, v___x_1778_);
v_i_1772_ = v___x_1779_;
goto _start;
}
else
{
return v___x_1775_;
}
}
}
else
{
uint8_t v___x_1781_; 
v___x_1781_ = 0;
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5___boxed(lean_object* v___x_1782_, lean_object* v_as_1783_, lean_object* v_i_1784_, lean_object* v_stop_1785_){
_start:
{
uint8_t v___x_61581__boxed_1786_; size_t v_i_boxed_1787_; size_t v_stop_boxed_1788_; uint8_t v_res_1789_; lean_object* v_r_1790_; 
v___x_61581__boxed_1786_ = lean_unbox(v___x_1782_);
v_i_boxed_1787_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_stop_boxed_1788_ = lean_unbox_usize(v_stop_1785_);
lean_dec(v_stop_1785_);
v_res_1789_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_61581__boxed_1786_, v_as_1783_, v_i_boxed_1787_, v_stop_boxed_1788_);
lean_dec_ref(v_as_1783_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(uint8_t v___x_1791_, uint8_t v___x_1792_, lean_object* v_as_1793_, size_t v_i_1794_, size_t v_stop_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_eq(v_i_1794_, v_stop_1795_);
if (v___x_1796_ == 0)
{
uint8_t v___x_1797_; uint8_t v___y_1799_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1797_ = 1;
v___x_1803_ = lean_array_uget_borrowed(v_as_1793_, v_i_1794_);
lean_inc(v___x_1803_);
v___x_1804_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_printsBlank(v___x_1803_);
if (v___x_1804_ == 0)
{
v___y_1799_ = v___x_1791_;
goto v___jp_1798_;
}
else
{
v___y_1799_ = v___x_1792_;
goto v___jp_1798_;
}
v___jp_1798_:
{
if (v___y_1799_ == 0)
{
size_t v___x_1800_; size_t v___x_1801_; 
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_add(v_i_1794_, v___x_1800_);
v_i_1794_ = v___x_1801_;
goto _start;
}
else
{
return v___x_1797_;
}
}
}
else
{
uint8_t v___x_1805_; 
v___x_1805_ = 0;
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6___boxed(lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_as_1808_, lean_object* v_i_1809_, lean_object* v_stop_1810_){
_start:
{
uint8_t v___x_61600__boxed_1811_; uint8_t v___x_61601__boxed_1812_; size_t v_i_boxed_1813_; size_t v_stop_boxed_1814_; uint8_t v_res_1815_; lean_object* v_r_1816_; 
v___x_61600__boxed_1811_ = lean_unbox(v___x_1806_);
v___x_61601__boxed_1812_ = lean_unbox(v___x_1807_);
v_i_boxed_1813_ = lean_unbox_usize(v_i_1809_);
lean_dec(v_i_1809_);
v_stop_boxed_1814_ = lean_unbox_usize(v_stop_1810_);
lean_dec(v_stop_1810_);
v_res_1815_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_61600__boxed_1811_, v___x_61601__boxed_1812_, v_as_1808_, v_i_boxed_1813_, v_stop_boxed_1814_);
lean_dec_ref(v_as_1808_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___x_1819_, lean_object* v___x_1820_, lean_object* v_a_1821_, lean_object* v_b_1822_){
_start:
{
if (lean_obj_tag(v_a_1821_) == 0)
{
lean_object* v_currPos_1823_; lean_object* v_searcher_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1857_; 
v_currPos_1823_ = lean_ctor_get(v_a_1821_, 0);
v_searcher_1824_ = lean_ctor_get(v_a_1821_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_a_1821_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1826_ = v_a_1821_;
v_isShared_1827_ = v_isSharedCheck_1857_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_searcher_1824_);
lean_inc(v_currPos_1823_);
lean_dec(v_a_1821_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1857_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v_it_1830_; lean_object* v_startInclusive_1831_; lean_object* v_endExclusive_1832_; uint8_t v_decide_1838_; 
v___x_1828_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v_decide_1838_ = lean_nat_dec_eq(v_searcher_1824_, v___x_1820_);
if (v_decide_1838_ == 0)
{
uint32_t v___x_1839_; uint32_t v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = 10;
v___x_1840_ = lean_string_utf8_get_fast(v___y_1818_, v_searcher_1824_);
v___x_1841_ = lean_uint32_dec_eq(v___x_1840_, v___x_1839_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_string_utf8_next_fast(v___y_1818_, v_searcher_1824_);
lean_dec(v_searcher_1824_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1842_);
v___x_1844_ = v___x_1826_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_currPos_1823_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
v_a_1821_ = v___x_1844_;
goto _start;
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_slice_1850_; lean_object* v_nextIt_1852_; 
v___x_1847_ = lean_string_utf8_next_fast(v___y_1818_, v_searcher_1824_);
v___x_1848_ = lean_nat_sub(v___x_1847_, v_searcher_1824_);
v___x_1849_ = lean_nat_add(v_searcher_1824_, v___x_1848_);
lean_dec(v___x_1848_);
v_slice_1850_ = l_String_Slice_subslice_x21(v___x_1819_, v_currPos_1823_, v_searcher_1824_);
lean_inc(v___x_1849_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1849_);
lean_ctor_set(v___x_1826_, 0, v___x_1849_);
v_nextIt_1852_ = v___x_1826_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1849_);
v_nextIt_1852_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v_startInclusive_1853_; lean_object* v_endExclusive_1854_; 
v_startInclusive_1853_ = lean_ctor_get(v_slice_1850_, 0);
lean_inc(v_startInclusive_1853_);
v_endExclusive_1854_ = lean_ctor_get(v_slice_1850_, 1);
lean_inc(v_endExclusive_1854_);
lean_dec_ref(v_slice_1850_);
v_it_1830_ = v_nextIt_1852_;
v_startInclusive_1831_ = v_startInclusive_1853_;
v_endExclusive_1832_ = v_endExclusive_1854_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v___x_1856_; 
lean_del_object(v___x_1826_);
lean_dec(v_searcher_1824_);
v___x_1856_ = lean_box(1);
lean_inc(v___x_1820_);
v_it_1830_ = v___x_1856_;
v_startInclusive_1831_ = v_currPos_1823_;
v_endExclusive_1832_ = v___x_1820_;
goto v___jp_1829_;
}
v___jp_1829_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_inc(v___y_1817_);
v___x_1833_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v___y_1817_, v___x_1828_);
v___x_1834_ = lean_string_utf8_extract_fast(v___y_1818_, v_startInclusive_1831_, v_endExclusive_1832_);
lean_dec(v_endExclusive_1832_);
lean_dec(v_startInclusive_1831_);
v___x_1835_ = lean_string_append(v___x_1833_, v___x_1834_);
lean_dec_ref(v___x_1834_);
v___x_1836_ = lean_array_push(v_b_1822_, v___x_1835_);
v_a_1821_ = v_it_1830_;
v_b_1822_ = v___x_1836_;
goto _start;
}
}
}
else
{
lean_dec(v___x_1820_);
return v_b_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg___boxed(lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___x_1860_, lean_object* v___x_1861_, lean_object* v_a_1862_, lean_object* v_b_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_1858_, v___y_1859_, v___x_1860_, v___x_1861_, v_a_1862_, v_b_1863_);
lean_dec_ref(v___x_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v_____r_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1870_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_isLinebreak(v___x_1865_);
v___x_1871_ = lean_box(v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1866_);
v___x_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v___y_1869_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0___boxed(lean_object* v___x_1875_, lean_object* v___x_1876_, lean_object* v_____r_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1875_, v___x_1876_, v_____r_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1878_);
return v_res_1880_;
}
}
static lean_object* _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0(void){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___redArg();
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(lean_object* v_upperBound_1888_, lean_object* v___y_1889_, lean_object* v_a_1890_, lean_object* v_b_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___y_1895_; uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_lt(v_a_1890_, v_upperBound_1888_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec(v_a_1890_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_b_1891_);
lean_ctor_set(v___x_1913_, 1, v___y_1893_);
return v___x_1913_;
}
else
{
lean_object* v_fst_1914_; lean_object* v_snd_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___y_1919_; lean_object* v___y_1923_; uint8_t v___y_1924_; lean_object* v___y_1939_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v_fst_1914_ = lean_ctor_get(v_b_1891_, 0);
lean_inc(v_fst_1914_);
v_snd_1915_ = lean_ctor_get(v_b_1891_, 1);
lean_inc(v_snd_1915_);
lean_dec_ref(v_b_1891_);
v___x_1916_ = lean_array_fget_borrowed(v___y_1889_, v_a_1890_);
lean_inc(v___x_1916_);
v___x_1917_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v_snd_1915_, v___x_1916_);
lean_dec(v_snd_1915_);
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = lean_nat_add(v_a_1890_, v___x_1943_);
v___x_1945_ = lean_array_get_size(v___y_1889_);
v___x_1946_ = lean_nat_dec_lt(v___x_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v___y_1939_ = v___x_1947_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_array_fget_borrowed(v___y_1889_, v___x_1944_);
lean_dec(v___x_1944_);
lean_inc(v___x_1948_);
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
v___y_1939_ = v___x_1949_;
goto v___jp_1938_;
}
v___jp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_box(0);
lean_inc(v___x_1916_);
v___x_1921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1916_, v___x_1917_, v___x_1920_, v___y_1892_, v___y_1919_);
v___y_1895_ = v___x_1921_;
goto v___jp_1894_;
}
v___jp_1922_:
{
uint8_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_unbox(v_fst_1914_);
lean_dec(v_fst_1914_);
lean_inc(v___y_1923_);
lean_inc(v___x_1916_);
v___x_1926_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v___x_1916_, v___y_1923_, v___x_1925_, v___y_1924_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___y_1923_) == 1)
{
lean_object* v_snd_1927_; lean_object* v___x_1928_; 
v_snd_1927_ = lean_ctor_get(v___x_1926_, 1);
lean_inc(v_snd_1927_);
lean_dec_ref(v___x_1926_);
lean_inc(v___x_1916_);
v___x_1928_ = l_Lean_Doc_RoleView_of(v___x_1916_);
if (lean_obj_tag(v___x_1928_) == 1)
{
lean_dec_ref_known(v___x_1928_, 1);
lean_dec_ref_known(v___y_1923_, 1);
v___y_1919_ = v_snd_1927_;
goto v___jp_1918_;
}
else
{
uint8_t v___x_1929_; 
lean_dec(v___x_1928_);
lean_inc(v___x_1916_);
v___x_1929_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_mergesInto(v___x_1916_, v___y_1923_);
if (v___x_1929_ == 0)
{
v___y_1919_ = v_snd_1927_;
goto v___jp_1918_;
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_fst_1932_; lean_object* v_snd_1933_; lean_object* v___x_1934_; 
v___x_1930_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_1931_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_1930_, v_snd_1927_);
v_fst_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_fst_1932_);
v_snd_1933_ = lean_ctor_get(v___x_1931_, 1);
lean_inc(v_snd_1933_);
lean_dec_ref(v___x_1931_);
lean_inc(v___x_1916_);
v___x_1934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1916_, v___x_1917_, v_fst_1932_, v___y_1892_, v_snd_1933_);
v___y_1895_ = v___x_1934_;
goto v___jp_1894_;
}
}
}
else
{
lean_object* v_snd_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v___y_1923_);
v_snd_1935_ = lean_ctor_get(v___x_1926_, 1);
lean_inc(v_snd_1935_);
lean_dec_ref(v___x_1926_);
v___x_1936_ = lean_box(0);
lean_inc(v___x_1916_);
v___x_1937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___lam__0(v___x_1916_, v___x_1917_, v___x_1936_, v___y_1892_, v_snd_1935_);
v___y_1895_ = v___x_1937_;
goto v___jp_1894_;
}
}
v___jp_1938_:
{
if (lean_obj_tag(v___x_1917_) == 0)
{
uint8_t v___x_1940_; 
v___x_1940_ = 0;
v___y_1923_ = v___y_1939_;
v___y_1924_ = v___x_1940_;
goto v___jp_1922_;
}
else
{
lean_object* v_val_1941_; uint8_t v_alternate_1942_; 
v_val_1941_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_val_1941_);
v_alternate_1942_ = lean_ctor_get_uint8(v_val_1941_, 1);
lean_dec(v_val_1941_);
v___y_1923_ = v___y_1939_;
v___y_1924_ = v_alternate_1942_;
goto v___jp_1922_;
}
}
}
v___jp_1894_:
{
lean_object* v_fst_1896_; 
v_fst_1896_ = lean_ctor_get(v___y_1895_, 0);
lean_inc(v_fst_1896_);
if (lean_obj_tag(v_fst_1896_) == 0)
{
lean_object* v_snd_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1890_);
v_snd_1897_ = lean_ctor_get(v___y_1895_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___y_1895_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v___y_1895_, 0);
lean_dec(v_unused_1906_);
v___x_1899_ = v___y_1895_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_snd_1897_);
lean_dec(v___y_1895_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_a_1901_; lean_object* v___x_1903_; 
v_a_1901_ = lean_ctor_get(v_fst_1896_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v_fst_1896_, 1);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_a_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1901_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_snd_1897_);
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
lean_object* v_snd_1907_; lean_object* v_a_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_snd_1907_ = lean_ctor_get(v___y_1895_, 1);
lean_inc(v_snd_1907_);
lean_dec_ref(v___y_1895_);
v_a_1908_ = lean_ctor_get(v_fst_1896_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v_fst_1896_, 1);
v___x_1909_ = lean_unsigned_to_nat(1u);
v___x_1910_ = lean_nat_add(v_a_1890_, v___x_1909_);
lean_dec(v_a_1890_);
v_a_1890_ = v___x_1910_;
v_b_1891_ = v_a_1908_;
v___y_1893_ = v_snd_1907_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(lean_object* v_stxs_1952_, uint8_t v_lineStart_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___y_1958_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1974_ = lean_array_get_size(v_stxs_1952_);
v___x_1975_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___closed__0));
v___x_1976_ = lean_nat_dec_lt(v___x_1956_, v___x_1974_);
if (v___x_1976_ == 0)
{
v___y_1958_ = v___x_1975_;
goto v___jp_1957_;
}
else
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_nat_dec_le(v___x_1974_, v___x_1974_);
if (v___x_1977_ == 0)
{
if (v___x_1976_ == 0)
{
v___y_1958_ = v___x_1975_;
goto v___jp_1957_;
}
else
{
size_t v___x_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = lean_usize_of_nat(v___x_1974_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1952_, v___x_1978_, v___x_1979_, v___x_1975_);
v___y_1958_ = v___x_1980_;
goto v___jp_1957_;
}
}
else
{
size_t v___x_1981_; size_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = ((size_t)0ULL);
v___x_1982_ = lean_usize_of_nat(v___x_1974_);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__1(v_stxs_1952_, v___x_1981_, v___x_1982_, v___x_1975_);
v___y_1958_ = v___x_1983_;
goto v___jp_1957_;
}
}
v___jp_1957_:
{
lean_object* v___x_1959_; lean_object* v_prev_x3f_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_snd_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v___x_1959_ = lean_array_get_size(v___y_1958_);
v_prev_x3f_1960_ = lean_box(0);
v___x_1961_ = lean_box(v_lineStart_1953_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
lean_ctor_set(v___x_1962_, 1, v_prev_x3f_1960_);
v___x_1963_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v___x_1959_, v___y_1958_, v___x_1956_, v___x_1962_, v_a_1954_, v_a_1955_);
lean_dec_ref(v___y_1958_);
v_snd_1964_ = lean_ctor_get(v___x_1963_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1963_, 0);
lean_dec(v_unused_1973_);
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_snd_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_box(0);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_snd_1964_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(uint32_t v_char_1984_, lean_object* v_inls_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v_delim_1990_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___x_2001_; lean_object* v_snd_2002_; lean_object* v___y_2004_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_1988_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_1989_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_emphRun(v_char_1984_, v_inls_1985_);
v_delim_1990_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__15(v_char_1984_, v___x_1989_, v___x_1988_);
v___x_2001_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1990_, v_a_1987_);
v_snd_2002_ = lean_ctor_get(v___x_2001_, 1);
lean_inc(v_snd_2002_);
lean_dec_ref(v___x_2001_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2012_ = lean_array_get_size(v_inls_1985_);
v___x_2013_ = lean_nat_dec_lt(v___x_2011_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_box(0);
v___y_2004_ = v___x_2014_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_array_fget_borrowed(v_inls_1985_, v___x_2011_);
lean_inc(v___x_2015_);
v___x_2016_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_openerChar(v___x_2015_);
v___y_2004_ = v___x_2016_;
goto v___jp_2003_;
}
v___jp_1991_:
{
size_t v_sz_1994_; size_t v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; lean_object* v___x_1998_; lean_object* v_snd_1999_; lean_object* v___x_2000_; 
v_sz_1994_ = lean_array_size(v_inls_1985_);
v___x_1995_ = ((size_t)0ULL);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_1994_, v___x_1995_, v_inls_1985_);
v___x_1997_ = 0;
v___x_1998_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_1996_, v___x_1997_, v___y_1992_, v___y_1993_);
lean_dec_ref(v___x_1996_);
v_snd_1999_ = lean_ctor_get(v___x_1998_, 1);
lean_inc(v_snd_1999_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v_delim_1990_, v_snd_1999_);
lean_dec_ref(v_delim_1990_);
return v___x_2000_;
}
v___jp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2005_ = lean_box_uint32(v_char_1984_);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
v___x_2007_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike_spec__16(v___y_2004_, v___x_2006_);
lean_dec_ref_known(v___x_2006_, 1);
lean_dec(v___y_2004_);
if (v___x_2007_ == 0)
{
v___y_1992_ = v_a_1986_;
v___y_1993_ = v_snd_2002_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v_snd_2010_; 
v___x_2008_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_zwsp___closed__0));
v___x_2009_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2008_, v_snd_2002_);
v_snd_2010_ = lean_ctor_get(v___x_2009_, 1);
lean_inc(v_snd_2010_);
lean_dec_ref(v___x_2009_);
v___y_1992_ = v_a_1986_;
v___y_1993_ = v_snd_2010_;
goto v___jp_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(lean_object* v___y_2023_, uint8_t v___x_2024_, lean_object* v_as_2025_, size_t v_sz_2026_, size_t v_i_2027_, lean_object* v_b_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
uint8_t v___x_2031_; 
v___x_2031_ = lean_usize_dec_lt(v_i_2027_, v_sz_2026_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; 
lean_dec_ref(v___y_2023_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_b_2028_);
lean_ctor_set(v___x_2032_, 1, v___y_2030_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; lean_object* v_snd_2034_; lean_object* v_a_2035_; lean_object* v_contents_2036_; lean_object* v___x_2037_; lean_object* v_snd_2038_; size_t v_sz_2039_; size_t v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v_snd_2045_; lean_object* v___x_2046_; lean_object* v_snd_2047_; lean_object* v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; 
v___x_2033_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2029_, v___y_2030_);
v_snd_2034_ = lean_ctor_get(v___x_2033_, 1);
lean_inc(v_snd_2034_);
lean_dec_ref(v___x_2033_);
v_a_2035_ = lean_array_uget_borrowed(v_as_2025_, v_i_2027_);
v_contents_2036_ = lean_ctor_get(v_a_2035_, 2);
lean_inc_ref(v___y_2023_);
v___x_2037_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2023_, v_contents_2036_, v_snd_2034_);
v_snd_2038_ = lean_ctor_get(v___x_2037_, 1);
lean_inc(v_snd_2038_);
lean_dec_ref(v___x_2037_);
v_sz_2039_ = lean_array_size(v_contents_2036_);
v___x_2040_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2036_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2039_, v___x_2040_, v_contents_2036_);
v___x_2042_ = lean_string_length(v___y_2023_);
v___x_2043_ = lean_nat_add(v___y_2029_, v___x_2042_);
v___x_2044_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2041_, v___x_2024_, v___x_2043_, v_snd_2038_);
lean_dec(v___x_2043_);
lean_dec_ref(v___x_2041_);
v_snd_2045_ = lean_ctor_get(v___x_2044_, 1);
lean_inc(v_snd_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2045_);
v_snd_2047_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_snd_2047_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = lean_box(0);
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2027_, v___x_2049_);
v_i_2027_ = v___x_2050_;
v_b_2028_ = v___x_2048_;
v___y_2030_ = v_snd_2047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(uint8_t v___x_2055_, uint8_t v_alternate_2056_, lean_object* v_as_2057_, size_t v_sz_2058_, size_t v_i_2059_, lean_object* v_b_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
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
lean_object* v___x_2065_; lean_object* v_snd_2066_; lean_object* v_a_2067_; lean_object* v___y_2069_; 
v___x_2065_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2061_, v___y_2062_);
v_snd_2066_ = lean_ctor_get(v___x_2065_, 1);
lean_inc(v_snd_2066_);
lean_dec_ref(v___x_2065_);
v_a_2067_ = lean_array_uget_borrowed(v_as_2057_, v_i_2059_);
if (v_alternate_2056_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_inc(v_b_2060_);
v___x_2087_ = l_Nat_reprFast(v_b_2060_);
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__0));
v___x_2089_ = lean_string_append(v___x_2087_, v___x_2088_);
v___y_2069_ = v___x_2089_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_inc(v_b_2060_);
v___x_2090_ = l_Nat_reprFast(v_b_2060_);
v___x_2091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___closed__1));
v___x_2092_ = lean_string_append(v___x_2090_, v___x_2091_);
v___y_2069_ = v___x_2092_;
goto v___jp_2068_;
}
v___jp_2068_:
{
lean_object* v_contents_2070_; lean_object* v___x_2071_; lean_object* v_snd_2072_; size_t v_sz_2073_; size_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v_snd_2079_; lean_object* v___x_2080_; lean_object* v_snd_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; size_t v___x_2084_; size_t v___x_2085_; 
v_contents_2070_ = lean_ctor_get(v_a_2067_, 2);
lean_inc_ref(v___y_2069_);
v___x_2071_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_itemStart___redArg(v___y_2069_, v_contents_2070_, v_snd_2066_);
v_snd_2072_ = lean_ctor_get(v___x_2071_, 1);
lean_inc(v_snd_2072_);
lean_dec_ref(v___x_2071_);
v_sz_2073_ = lean_array_size(v_contents_2070_);
v___x_2074_ = ((size_t)0ULL);
lean_inc_ref(v_contents_2070_);
v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2073_, v___x_2074_, v_contents_2070_);
v___x_2076_ = lean_string_length(v___y_2069_);
lean_dec_ref(v___y_2069_);
v___x_2077_ = lean_nat_add(v___y_2061_, v___x_2076_);
v___x_2078_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2075_, v___x_2055_, v___x_2077_, v_snd_2072_);
lean_dec(v___x_2077_);
lean_dec_ref(v___x_2075_);
v_snd_2079_ = lean_ctor_get(v___x_2078_, 1);
lean_inc(v_snd_2079_);
lean_dec_ref(v___x_2078_);
v___x_2080_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2079_);
v_snd_2081_ = lean_ctor_get(v___x_2080_, 1);
lean_inc(v_snd_2081_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = lean_nat_add(v_b_2060_, v___x_2082_);
lean_dec(v_b_2060_);
v___x_2084_ = ((size_t)1ULL);
v___x_2085_ = lean_usize_add(v_i_2059_, v___x_2084_);
v_i_2059_ = v___x_2085_;
v_b_2060_ = v___x_2083_;
v___y_2062_ = v_snd_2081_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(uint8_t v___x_2093_, lean_object* v_as_2094_, size_t v_sz_2095_, size_t v_i_2096_, lean_object* v_b_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_usize_dec_lt(v_i_2096_, v_sz_2095_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v_b_2097_);
lean_ctor_set(v___x_2101_, 1, v___y_2099_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; lean_object* v_snd_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_snd_2106_; lean_object* v_a_2107_; lean_object* v_term_2108_; lean_object* v___x_2109_; lean_object* v___y_2111_; lean_object* v___y_2112_; uint8_t v___x_2133_; 
v___x_2102_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v___y_2098_, v___y_2099_);
v_snd_2103_ = lean_ctor_get(v___x_2102_, 1);
lean_inc(v_snd_2103_);
lean_dec_ref(v___x_2102_);
v___x_2104_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__8));
v___x_2105_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2104_, v_snd_2103_);
v_snd_2106_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_snd_2106_);
lean_dec_ref(v___x_2105_);
v_a_2107_ = lean_array_uget_borrowed(v_as_2094_, v_i_2096_);
v_term_2108_ = lean_ctor_get(v_a_2107_, 2);
v___x_2109_ = lean_box(0);
v___x_2133_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_term_2108_);
if (v___x_2133_ == 0)
{
v___y_2111_ = v___y_2098_;
v___y_2112_ = v_snd_2106_;
goto v___jp_2110_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_snd_2136_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2135_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2134_, v_snd_2106_);
v_snd_2136_ = lean_ctor_get(v___x_2135_, 1);
lean_inc(v_snd_2136_);
lean_dec_ref(v___x_2135_);
v___y_2111_ = v___y_2098_;
v___y_2112_ = v_snd_2136_;
goto v___jp_2110_;
}
v___jp_2110_:
{
lean_object* v_term_2113_; lean_object* v_desc_2114_; size_t v_sz_2115_; size_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_snd_2119_; lean_object* v___x_2120_; lean_object* v_snd_2121_; size_t v_sz_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v_snd_2127_; lean_object* v___x_2128_; lean_object* v_snd_2129_; size_t v___x_2130_; size_t v___x_2131_; 
v_term_2113_ = lean_ctor_get(v_a_2107_, 2);
v_desc_2114_ = lean_ctor_get(v_a_2107_, 3);
v_sz_2115_ = lean_array_size(v_term_2113_);
v___x_2116_ = ((size_t)0ULL);
lean_inc_ref(v_term_2113_);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2115_, v___x_2116_, v_term_2113_);
v___x_2118_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2117_, v___x_2093_, v___y_2111_, v___y_2112_);
lean_dec_ref(v___x_2117_);
v_snd_2119_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_snd_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2119_);
v_snd_2121_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_snd_2121_);
lean_dec_ref(v___x_2120_);
v_sz_2122_ = lean_array_size(v_desc_2114_);
lean_inc_ref(v_desc_2114_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2122_, v___x_2116_, v_desc_2114_);
v___x_2124_ = lean_unsigned_to_nat(2u);
v___x_2125_ = lean_nat_add(v___y_2111_, v___x_2124_);
v___x_2126_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2123_, v___x_2093_, v___x_2125_, v_snd_2121_);
lean_dec(v___x_2125_);
lean_dec_ref(v___x_2123_);
v_snd_2127_ = lean_ctor_get(v___x_2126_, 1);
lean_inc(v_snd_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2127_);
v_snd_2129_ = lean_ctor_get(v___x_2128_, 1);
lean_inc(v_snd_2129_);
lean_dec_ref(v___x_2128_);
v___x_2130_ = ((size_t)1ULL);
v___x_2131_ = lean_usize_add(v_i_2096_, v___x_2130_);
v_i_2096_ = v___x_2131_;
v_b_2097_ = v___x_2109_;
v___y_2099_ = v_snd_2129_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(lean_object* v_stx_2140_, lean_object* v_next_x3f_2141_, uint8_t v_atLineStart_2142_, uint8_t v_alternate_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v___y_2147_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
lean_inc(v_stx_2140_);
v___x_2177_ = l_Lean_Syntax_getKind(v_stx_2140_);
v___x_2178_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__3));
v___x_2179_ = lean_name_eq(v___x_2177_, v___x_2178_);
lean_dec(v___x_2177_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
lean_inc(v_stx_2140_);
v___x_2180_ = l_Lean_Doc_ArgValView_of(v_stx_2140_);
if (lean_obj_tag(v___x_2180_) == 1)
{
lean_object* v_val_2181_; 
lean_dec(v_next_x3f_2141_);
lean_dec(v_stx_2140_);
v_val_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v___x_2180_, 1);
if (lean_obj_tag(v_val_2181_) == 1)
{
lean_object* v_x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_x_2182_ = lean_ctor_get(v_val_2181_, 0);
lean_inc(v_x_2182_);
lean_dec_ref_known(v_val_2181_, 1);
v___x_2183_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_x_2182_);
v___x_2184_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2183_, v_a_2145_);
lean_dec_ref(v___x_2183_);
return v___x_2184_;
}
else
{
lean_object* v_lit_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_lit_2185_ = lean_ctor_get(v_val_2181_, 0);
lean_inc(v_lit_2185_);
lean_dec(v_val_2181_);
v___x_2186_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_atomString(v_lit_2185_);
v___x_2187_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2186_, v_a_2145_);
lean_dec_ref(v___x_2186_);
return v___x_2187_;
}
}
else
{
lean_object* v___x_2188_; 
lean_dec(v___x_2180_);
lean_inc(v_stx_2140_);
v___x_2188_ = l_Lean_Doc_ArgView_of(v_stx_2140_);
if (lean_obj_tag(v___x_2188_) == 1)
{
lean_object* v_val_2189_; 
lean_dec(v_next_x3f_2141_);
lean_dec(v_stx_2140_);
v_val_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v___x_2188_, 1);
switch(lean_obj_tag(v_val_2189_))
{
case 0:
{
lean_object* v_val_2190_; lean_object* v___x_2191_; 
v_val_2190_ = lean_ctor_get(v_val_2189_, 1);
lean_inc(v_val_2190_);
lean_dec_ref_known(v_val_2189_, 2);
v___x_2191_ = lean_box(0);
v_stx_2140_ = v_val_2190_;
v_next_x3f_2141_ = v___x_2191_;
v_atLineStart_2142_ = v___x_2179_;
v_alternate_2143_ = v___x_2179_;
goto _start;
}
case 1:
{
lean_object* v_name_2193_; lean_object* v_val_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_snd_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_snd_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_snd_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_snd_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_name_2193_ = lean_ctor_get(v_val_2189_, 2);
lean_inc(v_name_2193_);
v_val_2194_ = lean_ctor_get(v_val_2189_, 4);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_val_2189_, 5);
v___x_2195_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__0));
v___x_2196_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2195_, v_a_2145_);
v_snd_2197_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_snd_2197_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2193_);
v___x_2199_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2198_, v_snd_2197_);
lean_dec_ref(v___x_2198_);
v_snd_2200_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_snd_2200_);
lean_dec_ref(v___x_2199_);
v___x_2201_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__4));
v___x_2202_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2201_, v_snd_2200_);
v_snd_2203_ = lean_ctor_get(v___x_2202_, 1);
lean_inc(v_snd_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = lean_box(0);
v___x_2205_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_val_2194_, v___x_2204_, v___x_2179_, v___x_2179_, v_a_2144_, v_snd_2203_);
v_snd_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__0));
v___x_2208_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2207_, v_snd_2206_);
return v___x_2208_;
}
default: 
{
lean_object* v_name_2209_; uint8_t v_isOn_2210_; lean_object* v___y_2212_; 
v_name_2209_ = lean_ctor_get(v_val_2189_, 2);
lean_inc(v_name_2209_);
v_isOn_2210_ = lean_ctor_get_uint8(v_val_2189_, sizeof(void*)*3);
lean_dec_ref_known(v_val_2189_, 3);
if (v_isOn_2210_ == 0)
{
lean_object* v___x_2217_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__13));
v___y_2212_ = v___x_2217_;
goto v___jp_2211_;
}
else
{
lean_object* v___x_2218_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__10));
v___y_2212_ = v___x_2218_;
goto v___jp_2211_;
}
v___jp_2211_:
{
lean_object* v___x_2213_; lean_object* v_snd_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2212_, v_a_2145_);
v_snd_2214_ = lean_ctor_get(v___x_2213_, 1);
lean_inc(v_snd_2214_);
lean_dec_ref(v___x_2213_);
v___x_2215_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2209_);
v___x_2216_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2215_, v_snd_2214_);
lean_dec_ref(v___x_2215_);
return v___x_2216_;
}
}
}
}
else
{
lean_object* v___x_2219_; 
lean_dec(v___x_2188_);
lean_inc(v_stx_2140_);
v___x_2219_ = l_Lean_Doc_LinkTargetView_of(v_stx_2140_);
if (lean_obj_tag(v___x_2219_) == 1)
{
lean_object* v_val_2220_; lean_object* v___x_2221_; 
lean_dec(v_next_x3f_2141_);
lean_dec(v_stx_2140_);
v_val_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_val_2220_, v_a_2145_);
lean_dec(v_val_2220_);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; 
lean_dec(v___x_2219_);
lean_inc(v_stx_2140_);
v___x_2222_ = l_Lean_Doc_InlineView_of(v_stx_2140_);
if (lean_obj_tag(v___x_2222_) == 1)
{
lean_object* v_val_2223_; 
lean_dec(v_stx_2140_);
v_val_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v___x_2222_, 1);
switch(lean_obj_tag(v_val_2223_))
{
case 0:
{
lean_object* v_view_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v_next_x3f_2141_);
v_view_2224_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2224_);
lean_dec_ref_known(v_val_2223_, 1);
v___x_2225_ = l_Lean_Doc_TextView_getVersoText(v_view_2224_);
lean_dec_ref(v_view_2224_);
v___x_2226_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString(v_atLineStart_2142_, v___x_2225_);
v___x_2227_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2226_, v_a_2145_);
lean_dec_ref(v___x_2226_);
return v___x_2227_;
}
case 1:
{
lean_object* v_view_2228_; lean_object* v_content_2229_; uint32_t v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_next_x3f_2141_);
v_view_2228_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2228_);
lean_dec_ref_known(v_val_2223_, 1);
v_content_2229_ = lean_ctor_get(v_view_2228_, 2);
lean_inc_ref(v_content_2229_);
lean_dec_ref(v_view_2228_);
v___x_2230_ = 95;
v___x_2231_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2230_, v_content_2229_, v_a_2144_, v_a_2145_);
return v___x_2231_;
}
case 2:
{
lean_object* v_view_2232_; lean_object* v_content_2233_; uint32_t v___x_2234_; lean_object* v___x_2235_; 
lean_dec(v_next_x3f_2141_);
v_view_2232_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2232_);
lean_dec_ref_known(v_val_2223_, 1);
v_content_2233_ = lean_ctor_get(v_view_2232_, 2);
lean_inc_ref(v_content_2233_);
lean_dec_ref(v_view_2232_);
v___x_2234_ = 42;
v___x_2235_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v___x_2234_, v_content_2233_, v_a_2144_, v_a_2145_);
return v___x_2235_;
}
case 3:
{
lean_object* v_view_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v_next_x3f_2141_);
v_view_2236_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2236_);
lean_dec_ref_known(v_val_2223_, 1);
v___x_2237_ = l_Lean_Doc_CodeView_getVersoCode(v_view_2236_);
lean_dec_ref(v_view_2236_);
v___x_2238_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2237_);
v___x_2239_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2238_, v_a_2145_);
lean_dec_ref(v___x_2238_);
return v___x_2239_;
}
case 4:
{
lean_object* v_view_2240_; lean_object* v___y_2242_; uint8_t v_mode_2248_; 
lean_dec(v_next_x3f_2141_);
v_view_2240_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2240_);
lean_dec_ref_known(v_val_2223_, 1);
v_mode_2248_ = lean_ctor_get_uint8(v_view_2240_, sizeof(void*)*3);
if (v_mode_2248_ == 0)
{
lean_object* v___x_2249_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__5));
v___y_2242_ = v___x_2249_;
goto v___jp_2241_;
}
else
{
lean_object* v___x_2250_; 
v___x_2250_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__6));
v___y_2242_ = v___x_2250_;
goto v___jp_2241_;
}
v___jp_2241_:
{
lean_object* v___x_2243_; lean_object* v_snd_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2243_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2242_, v_a_2145_);
v_snd_2244_ = lean_ctor_get(v___x_2243_, 1);
lean_inc(v_snd_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = l_Lean_Doc_MathView_getVersoCode(v_view_2240_);
lean_dec_ref(v_view_2240_);
v___x_2246_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString(v___x_2245_);
v___x_2247_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2246_, v_snd_2244_);
lean_dec_ref(v___x_2246_);
return v___x_2247_;
}
}
case 5:
{
lean_object* v_view_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v_snd_2254_; lean_object* v_content_2255_; lean_object* v_target_2256_; size_t v_sz_2257_; size_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v_snd_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_snd_2264_; lean_object* v___x_2265_; 
lean_dec(v_next_x3f_2141_);
v_view_2251_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2251_);
lean_dec_ref_known(v_val_2223_, 1);
v___x_2252_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2253_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2252_, v_a_2145_);
v_snd_2254_ = lean_ctor_get(v___x_2253_, 1);
lean_inc(v_snd_2254_);
lean_dec_ref(v___x_2253_);
v_content_2255_ = lean_ctor_get(v_view_2251_, 2);
lean_inc_ref(v_content_2255_);
v_target_2256_ = lean_ctor_get(v_view_2251_, 4);
lean_inc_ref(v_target_2256_);
lean_dec_ref(v_view_2251_);
v_sz_2257_ = lean_array_size(v_content_2255_);
v___x_2258_ = ((size_t)0ULL);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2257_, v___x_2258_, v_content_2255_);
v___x_2260_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2259_, v___x_2179_, v_a_2144_, v_snd_2254_);
lean_dec_ref(v___x_2259_);
v_snd_2261_ = lean_ctor_get(v___x_2260_, 1);
lean_inc(v_snd_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2263_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2262_, v_snd_2261_);
v_snd_2264_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_snd_2264_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2256_, v_snd_2264_);
lean_dec_ref(v_target_2256_);
return v___x_2265_;
}
case 6:
{
lean_object* v_view_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_snd_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v_snd_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_snd_2276_; lean_object* v_target_2277_; lean_object* v___x_2278_; 
lean_dec(v_next_x3f_2141_);
v_view_2266_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2266_);
lean_dec_ref_known(v_val_2223_, 1);
v___x_2267_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__7));
v___x_2268_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2267_, v_a_2145_);
v_snd_2269_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_snd_2269_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = l_Lean_Doc_ImageView_getAlt(v_view_2266_);
v___x_2271_ = l_Lean_Doc_escapeVersoImageAlt(v___x_2270_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2271_, v_snd_2269_);
lean_dec_ref(v___x_2271_);
v_snd_2273_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2273_);
lean_dec_ref(v___x_2272_);
v___x_2274_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2275_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2274_, v_snd_2273_);
v_snd_2276_ = lean_ctor_get(v___x_2275_, 1);
lean_inc(v_snd_2276_);
lean_dec_ref(v___x_2275_);
v_target_2277_ = lean_ctor_get(v_view_2266_, 4);
lean_inc_ref(v_target_2277_);
lean_dec_ref(v_view_2266_);
v___x_2278_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg(v_target_2277_, v_snd_2276_);
lean_dec_ref(v_target_2277_);
return v___x_2278_;
}
case 7:
{
lean_object* v_view_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v_snd_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v_snd_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec(v_next_x3f_2141_);
v_view_2279_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2279_);
lean_dec_ref_known(v_val_2223_, 1);
v___x_2280_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2281_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2280_, v_a_2145_);
v_snd_2282_ = lean_ctor_get(v___x_2281_, 1);
lean_inc(v_snd_2282_);
lean_dec_ref(v___x_2281_);
v___x_2283_ = l_Lean_Doc_FootnoteView_getName(v_view_2279_);
lean_dec_ref(v_view_2279_);
v___x_2284_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2283_, v_snd_2282_);
lean_dec_ref(v___x_2283_);
v_snd_2285_ = lean_ctor_get(v___x_2284_, 1);
lean_inc(v_snd_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2287_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2286_, v_snd_2285_);
return v___x_2287_;
}
case 8:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref_known(v_val_2223_, 1);
lean_dec(v_next_x3f_2141_);
v___x_2288_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2289_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2288_, v_a_2145_);
return v___x_2289_;
}
default: 
{
lean_object* v_view_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_snd_2293_; lean_object* v_name_2294_; lean_object* v_args_2295_; lean_object* v_content_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v_snd_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; lean_object* v_snd_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_snd_2307_; lean_object* v___x_2318_; 
v_view_2290_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_view_2290_);
lean_dec_ref_known(v_val_2223_, 1);
v___x_2291_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2292_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2291_, v_a_2145_);
v_snd_2293_ = lean_ctor_get(v___x_2292_, 1);
lean_inc(v_snd_2293_);
lean_dec_ref(v___x_2292_);
v_name_2294_ = lean_ctor_get(v_view_2290_, 2);
lean_inc(v_name_2294_);
v_args_2295_ = lean_ctor_get(v_view_2290_, 3);
lean_inc_ref(v_args_2295_);
v_content_2296_ = lean_ctor_get(v_view_2290_, 6);
lean_inc_ref(v_content_2296_);
lean_dec_ref(v_view_2290_);
v___x_2297_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2294_);
v___x_2298_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2297_, v_snd_2293_);
lean_dec_ref(v___x_2297_);
v_snd_2299_ = lean_ctor_get(v___x_2298_, 1);
lean_inc(v_snd_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = lean_box(0);
v_sz_2301_ = lean_array_size(v_args_2295_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2179_, v_args_2295_, v_sz_2301_, v___x_2302_, v___x_2300_, v_a_2144_, v_snd_2299_);
lean_dec_ref(v_args_2295_);
v_snd_2304_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_snd_2304_);
lean_dec_ref(v___x_2303_);
v___x_2305_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2306_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2305_, v_snd_2304_);
v_snd_2307_ = lean_ctor_get(v___x_2306_, 1);
lean_inc(v_snd_2307_);
lean_dec_ref(v___x_2306_);
v___x_2318_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_selfDelimiting_x3f(v_content_2296_);
if (lean_obj_tag(v___x_2318_) == 1)
{
lean_object* v_val_2319_; uint8_t v___x_2320_; 
v_val_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_val_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_runsInto(v_val_2319_, v_next_x3f_2141_);
if (v___x_2320_ == 0)
{
size_t v_sz_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_sz_2321_ = lean_array_size(v_content_2296_);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2321_, v___x_2302_, v_content_2296_);
v___x_2323_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2322_, v___x_2320_, v_a_2144_, v_snd_2307_);
lean_dec_ref(v___x_2322_);
return v___x_2323_;
}
else
{
goto v___jp_2308_;
}
}
else
{
lean_dec(v___x_2318_);
lean_dec(v_next_x3f_2141_);
goto v___jp_2308_;
}
v___jp_2308_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_snd_2311_; size_t v_sz_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v_snd_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2309_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2310_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2309_, v_snd_2307_);
v_snd_2311_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_snd_2311_);
lean_dec_ref(v___x_2310_);
v_sz_2312_ = lean_array_size(v_content_2296_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2312_, v___x_2302_, v_content_2296_);
v___x_2314_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2313_, v___x_2179_, v_a_2144_, v_snd_2311_);
lean_dec_ref(v___x_2313_);
v_snd_2315_ = lean_ctor_get(v___x_2314_, 1);
lean_inc(v_snd_2315_);
lean_dec_ref(v___x_2314_);
v___x_2316_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__2));
v___x_2317_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2316_, v_snd_2315_);
return v___x_2317_;
}
}
}
}
else
{
lean_object* v___x_2324_; 
lean_dec(v___x_2222_);
lean_dec(v_next_x3f_2141_);
lean_inc(v_stx_2140_);
v___x_2324_ = l_Lean_Doc_BlockView_of(v_stx_2140_);
if (lean_obj_tag(v___x_2324_) == 1)
{
lean_object* v_val_2325_; 
v_val_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_val_2325_);
lean_dec_ref_known(v___x_2324_, 1);
switch(lean_obj_tag(v_val_2325_))
{
case 0:
{
lean_object* v_view_2326_; lean_object* v_content_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
lean_dec(v_stx_2140_);
v_view_2326_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2326_);
lean_dec_ref_known(v_val_2325_, 1);
v_content_2327_ = lean_ctor_get(v_view_2326_, 1);
lean_inc_ref(v_content_2327_);
lean_dec_ref(v_view_2326_);
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = lean_array_get_size(v_content_2327_);
v___x_2330_ = lean_nat_dec_lt(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec_ref(v_content_2327_);
goto v___jp_2174_;
}
else
{
if (v___x_2330_ == 0)
{
lean_dec_ref(v_content_2327_);
goto v___jp_2174_;
}
else
{
size_t v___x_2331_; size_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___y_2335_; lean_object* v___y_2336_; 
v___x_2331_ = ((size_t)0ULL);
v___x_2332_ = lean_usize_of_nat(v___x_2329_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__5(v___x_2179_, v_content_2327_, v___x_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec_ref(v_content_2327_);
goto v___jp_2174_;
}
else
{
if (v___x_2179_ == 0)
{
lean_object* v___x_2342_; lean_object* v_snd_2343_; 
v___x_2342_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2343_ = lean_ctor_get(v___x_2342_, 1);
lean_inc(v_snd_2343_);
lean_dec_ref(v___x_2342_);
if (v___x_2330_ == 0)
{
goto v___jp_2344_;
}
else
{
if (v___x_2330_ == 0)
{
goto v___jp_2344_;
}
else
{
uint8_t v___x_2348_; 
v___x_2348_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__6(v___x_2333_, v___x_2179_, v_content_2327_, v___x_2331_, v___x_2332_);
if (v___x_2348_ == 0)
{
goto v___jp_2344_;
}
else
{
v___y_2335_ = v_a_2144_;
v___y_2336_ = v_snd_2343_;
goto v___jp_2334_;
}
}
}
v___jp_2344_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_snd_2347_; 
v___x_2345_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2346_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2345_, v_snd_2343_);
v_snd_2347_ = lean_ctor_get(v___x_2346_, 1);
lean_inc(v_snd_2347_);
lean_dec_ref(v___x_2346_);
v___y_2335_ = v_a_2144_;
v___y_2336_ = v_snd_2347_;
goto v___jp_2334_;
}
}
else
{
lean_dec_ref(v_content_2327_);
goto v___jp_2174_;
}
}
v___jp_2334_:
{
size_t v_sz_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v_snd_2340_; lean_object* v___x_2341_; 
v_sz_2337_ = lean_array_size(v_content_2327_);
v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2337_, v___x_2331_, v_content_2327_);
v___x_2339_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2338_, v___x_2333_, v___y_2335_, v___y_2336_);
lean_dec_ref(v___x_2338_);
v_snd_2340_ = lean_ctor_get(v___x_2339_, 1);
lean_inc(v_snd_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2340_);
return v___x_2341_;
}
}
}
}
case 1:
{
lean_object* v_view_2349_; lean_object* v___y_2351_; 
lean_dec(v_stx_2140_);
v_view_2349_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2349_);
lean_dec_ref_known(v_val_2325_, 1);
if (v_alternate_2143_ == 0)
{
lean_object* v___x_2359_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__11));
v___y_2351_ = v___x_2359_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2360_; 
v___x_2360_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__14));
v___y_2351_ = v___x_2360_;
goto v___jp_2350_;
}
v___jp_2350_:
{
lean_object* v_items_2352_; lean_object* v___x_2353_; size_t v_sz_2354_; size_t v___x_2355_; lean_object* v___x_2356_; lean_object* v_snd_2357_; lean_object* v___x_2358_; 
v_items_2352_ = lean_ctor_get(v_view_2349_, 1);
lean_inc_ref(v_items_2352_);
lean_dec_ref(v_view_2349_);
v___x_2353_ = lean_box(0);
v_sz_2354_ = lean_array_size(v_items_2352_);
v___x_2355_ = ((size_t)0ULL);
lean_inc_ref(v___y_2351_);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2351_, v___x_2179_, v_items_2352_, v_sz_2354_, v___x_2355_, v___x_2353_, v_a_2144_, v_a_2145_);
lean_dec_ref(v_items_2352_);
v_snd_2357_ = lean_ctor_get(v___x_2356_, 1);
lean_inc(v_snd_2357_);
lean_dec_ref(v___x_2356_);
v___x_2358_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2357_);
return v___x_2358_;
}
}
case 2:
{
lean_object* v_view_2361_; lean_object* v_start_2362_; lean_object* v_items_2363_; size_t v_sz_2364_; size_t v___x_2365_; lean_object* v___x_2366_; lean_object* v_snd_2367_; lean_object* v___x_2368_; 
lean_dec(v_stx_2140_);
v_view_2361_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2361_);
lean_dec_ref_known(v_val_2325_, 1);
v_start_2362_ = lean_ctor_get(v_view_2361_, 1);
lean_inc(v_start_2362_);
v_items_2363_ = lean_ctor_get(v_view_2361_, 2);
lean_inc_ref(v_items_2363_);
lean_dec_ref(v_view_2361_);
v_sz_2364_ = lean_array_size(v_items_2363_);
v___x_2365_ = ((size_t)0ULL);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_2179_, v_alternate_2143_, v_items_2363_, v_sz_2364_, v___x_2365_, v_start_2362_, v_a_2144_, v_a_2145_);
lean_dec_ref(v_items_2363_);
v_snd_2367_ = lean_ctor_get(v___x_2366_, 1);
lean_inc(v_snd_2367_);
lean_dec_ref(v___x_2366_);
v___x_2368_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2367_);
return v___x_2368_;
}
case 3:
{
lean_object* v_view_2369_; lean_object* v_items_2370_; lean_object* v___x_2371_; size_t v_sz_2372_; size_t v___x_2373_; lean_object* v___x_2374_; lean_object* v_snd_2375_; lean_object* v___x_2376_; 
lean_dec(v_stx_2140_);
v_view_2369_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2369_);
lean_dec_ref_known(v_val_2325_, 1);
v_items_2370_ = lean_ctor_get(v_view_2369_, 1);
lean_inc_ref(v_items_2370_);
lean_dec_ref(v_view_2369_);
v___x_2371_ = lean_box(0);
v_sz_2372_ = lean_array_size(v_items_2370_);
v___x_2373_ = ((size_t)0ULL);
v___x_2374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_2179_, v_items_2370_, v_sz_2372_, v___x_2373_, v___x_2371_, v_a_2144_, v_a_2145_);
lean_dec_ref(v_items_2370_);
v_snd_2375_ = lean_ctor_get(v___x_2374_, 1);
lean_inc(v_snd_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2375_);
return v___x_2376_;
}
case 4:
{
lean_object* v_view_2377_; lean_object* v___x_2378_; lean_object* v_snd_2379_; lean_object* v_content_2380_; lean_object* v___y_2382_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
lean_dec(v_stx_2140_);
v_view_2377_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2377_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2378_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2379_ = lean_ctor_get(v___x_2378_, 1);
lean_inc(v_snd_2379_);
lean_dec_ref(v___x_2378_);
v_content_2380_ = lean_ctor_get(v_view_2377_, 2);
lean_inc_ref(v_content_2380_);
lean_dec_ref(v_view_2377_);
v___x_2393_ = lean_array_get_size(v_content_2380_);
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_nat_dec_eq(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__12));
v___y_2382_ = v___x_2396_;
goto v___jp_2381_;
}
else
{
lean_object* v___x_2397_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__16));
v___y_2382_ = v___x_2397_;
goto v___jp_2381_;
}
v___jp_2381_:
{
lean_object* v___x_2383_; lean_object* v_snd_2384_; size_t v_sz_2385_; size_t v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_snd_2391_; lean_object* v___x_2392_; 
v___x_2383_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2382_, v_snd_2379_);
v_snd_2384_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_snd_2384_);
lean_dec_ref(v___x_2383_);
v_sz_2385_ = lean_array_size(v_content_2380_);
v___x_2386_ = ((size_t)0ULL);
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2385_, v___x_2386_, v_content_2380_);
v___x_2388_ = lean_unsigned_to_nat(2u);
v___x_2389_ = lean_nat_add(v_a_2144_, v___x_2388_);
v___x_2390_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2387_, v___x_2179_, v___x_2389_, v_snd_2384_);
lean_dec(v___x_2389_);
lean_dec_ref(v___x_2387_);
v_snd_2391_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_snd_2391_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2391_);
return v___x_2392_;
}
}
case 5:
{
lean_object* v_view_2398_; lean_object* v___x_2399_; lean_object* v_snd_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2425_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; uint8_t v___x_2444_; 
lean_dec(v_stx_2140_);
v_view_2398_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2398_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2399_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2400_ = lean_ctor_get(v___x_2399_, 1);
lean_inc(v_snd_2400_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2402_ = lean_unsigned_to_nat(3u);
v___x_2403_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_view_2398_);
v___x_2441_ = l_Lean_Doc_longestBacktickRun(v___x_2403_);
v___x_2442_ = lean_unsigned_to_nat(1u);
v___x_2443_ = lean_nat_add(v___x_2441_, v___x_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_nat_dec_le(v___x_2402_, v___x_2443_);
if (v___x_2444_ == 0)
{
lean_dec(v___x_2443_);
v___y_2425_ = v___x_2402_;
goto v___jp_2424_;
}
else
{
v___y_2425_ = v___x_2443_;
goto v___jp_2424_;
}
v___jp_2404_:
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_string_append(v___x_2403_, v___y_2406_);
v___y_2156_ = v___y_2405_;
v___y_2157_ = v___y_2406_;
v___y_2158_ = v___y_2407_;
v___y_2159_ = v___y_2408_;
v___y_2160_ = v___x_2409_;
goto v___jp_2155_;
}
v___jp_2410_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_snd_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v___x_2414_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2415_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2414_, v___y_2413_);
v_snd_2416_ = lean_ctor_get(v___x_2415_, 1);
lean_inc(v_snd_2416_);
lean_dec_ref(v___x_2415_);
v___x_2417_ = lean_string_utf8_byte_size(v___x_2403_);
v___x_2418_ = lean_unsigned_to_nat(0u);
v___x_2419_ = lean_nat_dec_eq(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_2421_ = lean_nat_dec_le(v___x_2420_, v___x_2417_);
if (v___x_2421_ == 0)
{
v___y_2405_ = v___y_2411_;
v___y_2406_ = v___x_2414_;
v___y_2407_ = v_snd_2416_;
v___y_2408_ = v___y_2412_;
goto v___jp_2404_;
}
else
{
lean_object* v___x_2422_; uint8_t v___x_2423_; 
v___x_2422_ = lean_nat_sub(v___x_2417_, v___x_2420_);
v___x_2423_ = lean_string_memcmp(v___x_2403_, v___x_2414_, v___x_2422_, v___x_2418_, v___x_2420_);
lean_dec(v___x_2422_);
if (v___x_2423_ == 0)
{
v___y_2405_ = v___y_2411_;
v___y_2406_ = v___x_2414_;
v___y_2407_ = v_snd_2416_;
v___y_2408_ = v___y_2412_;
goto v___jp_2404_;
}
else
{
v___y_2156_ = v___y_2411_;
v___y_2157_ = v___x_2414_;
v___y_2158_ = v_snd_2416_;
v___y_2159_ = v___y_2412_;
v___y_2160_ = v___x_2403_;
goto v___jp_2155_;
}
}
}
else
{
v___y_2156_ = v___y_2411_;
v___y_2157_ = v___x_2414_;
v___y_2158_ = v_snd_2416_;
v___y_2159_ = v___y_2412_;
v___y_2160_ = v___x_2403_;
goto v___jp_2155_;
}
}
v___jp_2424_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_name_x3f_2428_; 
v___x_2426_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_codeString_spec__0(v___y_2425_, v___x_2401_);
v___x_2427_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2426_, v_snd_2400_);
v_name_x3f_2428_ = lean_ctor_get(v_view_2398_, 2);
lean_inc(v_name_x3f_2428_);
if (lean_obj_tag(v_name_x3f_2428_) == 1)
{
lean_object* v_snd_2429_; lean_object* v_args_2430_; lean_object* v_val_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v_snd_2434_; lean_object* v___x_2435_; size_t v_sz_2436_; size_t v___x_2437_; lean_object* v___x_2438_; lean_object* v_snd_2439_; 
v_snd_2429_ = lean_ctor_get(v___x_2427_, 1);
lean_inc(v_snd_2429_);
lean_dec_ref(v___x_2427_);
v_args_2430_ = lean_ctor_get(v_view_2398_, 3);
lean_inc_ref(v_args_2430_);
lean_dec_ref(v_view_2398_);
v_val_2431_ = lean_ctor_get(v_name_x3f_2428_, 0);
lean_inc(v_val_2431_);
lean_dec_ref_known(v_name_x3f_2428_, 1);
v___x_2432_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_val_2431_);
v___x_2433_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2432_, v_snd_2429_);
lean_dec_ref(v___x_2432_);
v_snd_2434_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_snd_2434_);
lean_dec_ref(v___x_2433_);
v___x_2435_ = lean_box(0);
v_sz_2436_ = lean_array_size(v_args_2430_);
v___x_2437_ = ((size_t)0ULL);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2179_, v_args_2430_, v_sz_2436_, v___x_2437_, v___x_2435_, v_a_2144_, v_snd_2434_);
lean_dec_ref(v_args_2430_);
v_snd_2439_ = lean_ctor_get(v___x_2438_, 1);
lean_inc(v_snd_2439_);
lean_dec_ref(v___x_2438_);
v___y_2411_ = v___x_2426_;
v___y_2412_ = v_a_2144_;
v___y_2413_ = v_snd_2439_;
goto v___jp_2410_;
}
else
{
lean_object* v_snd_2440_; 
lean_dec(v_name_x3f_2428_);
lean_dec_ref(v_view_2398_);
v_snd_2440_ = lean_ctor_get(v___x_2427_, 1);
lean_inc(v_snd_2440_);
lean_dec_ref(v___x_2427_);
v___y_2411_ = v___x_2426_;
v___y_2412_ = v_a_2144_;
v___y_2413_ = v_snd_2440_;
goto v___jp_2410_;
}
}
}
case 6:
{
lean_object* v_view_2445_; lean_object* v___x_2446_; lean_object* v_snd_2447_; lean_object* v_name_2448_; lean_object* v_args_2449_; lean_object* v_content_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v_snd_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v_snd_2458_; lean_object* v___x_2459_; size_t v_sz_2460_; size_t v___x_2461_; lean_object* v___x_2462_; lean_object* v_snd_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v_snd_2466_; size_t v_sz_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_snd_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; lean_object* v_snd_2475_; lean_object* v___x_2476_; 
lean_dec(v_stx_2140_);
v_view_2445_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2445_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2446_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2447_ = lean_ctor_get(v___x_2446_, 1);
lean_inc(v_snd_2447_);
lean_dec_ref(v___x_2446_);
v_name_2448_ = lean_ctor_get(v_view_2445_, 2);
lean_inc(v_name_2448_);
v_args_2449_ = lean_ctor_get(v_view_2445_, 3);
lean_inc_ref(v_args_2449_);
v_content_2450_ = lean_ctor_get(v_view_2445_, 4);
lean_inc_ref(v_content_2450_);
lean_dec_ref(v_view_2445_);
v___x_2451_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2452_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_directiveRun(v_content_2450_);
v___x_2453_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__12(v___x_2452_, v___x_2451_);
v___x_2454_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2453_, v_snd_2447_);
v_snd_2455_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_snd_2455_);
lean_dec_ref(v___x_2454_);
v___x_2456_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2448_);
v___x_2457_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2456_, v_snd_2455_);
lean_dec_ref(v___x_2456_);
v_snd_2458_ = lean_ctor_get(v___x_2457_, 1);
lean_inc(v_snd_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = lean_box(0);
v_sz_2460_ = lean_array_size(v_args_2449_);
v___x_2461_ = ((size_t)0ULL);
v___x_2462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2179_, v_args_2449_, v_sz_2460_, v___x_2461_, v___x_2459_, v_a_2144_, v_snd_2458_);
lean_dec_ref(v_args_2449_);
v_snd_2463_ = lean_ctor_get(v___x_2462_, 1);
lean_inc(v_snd_2463_);
lean_dec_ref(v___x_2462_);
v___x_2464_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2465_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2464_, v_snd_2463_);
v_snd_2466_ = lean_ctor_get(v___x_2465_, 1);
lean_inc(v_snd_2466_);
lean_dec_ref(v___x_2465_);
v_sz_2467_ = lean_array_size(v_content_2450_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2467_, v___x_2461_, v_content_2450_);
v___x_2469_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2468_, v___x_2179_, v_a_2144_, v_snd_2466_);
lean_dec_ref(v___x_2468_);
v_snd_2470_ = lean_ctor_get(v___x_2469_, 1);
lean_inc(v_snd_2470_);
lean_dec_ref(v___x_2469_);
lean_inc(v_a_2144_);
v___x_2471_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2144_, v___x_2451_);
v___x_2472_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2471_, v_snd_2470_);
lean_dec_ref(v___x_2471_);
v_snd_2473_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_snd_2473_);
lean_dec_ref(v___x_2472_);
v___x_2474_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2453_, v_snd_2473_);
lean_dec_ref(v___x_2453_);
v_snd_2475_ = lean_ctor_get(v___x_2474_, 1);
lean_inc(v_snd_2475_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2475_);
return v___x_2476_;
}
case 7:
{
lean_object* v_view_2477_; lean_object* v___x_2478_; lean_object* v_snd_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_snd_2482_; lean_object* v_name_2483_; lean_object* v_args_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_snd_2487_; lean_object* v___x_2488_; size_t v_sz_2489_; size_t v___x_2490_; lean_object* v___x_2491_; lean_object* v_snd_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_snd_2495_; lean_object* v___x_2496_; 
lean_dec(v_stx_2140_);
v_view_2477_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2477_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2478_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2479_ = lean_ctor_get(v___x_2478_, 1);
lean_inc(v_snd_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__9));
v___x_2481_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2480_, v_snd_2479_);
v_snd_2482_ = lean_ctor_get(v___x_2481_, 1);
lean_inc(v_snd_2482_);
lean_dec_ref(v___x_2481_);
v_name_2483_ = lean_ctor_get(v_view_2477_, 2);
lean_inc(v_name_2483_);
v_args_2484_ = lean_ctor_get(v_view_2477_, 3);
lean_inc_ref(v_args_2484_);
lean_dec_ref(v_view_2477_);
v___x_2485_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_identString(v_name_2483_);
v___x_2486_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2485_, v_snd_2482_);
lean_dec_ref(v___x_2485_);
v_snd_2487_ = lean_ctor_get(v___x_2486_, 1);
lean_inc(v_snd_2487_);
lean_dec_ref(v___x_2486_);
v___x_2488_ = lean_box(0);
v_sz_2489_ = lean_array_size(v_args_2484_);
v___x_2490_ = ((size_t)0ULL);
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_2179_, v_args_2484_, v_sz_2489_, v___x_2490_, v___x_2488_, v_a_2144_, v_snd_2487_);
lean_dec_ref(v_args_2484_);
v_snd_2492_ = lean_ctor_get(v___x_2491_, 1);
lean_inc(v_snd_2492_);
lean_dec_ref(v___x_2491_);
v___x_2493_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__10));
v___x_2494_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2493_, v_snd_2492_);
v_snd_2495_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_snd_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2495_);
return v___x_2496_;
}
case 8:
{
lean_object* v_view_2497_; lean_object* v___x_2498_; lean_object* v_snd_2499_; lean_object* v_level_2500_; lean_object* v_content_2501_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_snd_2516_; uint8_t v___x_2517_; 
lean_dec(v_stx_2140_);
v_view_2497_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2497_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2498_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2499_ = lean_ctor_get(v___x_2498_, 1);
lean_inc(v_snd_2499_);
lean_dec_ref(v___x_2498_);
v_level_2500_ = lean_ctor_get(v_view_2497_, 2);
lean_inc(v_level_2500_);
v_content_2501_ = lean_ctor_get(v_view_2497_, 3);
lean_inc_ref(v_content_2501_);
lean_dec_ref(v_view_2497_);
v___x_2511_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__18));
v___x_2512_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__13(v_level_2500_, v___x_2511_);
v___x_2513_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2514_ = lean_string_append(v___x_2512_, v___x_2513_);
v___x_2515_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2514_, v_snd_2499_);
lean_dec_ref(v___x_2514_);
v_snd_2516_ = lean_ctor_get(v___x_2515_, 1);
lean_inc(v_snd_2516_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2501_);
if (v___x_2517_ == 0)
{
v___y_2503_ = v_a_2144_;
v___y_2504_ = v_snd_2516_;
goto v___jp_2502_;
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v_snd_2520_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2519_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2518_, v_snd_2516_);
v_snd_2520_ = lean_ctor_get(v___x_2519_, 1);
lean_inc(v_snd_2520_);
lean_dec_ref(v___x_2519_);
v___y_2503_ = v_a_2144_;
v___y_2504_ = v_snd_2520_;
goto v___jp_2502_;
}
v___jp_2502_:
{
size_t v_sz_2505_; size_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v_snd_2509_; lean_object* v___x_2510_; 
v_sz_2505_ = lean_array_size(v_content_2501_);
v___x_2506_ = ((size_t)0ULL);
v___x_2507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2505_, v___x_2506_, v_content_2501_);
v___x_2508_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2507_, v___x_2179_, v___y_2503_, v___y_2504_);
lean_dec_ref(v___x_2507_);
v_snd_2509_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_snd_2509_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2509_);
return v___x_2510_;
}
}
case 9:
{
lean_object* v_view_2521_; lean_object* v___x_2522_; lean_object* v_snd_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v_snd_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_snd_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_snd_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v_snd_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_snd_2538_; lean_object* v___x_2539_; 
lean_dec(v_stx_2140_);
v_view_2521_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2521_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2522_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2523_ = lean_ctor_get(v___x_2522_, 1);
lean_inc(v_snd_2523_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_linkTargetToString___redArg___closed__1));
v___x_2525_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2524_, v_snd_2523_);
v_snd_2526_ = lean_ctor_get(v___x_2525_, 1);
lean_inc(v_snd_2526_);
lean_dec_ref(v___x_2525_);
v___x_2527_ = l_Lean_Doc_LinkRefView_getName(v_view_2521_);
v___x_2528_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2527_, v_snd_2526_);
lean_dec_ref(v___x_2527_);
v_snd_2529_ = lean_ctor_get(v___x_2528_, 1);
lean_inc(v_snd_2529_);
lean_dec_ref(v___x_2528_);
v___x_2530_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2531_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2530_, v_snd_2529_);
v_snd_2532_ = lean_ctor_get(v___x_2531_, 1);
lean_inc(v_snd_2532_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2534_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2533_, v_snd_2532_);
v_snd_2535_ = lean_ctor_get(v___x_2534_, 1);
lean_inc(v_snd_2535_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = l_Lean_Doc_LinkRefView_getUrl(v_view_2521_);
lean_dec_ref(v_view_2521_);
v___x_2537_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2536_, v_snd_2535_);
lean_dec_ref(v___x_2536_);
v_snd_2538_ = lean_ctor_get(v___x_2537_, 1);
lean_inc(v_snd_2538_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2538_);
return v___x_2539_;
}
case 10:
{
lean_object* v_view_2540_; lean_object* v___x_2541_; lean_object* v_snd_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_snd_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v_snd_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_snd_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_snd_2554_; lean_object* v_content_2555_; lean_object* v___y_2557_; lean_object* v___y_2558_; uint8_t v___x_2565_; 
lean_dec(v_stx_2140_);
v_view_2540_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2540_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2541_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2542_ = lean_ctor_get(v___x_2541_, 1);
lean_inc(v_snd_2542_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__8));
v___x_2544_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2543_, v_snd_2542_);
v_snd_2545_ = lean_ctor_get(v___x_2544_, 1);
lean_inc(v_snd_2545_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = l_Lean_Doc_FootnoteRefView_getName(v_view_2540_);
v___x_2547_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2546_, v_snd_2545_);
lean_dec_ref(v___x_2546_);
v_snd_2548_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_snd_2548_);
lean_dec_ref(v___x_2547_);
v___x_2549_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__13));
v___x_2550_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2549_, v_snd_2548_);
v_snd_2551_ = lean_ctor_get(v___x_2550_, 1);
lean_inc(v_snd_2551_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2553_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2552_, v_snd_2551_);
v_snd_2554_ = lean_ctor_get(v___x_2553_, 1);
lean_inc(v_snd_2554_);
lean_dec_ref(v___x_2553_);
v_content_2555_ = lean_ctor_get(v_view_2540_, 4);
lean_inc_ref(v_content_2555_);
lean_dec_ref(v_view_2540_);
v___x_2565_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_leadingSpace(v_content_2555_);
if (v___x_2565_ == 0)
{
v___y_2557_ = v_a_2144_;
v___y_2558_ = v_snd_2554_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v_snd_2568_; 
v___x_2566_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString___closed__0));
v___x_2567_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2566_, v_snd_2554_);
v_snd_2568_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_snd_2568_);
lean_dec_ref(v___x_2567_);
v___y_2557_ = v_a_2144_;
v___y_2558_ = v_snd_2568_;
goto v___jp_2556_;
}
v___jp_2556_:
{
size_t v_sz_2559_; size_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_snd_2563_; lean_object* v___x_2564_; 
v_sz_2559_ = lean_array_size(v_content_2555_);
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__3(v_sz_2559_, v___x_2560_, v_content_2555_);
v___x_2562_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2561_, v___x_2179_, v___y_2557_, v___y_2558_);
lean_dec_ref(v___x_2561_);
v_snd_2563_ = lean_ctor_get(v___x_2562_, 1);
lean_inc(v_snd_2563_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2563_);
return v___x_2564_;
}
}
default: 
{
lean_object* v_view_2569_; lean_object* v___x_2570_; lean_object* v_snd_2571_; lean_object* v___y_2573_; lean_object* v___x_2586_; 
v_view_2569_ = lean_ctor_get(v_val_2325_, 0);
lean_inc_ref(v_view_2569_);
lean_dec_ref_known(v_val_2325_, 1);
v___x_2570_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock(v_a_2144_, v_a_2145_);
v_snd_2571_ = lean_ctor_get(v___x_2570_, 1);
lean_inc(v_snd_2571_);
lean_dec_ref(v___x_2570_);
v___x_2586_ = l_Lean_Syntax_getSubstring_x3f(v_stx_2140_, v___x_2179_, v___x_2179_);
lean_dec(v_stx_2140_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_contents_2587_; lean_object* v___x_2588_; 
v_contents_2587_ = lean_ctor_get(v_view_2569_, 2);
lean_inc(v_contents_2587_);
lean_dec_ref(v_view_2569_);
v___x_2588_ = l_Lean_Syntax_reprint(v_contents_2587_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v___x_2589_; 
v___x_2589_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___y_2573_ = v___x_2589_;
goto v___jp_2572_;
}
else
{
lean_object* v_val_2590_; 
v_val_2590_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v___x_2588_, 1);
v___y_2573_ = v_val_2590_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_val_2591_; lean_object* v_str_2592_; lean_object* v_startPos_2593_; lean_object* v_stopPos_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v_snd_2598_; lean_object* v___x_2599_; 
lean_dec_ref(v_view_2569_);
v_val_2591_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2591_);
lean_dec_ref_known(v___x_2586_, 1);
v_str_2592_ = lean_ctor_get(v_val_2591_, 0);
lean_inc_ref(v_str_2592_);
v_startPos_2593_ = lean_ctor_get(v_val_2591_, 1);
lean_inc(v_startPos_2593_);
v_stopPos_2594_ = lean_ctor_get(v_val_2591_, 2);
lean_inc(v_stopPos_2594_);
lean_dec(v_val_2591_);
v___x_2595_ = lean_string_utf8_extract(v_str_2592_, v_startPos_2593_, v_stopPos_2594_);
lean_dec(v_stopPos_2594_);
lean_dec(v_startPos_2593_);
lean_dec_ref(v_str_2592_);
lean_inc(v_a_2144_);
v___x_2596_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2144_, v___x_2595_);
v___x_2597_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2596_, v_snd_2571_);
lean_dec_ref(v___x_2596_);
v_snd_2598_ = lean_ctor_get(v___x_2597_, 1);
lean_inc(v_snd_2598_);
lean_dec_ref(v___x_2597_);
v___x_2599_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2598_);
return v___x_2599_;
}
v___jp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v_snd_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2574_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__14));
v___x_2575_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2574_, v_snd_2571_);
v_snd_2576_ = lean_ctor_get(v___x_2575_, 1);
lean_inc(v_snd_2576_);
lean_dec_ref(v___x_2575_);
lean_inc(v_a_2144_);
v___x_2577_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_reindented(v_a_2144_, v___y_2573_);
v___x_2578_ = lean_string_utf8_byte_size(v___x_2577_);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_nat_dec_eq(v___x_2578_, v___x_2579_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v_snd_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_snd_2585_; 
v___x_2581_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2577_, v_snd_2576_);
lean_dec_ref(v___x_2577_);
v_snd_2582_ = lean_ctor_get(v___x_2581_, 1);
lean_inc(v_snd_2582_);
lean_dec_ref(v___x_2581_);
v___x_2583_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2584_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2583_, v_snd_2582_);
v_snd_2585_ = lean_ctor_get(v___x_2584_, 1);
lean_inc(v_snd_2585_);
lean_dec_ref(v___x_2584_);
v___y_2147_ = v_snd_2585_;
goto v___jp_2146_;
}
else
{
lean_dec_ref(v___x_2577_);
v___y_2147_ = v_snd_2576_;
goto v___jp_2146_;
}
}
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_dec(v___x_2324_);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Syntax_formatStx(v_stx_2140_, v___x_2600_, v___x_2179_);
v___x_2602_ = l_Std_Format_defWidth;
v___x_2603_ = lean_unsigned_to_nat(0u);
v___x_2604_ = l_Std_Format_pretty(v___x_2601_, v___x_2602_, v___x_2603_, v___x_2603_);
v___x_2605_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2604_, v_a_2145_);
lean_dec_ref(v___x_2604_);
return v___x_2605_;
}
}
}
}
}
}
else
{
lean_object* v___x_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; 
lean_dec(v_next_x3f_2141_);
v___x_2606_ = l_Lean_Syntax_getArgs(v_stx_2140_);
lean_dec(v_stx_2140_);
v___x_2607_ = 0;
v___x_2608_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v___x_2606_, v___x_2607_, v_a_2144_, v_a_2145_);
lean_dec_ref(v___x_2606_);
return v___x_2608_;
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v_snd_2153_; lean_object* v___x_2154_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
lean_inc(v_a_2144_);
v___x_2149_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock_spec__0(v_a_2144_, v___x_2148_);
v___x_2150_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__4));
v___x_2151_ = lean_string_append(v___x_2149_, v___x_2150_);
v___x_2152_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2151_, v___y_2147_);
lean_dec_ref(v___x_2151_);
v_snd_2153_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_snd_2153_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2153_);
return v___x_2154_;
}
v___jp_2155_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v_snd_2170_; lean_object* v___x_2171_; lean_object* v_snd_2172_; lean_object* v___x_2173_; 
v___x_2161_ = lean_unsigned_to_nat(0u);
v___x_2162_ = lean_string_utf8_byte_size(v___y_2160_);
lean_inc_ref(v___y_2160_);
v___x_2163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2163_, 0, v___y_2160_);
lean_ctor_set(v___x_2163_, 1, v___x_2161_);
lean_ctor_set(v___x_2163_, 2, v___x_2162_);
v___x_2164_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
v___x_2165_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2166_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2159_, v___y_2160_, v___x_2163_, v___x_2162_, v___x_2164_, v___x_2165_);
lean_dec_ref_known(v___x_2163_, 3);
lean_dec_ref(v___y_2160_);
v___x_2167_ = lean_array_to_list(v___x_2166_);
v___x_2168_ = l_String_intercalate(v___y_2157_, v___x_2167_);
v___x_2169_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2168_, v___y_2158_);
lean_dec_ref(v___x_2168_);
v_snd_2170_ = lean_ctor_get(v___x_2169_, 1);
lean_inc(v_snd_2170_);
lean_dec_ref(v___x_2169_);
v___x_2171_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___y_2156_, v_snd_2170_);
lean_dec_ref(v___y_2156_);
v_snd_2172_ = lean_ctor_get(v___x_2171_, 1);
lean_inc(v_snd_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_endBlock___redArg(v_snd_2172_);
return v___x_2173_;
}
v___jp_2174_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v_a_2145_);
return v___x_2176_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(uint8_t v___x_2609_, lean_object* v_as_2610_, size_t v_sz_2611_, size_t v_i_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_usize_dec_lt(v_i_2612_, v_sz_2611_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v_b_2613_);
lean_ctor_set(v___x_2617_, 1, v___y_2615_);
return v___x_2617_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v_snd_2620_; lean_object* v_a_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v_snd_2624_; lean_object* v___x_2625_; size_t v___x_2626_; size_t v___x_2627_; 
v___x_2618_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_textString_needsEscape___closed__22));
v___x_2619_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_out___redArg(v___x_2618_, v___y_2615_);
v_snd_2620_ = lean_ctor_get(v___x_2619_, 1);
lean_inc(v_snd_2620_);
lean_dec_ref(v___x_2619_);
v_a_2621_ = lean_array_uget_borrowed(v_as_2610_, v_i_2612_);
v___x_2622_ = lean_box(0);
lean_inc(v_a_2621_);
v___x_2623_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_a_2621_, v___x_2622_, v___x_2609_, v___x_2609_, v___y_2614_, v_snd_2620_);
v_snd_2624_ = lean_ctor_get(v___x_2623_, 1);
lean_inc(v_snd_2624_);
lean_dec_ref(v___x_2623_);
v___x_2625_ = lean_box(0);
v___x_2626_ = ((size_t)1ULL);
v___x_2627_ = lean_usize_add(v_i_2612_, v___x_2626_);
v_i_2612_ = v___x_2627_;
v_b_2613_ = v___x_2625_;
v___y_2615_ = v_snd_2624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4___boxed(lean_object* v___x_2629_, lean_object* v_as_2630_, lean_object* v_sz_2631_, lean_object* v_i_2632_, lean_object* v_b_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v___x_61784__boxed_2636_; size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v___x_61784__boxed_2636_ = lean_unbox(v___x_2629_);
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2631_);
lean_dec(v_sz_2631_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2632_);
lean_dec(v_i_2632_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__4(v___x_61784__boxed_2636_, v_as_2630_, v_sz_boxed_2637_, v_i_boxed_2638_, v_b_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v_as_2630_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7___boxed(lean_object* v___y_2640_, lean_object* v___x_2641_, lean_object* v_as_2642_, lean_object* v_sz_2643_, lean_object* v_i_2644_, lean_object* v_b_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
uint8_t v___x_61802__boxed_2648_; size_t v_sz_boxed_2649_; size_t v_i_boxed_2650_; lean_object* v_res_2651_; 
v___x_61802__boxed_2648_ = lean_unbox(v___x_2641_);
v_sz_boxed_2649_ = lean_unbox_usize(v_sz_2643_);
lean_dec(v_sz_2643_);
v_i_boxed_2650_ = lean_unbox_usize(v_i_2644_);
lean_dec(v_i_2644_);
v_res_2651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__7(v___y_2640_, v___x_61802__boxed_2648_, v_as_2642_, v_sz_boxed_2649_, v_i_boxed_2650_, v_b_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v_as_2642_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq___boxed(lean_object* v_stxs_2652_, lean_object* v_lineStart_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
uint8_t v_lineStart_boxed_2656_; lean_object* v_res_2657_; 
v_lineStart_boxed_2656_ = lean_unbox(v_lineStart_2653_);
v_res_2657_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq(v_stxs_2652_, v_lineStart_boxed_2656_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_stxs_2652_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike___boxed(lean_object* v_char_2658_, lean_object* v_inls_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
uint32_t v_char_boxed_2662_; lean_object* v_res_2663_; 
v_char_boxed_2662_ = lean_unbox_uint32(v_char_2658_);
lean_dec(v_char_2658_);
v_res_2663_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_emphLike(v_char_boxed_2662_, v_inls_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2660_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8___boxed(lean_object* v___x_2664_, lean_object* v_alternate_2665_, lean_object* v_as_2666_, lean_object* v_sz_2667_, lean_object* v_i_2668_, lean_object* v_b_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v___x_61882__boxed_2672_; uint8_t v_alternate_boxed_2673_; size_t v_sz_boxed_2674_; size_t v_i_boxed_2675_; lean_object* v_res_2676_; 
v___x_61882__boxed_2672_ = lean_unbox(v___x_2664_);
v_alternate_boxed_2673_ = lean_unbox(v_alternate_2665_);
v_sz_boxed_2674_ = lean_unbox_usize(v_sz_2667_);
lean_dec(v_sz_2667_);
v_i_boxed_2675_ = lean_unbox_usize(v_i_2668_);
lean_dec(v_i_2668_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__8(v___x_61882__boxed_2672_, v_alternate_boxed_2673_, v_as_2666_, v_sz_boxed_2674_, v_i_boxed_2675_, v_b_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v_as_2666_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9___boxed(lean_object* v___x_2677_, lean_object* v_as_2678_, lean_object* v_sz_2679_, lean_object* v_i_2680_, lean_object* v_b_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v___x_61916__boxed_2684_; size_t v_sz_boxed_2685_; size_t v_i_boxed_2686_; lean_object* v_res_2687_; 
v___x_61916__boxed_2684_ = lean_unbox(v___x_2677_);
v_sz_boxed_2685_ = lean_unbox_usize(v_sz_2679_);
lean_dec(v_sz_2679_);
v_i_boxed_2686_ = lean_unbox_usize(v_i_2680_);
lean_dec(v_i_2680_);
v_res_2687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__9(v___x_61916__boxed_2684_, v_as_2678_, v_sz_boxed_2685_, v_i_boxed_2686_, v_b_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v_as_2678_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg___boxed(lean_object* v_upperBound_2688_, lean_object* v___y_2689_, lean_object* v_a_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2688_, v___y_2689_, v_a_2690_, v_b_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2689_);
lean_dec(v_upperBound_2688_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___boxed(lean_object* v_stx_2695_, lean_object* v_next_x3f_2696_, lean_object* v_atLineStart_2697_, lean_object* v_alternate_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
uint8_t v_atLineStart_boxed_2701_; uint8_t v_alternate_boxed_2702_; lean_object* v_res_2703_; 
v_atLineStart_boxed_2701_ = lean_unbox(v_atLineStart_2697_);
v_alternate_boxed_2702_ = lean_unbox(v_alternate_2698_);
v_res_2703_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2695_, v_next_x3f_2696_, v_atLineStart_boxed_2701_, v_alternate_boxed_2702_, v_a_2699_, v_a_2700_);
lean_dec(v_a_2699_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(lean_object* v_s_2704_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__0);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10___boxed(lean_object* v_s_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_String_Slice_splitToSubslice___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__10(v_s_2706_);
lean_dec_ref(v_s_2706_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(lean_object* v_upperBound_2708_, lean_object* v___y_2709_, lean_object* v_inst_2710_, lean_object* v_R_2711_, lean_object* v_a_2712_, lean_object* v_b_2713_, lean_object* v_c_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___redArg(v_upperBound_2708_, v___y_2709_, v_a_2712_, v_b_2713_, v___y_2715_, v___y_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0___boxed(lean_object* v_upperBound_2718_, lean_object* v___y_2719_, lean_object* v_inst_2720_, lean_object* v_R_2721_, lean_object* v_a_2722_, lean_object* v_b_2723_, lean_object* v_c_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_seq_spec__0(v_upperBound_2718_, v___y_2719_, v_inst_2720_, v_R_2721_, v_a_2722_, v_b_2723_, v_c_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2719_);
lean_dec(v_upperBound_2718_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___x_2730_, lean_object* v___x_2731_, lean_object* v_inst_2732_, lean_object* v_R_2733_, lean_object* v_a_2734_, lean_object* v_b_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___redArg(v___y_2728_, v___y_2729_, v___x_2730_, v___x_2731_, v_a_2734_, v_b_2735_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11___boxed(lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___x_2739_, lean_object* v___x_2740_, lean_object* v_inst_2741_, lean_object* v_R_2742_, lean_object* v_a_2743_, lean_object* v_b_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27_spec__11(v___y_2737_, v___y_2738_, v___x_2739_, v___x_2740_, v_inst_2741_, v_R_2742_, v_a_2743_, v_b_2744_);
lean_dec_ref(v___x_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(lean_object* v_s_2746_, lean_object* v_pos_2747_){
_start:
{
lean_object* v_str_2748_; lean_object* v_startInclusive_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v_decide_2753_; 
v_str_2748_ = lean_ctor_get(v_s_2746_, 0);
v_startInclusive_2749_ = lean_ctor_get(v_s_2746_, 1);
v___x_2750_ = lean_nat_add(v_startInclusive_2749_, v_pos_2747_);
v___x_2751_ = lean_nat_sub(v___x_2750_, v_startInclusive_2749_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v_decide_2753_ = lean_nat_dec_eq(v___x_2751_, v___x_2752_);
if (v_decide_2753_ == 0)
{
uint32_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint32_t v___x_2760_; uint8_t v___x_2761_; 
v___x_2754_ = 10;
lean_inc(v_startInclusive_2749_);
lean_inc_ref(v_str_2748_);
v___x_2755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2755_, 0, v_str_2748_);
lean_ctor_set(v___x_2755_, 1, v_startInclusive_2749_);
lean_ctor_set(v___x_2755_, 2, v___x_2750_);
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = lean_nat_sub(v___x_2751_, v___x_2756_);
lean_dec(v___x_2751_);
v___x_2758_ = l_String_Slice_posLE(v___x_2755_, v___x_2757_);
lean_dec_ref_known(v___x_2755_, 3);
v___x_2759_ = lean_nat_add(v_startInclusive_2749_, v___x_2758_);
v___x_2760_ = lean_string_utf8_get_fast(v_str_2748_, v___x_2759_);
lean_dec(v___x_2759_);
v___x_2761_ = lean_uint32_dec_eq(v___x_2760_, v___x_2754_);
if (v___x_2761_ == 0)
{
lean_dec(v___x_2758_);
return v_pos_2747_;
}
else
{
lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2762_ = lean_nat_add(v___x_2758_, v___x_2756_);
v___x_2763_ = lean_nat_dec_le(v___x_2762_, v_pos_2747_);
lean_dec(v___x_2762_);
if (v___x_2763_ == 0)
{
lean_dec(v___x_2758_);
return v_pos_2747_;
}
else
{
lean_dec(v_pos_2747_);
v_pos_2747_ = v___x_2758_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2751_);
lean_dec(v___x_2750_);
return v_pos_2747_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0___boxed(lean_object* v_s_2765_, lean_object* v_pos_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v_s_2765_, v_pos_2766_);
lean_dec_ref(v_s_2765_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(lean_object* v_s_2768_){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2769_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__0));
v___x_2770_ = lean_string_utf8_byte_size(v_s_2768_);
v___x_2771_ = lean_obj_once(&l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1, &l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1_once, _init_l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__1);
v___x_2772_ = lean_nat_dec_le(v___x_2771_, v___x_2770_);
if (v___x_2772_ == 0)
{
return v_s_2768_;
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2773_ = lean_unsigned_to_nat(0u);
v___x_2774_ = lean_nat_sub(v___x_2770_, v___x_2771_);
v___x_2775_ = lean_string_memcmp(v_s_2768_, v___x_2769_, v___x_2774_, v___x_2773_, v___x_2771_);
lean_dec(v___x_2774_);
if (v___x_2775_ == 0)
{
return v_s_2768_;
}
else
{
uint32_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2776_ = 10;
lean_inc_ref(v_s_2768_);
v___x_2777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2777_, 0, v_s_2768_);
lean_ctor_set(v___x_2777_, 1, v___x_2773_);
lean_ctor_set(v___x_2777_, 2, v___x_2770_);
v___x_2778_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline_spec__0(v___x_2777_, v___x_2770_);
lean_dec_ref_known(v___x_2777_, 3);
v___x_2779_ = lean_string_utf8_extract_fast(v_s_2768_, v___x_2773_, v___x_2778_);
lean_dec(v___x_2778_);
lean_dec_ref(v_s_2768_);
v___x_2780_ = lean_string_push(v___x_2779_, v___x_2776_);
return v___x_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(lean_object* v_stx_2781_, uint8_t v_alternate_2782_){
_start:
{
lean_object* v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v_snd_2788_; 
v___x_2783_ = lean_box(0);
v___x_2784_ = 0;
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2787_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27(v_stx_2781_, v___x_2783_, v___x_2784_, v_alternate_2782_, v___x_2785_, v___x_2786_);
v_snd_2788_ = lean_ctor_get(v___x_2787_, 1);
lean_inc(v_snd_2788_);
lean_dec_ref(v___x_2787_);
return v_snd_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString___boxed(lean_object* v_stx_2789_, lean_object* v_alternate_2790_){
_start:
{
uint8_t v_alternate_boxed_2791_; lean_object* v_res_2792_; 
v_alternate_boxed_2791_ = lean_unbox(v_alternate_2790_);
v_res_2792_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2789_, v_alternate_boxed_2791_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString(lean_object* v_stx_2793_, uint8_t v_alternate_2794_){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_stx_2793_, v_alternate_2794_);
v___x_2796_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoSyntaxToString___boxed(lean_object* v_stx_2797_, lean_object* v_alternate_2798_){
_start:
{
uint8_t v_alternate_boxed_2799_; lean_object* v_res_2800_; 
v_alternate_boxed_2799_ = lean_unbox(v_alternate_2798_);
v_res_2800_ = l_Lean_Doc_Parser_versoSyntaxToString(v_stx_2797_, v_alternate_boxed_2799_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___lam__0(lean_object* v_b_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v___x_2803_; 
lean_inc(v_b_2801_);
v___x_2803_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_blankParagraph(v_b_2801_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; uint8_t v___y_2806_; 
lean_inc(v_b_2801_);
v___x_2804_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_markerFor(v___y_2802_, v_b_2801_);
lean_dec(v___y_2802_);
if (lean_obj_tag(v___x_2804_) == 0)
{
v___y_2806_ = v___x_2803_;
goto v___jp_2805_;
}
else
{
lean_object* v_val_2809_; uint8_t v_alternate_2810_; 
v_val_2809_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_val_2809_);
v_alternate_2810_ = lean_ctor_get_uint8(v_val_2809_, 1);
lean_dec(v_val_2809_);
v___y_2806_ = v_alternate_2810_;
goto v___jp_2805_;
}
v___jp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_separatedToString(v_b_2801_, v___y_2806_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
lean_ctor_set(v___x_2808_, 1, v___x_2804_);
return v___x_2808_;
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec(v_b_2801_);
v___x_2811_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___y_2802_);
return v___x_2812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(lean_object* v_n_2813_, lean_object* v_f_2814_, lean_object* v_xs_2815_, lean_object* v_k_2816_, lean_object* v_acc_2817_, lean_object* v___y_2818_){
_start:
{
uint8_t v___x_2819_; 
v___x_2819_ = lean_nat_dec_lt(v_k_2816_, v_n_2813_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec(v_k_2816_);
lean_dec_ref(v_f_2814_);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_acc_2817_);
lean_ctor_set(v___x_2820_, 1, v___y_2818_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v_fst_2823_; lean_object* v_snd_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2821_ = lean_array_fget_borrowed(v_xs_2815_, v_k_2816_);
lean_inc_ref(v_f_2814_);
lean_inc(v___x_2821_);
v___x_2822_ = lean_apply_2(v_f_2814_, v___x_2821_, v___y_2818_);
v_fst_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_fst_2823_);
v_snd_2824_ = lean_ctor_get(v___x_2822_, 1);
lean_inc(v_snd_2824_);
lean_dec_ref(v___x_2822_);
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_nat_add(v_k_2816_, v___x_2825_);
lean_dec(v_k_2816_);
v___x_2827_ = lean_array_push(v_acc_2817_, v_fst_2823_);
v_k_2816_ = v___x_2826_;
v_acc_2817_ = v___x_2827_;
v___y_2818_ = v_snd_2824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg___boxed(lean_object* v_n_2829_, lean_object* v_f_2830_, lean_object* v_xs_2831_, lean_object* v_k_2832_, lean_object* v_acc_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2829_, v_f_2830_, v_xs_2831_, v_k_2832_, v_acc_2833_, v___y_2834_);
lean_dec_ref(v_xs_2831_);
lean_dec(v_n_2829_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(lean_object* v_blocks_2837_){
_start:
{
lean_object* v___f_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_fst_2844_; 
v___f_2838_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___closed__0));
v___x_2839_ = lean_array_get_size(v_blocks_2837_);
v___x_2840_ = lean_unsigned_to_nat(0u);
v___x_2841_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoSyntaxToString_x27___closed__1));
v___x_2842_ = lean_box(0);
v___x_2843_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v___x_2839_, v___f_2838_, v_blocks_2837_, v___x_2840_, v___x_2841_, v___x_2842_);
v_fst_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_fst_2844_);
lean_dec_ref(v___x_2843_);
return v_fst_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString___boxed(lean_object* v_blocks_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2845_);
lean_dec_ref(v_blocks_2845_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(lean_object* v_00_u03b1_2847_, lean_object* v_00_u03b2_2848_, lean_object* v_n_2849_, lean_object* v_f_2850_, lean_object* v_xs_2851_, lean_object* v_k_2852_, lean_object* v_h_2853_, lean_object* v_acc_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___redArg(v_n_2849_, v_f_2850_, v_xs_2851_, v_k_2852_, v_acc_2854_, v___y_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0___boxed(lean_object* v_00_u03b1_2857_, lean_object* v_00_u03b2_2858_, lean_object* v_n_2859_, lean_object* v_f_2860_, lean_object* v_xs_2861_, lean_object* v_k_2862_, lean_object* v_h_2863_, lean_object* v_acc_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString_spec__0(v_00_u03b1_2857_, v_00_u03b2_2858_, v_n_2859_, v_f_2860_, v_xs_2861_, v_k_2862_, v_h_2863_, v_acc_2864_, v___y_2865_);
lean_dec_ref(v_xs_2861_);
lean_dec(v_n_2859_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(lean_object* v_as_2867_, size_t v_i_2868_, size_t v_stop_2869_, lean_object* v_b_2870_){
_start:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_usize_dec_eq(v_i_2868_, v_stop_2869_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; 
v___x_2872_ = lean_array_uget_borrowed(v_as_2867_, v_i_2868_);
v___x_2873_ = lean_string_append(v_b_2870_, v___x_2872_);
v___x_2874_ = ((size_t)1ULL);
v___x_2875_ = lean_usize_add(v_i_2868_, v___x_2874_);
v_i_2868_ = v___x_2875_;
v_b_2870_ = v___x_2873_;
goto _start;
}
else
{
return v_b_2870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0___boxed(lean_object* v_as_2877_, lean_object* v_i_2878_, lean_object* v_stop_2879_, lean_object* v_b_2880_){
_start:
{
size_t v_i_boxed_2881_; size_t v_stop_boxed_2882_; lean_object* v_res_2883_; 
v_i_boxed_2881_ = lean_unbox_usize(v_i_2878_);
lean_dec(v_i_2878_);
v_stop_boxed_2882_ = lean_unbox_usize(v_stop_2879_);
lean_dec(v_stop_2879_);
v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v_as_2877_, v_i_boxed_2881_, v_stop_boxed_2882_, v_b_2880_);
lean_dec_ref(v_as_2877_);
return v_res_2883_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2885_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString(lean_object* v_blocks_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_startBlock___closed__2));
v___x_2888_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_2886_);
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = lean_array_get_size(v___x_2888_);
v___x_2891_ = lean_nat_dec_lt(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_dec_ref(v___x_2888_);
v___x_2892_ = lean_obj_once(&l_Lean_Doc_Parser_versoDocumentToString___closed__0, &l_Lean_Doc_Parser_versoDocumentToString___closed__0_once, _init_l_Lean_Doc_Parser_versoDocumentToString___closed__0);
return v___x_2892_;
}
else
{
size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2893_ = ((size_t)0ULL);
v___x_2894_ = lean_usize_of_nat(v___x_2890_);
v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Doc_Parser_versoDocumentToString_spec__0(v___x_2888_, v___x_2893_, v___x_2894_, v___x_2887_);
lean_dec_ref(v___x_2888_);
v___x_2896_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2895_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoDocumentToString___boxed(lean_object* v_blocks_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Doc_Parser_versoDocumentToString(v_blocks_2897_);
lean_dec_ref(v_blocks_2897_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; lean_object* v_stxTrav_2902_; lean_object* v_cur_2903_; lean_object* v___x_2904_; 
v___x_2901_ = lean_st_ref_get(v___y_2899_);
v_stxTrav_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc_ref(v_stxTrav_2902_);
lean_dec(v___x_2901_);
v_cur_2903_ = lean_ctor_get(v_stxTrav_2902_, 0);
lean_inc(v_cur_2903_);
lean_dec_ref(v_stxTrav_2902_);
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_cur_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg___boxed(lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2905_);
lean_dec(v___y_2905_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_2909_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___boxed(lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0(v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; lean_object* v_stxTrav_2923_; lean_object* v_leadWord_2924_; uint8_t v_leadWordIdent_2925_; uint8_t v_isUngrouped_2926_; uint8_t v_mustBeGrouped_2927_; lean_object* v_stack_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2939_; 
v___x_2922_ = lean_st_ref_take(v___y_2920_);
v_stxTrav_2923_ = lean_ctor_get(v___x_2922_, 0);
v_leadWord_2924_ = lean_ctor_get(v___x_2922_, 1);
v_leadWordIdent_2925_ = lean_ctor_get_uint8(v___x_2922_, sizeof(void*)*3);
v_isUngrouped_2926_ = lean_ctor_get_uint8(v___x_2922_, sizeof(void*)*3 + 1);
v_mustBeGrouped_2927_ = lean_ctor_get_uint8(v___x_2922_, sizeof(void*)*3 + 2);
v_stack_2928_ = lean_ctor_get(v___x_2922_, 2);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2930_ = v___x_2922_;
v_isShared_2931_ = v_isSharedCheck_2939_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_stack_2928_);
lean_inc(v_leadWord_2924_);
lean_inc(v_stxTrav_2923_);
lean_dec(v___x_2922_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2939_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = l_Lean_Syntax_Traverser_left(v_stxTrav_2923_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2933_);
v___x_2935_ = v___x_2930_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_leadWord_2924_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_stack_2928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2938_, sizeof(void*)*3, v_leadWordIdent_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_2938_, sizeof(void*)*3 + 1, v_isUngrouped_2926_);
lean_ctor_set_uint8(v_reuseFailAlloc_2938_, sizeof(void*)*3 + 2, v_mustBeGrouped_2927_);
v___x_2935_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_st_ref_put(v___y_2920_, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2932_);
return v___x_2937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg___boxed(lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2940_);
lean_dec(v___y_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2944_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___boxed(lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1(v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(lean_object* v_upperBound_2955_, lean_object* v___x_2956_, lean_object* v_rendered_2957_, lean_object* v_a_2958_, lean_object* v_b_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
uint8_t v___x_2965_; 
v___x_2965_ = lean_nat_dec_lt(v_a_2958_, v_upperBound_2955_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; 
lean_dec(v_a_2958_);
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_b_2959_);
return v___x_2966_;
}
else
{
lean_object* v___x_2967_; lean_object* v___y_2969_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2967_ = lean_box(0);
v___x_2975_ = lean_unsigned_to_nat(0u);
v___x_2976_ = lean_unsigned_to_nat(1u);
v___x_2977_ = lean_nat_sub(v___x_2956_, v___x_2976_);
v___x_2978_ = lean_nat_sub(v___x_2977_, v_a_2958_);
lean_dec(v___x_2977_);
v___x_2979_ = lean_array_fget_borrowed(v_rendered_2957_, v___x_2978_);
lean_dec(v___x_2978_);
v___x_2980_ = lean_nat_dec_eq(v_a_2958_, v___x_2975_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; 
lean_inc(v___x_2979_);
v___x_2981_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
v___y_2969_ = v___x_2981_;
goto v___jp_2968_;
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
lean_inc(v___x_2979_);
v___x_2982_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_oneTrailingNewline(v___x_2979_);
v___x_2983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2982_);
v___y_2969_ = v___x_2983_;
goto v___jp_2968_;
}
v___jp_2968_:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_PrettyPrinter_Formatter_push___redArg(v___y_2969_, v___y_2961_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v___x_2971_; 
lean_dec_ref_known(v___x_2970_, 1);
v___x_2971_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_Doc_Parser_document_formatter_spec__1___redArg(v___y_2961_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec_ref_known(v___x_2971_, 1);
v___x_2972_ = lean_unsigned_to_nat(1u);
v___x_2973_ = lean_nat_add(v_a_2958_, v___x_2972_);
lean_dec(v_a_2958_);
v_a_2958_ = v___x_2973_;
v_b_2959_ = v___x_2967_;
goto _start;
}
else
{
lean_dec(v_a_2958_);
return v___x_2971_;
}
}
else
{
lean_dec(v_a_2958_);
return v___x_2970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg___boxed(lean_object* v_upperBound_2984_, lean_object* v___x_2985_, lean_object* v_rendered_2986_, lean_object* v_a_2987_, lean_object* v_b_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_2984_, v___x_2985_, v_rendered_2986_, v_a_2987_, v_b_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_rendered_2986_);
lean_dec(v___x_2985_);
lean_dec(v_upperBound_2984_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0(lean_object* v___x_2995_, lean_object* v_rendered_2996_, lean_object* v___x_2997_, lean_object* v___x_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v___x_2995_, v___x_2995_, v_rendered_2996_, v___x_2997_, v___x_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3011_ == 0)
{
lean_object* v_unused_3012_; 
v_unused_3012_ = lean_ctor_get(v___x_3004_, 0);
lean_dec(v_unused_3012_);
v___x_3006_ = v___x_3004_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_dec(v___x_3004_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_2998_);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_2998_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
else
{
return v___x_3004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__0___boxed(lean_object* v___x_3013_, lean_object* v_rendered_3014_, lean_object* v___x_3015_, lean_object* v___x_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_Doc_Parser_document_formatter___lam__0(v___x_3013_, v_rendered_3014_, v___x_3015_, v___x_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec_ref(v_rendered_3014_);
lean_dec(v___x_3013_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1(lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___x_3028_; lean_object* v_a_3029_; lean_object* v_blocks_3030_; lean_object* v_rendered_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___f_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3028_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lean_Doc_Parser_document_formatter_spec__0___redArg(v___y_3024_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___x_3028_);
v_blocks_3030_ = l_Lean_TSyntax_getVersoBlocks(v_a_3029_);
lean_dec(v_a_3029_);
v_rendered_3031_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_versoBlocksToString(v_blocks_3030_);
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = lean_array_get_size(v_blocks_3030_);
lean_dec_ref(v_blocks_3030_);
v___x_3034_ = lean_box(0);
v___f_3035_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3035_, 0, v___x_3033_);
lean_closure_set(v___f_3035_, 1, v_rendered_3031_);
lean_closure_set(v___f_3035_, 2, v___x_3032_);
lean_closure_set(v___f_3035_, 3, v___x_3034_);
v___x_3036_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_visitArgs___boxed), 6, 1);
lean_closure_set(v___x_3036_, 0, v___f_3035_);
v___x_3037_ = l_Lean_PrettyPrinter_Formatter_visitArgs(v___x_3036_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___lam__1___boxed(lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_Doc_Parser_document_formatter___lam__1(v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter(lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_){
_start:
{
lean_object* v___f_3050_; lean_object* v___x_3051_; 
v___f_3050_ = ((lean_object*)(l_Lean_Doc_Parser_document_formatter___closed__0));
v___x_3051_ = l_Lean_PrettyPrinter_Formatter_concat(v___f_3050_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document_formatter___boxed(lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean_Doc_Parser_document_formatter(v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(lean_object* v_upperBound_3058_, lean_object* v___x_3059_, lean_object* v_rendered_3060_, lean_object* v_inst_3061_, lean_object* v_R_3062_, lean_object* v_a_3063_, lean_object* v_b_3064_, lean_object* v_c_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___redArg(v_upperBound_3058_, v___x_3059_, v_rendered_3060_, v_a_3063_, v_b_3064_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2___boxed(lean_object* v_upperBound_3072_, lean_object* v___x_3073_, lean_object* v_rendered_3074_, lean_object* v_inst_3075_, lean_object* v_R_3076_, lean_object* v_a_3077_, lean_object* v_b_3078_, lean_object* v_c_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_Parser_document_formatter_spec__2(v_upperBound_3072_, v___x_3073_, v_rendered_3074_, v_inst_3075_, v_R_3076_, v_a_3077_, v_b_3078_, v_c_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec_ref(v_rendered_3074_);
lean_dec(v___x_3073_);
lean_dec(v_upperBound_3072_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1(){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3103_ = l_Lean_PrettyPrinter_formatterAttribute;
v___x_3104_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__4));
v___x_3105_ = ((lean_object*)(l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___closed__6));
v___x_3106_ = lean_alloc_closure((void*)(l_Lean_Doc_Parser_document_formatter___boxed), 5, 0);
v___x_3107_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3103_, v___x_3104_, v___x_3105_, v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1___boxed(lean_object* v_a_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l___private_Lean_DocString_Formatter_0__Lean_Doc_Parser_document_formatter___regBuiltin_Lean_Doc_Parser_document_formatter__1();
return v_res_3109_;
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
