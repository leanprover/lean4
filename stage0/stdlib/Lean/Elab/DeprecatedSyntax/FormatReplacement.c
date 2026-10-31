// Lean compiler output
// Module: Lean.Elab.DeprecatedSyntax.FormatReplacement
// Imports: public import Lean.CoreM import Lean.Meta.TryThis import Lean.PrettyPrinter.Formatter import Lean.PrettyPrinter.Parenthesizer
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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_parseTokenCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_needsTokenSeparator(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_maxPrec;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTrailingSize(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_bindsAsTightly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_bindsAsTightly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__0 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__1 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__4 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__4_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__5 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__7 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__7_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__8 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__10 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__10_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__12 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__13 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__13_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__14 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__14_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__15 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__15_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__17 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__15_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__19 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__19_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__20 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__20_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__21 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__21_value;
static lean_once_cell_t l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__22;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__23 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__23_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "DeprecatedSyntax"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__24 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__23_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__24_value),LEAN_SCALAR_PTR_LITERAL(10, 222, 164, 70, 82, 80, 248, 201)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__25_value)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__26 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__27 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__27_value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__28 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__28_value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__28_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__29 = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__29_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__0 = (const lean_object*)&l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__0_value;
static const lean_string_object l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__1 = (const lean_object*)&l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_DeprecatedSyntax_formatReplacement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_DeprecatedSyntax_formatReplacement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences(lean_object* v_cat_4_, lean_object* v_stx_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_9_ = lean_unsigned_to_nat(0u);
v___x_10_ = lean_box(0);
v___x_11_ = 0;
v___x_12_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences___closed__0));
v___x_13_ = l_Lean_Syntax_Traverser_fromSyntax(v_stx_5_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_14_);
lean_ctor_set(v___x_15_, 2, v___x_10_);
lean_ctor_set(v___x_15_, 3, v___x_14_);
lean_ctor_set(v___x_15_, 4, v___x_14_);
lean_ctor_set(v___x_15_, 5, v___x_10_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*6, v___x_11_);
v___x_16_ = lean_st_mk_ref(v___x_15_);
v___x_17_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizeCategoryCore(v_cat_4_, v___x_9_, v___x_12_, v___x_16_, v_a_6_, v_a_7_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_30_; 
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_30_ == 0)
{
lean_object* v_unused_31_; 
v_unused_31_ = lean_ctor_get(v___x_17_, 0);
lean_dec(v_unused_31_);
v___x_19_ = v___x_17_;
v_isShared_20_ = v_isSharedCheck_30_;
goto v_resetjp_18_;
}
else
{
lean_dec(v___x_17_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_30_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v_minPrec_22_; lean_object* v_trailPrec_23_; lean_object* v_trailCat_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_21_ = lean_st_ref_get(v___x_16_);
lean_dec(v___x_16_);
v_minPrec_22_ = lean_ctor_get(v___x_21_, 3);
lean_inc(v_minPrec_22_);
v_trailPrec_23_ = lean_ctor_get(v___x_21_, 4);
lean_inc(v_trailPrec_23_);
v_trailCat_24_ = lean_ctor_get(v___x_21_, 5);
lean_inc(v_trailCat_24_);
lean_dec(v___x_21_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v_trailPrec_23_);
lean_ctor_set(v___x_25_, 1, v_trailCat_24_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v_minPrec_22_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_26_);
v___x_28_ = v___x_19_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
lean_dec(v___x_16_);
v_a_32_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_17_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_17_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences___boxed(lean_object* v_cat_40_, lean_object* v_stx_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences(v_cat_40_, v_stx_41_, v_a_42_, v_a_43_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_bindsAsTightly(lean_object* v_cat_46_, lean_object* v_stx_47_, lean_object* v_newStx_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
lean_inc(v_cat_46_);
v___x_52_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences(v_cat_46_, v_stx_47_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_snd_54_; lean_object* v_fst_55_; lean_object* v_fst_56_; lean_object* v_snd_57_; lean_object* v___x_58_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
lean_dec_ref_known(v___x_52_, 1);
v_snd_54_ = lean_ctor_get(v_a_53_, 1);
lean_inc(v_snd_54_);
v_fst_55_ = lean_ctor_get(v_a_53_, 0);
lean_inc(v_fst_55_);
lean_dec(v_a_53_);
v_fst_56_ = lean_ctor_get(v_snd_54_, 0);
lean_inc(v_fst_56_);
v_snd_57_ = lean_ctor_get(v_snd_54_, 1);
lean_inc(v_snd_57_);
lean_dec(v_snd_54_);
v___x_58_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_syntaxPrecedences(v_cat_46_, v_newStx_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_95_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_95_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_95_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_95_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
uint8_t v___y_64_; lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v_fst_76_; lean_object* v_snd_77_; uint8_t v___y_79_; lean_object* v___y_80_; uint8_t v___y_84_; lean_object* v_fst_87_; 
v_fst_76_ = lean_ctor_get(v_a_59_, 0);
lean_inc(v_fst_76_);
v_snd_77_ = lean_ctor_get(v_a_59_, 1);
lean_inc(v_snd_77_);
lean_dec(v_a_59_);
v_fst_87_ = lean_ctor_get(v_snd_77_, 0);
lean_inc(v_fst_87_);
if (lean_obj_tag(v_fst_87_) == 0)
{
uint8_t v___x_88_; 
lean_dec(v_snd_77_);
lean_dec(v_snd_57_);
lean_dec(v_fst_56_);
v___x_88_ = 1;
v___y_84_ = v___x_88_;
goto v___jp_83_;
}
else
{
if (lean_obj_tag(v_fst_56_) == 0)
{
uint8_t v___x_89_; 
lean_dec_ref_known(v_fst_87_, 1);
lean_dec(v_snd_77_);
lean_dec(v_snd_57_);
v___x_89_ = 0;
v___y_84_ = v___x_89_;
goto v___jp_83_;
}
else
{
lean_object* v_snd_90_; lean_object* v_val_91_; lean_object* v_val_92_; uint8_t v___x_93_; 
v_snd_90_ = lean_ctor_get(v_snd_77_, 1);
lean_inc(v_snd_90_);
lean_dec(v_snd_77_);
v_val_91_ = lean_ctor_get(v_fst_87_, 0);
lean_inc(v_val_91_);
lean_dec_ref_known(v_fst_87_, 1);
v_val_92_ = lean_ctor_get(v_fst_56_, 0);
lean_inc(v_val_92_);
lean_dec_ref_known(v_fst_56_, 1);
v___x_93_ = lean_name_eq(v_snd_90_, v_snd_57_);
lean_dec(v_snd_57_);
lean_dec(v_snd_90_);
if (v___x_93_ == 0)
{
lean_dec(v_val_92_);
lean_dec(v_val_91_);
v___y_84_ = v___x_93_;
goto v___jp_83_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = lean_nat_dec_le(v_val_92_, v_val_91_);
lean_dec(v_val_91_);
lean_dec(v_val_92_);
v___y_84_ = v___x_94_;
goto v___jp_83_;
}
}
}
v___jp_63_:
{
uint8_t v___x_67_; 
v___x_67_ = lean_nat_dec_le(v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec(v___y_65_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_box(v___x_67_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_68_);
v___x_70_ = v___x_61_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_72_ = lean_box(v___y_64_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_72_);
v___x_74_ = v___x_61_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
v___jp_78_:
{
if (lean_obj_tag(v_fst_76_) == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___y_64_ = v___y_79_;
v___y_65_ = v___y_80_;
v___y_66_ = v___x_81_;
goto v___jp_63_;
}
else
{
lean_object* v_val_82_; 
v_val_82_ = lean_ctor_get(v_fst_76_, 0);
lean_inc(v_val_82_);
lean_dec_ref_known(v_fst_76_, 1);
v___y_64_ = v___y_79_;
v___y_65_ = v___y_80_;
v___y_66_ = v_val_82_;
goto v___jp_63_;
}
}
v___jp_83_:
{
if (lean_obj_tag(v_fst_55_) == 0)
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Parser_maxPrec;
v___y_79_ = v___y_84_;
v___y_80_ = v___x_85_;
goto v___jp_78_;
}
else
{
lean_object* v_val_86_; 
v_val_86_ = lean_ctor_get(v_fst_55_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v_fst_55_, 1);
v___y_79_ = v___y_84_;
v___y_80_ = v_val_86_;
goto v___jp_78_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec(v_snd_57_);
lean_dec(v_fst_56_);
lean_dec(v_fst_55_);
v_a_96_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_58_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_58_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec(v_newStx_48_);
lean_dec(v_cat_46_);
v_a_104_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_52_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_52_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_bindsAsTightly___boxed(lean_object* v_cat_112_, lean_object* v_stx_113_, lean_object* v_newStx_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_bindsAsTightly(v_cat_112_, v_stx_113_, v_newStx_114_, v_a_115_, v_a_116_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_118_;
}
}
static lean_object* _init_l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__22(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__21));
v___x_165_ = l_String_toRawSubstring_x27(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement(lean_object* v_cat_180_, lean_object* v_stx_181_, lean_object* v_newStx_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_186_; uint8_t v___x_187_; uint8_t v_a_189_; 
v___x_186_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__1));
v___x_187_ = lean_name_eq(v_cat_180_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__29));
v___x_252_ = lean_name_eq(v_cat_180_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_stx_181_);
lean_dec(v_cat_180_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v_newStx_182_);
return v___x_253_;
}
else
{
goto v___jp_226_;
}
}
else
{
goto v___jp_226_;
}
v___jp_188_:
{
if (v___x_187_ == 0)
{
lean_object* v_ref_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_ref_190_ = lean_ctor_get(v_a_183_, 2);
v___x_191_ = l_Lean_SourceInfo_fromRef(v_ref_190_, v___x_187_);
v___x_192_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__6));
v___x_193_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__7));
lean_inc_n(v___x_191_, 5);
v___x_194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_191_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__9));
v___x_196_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__11));
v___x_197_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__13));
v___x_198_ = l_Lean_Syntax_node1(v___x_191_, v___x_197_, v_newStx_182_);
v___x_199_ = l_Lean_Syntax_node1(v___x_191_, v___x_196_, v___x_198_);
v___x_200_ = l_Lean_Syntax_node1(v___x_191_, v___x_195_, v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__14));
v___x_202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_191_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_Lean_Syntax_node3(v___x_191_, v___x_192_, v___x_194_, v___x_200_, v___x_202_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_toCold_205_; lean_object* v_ref_206_; lean_object* v_quotContext_207_; lean_object* v_currMacroScope_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_toCold_205_ = lean_ctor_get(v_a_183_, 0);
v_ref_206_ = lean_ctor_get(v_a_183_, 2);
v_quotContext_207_ = lean_ctor_get(v_toCold_205_, 8);
v_currMacroScope_208_ = lean_ctor_get(v_toCold_205_, 9);
v___x_209_ = l_Lean_SourceInfo_fromRef(v_ref_206_, v_a_189_);
v___x_210_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__16));
v___x_211_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__18));
v___x_212_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__7));
lean_inc_n(v___x_209_, 5);
v___x_213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_209_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__20));
v___x_215_ = lean_obj_once(&l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__22, &l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__22_once, _init_l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__22);
v___x_216_ = lean_box(0);
lean_inc(v_currMacroScope_208_);
lean_inc(v_quotContext_207_);
v___x_217_ = l_Lean_addMacroScope(v_quotContext_207_, v___x_216_, v_currMacroScope_208_);
v___x_218_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__27));
v___x_219_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_219_, 0, v___x_209_);
lean_ctor_set(v___x_219_, 1, v___x_215_);
lean_ctor_set(v___x_219_, 2, v___x_217_);
lean_ctor_set(v___x_219_, 3, v___x_218_);
v___x_220_ = l_Lean_Syntax_node1(v___x_209_, v___x_214_, v___x_219_);
v___x_221_ = l_Lean_Syntax_node2(v___x_209_, v___x_211_, v___x_213_, v___x_220_);
v___x_222_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__14));
v___x_223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_209_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_Syntax_node3(v___x_209_, v___x_210_, v___x_221_, v_newStx_182_, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
v___jp_226_:
{
lean_object* v___x_227_; 
lean_inc(v_newStx_182_);
v___x_227_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_bindsAsTightly(v_cat_180_, v_stx_181_, v_newStx_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_237_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_237_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_237_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
uint8_t v___x_232_; 
v___x_232_ = lean_unbox(v_a_228_);
if (v___x_232_ == 0)
{
uint8_t v___x_233_; 
lean_del_object(v___x_230_);
v___x_233_ = lean_unbox(v_a_228_);
lean_dec(v_a_228_);
v_a_189_ = v___x_233_;
goto v___jp_188_;
}
else
{
lean_object* v___x_235_; 
lean_dec(v_a_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v_newStx_182_);
v___x_235_ = v___x_230_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_newStx_182_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_250_; 
v_a_238_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_250_ == 0)
{
v___x_240_ = v___x_227_;
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_227_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_250_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
uint8_t v___x_242_; 
v___x_242_ = l_Lean_Exception_isInterrupt(v_a_238_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
lean_inc(v_a_238_);
v___x_243_ = l_Lean_Exception_isRuntime(v_a_238_);
if (v___x_243_ == 0)
{
lean_del_object(v___x_240_);
lean_dec(v_a_238_);
v_a_189_ = v___x_243_;
goto v___jp_188_;
}
else
{
lean_object* v___x_245_; 
lean_dec(v_newStx_182_);
if (v_isShared_241_ == 0)
{
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_238_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v___x_248_; 
lean_dec(v_newStx_182_);
if (v_isShared_241_ == 0)
{
v___x_248_ = v___x_240_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_238_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___boxed(lean_object* v_cat_254_, lean_object* v_stx_255_, lean_object* v_newStx_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement(v_cat_254_, v_stx_255_, v_newStx_256_, v_a_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_260_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__2(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
if (lean_obj_tag(v_x_262_) == 0)
{
uint8_t v___x_263_; 
v___x_263_ = 1;
return v___x_263_;
}
else
{
uint8_t v___x_264_; 
v___x_264_ = 0;
return v___x_264_;
}
}
else
{
if (lean_obj_tag(v_x_262_) == 0)
{
uint8_t v___x_265_; 
v___x_265_ = 0;
return v___x_265_;
}
else
{
lean_object* v_val_266_; lean_object* v_val_267_; uint8_t v___x_268_; 
v_val_266_ = lean_ctor_get(v_x_261_, 0);
v_val_267_ = lean_ctor_get(v_x_262_, 0);
v___x_268_ = l_Lean_Parser_instBEqError_beq(v_val_266_, v_val_267_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__2___boxed(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_instBEqOption_beq___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__2(v_x_269_, v_x_270_);
lean_dec(v_x_270_);
lean_dec(v_x_269_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___redArg(lean_object* v___x_273_, lean_object* v_right_274_, lean_object* v_a_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_snd_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_359_; 
v_snd_279_ = lean_ctor_get(v_a_275_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_359_ == 0)
{
lean_object* v_unused_360_; 
v_unused_360_ = lean_ctor_get(v_a_275_, 0);
lean_dec(v_unused_360_);
v___x_281_ = v_a_275_;
v_isShared_282_ = v_isSharedCheck_359_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_snd_279_);
lean_dec(v_a_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_359_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_283_ = lean_box(0);
v___x_284_ = lean_string_utf8_byte_size(v_snd_279_);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_nat_dec_eq(v___x_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
lean_inc_ref(v___x_273_);
lean_inc(v_snd_279_);
v___x_287_ = l_Lean_PrettyPrinter_Formatter_parseTokenCore(v_snd_279_, v___x_273_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v_stxStack_298_; lean_object* v_pos_299_; lean_object* v_errorMsg_300_; uint8_t v___x_301_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v_stxStack_298_ = lean_ctor_get(v_a_288_, 0);
lean_inc_ref(v_stxStack_298_);
v_pos_299_ = lean_ctor_get(v_a_288_, 2);
lean_inc(v_pos_299_);
v_errorMsg_300_ = lean_ctor_get(v_a_288_, 4);
lean_inc(v_errorMsg_300_);
lean_dec(v_a_288_);
v___x_301_ = l_instBEqOption_beq___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__2(v_errorMsg_300_, v___x_283_);
lean_dec(v_errorMsg_300_);
if (v___x_301_ == 0)
{
lean_dec(v_pos_299_);
lean_dec_ref(v_stxStack_298_);
goto v___jp_289_;
}
else
{
uint8_t v_decide_302_; 
v_decide_302_ = lean_nat_dec_eq(v_pos_299_, v___x_285_);
if (v_decide_302_ == 0)
{
uint8_t v_decide_303_; 
lean_del_object(v___x_281_);
v_decide_303_ = lean_nat_dec_eq(v_pos_299_, v___x_284_);
if (v_decide_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref(v_stxStack_298_);
lean_inc(v_snd_279_);
v___x_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_304_, 0, v_snd_279_);
lean_ctor_set(v___x_304_, 1, v___x_285_);
lean_ctor_set(v___x_304_, 2, v___x_284_);
v___x_305_ = l_String_Slice_pos_x21(v___x_304_, v_pos_299_);
lean_dec(v_pos_299_);
lean_dec_ref_known(v___x_304_, 3);
v___x_306_ = lean_string_utf8_extract_fast(v_snd_279_, v___x_305_, v___x_284_);
lean_dec(v___x_305_);
lean_dec(v_snd_279_);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_283_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v_a_275_ = v___x_307_;
goto _start;
}
else
{
lean_object* v___x_309_; 
lean_dec(v_pos_299_);
lean_inc_ref(v___x_273_);
lean_inc_ref(v_right_274_);
v___x_309_ = l_Lean_PrettyPrinter_Formatter_parseTokenCore(v_right_274_, v___x_273_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; uint8_t v___y_312_; lean_object* v_stxStack_334_; lean_object* v_errorMsg_335_; uint8_t v___x_336_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_stxStack_334_ = lean_ctor_get(v_a_310_, 0);
lean_inc_ref(v_stxStack_334_);
v_errorMsg_335_ = lean_ctor_get(v_a_310_, 4);
lean_inc(v_errorMsg_335_);
lean_dec(v_a_310_);
v___x_336_ = l_instBEqOption_beq___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__2(v_errorMsg_335_, v___x_283_);
lean_dec(v_errorMsg_335_);
if (v___x_336_ == 0)
{
lean_dec_ref(v_stxStack_334_);
v___y_312_ = v_decide_302_;
goto v___jp_311_;
}
else
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_334_);
lean_dec_ref(v_stxStack_334_);
v___x_338_ = l_Lean_Syntax_isIdent(v___x_337_);
lean_dec(v___x_337_);
v___y_312_ = v___x_338_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; 
v___x_313_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_298_);
lean_dec_ref(v_stxStack_298_);
v___x_314_ = l_Lean_Syntax_isIdent(v___x_313_);
lean_dec(v___x_313_);
lean_inc(v_snd_279_);
v___x_315_ = l_Lean_PrettyPrinter_Formatter_needsTokenSeparator(v_snd_279_, v_right_274_, v___x_314_, v___y_312_, v___x_273_, v___y_276_, v___y_277_);
lean_dec_ref(v_right_274_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_325_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_325_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_325_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_a_316_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_snd_279_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_snd_279_);
v_a_326_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_315_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_315_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v_stxStack_298_);
lean_dec(v_snd_279_);
lean_dec_ref(v_right_274_);
lean_dec_ref(v___x_273_);
v_a_339_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_309_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_309_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
else
{
lean_dec(v_pos_299_);
lean_dec_ref(v_stxStack_298_);
goto v___jp_289_;
}
}
v___jp_289_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_290_ = lean_unsigned_to_nat(1u);
lean_inc(v_snd_279_);
v___x_291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_291_, 0, v_snd_279_);
lean_ctor_set(v___x_291_, 1, v___x_285_);
lean_ctor_set(v___x_291_, 2, v___x_284_);
v___x_292_ = l_String_Slice_Pos_nextn(v___x_291_, v___x_285_, v___x_290_);
lean_dec_ref_known(v___x_291_, 3);
v___x_293_ = lean_string_utf8_extract_fast(v_snd_279_, v___x_292_, v___x_284_);
lean_dec(v___x_292_);
lean_dec(v_snd_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_293_);
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_295_ = v___x_281_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_297_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
v_a_275_ = v___x_295_;
goto _start;
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_del_object(v___x_281_);
lean_dec(v_snd_279_);
lean_dec_ref(v_right_274_);
lean_dec_ref(v___x_273_);
v_a_347_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_287_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_287_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v___x_356_; 
lean_dec_ref(v_right_274_);
lean_dec_ref(v___x_273_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_356_ = v___x_281_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_snd_279_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___redArg___boxed(lean_object* v___x_361_, lean_object* v_right_362_, lean_object* v_a_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___redArg(v___x_361_, v_right_362_, v_a_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__1(lean_object* v_s_368_, lean_object* v_pos_369_){
_start:
{
lean_object* v_str_370_; lean_object* v_startInclusive_371_; lean_object* v_endExclusive_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v_decide_376_; 
v_str_370_ = lean_ctor_get(v_s_368_, 0);
v_startInclusive_371_ = lean_ctor_get(v_s_368_, 1);
v_endExclusive_372_ = lean_ctor_get(v_s_368_, 2);
v___x_373_ = lean_nat_add(v_startInclusive_371_, v_pos_369_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_nat_sub(v_endExclusive_372_, v___x_373_);
v_decide_376_ = lean_nat_dec_eq(v___x_374_, v___x_375_);
lean_dec(v___x_375_);
if (v_decide_376_ == 0)
{
uint32_t v___x_377_; uint32_t v___x_378_; uint8_t v___x_379_; 
v___x_377_ = lean_string_utf8_get_fast(v_str_370_, v___x_373_);
v___x_378_ = 32;
v___x_379_ = lean_uint32_dec_eq(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
uint32_t v___x_380_; uint8_t v___x_381_; 
v___x_380_ = 9;
v___x_381_ = lean_uint32_dec_eq(v___x_377_, v___x_380_);
if (v___x_381_ == 0)
{
uint32_t v___x_382_; uint8_t v___x_383_; 
v___x_382_ = 13;
v___x_383_ = lean_uint32_dec_eq(v___x_377_, v___x_382_);
if (v___x_383_ == 0)
{
uint32_t v___x_384_; uint8_t v___x_385_; 
v___x_384_ = 10;
v___x_385_ = lean_uint32_dec_eq(v___x_377_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_386_ = lean_string_utf8_next_fast(v_str_370_, v___x_373_);
v___x_387_ = lean_nat_sub(v___x_386_, v___x_373_);
lean_dec(v___x_373_);
v___x_388_ = lean_nat_add(v_pos_369_, v___x_387_);
lean_dec(v___x_387_);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_pos_369_, v___x_389_);
v___x_391_ = lean_nat_dec_le(v___x_390_, v___x_388_);
lean_dec(v___x_390_);
if (v___x_391_ == 0)
{
lean_dec(v___x_388_);
return v_pos_369_;
}
else
{
lean_dec(v_pos_369_);
v_pos_369_ = v___x_388_;
goto _start;
}
}
else
{
lean_dec(v___x_373_);
return v_pos_369_;
}
}
else
{
lean_dec(v___x_373_);
return v_pos_369_;
}
}
else
{
lean_dec(v___x_373_);
return v_pos_369_;
}
}
else
{
lean_dec(v___x_373_);
return v_pos_369_;
}
}
else
{
lean_dec(v___x_373_);
return v_pos_369_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__1___boxed(lean_object* v_s_393_, lean_object* v_pos_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__1(v_s_393_, v_pos_394_);
lean_dec_ref(v_s_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__0(lean_object* v_s_396_, lean_object* v_pos_397_){
_start:
{
lean_object* v_str_398_; lean_object* v_startInclusive_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v_decide_403_; 
v_str_398_ = lean_ctor_get(v_s_396_, 0);
v_startInclusive_399_ = lean_ctor_get(v_s_396_, 1);
v___x_400_ = lean_nat_add(v_startInclusive_399_, v_pos_397_);
v___x_401_ = lean_nat_sub(v___x_400_, v_startInclusive_399_);
v___x_402_ = lean_unsigned_to_nat(0u);
v_decide_403_ = lean_nat_dec_eq(v___x_401_, v___x_402_);
if (v_decide_403_ == 0)
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint32_t v___x_409_; uint32_t v___x_410_; uint8_t v___x_411_; 
lean_inc(v_startInclusive_399_);
lean_inc_ref(v_str_398_);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_str_398_);
lean_ctor_set(v___x_404_, 1, v_startInclusive_399_);
lean_ctor_set(v___x_404_, 2, v___x_400_);
v___x_405_ = lean_unsigned_to_nat(1u);
v___x_406_ = lean_nat_sub(v___x_401_, v___x_405_);
lean_dec(v___x_401_);
v___x_407_ = l_String_Slice_posLE(v___x_404_, v___x_406_);
lean_dec_ref_known(v___x_404_, 3);
v___x_408_ = lean_nat_add(v_startInclusive_399_, v___x_407_);
v___x_409_ = lean_string_utf8_get_fast(v_str_398_, v___x_408_);
lean_dec(v___x_408_);
v___x_410_ = 32;
v___x_411_ = lean_uint32_dec_eq(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
uint32_t v___x_412_; uint8_t v___x_413_; 
v___x_412_ = 9;
v___x_413_ = lean_uint32_dec_eq(v___x_409_, v___x_412_);
if (v___x_413_ == 0)
{
uint32_t v___x_414_; uint8_t v___x_415_; 
v___x_414_ = 13;
v___x_415_ = lean_uint32_dec_eq(v___x_409_, v___x_414_);
if (v___x_415_ == 0)
{
uint32_t v___x_416_; uint8_t v___x_417_; 
v___x_416_ = 10;
v___x_417_ = lean_uint32_dec_eq(v___x_409_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_nat_add(v___x_407_, v___x_405_);
v___x_419_ = lean_nat_dec_le(v___x_418_, v_pos_397_);
lean_dec(v___x_418_);
if (v___x_419_ == 0)
{
lean_dec(v___x_407_);
return v_pos_397_;
}
else
{
lean_dec(v_pos_397_);
v_pos_397_ = v___x_407_;
goto _start;
}
}
else
{
lean_dec(v___x_407_);
return v_pos_397_;
}
}
else
{
lean_dec(v___x_407_);
return v_pos_397_;
}
}
else
{
lean_dec(v___x_407_);
return v_pos_397_;
}
}
else
{
lean_dec(v___x_407_);
return v_pos_397_;
}
}
else
{
lean_dec(v___x_401_);
lean_dec(v___x_400_);
return v_pos_397_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__0___boxed(lean_object* v_s_421_, lean_object* v_pos_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__0(v_s_421_, v_pos_422_);
lean_dec_ref(v_s_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween(lean_object* v_left_424_, lean_object* v_right_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_str_433_; lean_object* v_startInclusive_434_; lean_object* v_endExclusive_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_left_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_str_433_ = lean_ctor_get(v_left_424_, 0);
v_startInclusive_434_ = lean_ctor_get(v_left_424_, 1);
v_endExclusive_435_ = lean_ctor_get(v_left_424_, 2);
v___x_436_ = lean_nat_sub(v_endExclusive_435_, v_startInclusive_434_);
v___x_437_ = l_String_Slice_Pos_revSkipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__0(v_left_424_, v___x_436_);
v___x_438_ = lean_nat_add(v_startInclusive_434_, v___x_437_);
lean_dec(v___x_437_);
v_left_439_ = lean_string_utf8_extract_fast(v_str_433_, v___x_438_, v_endExclusive_435_);
lean_dec(v___x_438_);
v___x_440_ = lean_string_utf8_byte_size(v_left_439_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_nat_dec_eq(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v_str_443_; lean_object* v_startInclusive_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_right_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_str_443_ = lean_ctor_get(v_right_425_, 0);
v_startInclusive_444_ = lean_ctor_get(v_right_425_, 1);
v___x_445_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__1(v_right_425_, v___x_441_);
v___x_446_ = lean_nat_add(v_startInclusive_444_, v___x_445_);
lean_dec(v___x_445_);
v_right_447_ = lean_string_utf8_extract_fast(v_str_443_, v_startInclusive_444_, v___x_446_);
lean_dec(v___x_446_);
v___x_448_ = lean_string_utf8_byte_size(v_right_447_);
v___x_449_ = lean_nat_dec_eq(v___x_448_, v___x_441_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v_env_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_450_ = lean_st_ref_get(v_a_427_);
v_env_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc_ref(v_env_451_);
lean_dec(v___x_450_);
v___x_452_ = l_Lean_Parser_getTokenTable(v_env_451_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_left_439_);
v___x_455_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___redArg(v___x_452_, v_right_447_, v___x_454_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_469_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_469_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_469_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_469_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_fst_460_; 
v_fst_460_ = lean_ctor_get(v_a_456_, 0);
lean_inc(v_fst_460_);
lean_dec(v_a_456_);
if (lean_obj_tag(v_fst_460_) == 0)
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_box(v___x_449_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_461_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
else
{
lean_object* v_val_465_; lean_object* v___x_467_; 
v_val_465_ = lean_ctor_get(v_fst_460_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v_fst_460_, 1);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v_val_465_);
v___x_467_ = v___x_458_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_val_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
v_a_470_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_455_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_455_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_dec_ref(v_right_447_);
lean_dec_ref(v_left_439_);
goto v___jp_429_;
}
}
else
{
lean_dec_ref(v_left_439_);
goto v___jp_429_;
}
v___jp_429_:
{
uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = 0;
v___x_431_ = lean_box(v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween___boxed(lean_object* v_left_478_, lean_object* v_right_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween(v_left_478_, v_right_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec_ref(v_right_479_);
lean_dec_ref(v_left_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3(lean_object* v___x_484_, lean_object* v_right_485_, lean_object* v_inst_486_, lean_object* v_a_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___redArg(v___x_484_, v_right_485_, v_a_487_, v___y_488_, v___y_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3___boxed(lean_object* v___x_492_, lean_object* v_right_493_, lean_object* v_inst_494_, lean_object* v_a_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween_spec__3(v___x_492_, v_right_493_, v_inst_494_, v_a_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DeprecatedSyntax_formatReplacement(lean_object* v_cat_502_, lean_object* v_stx_503_, lean_object* v_newStx_504_, lean_object* v_range_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___x_540_; 
lean_inc(v_stx_503_);
lean_inc(v_cat_502_);
v___x_540_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement(v_cat_502_, v_stx_503_, v_newStx_504_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_toCold_541_; lean_object* v_a_542_; lean_object* v_fileMap_543_; lean_object* v___x_544_; lean_object* v_fst_545_; lean_object* v_snd_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_608_; 
v_toCold_541_ = lean_ctor_get(v_a_506_, 0);
v_a_542_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_540_, 1);
v_fileMap_543_ = lean_ctor_get(v_toCold_541_, 1);
lean_inc_ref(v_range_505_);
lean_inc_ref(v_fileMap_543_);
v___x_544_ = l_Lean_Meta_Tactic_TryThis_getIndentAndColumn(v_fileMap_543_, v_range_505_);
v_fst_545_ = lean_ctor_get(v___x_544_, 0);
v_snd_546_ = lean_ctor_get(v___x_544_, 1);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_608_ == 0)
{
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_608_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_snd_546_);
lean_inc(v_fst_545_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_608_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
lean_inc(v_a_542_);
lean_inc(v_cat_502_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v_a_542_);
lean_ctor_set(v___x_548_, 0, v_cat_502_);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_cat_502_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_a_542_);
v___x_551_ = v_reuseFailAlloc_607_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_box(0);
v___x_553_ = l_Lean_Meta_Tactic_TryThis_SuggestionText_prettyExtra(v___x_551_, v___x_552_, v_fst_545_, v_snd_546_, v_a_506_, v_a_507_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_606_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_606_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_606_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_606_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_source_558_; lean_object* v_start_559_; lean_object* v_stop_560_; lean_object* v_text_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_source_558_ = lean_ctor_get(v_fileMap_543_, 0);
v_start_559_ = lean_ctor_get(v_range_505_, 0);
lean_inc(v_start_559_);
v_stop_560_ = lean_ctor_get(v_range_505_, 1);
lean_inc(v_stop_560_);
lean_dec_ref(v_range_505_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_string_utf8_byte_size(v_source_558_);
lean_inc_ref_n(v_source_558_, 2);
v___x_588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_588_, 0, v_source_558_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
lean_ctor_set(v___x_588_, 2, v___x_587_);
v___x_589_ = l_String_Slice_pos_x21(v___x_588_, v_start_559_);
lean_dec(v_start_559_);
lean_dec_ref_known(v___x_588_, 3);
v___x_590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_590_, 0, v_source_558_);
lean_ctor_set(v___x_590_, 1, v___x_586_);
lean_ctor_set(v___x_590_, 2, v___x_589_);
v___x_591_ = lean_string_utf8_byte_size(v_a_554_);
lean_inc(v_a_554_);
v___x_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_592_, 0, v_a_554_);
lean_ctor_set(v___x_592_, 1, v___x_586_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
v___x_593_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween(v___x_590_, v___x_592_, v_a_506_, v_a_507_);
lean_dec_ref_known(v___x_592_, 3);
lean_dec_ref_known(v___x_590_, 3);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; uint8_t v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = lean_unbox(v_a_594_);
lean_dec(v_a_594_);
if (v___x_595_ == 0)
{
v_text_562_ = v_a_554_;
v___y_563_ = v_a_506_;
v___y_564_ = v_a_507_;
goto v___jp_561_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__0));
v___x_597_ = lean_string_append(v___x_596_, v_a_554_);
lean_dec(v_a_554_);
v_text_562_ = v___x_597_;
v___y_563_ = v_a_506_;
v___y_564_ = v_a_507_;
goto v___jp_561_;
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_stop_560_);
lean_del_object(v___x_556_);
lean_dec(v_a_554_);
lean_dec(v_a_542_);
lean_dec(v_stx_503_);
lean_dec(v_cat_502_);
v_a_598_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_593_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_593_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
v___jp_561_:
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = l_Lean_Syntax_getTrailingSize(v_stx_503_);
lean_dec(v_stx_503_);
v___x_567_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
lean_dec(v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_568_ = lean_string_utf8_byte_size(v_source_558_);
lean_inc_ref_n(v_source_558_, 2);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v_source_558_);
lean_ctor_set(v___x_569_, 1, v___x_565_);
lean_ctor_set(v___x_569_, 2, v___x_568_);
v___x_570_ = l_String_Slice_pos_x21(v___x_569_, v_stop_560_);
lean_dec(v_stop_560_);
lean_dec_ref_known(v___x_569_, 3);
lean_inc(v___x_570_);
v___x_571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_571_, 0, v_source_558_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
lean_ctor_set(v___x_571_, 2, v___x_568_);
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_parenthesizeReplacement___closed__1));
v___x_573_ = lean_name_eq(v_cat_502_, v___x_572_);
lean_dec(v_cat_502_);
if (v___x_573_ == 0)
{
lean_dec(v___x_570_);
lean_del_object(v___x_556_);
lean_dec(v_a_542_);
v___y_510_ = v___x_565_;
v___y_511_ = v_text_562_;
v___y_512_ = v___y_564_;
v___y_513_ = v___y_563_;
v___y_514_ = v___x_571_;
goto v___jp_509_;
}
else
{
uint8_t v___x_574_; 
v___x_574_ = l_Lean_Syntax_isIdent(v_a_542_);
lean_dec(v_a_542_);
if (v___x_574_ == 0)
{
lean_dec(v___x_570_);
lean_del_object(v___x_556_);
v___y_510_ = v___x_565_;
v___y_511_ = v_text_562_;
v___y_512_ = v___y_564_;
v___y_513_ = v___y_563_;
v___y_514_ = v___x_571_;
goto v___jp_509_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_sub(v___x_568_, v___x_570_);
v___x_577_ = lean_nat_dec_le(v___x_575_, v___x_576_);
lean_dec(v___x_576_);
if (v___x_577_ == 0)
{
lean_dec(v___x_570_);
lean_del_object(v___x_556_);
v___y_510_ = v___x_565_;
v___y_511_ = v_text_562_;
v___y_512_ = v___y_564_;
v___y_513_ = v___y_563_;
v___y_514_ = v___x_571_;
goto v___jp_509_;
}
else
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = ((lean_object*)(l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__1));
v___x_579_ = lean_string_memcmp(v_source_558_, v___x_578_, v___x_570_, v___x_565_, v___x_575_);
lean_dec(v___x_570_);
if (v___x_579_ == 0)
{
lean_del_object(v___x_556_);
v___y_510_ = v___x_565_;
v___y_511_ = v_text_562_;
v___y_512_ = v___y_564_;
v___y_513_ = v___y_563_;
v___y_514_ = v___x_571_;
goto v___jp_509_;
}
else
{
lean_object* v___x_581_; 
lean_dec_ref_known(v___x_571_, 3);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_text_562_);
v___x_581_ = v___x_556_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_text_562_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
else
{
lean_object* v___x_584_; 
lean_dec(v_stop_560_);
lean_dec(v_a_542_);
lean_dec(v_cat_502_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v_text_562_);
v___x_584_ = v___x_556_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_text_562_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
else
{
lean_dec(v_a_542_);
lean_dec_ref(v_range_505_);
lean_dec(v_stx_503_);
lean_dec(v_cat_502_);
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_range_505_);
lean_dec(v_stx_503_);
lean_dec(v_cat_502_);
v_a_609_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_540_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_540_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
v___jp_509_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_string_utf8_byte_size(v___y_511_);
lean_inc_ref(v___y_511_);
v___x_516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_516_, 0, v___y_511_);
lean_ctor_set(v___x_516_, 1, v___y_510_);
lean_ctor_set(v___x_516_, 2, v___x_515_);
v___x_517_ = l___private_Lean_Elab_DeprecatedSyntax_FormatReplacement_0__Lean_Elab_DeprecatedSyntax_needsSpaceBetween(v___x_516_, v___y_514_, v___y_513_, v___y_512_);
lean_dec_ref(v___y_514_);
lean_dec_ref_known(v___x_516_, 3);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_531_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_531_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_531_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_531_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
uint8_t v___x_522_; 
v___x_522_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_522_ == 0)
{
lean_object* v___x_524_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___y_511_);
v___x_524_ = v___x_520_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___y_511_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_526_ = ((lean_object*)(l_Lean_Elab_DeprecatedSyntax_formatReplacement___closed__0));
v___x_527_ = lean_string_append(v___y_511_, v___x_526_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_527_);
v___x_529_ = v___x_520_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v___y_511_);
v_a_532_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_517_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_517_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_DeprecatedSyntax_formatReplacement___boxed(lean_object* v_cat_617_, lean_object* v_stx_618_, lean_object* v_newStx_619_, lean_object* v_range_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Elab_DeprecatedSyntax_formatReplacement(v_cat_617_, v_stx_618_, v_newStx_619_, v_range_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
return v_res_624_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Meta_TryThis(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeprecatedSyntax_FormatReplacement(builtin);
}
#ifdef __cplusplus
}
#endif
