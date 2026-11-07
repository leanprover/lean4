// Lean compiler output
// Module: Lean.Data.Markdown.Inline
// Imports: public import Init.Data.Hashable public import Std.Data.HashMap public import Init.Data.String.Subslice public import Init.Data.String.Lemmas.Order import Init.Data.String.OrderInstances import Init.Data.String.Iterate import Init.While import Init.Data.String.TakeDrop public import Init.Data.String.FindPos import Lean.Data.Markdown.Unicode.CaseFolding import Lean.Data.Markdown.Text public import Lean.Data.Markdown.Lines
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Markdown_decodeText(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Lines_singleton___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_span___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_Lines_extent___redArg(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Markdown_pushCaseFolded(lean_object*, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Markdown_Lines_text(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lean_Markdown_Lines_first___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_instInhabitedExtensions_default;
LEAN_EXPORT uint8_t l_Lean_Markdown_instInhabitedExtensions;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTitle_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTitle(lean_object*);
static const lean_string_object l_Lean_Markdown_LinkTitle_text___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Markdown_LinkTitle_text___closed__0 = (const lean_object*)&l_Lean_Markdown_LinkTitle_text___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTitle_text(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTitle_text___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_text(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_text___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef___boxed(lean_object*);
static const lean_string_object l_Lean_Markdown_instInhabitedExternalRef_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Markdown_instInhabitedExternalRef_default___closed__0 = (const lean_object*)&l_Lean_Markdown_instInhabitedExternalRef_default___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_instInhabitedExternalRef_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_instInhabitedExternalRef_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Markdown_instInhabitedExternalRef_default___closed__1 = (const lean_object*)&l_Lean_Markdown_instInhabitedExternalRef_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instInhabitedExternalRef_default = (const lean_object*)&l_Lean_Markdown_instInhabitedExternalRef_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instInhabitedExternalRef = (const lean_object*)&l_Lean_Markdown_instInhabitedExternalRef_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_inDocument_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_inDocument_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_inDocument_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_external_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_external_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_external_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_destination(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_destination___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_title_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_title_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_full_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_full_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_collapsed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_collapsed_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_collapsed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_shortcut_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_shortcut_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_shortcut_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_inline_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_inline_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_inline_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_reference_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_reference_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_reference_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_MathContent_text_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_MathContent_text_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Markdown_MathContent_text___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Markdown_MathContent_text___lam__0___closed__0 = (const lean_object*)&l_Lean_Markdown_MathContent_text___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_MathContent_text___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_MathContent_text___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___at___00Lean_Markdown_MathContent_text_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_MathContent_text(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___at___00Lean_Markdown_MathContent_text_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_InlineCodeContent_text_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_InlineCodeContent_text_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCodeContent_text(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCodeContent_text___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_text_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_text_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_code_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_code_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_code_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_italic_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_italic_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_italic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_bold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_bold_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_bold_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_link_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_link_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_link_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_image_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_image_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_image_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_hardBreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_hardBreak_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_hardBreak_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_autolink_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_autolink_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_autolink_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_math_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_math_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_math_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_html_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_html_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_html_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_softBreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_softBreak_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_softBreak_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_escape_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_escape_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_escape_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_entity_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_entity_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_entity_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_extent___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_extent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_extent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destinationSource_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destinationSource_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destinationSource_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destination(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destination___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_title_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_title_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extent___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Inline_0__Lean_Markdown_Inline_plainText_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_Inline_plainText_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_plainText(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_plainText___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_Inline_plainText_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqLinkLabel_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqLinkLabel_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instBEqLinkLabel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instBEqLinkLabel_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instBEqLinkLabel___closed__0 = (const lean_object*)&l_Lean_Markdown_instBEqLinkLabel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instBEqLinkLabel = (const lean_object*)&l_Lean_Markdown_instBEqLinkLabel___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableLinkLabel_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableLinkLabel_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Markdown_instHashableLinkLabel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instHashableLinkLabel_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instHashableLinkLabel___closed__0 = (const lean_object*)&l_Lean_Markdown_instHashableLinkLabel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instHashableLinkLabel = (const lean_object*)&l_Lean_Markdown_instHashableLinkLabel___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Markdown_instReprLinkLabel_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__7;
static const lean_string_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__9;
static lean_once_cell_t l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__10;
static const lean_ctor_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprLinkLabel_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprLinkLabel_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Markdown_instReprLinkLabel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Markdown_instReprLinkLabel_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Markdown_instReprLinkLabel___closed__0 = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Markdown_instReprLinkLabel = (const lean_object*)&l_Lean_Markdown_instReprLinkLabel___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___lam__0(uint32_t, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_normalizeLabel_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_normalizeLabel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Markdown_normalizeLabel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_normalizeLabel___closed__0 = (const lean_object*)&l_Lean_Markdown_normalizeLabel___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_normalizeLabel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_instInhabitedExternalRef_default___closed__0_value),((lean_object*)&l_Lean_Markdown_normalizeLabel___closed__0_value)}};
static const lean_object* l_Lean_Markdown_normalizeLabel___closed__1 = (const lean_object*)&l_Lean_Markdown_normalizeLabel___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_normalizeLabel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_normalizeLabel___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkLabel_ofString(lean_object*);
static uint8_t _init_l_Lean_Markdown_instInhabitedExtensions_default(void){
_start:
{
uint8_t v___x_1_; 
v___x_1_ = 0;
return v___x_1_;
}
}
static uint8_t _init_l_Lean_Markdown_instInhabitedExtensions(void){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTitle_default(lean_object* v_s_3_){
_start:
{
lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_15_; 
v_startInclusive_4_ = lean_ctor_get(v_s_3_, 1);
v_endExclusive_5_ = lean_ctor_get(v_s_3_, 2);
v_isSharedCheck_15_ = !lean_is_exclusive(v_s_3_);
if (v_isSharedCheck_15_ == 0)
{
lean_object* v_unused_16_; 
v_unused_16_ = lean_ctor_get(v_s_3_, 0);
lean_dec(v_unused_16_);
v___x_7_ = v_s_3_;
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_endExclusive_5_);
lean_inc(v_startInclusive_4_);
lean_dec(v_s_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_15_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_13_; 
v___x_9_ = lean_nat_sub(v_endExclusive_5_, v_startInclusive_4_);
lean_dec(v_startInclusive_4_);
lean_dec(v_endExclusive_5_);
lean_inc(v___x_9_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
lean_inc_ref_n(v___x_10_, 2);
v___x_11_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_10_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v___x_10_);
lean_ctor_set(v___x_7_, 1, v___x_11_);
lean_ctor_set(v___x_7_, 0, v___x_10_);
v___x_13_ = v___x_7_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_14_; 
v_reuseFailAlloc_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_14_, 0, v___x_10_);
lean_ctor_set(v_reuseFailAlloc_14_, 1, v___x_11_);
lean_ctor_set(v_reuseFailAlloc_14_, 2, v___x_10_);
v___x_13_ = v_reuseFailAlloc_14_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTitle(lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Markdown_instInhabitedLinkTitle_default(v_a_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTitle_text(lean_object* v_s_20_, lean_object* v_t_21_){
_start:
{
lean_object* v_content_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v_content_22_ = lean_ctor_get(v_t_21_, 1);
lean_inc_ref(v_content_22_);
lean_dec_ref(v_t_21_);
v___x_23_ = ((lean_object*)(l_Lean_Markdown_LinkTitle_text___closed__0));
v___x_24_ = l_Lean_Markdown_Lines_text(v_s_20_, v_content_22_, v___x_23_);
v___x_25_ = l_Lean_Markdown_decodeText(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTitle_text___boxed(lean_object* v_s_26_, lean_object* v_t_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Markdown_LinkTitle_text(v_s_26_, v_t_27_);
lean_dec_ref(v_s_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination_default(lean_object* v_s_29_){
_start:
{
lean_object* v_startInclusive_30_; lean_object* v_endExclusive_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_startInclusive_30_ = lean_ctor_get(v_s_29_, 1);
v_endExclusive_31_ = lean_ctor_get(v_s_29_, 2);
v___x_32_ = lean_box(0);
v___x_33_ = lean_nat_sub(v_endExclusive_31_, v_startInclusive_30_);
lean_inc(v___x_33_);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_33_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_32_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination_default___boxed(lean_object* v_s_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Markdown_instInhabitedLinkDestination_default(v_s_36_);
lean_dec_ref(v_s_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination(lean_object* v_a_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Markdown_instInhabitedLinkDestination_default(v_a_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkDestination___boxed(lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Markdown_instInhabitedLinkDestination(v_a_40_);
lean_dec_ref(v_a_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_text(lean_object* v_s_42_, lean_object* v_d_43_){
_start:
{
lean_object* v_url_44_; lean_object* v_startInclusive_45_; lean_object* v_endExclusive_46_; lean_object* v_str_47_; lean_object* v_startInclusive_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_url_44_ = lean_ctor_get(v_d_43_, 1);
v_startInclusive_45_ = lean_ctor_get(v_url_44_, 0);
v_endExclusive_46_ = lean_ctor_get(v_url_44_, 1);
v_str_47_ = lean_ctor_get(v_s_42_, 0);
v_startInclusive_48_ = lean_ctor_get(v_s_42_, 1);
v___x_49_ = lean_nat_add(v_startInclusive_48_, v_startInclusive_45_);
v___x_50_ = lean_nat_add(v_startInclusive_48_, v_endExclusive_46_);
v___x_51_ = lean_string_utf8_extract_fast(v_str_47_, v___x_49_, v___x_50_);
lean_dec(v___x_50_);
lean_dec(v___x_49_);
v___x_52_ = l_Lean_Markdown_decodeText(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_text___boxed(lean_object* v_s_53_, lean_object* v_d_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Markdown_LinkDestination_text(v_s_53_, v_d_54_);
lean_dec_ref(v_d_54_);
lean_dec_ref(v_s_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef_default(lean_object* v_s_56_){
_start:
{
lean_object* v_startInclusive_57_; lean_object* v_endExclusive_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_startInclusive_57_ = lean_ctor_get(v_s_56_, 1);
v_endExclusive_58_ = lean_ctor_get(v_s_56_, 2);
v___x_59_ = lean_nat_sub(v_endExclusive_58_, v_startInclusive_57_);
lean_inc(v___x_59_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
lean_inc_ref_n(v___x_60_, 3);
v___x_61_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_60_);
v___x_62_ = l_Lean_Markdown_instInhabitedLinkDestination_default(v_s_56_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_64_, 0, v___x_60_);
lean_ctor_set(v___x_64_, 1, v___x_61_);
lean_ctor_set(v___x_64_, 2, v___x_60_);
lean_ctor_set(v___x_64_, 3, v___x_60_);
lean_ctor_set(v___x_64_, 4, v___x_62_);
lean_ctor_set(v___x_64_, 5, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef_default___boxed(lean_object* v_s_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Markdown_instInhabitedRefDef_default(v_s_65_);
lean_dec_ref(v_s_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef(lean_object* v_a_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Markdown_instInhabitedRefDef_default(v_a_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefDef___boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Markdown_instInhabitedRefDef(v_a_69_);
lean_dec_ref(v_a_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl___redArg(lean_object* v_x_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_tag_nat(v_x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl___redArg___boxed(lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Markdown_RefTarget_ctorIdx___impl___redArg(v_x_80_);
lean_dec_ref(v_x_80_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl(lean_object* v_s_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_tag_nat(v_x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorIdx___impl___boxed(lean_object* v_s_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Markdown_RefTarget_ctorIdx___impl(v_s_85_, v_x_86_);
lean_dec_ref(v_x_86_);
lean_dec_ref(v_s_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorElim___redArg(lean_object* v_t_88_, lean_object* v_k_89_){
_start:
{
lean_object* v_definition_90_; lean_object* v___x_91_; 
v_definition_90_ = lean_ctor_get(v_t_88_, 0);
lean_inc_ref(v_definition_90_);
lean_dec_ref(v_t_88_);
v___x_91_ = lean_apply_1(v_k_89_, v_definition_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorElim(lean_object* v_s_92_, lean_object* v_motive_93_, lean_object* v_ctorIdx_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_k_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Markdown_RefTarget_ctorElim___redArg(v_t_95_, v_k_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_ctorElim___boxed(lean_object* v_s_99_, lean_object* v_motive_100_, lean_object* v_ctorIdx_101_, lean_object* v_t_102_, lean_object* v_h_103_, lean_object* v_k_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Markdown_RefTarget_ctorElim(v_s_99_, v_motive_100_, v_ctorIdx_101_, v_t_102_, v_h_103_, v_k_104_);
lean_dec(v_ctorIdx_101_);
lean_dec_ref(v_s_99_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_inDocument_elim___redArg(lean_object* v_t_106_, lean_object* v_inDocument_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Markdown_RefTarget_ctorElim___redArg(v_t_106_, v_inDocument_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_inDocument_elim(lean_object* v_s_109_, lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_inDocument_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Markdown_RefTarget_ctorElim___redArg(v_t_111_, v_inDocument_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_inDocument_elim___boxed(lean_object* v_s_115_, lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_inDocument_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Markdown_RefTarget_inDocument_elim(v_s_115_, v_motive_116_, v_t_117_, v_h_118_, v_inDocument_119_);
lean_dec_ref(v_s_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_external_elim___redArg(lean_object* v_t_121_, lean_object* v_external_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Markdown_RefTarget_ctorElim___redArg(v_t_121_, v_external_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_external_elim(lean_object* v_s_124_, lean_object* v_motive_125_, lean_object* v_t_126_, lean_object* v_h_127_, lean_object* v_external_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Markdown_RefTarget_ctorElim___redArg(v_t_126_, v_external_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_external_elim___boxed(lean_object* v_s_130_, lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_external_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Markdown_RefTarget_external_elim(v_s_130_, v_motive_131_, v_t_132_, v_h_133_, v_external_134_);
lean_dec_ref(v_s_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget_default(lean_object* v_s_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = l_Lean_Markdown_instInhabitedRefDef_default(v_s_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget_default___boxed(lean_object* v_s_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Markdown_instInhabitedRefTarget_default(v_s_139_);
lean_dec_ref(v_s_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget(lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Markdown_instInhabitedRefTarget_default(v_a_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedRefTarget___boxed(lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Markdown_instInhabitedRefTarget(v_a_143_);
lean_dec_ref(v_a_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_destination(lean_object* v_s_145_, lean_object* v_x_146_){
_start:
{
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v_definition_147_; lean_object* v_destination_148_; lean_object* v___x_149_; 
v_definition_147_ = lean_ctor_get(v_x_146_, 0);
v_destination_148_ = lean_ctor_get(v_definition_147_, 4);
v___x_149_ = l_Lean_Markdown_LinkDestination_text(v_s_145_, v_destination_148_);
return v___x_149_;
}
else
{
lean_object* v_ref_150_; lean_object* v_destination_151_; 
v_ref_150_ = lean_ctor_get(v_x_146_, 0);
v_destination_151_ = lean_ctor_get(v_ref_150_, 0);
lean_inc_ref(v_destination_151_);
return v_destination_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_destination___boxed(lean_object* v_s_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Markdown_RefTarget_destination(v_s_152_, v_x_153_);
lean_dec_ref(v_x_153_);
lean_dec_ref(v_s_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_title_x3f(lean_object* v_s_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v_definition_157_; lean_object* v_title_x3f_158_; 
v_definition_157_ = lean_ctor_get(v_x_156_, 0);
lean_inc_ref(v_definition_157_);
lean_dec_ref_known(v_x_156_, 1);
v_title_x3f_158_ = lean_ctor_get(v_definition_157_, 5);
lean_inc(v_title_x3f_158_);
lean_dec_ref(v_definition_157_);
if (lean_obj_tag(v_title_x3f_158_) == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v_val_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
v_val_160_ = lean_ctor_get(v_title_x3f_158_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_title_x3f_158_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v_title_x3f_158_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_val_160_);
lean_dec(v_title_x3f_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = l_Lean_Markdown_LinkTitle_text(v_s_155_, v_val_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v_ref_169_; lean_object* v_title_x3f_170_; 
v_ref_169_ = lean_ctor_get(v_x_156_, 0);
lean_inc_ref(v_ref_169_);
lean_dec_ref_known(v_x_156_, 1);
v_title_x3f_170_ = lean_ctor_get(v_ref_169_, 1);
lean_inc(v_title_x3f_170_);
lean_dec_ref(v_ref_169_);
return v_title_x3f_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_RefTarget_title_x3f___boxed(lean_object* v_s_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Markdown_RefTarget_title_x3f(v_s_171_, v_x_172_);
lean_dec_ref(v_s_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl___redArg(lean_object* v_x_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_tag_nat(v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl___redArg___boxed(lean_object* v_x_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl___redArg(v_x_176_);
lean_dec(v_x_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl(lean_object* v_s_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_tag_nat(v_x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl___boxed(lean_object* v_s_181_, lean_object* v_x_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Markdown_ReferenceLinkForm_ctorIdx___impl(v_s_181_, v_x_182_);
lean_dec(v_x_182_);
lean_dec_ref(v_s_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(lean_object* v_t_184_, lean_object* v_k_185_){
_start:
{
if (lean_obj_tag(v_t_184_) == 2)
{
return v_k_185_;
}
else
{
lean_object* v_openBracket_186_; lean_object* v_closeBracket_187_; lean_object* v___x_188_; 
v_openBracket_186_ = lean_ctor_get(v_t_184_, 0);
lean_inc_ref(v_openBracket_186_);
v_closeBracket_187_ = lean_ctor_get(v_t_184_, 1);
lean_inc_ref(v_closeBracket_187_);
lean_dec(v_t_184_);
v___x_188_ = lean_apply_2(v_k_185_, v_openBracket_186_, v_closeBracket_187_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorElim(lean_object* v_s_189_, lean_object* v_motive_190_, lean_object* v_ctorIdx_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_k_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(v_t_192_, v_k_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_ctorElim___boxed(lean_object* v_s_196_, lean_object* v_motive_197_, lean_object* v_ctorIdx_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_k_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim(v_s_196_, v_motive_197_, v_ctorIdx_198_, v_t_199_, v_h_200_, v_k_201_);
lean_dec(v_ctorIdx_198_);
lean_dec_ref(v_s_196_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_full_elim___redArg(lean_object* v_t_203_, lean_object* v_full_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(v_t_203_, v_full_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_full_elim(lean_object* v_s_206_, lean_object* v_motive_207_, lean_object* v_t_208_, lean_object* v_h_209_, lean_object* v_full_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(v_t_208_, v_full_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_full_elim___boxed(lean_object* v_s_212_, lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_full_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Markdown_ReferenceLinkForm_full_elim(v_s_212_, v_motive_213_, v_t_214_, v_h_215_, v_full_216_);
lean_dec_ref(v_s_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_collapsed_elim___redArg(lean_object* v_t_218_, lean_object* v_collapsed_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(v_t_218_, v_collapsed_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_collapsed_elim(lean_object* v_s_221_, lean_object* v_motive_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_collapsed_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(v_t_223_, v_collapsed_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_collapsed_elim___boxed(lean_object* v_s_227_, lean_object* v_motive_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_collapsed_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Markdown_ReferenceLinkForm_collapsed_elim(v_s_227_, v_motive_228_, v_t_229_, v_h_230_, v_collapsed_231_);
lean_dec_ref(v_s_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_shortcut_elim___redArg(lean_object* v_t_233_, lean_object* v_shortcut_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(v_t_233_, v_shortcut_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_shortcut_elim(lean_object* v_s_236_, lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_shortcut_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Markdown_ReferenceLinkForm_ctorElim___redArg(v_t_238_, v_shortcut_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_ReferenceLinkForm_shortcut_elim___boxed(lean_object* v_s_242_, lean_object* v_motive_243_, lean_object* v_t_244_, lean_object* v_h_245_, lean_object* v_shortcut_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Markdown_ReferenceLinkForm_shortcut_elim(v_s_242_, v_motive_243_, v_t_244_, v_h_245_, v_shortcut_246_);
lean_dec_ref(v_s_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm_default(lean_object* v_s_248_){
_start:
{
lean_object* v_startInclusive_249_; lean_object* v_endExclusive_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_startInclusive_249_ = lean_ctor_get(v_s_248_, 1);
v_endExclusive_250_ = lean_ctor_get(v_s_248_, 2);
v___x_251_ = lean_nat_sub(v_endExclusive_250_, v_startInclusive_249_);
lean_inc(v___x_251_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc_ref(v___x_252_);
v___x_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm_default___boxed(lean_object* v_s_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Markdown_instInhabitedReferenceLinkForm_default(v_s_254_);
lean_dec_ref(v_s_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm(lean_object* v_a_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Markdown_instInhabitedReferenceLinkForm_default(v_a_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedReferenceLinkForm___boxed(lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Markdown_instInhabitedReferenceLinkForm(v_a_258_);
lean_dec_ref(v_a_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl___redArg(lean_object* v_x_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_tag_nat(v_x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl___redArg___boxed(lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Markdown_LinkTarget_ctorIdx___impl___redArg(v_x_262_);
lean_dec_ref(v_x_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl(lean_object* v_s_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = lean_obj_tag_nat(v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorIdx___impl___boxed(lean_object* v_s_267_, lean_object* v_x_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Markdown_LinkTarget_ctorIdx___impl(v_s_267_, v_x_268_);
lean_dec_ref(v_x_268_);
lean_dec_ref(v_s_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorElim___redArg(lean_object* v_t_270_, lean_object* v_k_271_){
_start:
{
if (lean_obj_tag(v_t_270_) == 0)
{
lean_object* v_openParen_272_; lean_object* v_destination_273_; lean_object* v_closeParen_274_; lean_object* v_title_x3f_275_; lean_object* v___x_276_; 
v_openParen_272_ = lean_ctor_get(v_t_270_, 0);
lean_inc_ref(v_openParen_272_);
v_destination_273_ = lean_ctor_get(v_t_270_, 1);
lean_inc_ref(v_destination_273_);
v_closeParen_274_ = lean_ctor_get(v_t_270_, 2);
lean_inc_ref(v_closeParen_274_);
v_title_x3f_275_ = lean_ctor_get(v_t_270_, 3);
lean_inc(v_title_x3f_275_);
lean_dec_ref_known(v_t_270_, 4);
v___x_276_ = lean_apply_4(v_k_271_, v_openParen_272_, v_destination_273_, v_closeParen_274_, v_title_x3f_275_);
return v___x_276_;
}
else
{
lean_object* v_refTarget_277_; lean_object* v_label_278_; lean_object* v_form_279_; lean_object* v___x_280_; 
v_refTarget_277_ = lean_ctor_get(v_t_270_, 0);
lean_inc_ref(v_refTarget_277_);
v_label_278_ = lean_ctor_get(v_t_270_, 1);
lean_inc_ref(v_label_278_);
v_form_279_ = lean_ctor_get(v_t_270_, 2);
lean_inc(v_form_279_);
lean_dec_ref_known(v_t_270_, 3);
v___x_280_ = lean_apply_3(v_k_271_, v_refTarget_277_, v_label_278_, v_form_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorElim(lean_object* v_s_281_, lean_object* v_motive_282_, lean_object* v_ctorIdx_283_, lean_object* v_t_284_, lean_object* v_h_285_, lean_object* v_k_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Markdown_LinkTarget_ctorElim___redArg(v_t_284_, v_k_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_ctorElim___boxed(lean_object* v_s_288_, lean_object* v_motive_289_, lean_object* v_ctorIdx_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_k_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Markdown_LinkTarget_ctorElim(v_s_288_, v_motive_289_, v_ctorIdx_290_, v_t_291_, v_h_292_, v_k_293_);
lean_dec(v_ctorIdx_290_);
lean_dec_ref(v_s_288_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_inline_elim___redArg(lean_object* v_t_295_, lean_object* v_inline_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Markdown_LinkTarget_ctorElim___redArg(v_t_295_, v_inline_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_inline_elim(lean_object* v_s_298_, lean_object* v_motive_299_, lean_object* v_t_300_, lean_object* v_h_301_, lean_object* v_inline_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Markdown_LinkTarget_ctorElim___redArg(v_t_300_, v_inline_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_inline_elim___boxed(lean_object* v_s_304_, lean_object* v_motive_305_, lean_object* v_t_306_, lean_object* v_h_307_, lean_object* v_inline_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Markdown_LinkTarget_inline_elim(v_s_304_, v_motive_305_, v_t_306_, v_h_307_, v_inline_308_);
lean_dec_ref(v_s_304_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_reference_elim___redArg(lean_object* v_t_310_, lean_object* v_reference_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Markdown_LinkTarget_ctorElim___redArg(v_t_310_, v_reference_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_reference_elim(lean_object* v_s_313_, lean_object* v_motive_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_reference_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Markdown_LinkTarget_ctorElim___redArg(v_t_315_, v_reference_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_reference_elim___boxed(lean_object* v_s_319_, lean_object* v_motive_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_reference_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Markdown_LinkTarget_reference_elim(v_s_319_, v_motive_320_, v_t_321_, v_h_322_, v_reference_323_);
lean_dec_ref(v_s_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget_default(lean_object* v_s_325_){
_start:
{
lean_object* v_startInclusive_326_; lean_object* v_endExclusive_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_startInclusive_326_ = lean_ctor_get(v_s_325_, 1);
v_endExclusive_327_ = lean_ctor_get(v_s_325_, 2);
v___x_328_ = lean_nat_sub(v_endExclusive_327_, v_startInclusive_326_);
lean_inc(v___x_328_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = l_Lean_Markdown_instInhabitedLinkDestination_default(v_s_325_);
v___x_331_ = lean_box(0);
lean_inc_ref(v___x_329_);
v___x_332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_332_, 0, v___x_329_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
lean_ctor_set(v___x_332_, 3, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget_default___boxed(lean_object* v_s_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Markdown_instInhabitedLinkTarget_default(v_s_333_);
lean_dec_ref(v_s_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget(lean_object* v_a_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Markdown_instInhabitedLinkTarget_default(v_a_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedLinkTarget___boxed(lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Markdown_instInhabitedLinkTarget(v_a_337_);
lean_dec_ref(v_a_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent_default(lean_object* v_s_339_){
_start:
{
lean_object* v_startInclusive_340_; lean_object* v_endExclusive_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_startInclusive_340_ = lean_ctor_get(v_s_339_, 1);
v_endExclusive_341_ = lean_ctor_get(v_s_339_, 2);
v___x_342_ = lean_nat_sub(v_endExclusive_341_, v_startInclusive_340_);
lean_inc(v___x_342_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent_default___boxed(lean_object* v_s_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Markdown_instInhabitedInlineCodeContent_default(v_s_345_);
lean_dec_ref(v_s_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent(lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Markdown_instInhabitedInlineCodeContent_default(v_a_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineCodeContent___boxed(lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Markdown_instInhabitedInlineCodeContent(v_a_349_);
lean_dec_ref(v_a_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent_default(lean_object* v_s_351_){
_start:
{
lean_object* v_startInclusive_352_; lean_object* v_endExclusive_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_startInclusive_352_ = lean_ctor_get(v_s_351_, 1);
v_endExclusive_353_ = lean_ctor_get(v_s_351_, 2);
v___x_354_ = lean_nat_sub(v_endExclusive_353_, v_startInclusive_352_);
lean_inc(v___x_354_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent_default___boxed(lean_object* v_s_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Markdown_instInhabitedMathContent_default(v_s_357_);
lean_dec_ref(v_s_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent(lean_object* v_a_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Markdown_instInhabitedMathContent_default(v_a_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedMathContent___boxed(lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Markdown_instInhabitedMathContent(v_a_361_);
lean_dec_ref(v_a_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_MathContent_text_spec__0(lean_object* v_s_363_, lean_object* v_pos_364_){
_start:
{
lean_object* v_str_365_; lean_object* v_startInclusive_366_; lean_object* v_endExclusive_367_; lean_object* v___x_368_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v_decide_379_; 
v_str_365_ = lean_ctor_get(v_s_363_, 0);
v_startInclusive_366_ = lean_ctor_get(v_s_363_, 1);
v_endExclusive_367_ = lean_ctor_get(v_s_363_, 2);
v___x_368_ = lean_nat_add(v_startInclusive_366_, v_pos_364_);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_nat_sub(v_endExclusive_367_, v___x_368_);
v_decide_379_ = lean_nat_dec_eq(v___x_377_, v___x_378_);
lean_dec(v___x_378_);
if (v_decide_379_ == 0)
{
uint32_t v___x_380_; uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_380_ = lean_string_utf8_get_fast(v_str_365_, v___x_368_);
v___x_381_ = 32;
v___x_382_ = lean_uint32_dec_eq(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
uint32_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = 9;
v___x_384_ = lean_uint32_dec_eq(v___x_380_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v___x_368_);
return v_pos_364_;
}
else
{
goto v___jp_369_;
}
}
else
{
goto v___jp_369_;
}
}
else
{
lean_dec(v___x_368_);
return v_pos_364_;
}
v___jp_369_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_370_ = lean_string_utf8_next_fast(v_str_365_, v___x_368_);
v___x_371_ = lean_nat_sub(v___x_370_, v___x_368_);
lean_dec(v___x_368_);
v___x_372_ = lean_nat_add(v_pos_364_, v___x_371_);
lean_dec(v___x_371_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_pos_364_, v___x_373_);
v___x_375_ = lean_nat_dec_le(v___x_374_, v___x_372_);
lean_dec(v___x_374_);
if (v___x_375_ == 0)
{
lean_dec(v___x_372_);
return v_pos_364_;
}
else
{
lean_dec(v_pos_364_);
v_pos_364_ = v___x_372_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_MathContent_text_spec__0___boxed(lean_object* v_s_385_, lean_object* v_pos_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_MathContent_text_spec__0(v_s_385_, v_pos_386_);
lean_dec_ref(v_s_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_MathContent_text___lam__0(lean_object* v_startInclusive_389_, lean_object* v_str_390_, lean_object* v___x_391_, lean_object* v_line_392_, lean_object* v_____s_393_){
_start:
{
lean_object* v_out_395_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_string_utf8_byte_size(v_____s_393_);
v___x_413_ = lean_nat_dec_le(v___x_391_, v___x_412_);
if (v___x_413_ == 0)
{
goto v___jp_409_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_414_ = ((lean_object*)(l_Lean_Markdown_MathContent_text___lam__0___closed__0));
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_nat_sub(v___x_412_, v___x_391_);
v___x_417_ = lean_string_memcmp(v_____s_393_, v___x_414_, v___x_416_, v___x_415_, v___x_391_);
lean_dec(v___x_416_);
if (v___x_417_ == 0)
{
goto v___jp_409_;
}
else
{
v_out_395_ = v_____s_393_;
goto v___jp_394_;
}
}
v___jp_394_:
{
lean_object* v_startInclusive_396_; lean_object* v_endExclusive_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_out_407_; lean_object* v___x_408_; 
v_startInclusive_396_ = lean_ctor_get(v_line_392_, 0);
v_endExclusive_397_ = lean_ctor_get(v_line_392_, 1);
v___x_398_ = lean_nat_add(v_startInclusive_389_, v_startInclusive_396_);
v___x_399_ = lean_nat_add(v_startInclusive_389_, v_endExclusive_397_);
v___x_400_ = lean_string_utf8_extract_fast(v_str_390_, v___x_398_, v___x_399_);
lean_dec(v___x_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_string_utf8_byte_size(v___x_400_);
lean_inc_ref(v___x_400_);
v___x_403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_403_, 0, v___x_400_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
v___x_404_ = l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_MathContent_text_spec__0(v___x_403_, v___x_401_);
lean_dec_ref_known(v___x_403_, 3);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_400_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
v___x_406_ = l_String_Slice_toString(v___x_405_);
lean_dec_ref_known(v___x_405_, 3);
v_out_407_ = lean_string_append(v_out_395_, v___x_406_);
lean_dec_ref(v___x_406_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_out_407_);
return v___x_408_;
}
v___jp_409_:
{
uint32_t v___x_410_; lean_object* v_out_411_; 
v___x_410_ = 32;
v_out_411_ = lean_string_push(v_____s_393_, v___x_410_);
v_out_395_ = v_out_411_;
goto v___jp_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_MathContent_text___lam__0___boxed(lean_object* v_startInclusive_418_, lean_object* v_str_419_, lean_object* v___x_420_, lean_object* v_line_421_, lean_object* v_____s_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Markdown_MathContent_text___lam__0(v_startInclusive_418_, v_str_419_, v___x_420_, v_line_421_, v_____s_422_);
lean_dec_ref(v_line_421_);
lean_dec(v___x_420_);
lean_dec_ref(v_str_419_);
lean_dec(v_startInclusive_418_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___at___00Lean_Markdown_MathContent_text_spec__1___redArg(lean_object* v_f_424_, lean_object* v_s_425_, lean_object* v_b_426_){
_start:
{
lean_object* v_array_427_; lean_object* v_start_428_; lean_object* v_stop_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_444_; 
v_array_427_ = lean_ctor_get(v_s_425_, 0);
v_start_428_ = lean_ctor_get(v_s_425_, 1);
v_stop_429_ = lean_ctor_get(v_s_425_, 2);
v_isSharedCheck_444_ = !lean_is_exclusive(v_s_425_);
if (v_isSharedCheck_444_ == 0)
{
v___x_431_ = v_s_425_;
v_isShared_432_ = v_isSharedCheck_444_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_stop_429_);
lean_inc(v_start_428_);
lean_inc(v_array_427_);
lean_dec(v_s_425_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_444_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = lean_nat_dec_lt(v_start_428_, v_stop_429_);
if (v___x_433_ == 0)
{
lean_del_object(v___x_431_);
lean_dec(v_stop_429_);
lean_dec(v_start_428_);
lean_dec_ref(v_array_427_);
lean_dec_ref(v_f_424_);
return v_b_426_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_array_fget_borrowed(v_array_427_, v_start_428_);
lean_inc_ref(v_f_424_);
lean_inc(v___x_434_);
v___x_435_ = lean_apply_2(v_f_424_, v___x_434_, v_b_426_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; 
lean_del_object(v___x_431_);
lean_dec(v_stop_429_);
lean_dec(v_start_428_);
lean_dec_ref(v_array_427_);
lean_dec_ref(v_f_424_);
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v___x_435_, 1);
return v_a_436_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v_a_437_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_435_, 1);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_start_428_, v___x_438_);
lean_dec(v_start_428_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_439_);
v___x_441_ = v___x_431_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_array_427_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_stop_429_);
v___x_441_ = v_reuseFailAlloc_443_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v_s_425_ = v___x_441_;
v_b_426_ = v_a_437_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_MathContent_text(lean_object* v_s_445_, lean_object* v_content_446_){
_start:
{
lean_object* v___x_447_; lean_object* v_startInclusive_448_; lean_object* v_endExclusive_449_; lean_object* v_str_450_; lean_object* v_startInclusive_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_out_454_; lean_object* v___x_455_; lean_object* v___f_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_447_ = l_Lean_Markdown_Lines_first___redArg(v_content_446_);
v_startInclusive_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_startInclusive_448_);
v_endExclusive_449_ = lean_ctor_get(v___x_447_, 1);
lean_inc(v_endExclusive_449_);
lean_dec_ref(v___x_447_);
v_str_450_ = lean_ctor_get(v_s_445_, 0);
lean_inc_ref(v_str_450_);
v_startInclusive_451_ = lean_ctor_get(v_s_445_, 1);
lean_inc(v_startInclusive_451_);
lean_dec_ref(v_s_445_);
v___x_452_ = lean_nat_add(v_startInclusive_451_, v_startInclusive_448_);
lean_dec(v_startInclusive_448_);
v___x_453_ = lean_nat_add(v_startInclusive_451_, v_endExclusive_449_);
lean_dec(v_endExclusive_449_);
v_out_454_ = lean_string_utf8_extract_fast(v_str_450_, v___x_452_, v___x_453_);
lean_dec(v___x_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_unsigned_to_nat(1u);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_Markdown_MathContent_text___lam__0___boxed), 5, 3);
lean_closure_set(v___f_456_, 0, v_startInclusive_451_);
lean_closure_set(v___f_456_, 1, v_str_450_);
lean_closure_set(v___f_456_, 2, v___x_455_);
v___x_457_ = lean_array_get_size(v_content_446_);
v___x_458_ = l_Array_toSubarray___redArg(v_content_446_, v___x_455_, v___x_457_);
v___x_459_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___at___00Lean_Markdown_MathContent_text_spec__1___redArg(v___f_456_, v___x_458_, v_out_454_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___at___00Lean_Markdown_MathContent_text_spec__1(lean_object* v_00_u03b2_460_, lean_object* v_f_461_, lean_object* v_s_462_, lean_object* v_b_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l___private_Init_Data_Stream_0__Std_Stream_forIn_visit___at___00Lean_Markdown_MathContent_text_spec__1___redArg(v_f_461_, v_s_462_, v_b_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_InlineCodeContent_text_spec__0(lean_object* v_s_465_, lean_object* v_pos_466_){
_start:
{
lean_object* v_str_467_; lean_object* v_startInclusive_468_; lean_object* v_endExclusive_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v_decide_473_; 
v_str_467_ = lean_ctor_get(v_s_465_, 0);
v_startInclusive_468_ = lean_ctor_get(v_s_465_, 1);
v_endExclusive_469_ = lean_ctor_get(v_s_465_, 2);
v___x_470_ = lean_nat_add(v_startInclusive_468_, v_pos_466_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_nat_sub(v_endExclusive_469_, v___x_470_);
v_decide_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
lean_dec(v___x_472_);
if (v_decide_473_ == 0)
{
uint32_t v___x_474_; uint32_t v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_string_utf8_get_fast(v_str_467_, v___x_470_);
v___x_475_ = 32;
v___x_476_ = lean_uint32_dec_eq(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_dec(v___x_470_);
return v_pos_466_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_477_ = lean_string_utf8_next_fast(v_str_467_, v___x_470_);
v___x_478_ = lean_nat_sub(v___x_477_, v___x_470_);
lean_dec(v___x_470_);
v___x_479_ = lean_nat_add(v_pos_466_, v___x_478_);
lean_dec(v___x_478_);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_pos_466_, v___x_480_);
v___x_482_ = lean_nat_dec_le(v___x_481_, v___x_479_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
lean_dec(v___x_479_);
return v_pos_466_;
}
else
{
lean_dec(v_pos_466_);
v_pos_466_ = v___x_479_;
goto _start;
}
}
}
else
{
lean_dec(v___x_470_);
return v_pos_466_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_InlineCodeContent_text_spec__0___boxed(lean_object* v_s_484_, lean_object* v_pos_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_InlineCodeContent_text_spec__0(v_s_484_, v_pos_485_);
lean_dec_ref(v_s_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCodeContent_text(lean_object* v_s_487_, lean_object* v_content_488_){
_start:
{
lean_object* v___x_489_; lean_object* v_joined_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v_decide_493_; 
v___x_489_ = ((lean_object*)(l_Lean_Markdown_MathContent_text___lam__0___closed__0));
v_joined_490_ = l_Lean_Markdown_Lines_text(v_s_487_, v_content_488_, v___x_489_);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_string_utf8_byte_size(v_joined_490_);
v_decide_493_ = lean_nat_dec_eq(v___x_491_, v___x_492_);
if (v_decide_493_ == 0)
{
uint32_t v___x_494_; uint32_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = 32;
v___x_495_ = lean_string_utf8_get_fast(v_joined_490_, v___x_491_);
v___x_496_ = lean_uint32_dec_eq(v___x_495_, v___x_494_);
if (v___x_496_ == 0)
{
return v_joined_490_;
}
else
{
uint8_t v_decide_497_; 
v_decide_497_ = lean_nat_dec_eq(v___x_492_, v___x_491_);
if (v_decide_497_ == 0)
{
lean_object* v_sl_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint32_t v___x_502_; uint8_t v___x_503_; 
lean_inc_ref(v_joined_490_);
v_sl_498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_sl_498_, 0, v_joined_490_);
lean_ctor_set(v_sl_498_, 1, v___x_491_);
lean_ctor_set(v_sl_498_, 2, v___x_492_);
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_sub(v___x_492_, v___x_499_);
v___x_501_ = l_String_Slice_posLE(v_sl_498_, v___x_500_);
v___x_502_ = lean_string_utf8_get_fast(v_joined_490_, v___x_501_);
lean_dec(v___x_501_);
v___x_503_ = lean_uint32_dec_eq(v___x_502_, v___x_494_);
if (v___x_503_ == 0)
{
lean_dec_ref_known(v_sl_498_, 3);
return v_joined_490_;
}
else
{
lean_object* v___x_504_; uint8_t v_decide_505_; 
v___x_504_ = l_String_Slice_Pos_skipWhile___at___00Lean_Markdown_InlineCodeContent_text_spec__0(v_sl_498_, v___x_491_);
v_decide_505_ = lean_nat_dec_eq(v___x_504_, v___x_492_);
lean_dec(v___x_504_);
if (v_decide_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_506_ = l_String_Slice_Pos_nextn(v_sl_498_, v___x_491_, v___x_499_);
lean_dec_ref_known(v_sl_498_, 3);
lean_inc(v___x_506_);
lean_inc_ref(v_joined_490_);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v_joined_490_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_ctor_set(v___x_507_, 2, v___x_492_);
v___x_508_ = lean_nat_sub(v___x_492_, v___x_506_);
v___x_509_ = l_String_Slice_Pos_prevn(v___x_507_, v___x_508_, v___x_499_);
lean_dec_ref_known(v___x_507_, 3);
v___x_510_ = lean_nat_add(v___x_506_, v___x_509_);
lean_dec(v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_511_, 0, v_joined_490_);
lean_ctor_set(v___x_511_, 1, v___x_506_);
lean_ctor_set(v___x_511_, 2, v___x_510_);
v___x_512_ = l_String_Slice_toString(v___x_511_);
lean_dec_ref_known(v___x_511_, 3);
return v___x_512_;
}
else
{
lean_dec_ref_known(v_sl_498_, 3);
return v_joined_490_;
}
}
}
else
{
return v_joined_490_;
}
}
}
else
{
return v_joined_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineCodeContent_text___boxed(lean_object* v_s_513_, lean_object* v_content_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_Markdown_InlineCodeContent_text(v_s_513_, v_content_514_);
lean_dec_ref(v_s_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl___redArg(lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_tag_nat(v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl___redArg___boxed(lean_object* v_x_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Markdown_Inline_ctorIdx___impl___redArg(v_x_518_);
lean_dec_ref(v_x_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl(lean_object* v_s_520_, lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_tag_nat(v_x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorIdx___impl___boxed(lean_object* v_s_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Markdown_Inline_ctorIdx___impl(v_s_523_, v_x_524_);
lean_dec_ref(v_x_524_);
lean_dec_ref(v_s_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorElim___redArg(lean_object* v_t_526_, lean_object* v_k_527_){
_start:
{
switch(lean_obj_tag(v_t_526_))
{
case 1:
{
lean_object* v_openTicks_528_; lean_object* v_content_529_; lean_object* v_closeTicks_530_; lean_object* v___x_531_; 
v_openTicks_528_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_openTicks_528_);
v_content_529_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_content_529_);
v_closeTicks_530_ = lean_ctor_get(v_t_526_, 2);
lean_inc_ref(v_closeTicks_530_);
lean_dec_ref_known(v_t_526_, 3);
v___x_531_ = lean_apply_3(v_k_527_, v_openTicks_528_, v_content_529_, v_closeTicks_530_);
return v___x_531_;
}
case 2:
{
lean_object* v_openDelim_532_; lean_object* v_content_533_; lean_object* v_closeDelim_534_; lean_object* v___x_535_; 
v_openDelim_532_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_openDelim_532_);
v_content_533_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_content_533_);
v_closeDelim_534_ = lean_ctor_get(v_t_526_, 2);
lean_inc_ref(v_closeDelim_534_);
lean_dec_ref_known(v_t_526_, 3);
v___x_535_ = lean_apply_3(v_k_527_, v_openDelim_532_, v_content_533_, v_closeDelim_534_);
return v___x_535_;
}
case 3:
{
lean_object* v_openDelim_536_; lean_object* v_content_537_; lean_object* v_closeDelim_538_; lean_object* v___x_539_; 
v_openDelim_536_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_openDelim_536_);
v_content_537_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_content_537_);
v_closeDelim_538_ = lean_ctor_get(v_t_526_, 2);
lean_inc_ref(v_closeDelim_538_);
lean_dec_ref_known(v_t_526_, 3);
v___x_539_ = lean_apply_3(v_k_527_, v_openDelim_536_, v_content_537_, v_closeDelim_538_);
return v___x_539_;
}
case 4:
{
lean_object* v_openBracket_540_; lean_object* v_text_541_; lean_object* v_closeBracket_542_; lean_object* v_target_543_; lean_object* v___x_544_; 
v_openBracket_540_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_openBracket_540_);
v_text_541_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_text_541_);
v_closeBracket_542_ = lean_ctor_get(v_t_526_, 2);
lean_inc_ref(v_closeBracket_542_);
v_target_543_ = lean_ctor_get(v_t_526_, 3);
lean_inc_ref(v_target_543_);
lean_dec_ref_known(v_t_526_, 4);
v___x_544_ = lean_apply_4(v_k_527_, v_openBracket_540_, v_text_541_, v_closeBracket_542_, v_target_543_);
return v___x_544_;
}
case 5:
{
lean_object* v_bang_545_; lean_object* v_openBracket_546_; lean_object* v_alt_547_; lean_object* v_closeBracket_548_; lean_object* v_target_549_; lean_object* v___x_550_; 
v_bang_545_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_bang_545_);
v_openBracket_546_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_openBracket_546_);
v_alt_547_ = lean_ctor_get(v_t_526_, 2);
lean_inc_ref(v_alt_547_);
v_closeBracket_548_ = lean_ctor_get(v_t_526_, 3);
lean_inc_ref(v_closeBracket_548_);
v_target_549_ = lean_ctor_get(v_t_526_, 4);
lean_inc_ref(v_target_549_);
lean_dec_ref_known(v_t_526_, 5);
v___x_550_ = lean_apply_5(v_k_527_, v_bang_545_, v_openBracket_546_, v_alt_547_, v_closeBracket_548_, v_target_549_);
return v___x_550_;
}
case 6:
{
lean_object* v_marker_551_; lean_object* v_newline_552_; lean_object* v___x_553_; 
v_marker_551_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_marker_551_);
v_newline_552_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_newline_552_);
lean_dec_ref_known(v_t_526_, 2);
v___x_553_ = lean_apply_2(v_k_527_, v_marker_551_, v_newline_552_);
return v___x_553_;
}
case 7:
{
lean_object* v_openAngle_554_; lean_object* v_url_555_; lean_object* v_closeAngle_556_; uint8_t v_isEmail_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_openAngle_554_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_openAngle_554_);
v_url_555_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_url_555_);
v_closeAngle_556_ = lean_ctor_get(v_t_526_, 2);
lean_inc_ref(v_closeAngle_556_);
v_isEmail_557_ = lean_ctor_get_uint8(v_t_526_, sizeof(void*)*3);
lean_dec_ref_known(v_t_526_, 3);
v___x_558_ = lean_box(v_isEmail_557_);
v___x_559_ = lean_apply_4(v_k_527_, v_openAngle_554_, v_url_555_, v_closeAngle_556_, v___x_558_);
return v___x_559_;
}
case 8:
{
lean_object* v_openDollars_560_; lean_object* v_content_561_; lean_object* v_closeDollars_562_; uint8_t v_display_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_openDollars_560_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_openDollars_560_);
v_content_561_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_content_561_);
v_closeDollars_562_ = lean_ctor_get(v_t_526_, 2);
lean_inc_ref(v_closeDollars_562_);
v_display_563_ = lean_ctor_get_uint8(v_t_526_, sizeof(void*)*3);
lean_dec_ref_known(v_t_526_, 3);
v___x_564_ = lean_box(v_display_563_);
v___x_565_ = lean_apply_4(v_k_527_, v_openDollars_560_, v_content_561_, v_closeDollars_562_, v___x_564_);
return v___x_565_;
}
case 11:
{
lean_object* v_backslash_566_; lean_object* v_char_567_; lean_object* v___x_568_; 
v_backslash_566_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_backslash_566_);
v_char_567_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_char_567_);
lean_dec_ref_known(v_t_526_, 2);
v___x_568_ = lean_apply_2(v_k_527_, v_backslash_566_, v_char_567_);
return v___x_568_;
}
case 12:
{
lean_object* v_range_569_; lean_object* v_value_570_; lean_object* v___x_571_; 
v_range_569_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_range_569_);
v_value_570_ = lean_ctor_get(v_t_526_, 1);
lean_inc_ref(v_value_570_);
lean_dec_ref_known(v_t_526_, 2);
v___x_571_ = lean_apply_2(v_k_527_, v_range_569_, v_value_570_);
return v___x_571_;
}
default: 
{
lean_object* v_range_572_; lean_object* v___x_573_; 
v_range_572_ = lean_ctor_get(v_t_526_, 0);
lean_inc_ref(v_range_572_);
lean_dec_ref(v_t_526_);
v___x_573_ = lean_apply_1(v_k_527_, v_range_572_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorElim(lean_object* v_s_574_, lean_object* v_motive__1_575_, lean_object* v_ctorIdx_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_k_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_577_, v_k_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_ctorElim___boxed(lean_object* v_s_581_, lean_object* v_motive__1_582_, lean_object* v_ctorIdx_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_k_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Markdown_Inline_ctorElim(v_s_581_, v_motive__1_582_, v_ctorIdx_583_, v_t_584_, v_h_585_, v_k_586_);
lean_dec(v_ctorIdx_583_);
lean_dec_ref(v_s_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_text_elim___redArg(lean_object* v_t_588_, lean_object* v_text_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_588_, v_text_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_text_elim(lean_object* v_s_591_, lean_object* v_motive__1_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_text_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_593_, v_text_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_text_elim___boxed(lean_object* v_s_597_, lean_object* v_motive__1_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_text_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Markdown_Inline_text_elim(v_s_597_, v_motive__1_598_, v_t_599_, v_h_600_, v_text_601_);
lean_dec_ref(v_s_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_code_elim___redArg(lean_object* v_t_603_, lean_object* v_code_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_603_, v_code_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_code_elim(lean_object* v_s_606_, lean_object* v_motive__1_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_code_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_608_, v_code_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_code_elim___boxed(lean_object* v_s_612_, lean_object* v_motive__1_613_, lean_object* v_t_614_, lean_object* v_h_615_, lean_object* v_code_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Markdown_Inline_code_elim(v_s_612_, v_motive__1_613_, v_t_614_, v_h_615_, v_code_616_);
lean_dec_ref(v_s_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_italic_elim___redArg(lean_object* v_t_618_, lean_object* v_italic_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_618_, v_italic_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_italic_elim(lean_object* v_s_621_, lean_object* v_motive__1_622_, lean_object* v_t_623_, lean_object* v_h_624_, lean_object* v_italic_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_623_, v_italic_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_italic_elim___boxed(lean_object* v_s_627_, lean_object* v_motive__1_628_, lean_object* v_t_629_, lean_object* v_h_630_, lean_object* v_italic_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Markdown_Inline_italic_elim(v_s_627_, v_motive__1_628_, v_t_629_, v_h_630_, v_italic_631_);
lean_dec_ref(v_s_627_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_bold_elim___redArg(lean_object* v_t_633_, lean_object* v_bold_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_633_, v_bold_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_bold_elim(lean_object* v_s_636_, lean_object* v_motive__1_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_bold_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_638_, v_bold_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_bold_elim___boxed(lean_object* v_s_642_, lean_object* v_motive__1_643_, lean_object* v_t_644_, lean_object* v_h_645_, lean_object* v_bold_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Markdown_Inline_bold_elim(v_s_642_, v_motive__1_643_, v_t_644_, v_h_645_, v_bold_646_);
lean_dec_ref(v_s_642_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_link_elim___redArg(lean_object* v_t_648_, lean_object* v_link_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_648_, v_link_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_link_elim(lean_object* v_s_651_, lean_object* v_motive__1_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_link_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_653_, v_link_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_link_elim___boxed(lean_object* v_s_657_, lean_object* v_motive__1_658_, lean_object* v_t_659_, lean_object* v_h_660_, lean_object* v_link_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Markdown_Inline_link_elim(v_s_657_, v_motive__1_658_, v_t_659_, v_h_660_, v_link_661_);
lean_dec_ref(v_s_657_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_image_elim___redArg(lean_object* v_t_663_, lean_object* v_image_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_663_, v_image_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_image_elim(lean_object* v_s_666_, lean_object* v_motive__1_667_, lean_object* v_t_668_, lean_object* v_h_669_, lean_object* v_image_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_668_, v_image_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_image_elim___boxed(lean_object* v_s_672_, lean_object* v_motive__1_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_image_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Markdown_Inline_image_elim(v_s_672_, v_motive__1_673_, v_t_674_, v_h_675_, v_image_676_);
lean_dec_ref(v_s_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_hardBreak_elim___redArg(lean_object* v_t_678_, lean_object* v_hardBreak_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_678_, v_hardBreak_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_hardBreak_elim(lean_object* v_s_681_, lean_object* v_motive__1_682_, lean_object* v_t_683_, lean_object* v_h_684_, lean_object* v_hardBreak_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_683_, v_hardBreak_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_hardBreak_elim___boxed(lean_object* v_s_687_, lean_object* v_motive__1_688_, lean_object* v_t_689_, lean_object* v_h_690_, lean_object* v_hardBreak_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Markdown_Inline_hardBreak_elim(v_s_687_, v_motive__1_688_, v_t_689_, v_h_690_, v_hardBreak_691_);
lean_dec_ref(v_s_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_autolink_elim___redArg(lean_object* v_t_693_, lean_object* v_autolink_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_693_, v_autolink_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_autolink_elim(lean_object* v_s_696_, lean_object* v_motive__1_697_, lean_object* v_t_698_, lean_object* v_h_699_, lean_object* v_autolink_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_698_, v_autolink_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_autolink_elim___boxed(lean_object* v_s_702_, lean_object* v_motive__1_703_, lean_object* v_t_704_, lean_object* v_h_705_, lean_object* v_autolink_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Markdown_Inline_autolink_elim(v_s_702_, v_motive__1_703_, v_t_704_, v_h_705_, v_autolink_706_);
lean_dec_ref(v_s_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_math_elim___redArg(lean_object* v_t_708_, lean_object* v_math_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_708_, v_math_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_math_elim(lean_object* v_s_711_, lean_object* v_motive__1_712_, lean_object* v_t_713_, lean_object* v_h_714_, lean_object* v_math_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_713_, v_math_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_math_elim___boxed(lean_object* v_s_717_, lean_object* v_motive__1_718_, lean_object* v_t_719_, lean_object* v_h_720_, lean_object* v_math_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Markdown_Inline_math_elim(v_s_717_, v_motive__1_718_, v_t_719_, v_h_720_, v_math_721_);
lean_dec_ref(v_s_717_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_html_elim___redArg(lean_object* v_t_723_, lean_object* v_html_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_723_, v_html_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_html_elim(lean_object* v_s_726_, lean_object* v_motive__1_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_html_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_728_, v_html_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_html_elim___boxed(lean_object* v_s_732_, lean_object* v_motive__1_733_, lean_object* v_t_734_, lean_object* v_h_735_, lean_object* v_html_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_Markdown_Inline_html_elim(v_s_732_, v_motive__1_733_, v_t_734_, v_h_735_, v_html_736_);
lean_dec_ref(v_s_732_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_softBreak_elim___redArg(lean_object* v_t_738_, lean_object* v_softBreak_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_738_, v_softBreak_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_softBreak_elim(lean_object* v_s_741_, lean_object* v_motive__1_742_, lean_object* v_t_743_, lean_object* v_h_744_, lean_object* v_softBreak_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_743_, v_softBreak_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_softBreak_elim___boxed(lean_object* v_s_747_, lean_object* v_motive__1_748_, lean_object* v_t_749_, lean_object* v_h_750_, lean_object* v_softBreak_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Markdown_Inline_softBreak_elim(v_s_747_, v_motive__1_748_, v_t_749_, v_h_750_, v_softBreak_751_);
lean_dec_ref(v_s_747_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_escape_elim___redArg(lean_object* v_t_753_, lean_object* v_escape_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_753_, v_escape_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_escape_elim(lean_object* v_s_756_, lean_object* v_motive__1_757_, lean_object* v_t_758_, lean_object* v_h_759_, lean_object* v_escape_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_758_, v_escape_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_escape_elim___boxed(lean_object* v_s_762_, lean_object* v_motive__1_763_, lean_object* v_t_764_, lean_object* v_h_765_, lean_object* v_escape_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Markdown_Inline_escape_elim(v_s_762_, v_motive__1_763_, v_t_764_, v_h_765_, v_escape_766_);
lean_dec_ref(v_s_762_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_entity_elim___redArg(lean_object* v_t_768_, lean_object* v_entity_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_768_, v_entity_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_entity_elim(lean_object* v_s_771_, lean_object* v_motive__1_772_, lean_object* v_t_773_, lean_object* v_h_774_, lean_object* v_entity_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Markdown_Inline_ctorElim___redArg(v_t_773_, v_entity_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_entity_elim___boxed(lean_object* v_s_777_, lean_object* v_motive__1_778_, lean_object* v_t_779_, lean_object* v_h_780_, lean_object* v_entity_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Markdown_Inline_entity_elim(v_s_777_, v_motive__1_778_, v_t_779_, v_h_780_, v_entity_781_);
lean_dec_ref(v_s_777_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline_default(lean_object* v_s_783_){
_start:
{
lean_object* v_startInclusive_784_; lean_object* v_endExclusive_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v_startInclusive_784_ = lean_ctor_get(v_s_783_, 1);
v_endExclusive_785_ = lean_ctor_get(v_s_783_, 2);
v___x_786_ = lean_nat_sub(v_endExclusive_785_, v_startInclusive_784_);
lean_inc(v___x_786_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline_default___boxed(lean_object* v_s_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Markdown_instInhabitedInline_default(v_s_789_);
lean_dec_ref(v_s_789_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline(lean_object* v_a_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Markdown_instInhabitedInline_default(v_a_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInline___boxed(lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Markdown_instInhabitedInline(v_a_793_);
lean_dec_ref(v_a_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_extent___redArg(lean_object* v_d_795_){
_start:
{
lean_object* v_angles_x3f_796_; 
v_angles_x3f_796_ = lean_ctor_get(v_d_795_, 0);
if (lean_obj_tag(v_angles_x3f_796_) == 0)
{
lean_object* v_url_797_; 
v_url_797_ = lean_ctor_get(v_d_795_, 1);
lean_inc_ref(v_url_797_);
lean_dec_ref(v_d_795_);
return v_url_797_;
}
else
{
lean_object* v_val_798_; lean_object* v_fst_799_; lean_object* v_snd_800_; lean_object* v___x_801_; 
lean_inc_ref(v_angles_x3f_796_);
lean_dec_ref(v_d_795_);
v_val_798_ = lean_ctor_get(v_angles_x3f_796_, 0);
lean_inc(v_val_798_);
lean_dec_ref_known(v_angles_x3f_796_, 1);
v_fst_799_ = lean_ctor_get(v_val_798_, 0);
lean_inc(v_fst_799_);
v_snd_800_ = lean_ctor_get(v_val_798_, 1);
lean_inc(v_snd_800_);
lean_dec(v_val_798_);
v___x_801_ = l_Lean_Markdown_span___redArg(v_fst_799_, v_snd_800_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_extent(lean_object* v_s_802_, lean_object* v_d_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Markdown_LinkDestination_extent___redArg(v_d_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkDestination_extent___boxed(lean_object* v_s_805_, lean_object* v_d_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Markdown_LinkDestination_extent(v_s_805_, v_d_806_);
lean_dec_ref(v_s_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f___redArg(lean_object* v_x_808_){
_start:
{
lean_object* v_closeBracket_810_; 
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v_closeParen_813_; lean_object* v_endExclusive_814_; lean_object* v___x_815_; 
v_closeParen_813_ = lean_ctor_get(v_x_808_, 2);
v_endExclusive_814_ = lean_ctor_get(v_closeParen_813_, 1);
lean_inc(v_endExclusive_814_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_endExclusive_814_);
return v___x_815_;
}
else
{
lean_object* v_form_816_; 
v_form_816_ = lean_ctor_get(v_x_808_, 2);
if (lean_obj_tag(v_form_816_) == 2)
{
lean_object* v___x_817_; 
v___x_817_ = lean_box(0);
return v___x_817_;
}
else
{
lean_object* v_closeBracket_818_; 
v_closeBracket_818_ = lean_ctor_get(v_form_816_, 1);
v_closeBracket_810_ = v_closeBracket_818_;
goto v___jp_809_;
}
}
v___jp_809_:
{
lean_object* v_endExclusive_811_; lean_object* v___x_812_; 
v_endExclusive_811_ = lean_ctor_get(v_closeBracket_810_, 1);
lean_inc(v_endExclusive_811_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v_endExclusive_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f___redArg___boxed(lean_object* v_x_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Markdown_LinkTarget_stop_x3f___redArg(v_x_819_);
lean_dec_ref(v_x_819_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f(lean_object* v_s_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Markdown_LinkTarget_stop_x3f___redArg(v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_stop_x3f___boxed(lean_object* v_s_824_, lean_object* v_x_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Markdown_LinkTarget_stop_x3f(v_s_824_, v_x_825_);
lean_dec_ref(v_x_825_);
lean_dec_ref(v_s_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destinationSource_x3f___redArg(lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_827_) == 0)
{
lean_object* v_destination_828_; lean_object* v___x_829_; 
v_destination_828_ = lean_ctor_get(v_x_827_, 1);
lean_inc_ref(v_destination_828_);
lean_dec_ref_known(v_x_827_, 4);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_destination_828_);
return v___x_829_;
}
else
{
lean_object* v_refTarget_830_; 
v_refTarget_830_ = lean_ctor_get(v_x_827_, 0);
lean_inc_ref(v_refTarget_830_);
lean_dec_ref_known(v_x_827_, 3);
if (lean_obj_tag(v_refTarget_830_) == 0)
{
lean_object* v_definition_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_839_; 
v_definition_831_ = lean_ctor_get(v_refTarget_830_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_refTarget_830_);
if (v_isSharedCheck_839_ == 0)
{
v___x_833_ = v_refTarget_830_;
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_definition_831_);
lean_dec(v_refTarget_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_839_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_destination_835_; lean_object* v___x_837_; 
v_destination_835_ = lean_ctor_get(v_definition_831_, 4);
lean_inc_ref(v_destination_835_);
lean_dec_ref(v_definition_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 1);
lean_ctor_set(v___x_833_, 0, v_destination_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_destination_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref_known(v_refTarget_830_, 1);
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destinationSource_x3f(lean_object* v_s_841_, lean_object* v_x_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Markdown_LinkTarget_destinationSource_x3f___redArg(v_x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destinationSource_x3f___boxed(lean_object* v_s_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Markdown_LinkTarget_destinationSource_x3f(v_s_844_, v_x_845_);
lean_dec_ref(v_s_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f___redArg(lean_object* v_x_847_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
lean_object* v_title_x3f_848_; 
v_title_x3f_848_ = lean_ctor_get(v_x_847_, 3);
lean_inc(v_title_x3f_848_);
return v_title_x3f_848_;
}
else
{
lean_object* v_refTarget_849_; 
v_refTarget_849_ = lean_ctor_get(v_x_847_, 0);
if (lean_obj_tag(v_refTarget_849_) == 0)
{
lean_object* v_definition_850_; lean_object* v_title_x3f_851_; 
v_definition_850_ = lean_ctor_get(v_refTarget_849_, 0);
v_title_x3f_851_ = lean_ctor_get(v_definition_850_, 5);
lean_inc(v_title_x3f_851_);
return v_title_x3f_851_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = lean_box(0);
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f___redArg___boxed(lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Markdown_LinkTarget_titleSource_x3f___redArg(v_x_853_);
lean_dec_ref(v_x_853_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f(lean_object* v_s_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Markdown_LinkTarget_titleSource_x3f___redArg(v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_titleSource_x3f___boxed(lean_object* v_s_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Markdown_LinkTarget_titleSource_x3f(v_s_858_, v_x_859_);
lean_dec_ref(v_x_859_);
lean_dec_ref(v_s_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destination(lean_object* v_s_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v_destination_863_; lean_object* v___x_864_; 
v_destination_863_ = lean_ctor_get(v_x_862_, 1);
v___x_864_ = l_Lean_Markdown_LinkDestination_text(v_s_861_, v_destination_863_);
return v___x_864_;
}
else
{
lean_object* v_refTarget_865_; lean_object* v___x_866_; 
v_refTarget_865_ = lean_ctor_get(v_x_862_, 0);
v___x_866_ = l_Lean_Markdown_RefTarget_destination(v_s_861_, v_refTarget_865_);
return v___x_866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_destination___boxed(lean_object* v_s_867_, lean_object* v_x_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Markdown_LinkTarget_destination(v_s_867_, v_x_868_);
lean_dec_ref(v_x_868_);
lean_dec_ref(v_s_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_title_x3f(lean_object* v_s_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v_title_x3f_872_; 
v_title_x3f_872_ = lean_ctor_get(v_x_871_, 3);
lean_inc(v_title_x3f_872_);
lean_dec_ref_known(v_x_871_, 4);
if (lean_obj_tag(v_title_x3f_872_) == 0)
{
lean_object* v___x_873_; 
v___x_873_ = lean_box(0);
return v___x_873_;
}
else
{
lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_882_; 
v_val_874_ = lean_ctor_get(v_title_x3f_872_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v_title_x3f_872_);
if (v_isSharedCheck_882_ == 0)
{
v___x_876_ = v_title_x3f_872_;
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_dec(v_title_x3f_872_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = l_Lean_Markdown_LinkTitle_text(v_s_870_, v_val_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_refTarget_883_; lean_object* v___x_884_; 
v_refTarget_883_ = lean_ctor_get(v_x_871_, 0);
lean_inc_ref(v_refTarget_883_);
lean_dec_ref_known(v_x_871_, 3);
v___x_884_ = l_Lean_Markdown_RefTarget_title_x3f(v_s_870_, v_refTarget_883_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkTarget_title_x3f___boxed(lean_object* v_s_885_, lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Markdown_LinkTarget_title_x3f(v_s_885_, v_x_886_);
lean_dec_ref(v_s_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extent___redArg(lean_object* v_x_888_){
_start:
{
switch(lean_obj_tag(v_x_888_))
{
case 0:
{
lean_object* v_range_889_; 
v_range_889_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_range_889_);
lean_dec_ref_known(v_x_888_, 1);
return v_range_889_;
}
case 4:
{
lean_object* v_openBracket_890_; lean_object* v_closeBracket_891_; lean_object* v_target_892_; lean_object* v_startInclusive_893_; lean_object* v___x_894_; 
v_openBracket_890_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_openBracket_890_);
v_closeBracket_891_ = lean_ctor_get(v_x_888_, 2);
lean_inc_ref(v_closeBracket_891_);
v_target_892_ = lean_ctor_get(v_x_888_, 3);
lean_inc_ref(v_target_892_);
lean_dec_ref_known(v_x_888_, 4);
v_startInclusive_893_ = lean_ctor_get(v_openBracket_890_, 0);
lean_inc(v_startInclusive_893_);
lean_dec_ref(v_openBracket_890_);
v___x_894_ = l_Lean_Markdown_LinkTarget_stop_x3f___redArg(v_target_892_);
lean_dec_ref(v_target_892_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_endExclusive_895_; lean_object* v___x_896_; 
v_endExclusive_895_ = lean_ctor_get(v_closeBracket_891_, 1);
lean_inc(v_endExclusive_895_);
lean_dec_ref(v_closeBracket_891_);
v___x_896_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_893_, v_endExclusive_895_);
return v___x_896_;
}
else
{
lean_object* v_val_897_; lean_object* v___x_898_; 
lean_dec_ref(v_closeBracket_891_);
v_val_897_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_894_, 1);
v___x_898_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_893_, v_val_897_);
return v___x_898_;
}
}
case 5:
{
lean_object* v_bang_899_; lean_object* v_closeBracket_900_; lean_object* v_target_901_; lean_object* v_startInclusive_902_; lean_object* v___x_903_; 
v_bang_899_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_bang_899_);
v_closeBracket_900_ = lean_ctor_get(v_x_888_, 3);
lean_inc_ref(v_closeBracket_900_);
v_target_901_ = lean_ctor_get(v_x_888_, 4);
lean_inc_ref(v_target_901_);
lean_dec_ref_known(v_x_888_, 5);
v_startInclusive_902_ = lean_ctor_get(v_bang_899_, 0);
lean_inc(v_startInclusive_902_);
lean_dec_ref(v_bang_899_);
v___x_903_ = l_Lean_Markdown_LinkTarget_stop_x3f___redArg(v_target_901_);
lean_dec_ref(v_target_901_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_endExclusive_904_; lean_object* v___x_905_; 
v_endExclusive_904_ = lean_ctor_get(v_closeBracket_900_, 1);
lean_inc(v_endExclusive_904_);
lean_dec_ref(v_closeBracket_900_);
v___x_905_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_902_, v_endExclusive_904_);
return v___x_905_;
}
else
{
lean_object* v_val_906_; lean_object* v___x_907_; 
lean_dec_ref(v_closeBracket_900_);
v_val_906_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_903_, 1);
v___x_907_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_902_, v_val_906_);
return v___x_907_;
}
}
case 6:
{
lean_object* v_marker_908_; lean_object* v_newline_909_; lean_object* v___x_910_; 
v_marker_908_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_marker_908_);
v_newline_909_ = lean_ctor_get(v_x_888_, 1);
lean_inc_ref(v_newline_909_);
lean_dec_ref_known(v_x_888_, 2);
v___x_910_ = l_Lean_Markdown_span___redArg(v_marker_908_, v_newline_909_);
return v___x_910_;
}
case 9:
{
lean_object* v_lines_911_; lean_object* v___x_912_; 
v_lines_911_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_lines_911_);
lean_dec_ref_known(v_x_888_, 1);
v___x_912_ = l_Lean_Markdown_Lines_extent___redArg(v_lines_911_);
lean_dec_ref(v_lines_911_);
return v___x_912_;
}
case 10:
{
lean_object* v_range_913_; 
v_range_913_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_range_913_);
lean_dec_ref_known(v_x_888_, 1);
return v_range_913_;
}
case 11:
{
lean_object* v_backslash_914_; lean_object* v_char_915_; lean_object* v___x_916_; 
v_backslash_914_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_backslash_914_);
v_char_915_ = lean_ctor_get(v_x_888_, 1);
lean_inc_ref(v_char_915_);
lean_dec_ref_known(v_x_888_, 2);
v___x_916_ = l_Lean_Markdown_span___redArg(v_backslash_914_, v_char_915_);
return v___x_916_;
}
case 12:
{
lean_object* v_range_917_; 
v_range_917_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_range_917_);
lean_dec_ref_known(v_x_888_, 2);
return v_range_917_;
}
default: 
{
lean_object* v_openTicks_918_; lean_object* v_closeTicks_919_; lean_object* v___x_920_; 
v_openTicks_918_ = lean_ctor_get(v_x_888_, 0);
lean_inc_ref(v_openTicks_918_);
v_closeTicks_919_ = lean_ctor_get(v_x_888_, 2);
lean_inc_ref(v_closeTicks_919_);
lean_dec_ref(v_x_888_);
v___x_920_ = l_Lean_Markdown_span___redArg(v_openTicks_918_, v_closeTicks_919_);
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extent(lean_object* v_s_921_, lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Markdown_Inline_extent___redArg(v_x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extent___boxed(lean_object* v_s_924_, lean_object* v_x_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Markdown_Inline_extent(v_s_924_, v_x_925_);
lean_dec_ref(v_s_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f___redArg(lean_object* v_inlines_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_array_get_size(v_inlines_927_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
v___x_931_ = lean_box(0);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_sub(v___x_929_, v___x_932_);
v___x_934_ = lean_nat_dec_lt(v___x_933_, v___x_929_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
lean_dec(v___x_933_);
v___x_935_ = lean_box(0);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_936_ = lean_array_fget_borrowed(v_inlines_927_, v___x_928_);
v___x_937_ = lean_array_fget_borrowed(v_inlines_927_, v___x_933_);
lean_dec(v___x_933_);
lean_inc(v___x_936_);
v___x_938_ = l_Lean_Markdown_Inline_extent___redArg(v___x_936_);
lean_inc(v___x_937_);
v___x_939_ = l_Lean_Markdown_Inline_extent___redArg(v___x_937_);
v___x_940_ = l_Lean_Markdown_span___redArg(v___x_938_, v___x_939_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f___redArg___boxed(lean_object* v_inlines_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Markdown_Inline_extentOf_x3f___redArg(v_inlines_942_);
lean_dec_ref(v_inlines_942_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f(lean_object* v_s_944_, lean_object* v_inlines_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Markdown_Inline_extentOf_x3f___redArg(v_inlines_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_extentOf_x3f___boxed(lean_object* v_s_947_, lean_object* v_inlines_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Markdown_Inline_extentOf_x3f(v_s_947_, v_inlines_948_);
lean_dec_ref(v_inlines_948_);
lean_dec_ref(v_s_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Inline_0__Lean_Markdown_Inline_plainText_go(lean_object* v_s_950_, lean_object* v_a_951_){
_start:
{
switch(lean_obj_tag(v_a_951_))
{
case 0:
{
lean_object* v_range_952_; lean_object* v_startInclusive_953_; lean_object* v_endExclusive_954_; lean_object* v_str_955_; lean_object* v_startInclusive_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_range_952_ = lean_ctor_get(v_a_951_, 0);
lean_inc_ref(v_range_952_);
lean_dec_ref_known(v_a_951_, 1);
v_startInclusive_953_ = lean_ctor_get(v_range_952_, 0);
lean_inc(v_startInclusive_953_);
v_endExclusive_954_ = lean_ctor_get(v_range_952_, 1);
lean_inc(v_endExclusive_954_);
lean_dec_ref(v_range_952_);
v_str_955_ = lean_ctor_get(v_s_950_, 0);
lean_inc_ref(v_str_955_);
v_startInclusive_956_ = lean_ctor_get(v_s_950_, 1);
lean_inc(v_startInclusive_956_);
lean_dec_ref(v_s_950_);
v___x_957_ = lean_nat_add(v_startInclusive_956_, v_startInclusive_953_);
lean_dec(v_startInclusive_953_);
v___x_958_ = lean_nat_add(v_startInclusive_956_, v_endExclusive_954_);
lean_dec(v_endExclusive_954_);
lean_dec(v_startInclusive_956_);
v___x_959_ = lean_string_utf8_extract_fast(v_str_955_, v___x_957_, v___x_958_);
lean_dec(v___x_958_);
lean_dec(v___x_957_);
lean_dec_ref(v_str_955_);
return v___x_959_;
}
case 1:
{
lean_object* v_content_960_; lean_object* v___x_961_; 
v_content_960_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_content_960_);
lean_dec_ref_known(v_a_951_, 3);
v___x_961_ = l_Lean_Markdown_InlineCodeContent_text(v_s_950_, v_content_960_);
lean_dec_ref(v_s_950_);
return v___x_961_;
}
case 2:
{
lean_object* v_content_962_; lean_object* v___x_963_; 
v_content_962_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_content_962_);
lean_dec_ref_known(v_a_951_, 3);
v___x_963_ = l_Lean_Markdown_Inline_plainText(v_s_950_, v_content_962_);
lean_dec_ref(v_content_962_);
return v___x_963_;
}
case 3:
{
lean_object* v_content_964_; lean_object* v___x_965_; 
v_content_964_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_content_964_);
lean_dec_ref_known(v_a_951_, 3);
v___x_965_ = l_Lean_Markdown_Inline_plainText(v_s_950_, v_content_964_);
lean_dec_ref(v_content_964_);
return v___x_965_;
}
case 4:
{
lean_object* v_text_966_; lean_object* v___x_967_; 
v_text_966_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_text_966_);
lean_dec_ref_known(v_a_951_, 4);
v___x_967_ = l_Lean_Markdown_Inline_plainText(v_s_950_, v_text_966_);
lean_dec_ref(v_text_966_);
return v___x_967_;
}
case 5:
{
lean_object* v_alt_968_; lean_object* v___x_969_; 
v_alt_968_ = lean_ctor_get(v_a_951_, 2);
lean_inc_ref(v_alt_968_);
lean_dec_ref_known(v_a_951_, 5);
v___x_969_ = l_Lean_Markdown_Inline_plainText(v_s_950_, v_alt_968_);
lean_dec_ref(v_alt_968_);
return v___x_969_;
}
case 7:
{
lean_object* v_url_970_; lean_object* v_startInclusive_971_; lean_object* v_endExclusive_972_; lean_object* v_str_973_; lean_object* v_startInclusive_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_url_970_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_url_970_);
lean_dec_ref_known(v_a_951_, 3);
v_startInclusive_971_ = lean_ctor_get(v_url_970_, 0);
lean_inc(v_startInclusive_971_);
v_endExclusive_972_ = lean_ctor_get(v_url_970_, 1);
lean_inc(v_endExclusive_972_);
lean_dec_ref(v_url_970_);
v_str_973_ = lean_ctor_get(v_s_950_, 0);
lean_inc_ref(v_str_973_);
v_startInclusive_974_ = lean_ctor_get(v_s_950_, 1);
lean_inc(v_startInclusive_974_);
lean_dec_ref(v_s_950_);
v___x_975_ = lean_nat_add(v_startInclusive_974_, v_startInclusive_971_);
lean_dec(v_startInclusive_971_);
v___x_976_ = lean_nat_add(v_startInclusive_974_, v_endExclusive_972_);
lean_dec(v_endExclusive_972_);
lean_dec(v_startInclusive_974_);
v___x_977_ = lean_string_utf8_extract_fast(v_str_973_, v___x_975_, v___x_976_);
lean_dec(v___x_976_);
lean_dec(v___x_975_);
lean_dec_ref(v_str_973_);
return v___x_977_;
}
case 8:
{
lean_object* v_content_978_; lean_object* v___x_979_; 
v_content_978_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_content_978_);
lean_dec_ref_known(v_a_951_, 3);
v___x_979_ = l_Lean_Markdown_MathContent_text(v_s_950_, v_content_978_);
return v___x_979_;
}
case 9:
{
lean_object* v___x_980_; 
lean_dec_ref_known(v_a_951_, 1);
lean_dec_ref(v_s_950_);
v___x_980_ = ((lean_object*)(l_Lean_Markdown_instInhabitedExternalRef_default___closed__0));
return v___x_980_;
}
case 11:
{
lean_object* v_char_981_; lean_object* v_startInclusive_982_; lean_object* v_endExclusive_983_; lean_object* v_str_984_; lean_object* v_startInclusive_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_char_981_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_char_981_);
lean_dec_ref_known(v_a_951_, 2);
v_startInclusive_982_ = lean_ctor_get(v_char_981_, 0);
lean_inc(v_startInclusive_982_);
v_endExclusive_983_ = lean_ctor_get(v_char_981_, 1);
lean_inc(v_endExclusive_983_);
lean_dec_ref(v_char_981_);
v_str_984_ = lean_ctor_get(v_s_950_, 0);
lean_inc_ref(v_str_984_);
v_startInclusive_985_ = lean_ctor_get(v_s_950_, 1);
lean_inc(v_startInclusive_985_);
lean_dec_ref(v_s_950_);
v___x_986_ = lean_nat_add(v_startInclusive_985_, v_startInclusive_982_);
lean_dec(v_startInclusive_982_);
v___x_987_ = lean_nat_add(v_startInclusive_985_, v_endExclusive_983_);
lean_dec(v_endExclusive_983_);
lean_dec(v_startInclusive_985_);
v___x_988_ = lean_string_utf8_extract_fast(v_str_984_, v___x_986_, v___x_987_);
lean_dec(v___x_987_);
lean_dec(v___x_986_);
lean_dec_ref(v_str_984_);
return v___x_988_;
}
case 12:
{
lean_object* v_value_989_; 
lean_dec_ref(v_s_950_);
v_value_989_ = lean_ctor_get(v_a_951_, 1);
lean_inc_ref(v_value_989_);
lean_dec_ref_known(v_a_951_, 2);
return v_value_989_;
}
default: 
{
lean_object* v___x_990_; 
lean_dec_ref(v_a_951_);
lean_dec_ref(v_s_950_);
v___x_990_ = ((lean_object*)(l_Lean_Markdown_LinkTitle_text___closed__0));
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_Inline_plainText_spec__1(lean_object* v_s_991_, lean_object* v_as_992_, size_t v_i_993_, size_t v_stop_994_, lean_object* v_b_995_){
_start:
{
uint8_t v___x_996_; 
v___x_996_ = lean_usize_dec_eq(v_i_993_, v_stop_994_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; size_t v___x_1000_; size_t v___x_1001_; 
v___x_997_ = lean_array_uget_borrowed(v_as_992_, v_i_993_);
lean_inc(v___x_997_);
lean_inc_ref(v_s_991_);
v___x_998_ = l___private_Lean_Data_Markdown_Inline_0__Lean_Markdown_Inline_plainText_go(v_s_991_, v___x_997_);
v___x_999_ = lean_string_append(v_b_995_, v___x_998_);
lean_dec_ref(v___x_998_);
v___x_1000_ = ((size_t)1ULL);
v___x_1001_ = lean_usize_add(v_i_993_, v___x_1000_);
v_i_993_ = v___x_1001_;
v_b_995_ = v___x_999_;
goto _start;
}
else
{
lean_dec_ref(v_s_991_);
return v_b_995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_plainText(lean_object* v_s_1003_, lean_object* v_inlines_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1005_ = ((lean_object*)(l_Lean_Markdown_instInhabitedExternalRef_default___closed__0));
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_array_get_size(v_inlines_1004_);
v___x_1008_ = lean_nat_dec_lt(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec_ref(v_s_1003_);
return v___x_1005_;
}
else
{
size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = lean_usize_of_nat(v___x_1007_);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_Inline_plainText_spec__1(v_s_1003_, v_inlines_1004_, v___x_1009_, v___x_1010_, v___x_1005_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Inline_plainText___boxed(lean_object* v_s_1012_, lean_object* v_inlines_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Markdown_Inline_plainText(v_s_1012_, v_inlines_1013_);
lean_dec_ref(v_inlines_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_Inline_plainText_spec__1___boxed(lean_object* v_s_1015_, lean_object* v_as_1016_, lean_object* v_i_1017_, lean_object* v_stop_1018_, lean_object* v_b_1019_){
_start:
{
size_t v_i_boxed_1020_; size_t v_stop_boxed_1021_; lean_object* v_res_1022_; 
v_i_boxed_1020_ = lean_unbox_usize(v_i_1017_);
lean_dec(v_i_1017_);
v_stop_boxed_1021_ = lean_unbox_usize(v_stop_1018_);
lean_dec(v_stop_1018_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Markdown_Inline_plainText_spec__1(v_s_1015_, v_as_1016_, v_i_boxed_1020_, v_stop_boxed_1021_, v_b_1019_);
lean_dec_ref(v_as_1016_);
return v_res_1022_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_instBEqLinkLabel_beq(lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_string_dec_eq(v_x_1023_, v_x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instBEqLinkLabel_beq___boxed(lean_object* v_x_1026_, lean_object* v_x_1027_){
_start:
{
uint8_t v_res_1028_; lean_object* v_r_1029_; 
v_res_1028_ = l_Lean_Markdown_instBEqLinkLabel_beq(v_x_1026_, v_x_1027_);
lean_dec_ref(v_x_1027_);
lean_dec_ref(v_x_1026_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT uint64_t l_Lean_Markdown_instHashableLinkLabel_hash(lean_object* v_x_1032_){
_start:
{
uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; 
v___x_1033_ = 0ULL;
v___x_1034_ = lean_string_hash(v_x_1032_);
v___x_1035_ = lean_uint64_mix_hash(v___x_1033_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instHashableLinkLabel_hash___boxed(lean_object* v_x_1036_){
_start:
{
uint64_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Lean_Markdown_instHashableLinkLabel_hash(v_x_1036_);
lean_dec_ref(v_x_1036_);
v_r_1038_ = lean_box_uint64(v_res_1037_);
return v_r_1038_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Markdown_instReprLinkLabel_repr_spec__0(lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_nat_to_int(v_a_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_unsigned_to_nat(8u);
v___x_1057_ = lean_nat_to_int(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__0));
v___x_1060_ = lean_string_length(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = lean_obj_once(&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__9, &l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__9_once, _init_l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__9);
v___x_1062_ = lean_nat_to_int(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprLinkLabel_repr___redArg(lean_object* v_x_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1068_ = ((lean_object*)(l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__6));
v___x_1069_ = lean_obj_once(&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__7, &l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__7_once, _init_l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__7);
v___x_1070_ = l_String_quote(v_x_1067_);
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1069_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = 0;
v___x_1074_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1068_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__10, &l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__10_once, _init_l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__10);
v___x_1077_ = ((lean_object*)(l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__11));
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1075_);
v___x_1079_ = ((lean_object*)(l_Lean_Markdown_instReprLinkLabel_repr___redArg___closed__12));
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1076_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*1, v___x_1073_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprLinkLabel_repr(lean_object* v_x_1083_, lean_object* v_prec_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Markdown_instReprLinkLabel_repr___redArg(v_x_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instReprLinkLabel_repr___boxed(lean_object* v_x_1086_, lean_object* v_prec_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Markdown_instReprLinkLabel_repr(v_x_1086_, v_prec_1087_);
lean_dec(v_prec_1087_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___lam__0(uint32_t v___x_1091_, uint8_t v_sawWs_1092_, uint8_t v___x_1093_, lean_object* v_____r_1094_, lean_object* v_out_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1096_ = l_Lean_Markdown_pushCaseFolded(v_out_1095_, v___x_1091_);
v___x_1097_ = lean_box(v_sawWs_1092_);
v___x_1098_ = lean_box(v___x_1093_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1096_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___lam__0___boxed(lean_object* v___x_1102_, lean_object* v_sawWs_1103_, lean_object* v___x_1104_, lean_object* v_____r_1105_, lean_object* v_out_1106_){
_start:
{
uint32_t v___x_1778__boxed_1107_; uint8_t v_sawWs_boxed_1108_; uint8_t v___x_1779__boxed_1109_; lean_object* v_res_1110_; 
v___x_1778__boxed_1107_ = lean_unbox_uint32(v___x_1102_);
lean_dec(v___x_1102_);
v_sawWs_boxed_1108_ = lean_unbox(v_sawWs_1103_);
v___x_1779__boxed_1109_ = lean_unbox(v___x_1104_);
v_res_1110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___lam__0(v___x_1778__boxed_1107_, v_sawWs_boxed_1108_, v___x_1779__boxed_1109_, v_____r_1105_, v_out_1106_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg(lean_object* v___x_1111_, lean_object* v___x_1112_, lean_object* v___x_1113_, lean_object* v_a_1114_, lean_object* v_b_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v_decide_1117_; 
v___x_1116_ = lean_nat_sub(v___x_1111_, v___x_1112_);
v_decide_1117_ = lean_nat_dec_eq(v_a_1114_, v___x_1116_);
lean_dec(v___x_1116_);
if (v_decide_1117_ == 0)
{
lean_object* v_snd_1118_; lean_object* v_fst_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1165_; 
v_snd_1118_ = lean_ctor_get(v_b_1115_, 1);
v_fst_1119_ = lean_ctor_get(v_b_1115_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_b_1115_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1121_ = v_b_1115_;
v_isShared_1122_ = v_isSharedCheck_1165_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_snd_1118_);
lean_inc(v_fst_1119_);
lean_dec(v_b_1115_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1165_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1164_; 
v_fst_1123_ = lean_ctor_get(v_snd_1118_, 0);
v_snd_1124_ = lean_ctor_get(v_snd_1118_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_snd_1118_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1126_ = v_snd_1118_;
v_isShared_1127_ = v_isSharedCheck_1164_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_snd_1124_);
lean_inc(v_fst_1123_);
lean_dec(v_snd_1118_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1164_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___y_1142_; uint32_t v___x_1146_; uint32_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1128_ = lean_nat_add(v___x_1112_, v_a_1114_);
lean_dec(v_a_1114_);
v___x_1129_ = lean_string_utf8_next_fast(v___x_1113_, v___x_1128_);
v___x_1130_ = lean_nat_sub(v___x_1129_, v___x_1112_);
v___x_1146_ = lean_string_utf8_get_fast(v___x_1113_, v___x_1128_);
lean_dec(v___x_1128_);
v___x_1147_ = 32;
v___x_1148_ = lean_uint32_dec_eq(v___x_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint32_t v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = 9;
v___x_1150_ = lean_uint32_dec_eq(v___x_1146_, v___x_1149_);
if (v___x_1150_ == 0)
{
uint32_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 13;
v___x_1152_ = lean_uint32_dec_eq(v___x_1146_, v___x_1151_);
if (v___x_1152_ == 0)
{
uint32_t v___x_1153_; uint8_t v_sawWs_1154_; 
v___x_1153_ = 10;
v_sawWs_1154_ = lean_uint32_dec_eq(v___x_1146_, v___x_1153_);
if (v_sawWs_1154_ == 0)
{
uint8_t v___x_1155_; uint8_t v___x_1159_; 
lean_del_object(v___x_1126_);
lean_del_object(v___x_1121_);
v___x_1155_ = 1;
v___x_1159_ = lean_unbox(v_snd_1124_);
lean_dec(v_snd_1124_);
if (v___x_1159_ == 0)
{
lean_dec(v_fst_1123_);
goto v___jp_1156_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_unbox(v_fst_1123_);
lean_dec(v_fst_1123_);
if (v___x_1160_ == 0)
{
goto v___jp_1156_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_string_push(v_fst_1119_, v___x_1147_);
v___x_1162_ = lean_box(0);
v___x_1163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___lam__0(v___x_1146_, v_sawWs_1154_, v___x_1155_, v___x_1162_, v___x_1161_);
v___y_1142_ = v___x_1163_;
goto v___jp_1141_;
}
}
v___jp_1156_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_box(0);
v___x_1158_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___lam__0(v___x_1146_, v_sawWs_1154_, v___x_1155_, v___x_1157_, v_fst_1119_);
v___y_1142_ = v___x_1158_;
goto v___jp_1141_;
}
}
else
{
lean_dec(v_fst_1123_);
goto v___jp_1131_;
}
}
else
{
lean_dec(v_fst_1123_);
goto v___jp_1131_;
}
}
else
{
lean_dec(v_fst_1123_);
goto v___jp_1131_;
}
}
else
{
lean_dec(v_fst_1123_);
goto v___jp_1131_;
}
v___jp_1131_:
{
uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = 1;
v___x_1133_ = lean_box(v___x_1132_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1133_);
v___x_1135_ = v___x_1126_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_snd_1124_);
v___x_1135_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1135_);
v___x_1137_ = v___x_1121_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_fst_1119_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
v_a_1114_ = v___x_1130_;
v_b_1115_ = v___x_1137_;
goto _start;
}
}
}
v___jp_1141_:
{
if (lean_obj_tag(v___y_1142_) == 0)
{
lean_object* v_a_1143_; 
lean_dec(v___x_1130_);
v_a_1143_ = lean_ctor_get(v___y_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___y_1142_, 1);
return v_a_1143_;
}
else
{
lean_object* v_a_1144_; 
v_a_1144_ = lean_ctor_get(v___y_1142_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___y_1142_, 1);
v_a_1114_ = v___x_1130_;
v_b_1115_ = v_a_1144_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_1114_);
return v_b_1115_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg___boxed(lean_object* v___x_1166_, lean_object* v___x_1167_, lean_object* v___x_1168_, lean_object* v_a_1169_, lean_object* v_b_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg(v___x_1166_, v___x_1167_, v___x_1168_, v_a_1169_, v_b_1170_);
lean_dec_ref(v___x_1168_);
lean_dec(v___x_1167_);
lean_dec(v___x_1166_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_normalizeLabel_spec__1(lean_object* v_s_1172_, lean_object* v_as_1173_, size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_b_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_lt(v_i_1175_, v_sz_1174_);
if (v___x_1177_ == 0)
{
return v_b_1176_;
}
else
{
lean_object* v_snd_1178_; lean_object* v_fst_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1226_; 
v_snd_1178_ = lean_ctor_get(v_b_1176_, 1);
v_fst_1179_ = lean_ctor_get(v_b_1176_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_b_1176_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1181_ = v_b_1176_;
v_isShared_1182_ = v_isSharedCheck_1226_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1179_);
lean_dec(v_b_1176_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1226_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1225_; 
v_fst_1183_ = lean_ctor_get(v_snd_1178_, 0);
v_snd_1184_ = lean_ctor_get(v_snd_1178_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_snd_1178_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1186_ = v_snd_1178_;
v_isShared_1187_ = v_isSharedCheck_1225_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_snd_1184_);
lean_inc(v_fst_1183_);
lean_dec(v_snd_1178_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1225_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_a_1188_; lean_object* v_startInclusive_1189_; lean_object* v_endExclusive_1190_; lean_object* v_str_1191_; lean_object* v_startInclusive_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v_a_1188_ = lean_array_uget_borrowed(v_as_1173_, v_i_1175_);
v_startInclusive_1189_ = lean_ctor_get(v_a_1188_, 0);
v_endExclusive_1190_ = lean_ctor_get(v_a_1188_, 1);
v_str_1191_ = lean_ctor_get(v_s_1172_, 0);
v_startInclusive_1192_ = lean_ctor_get(v_s_1172_, 1);
v___x_1193_ = lean_nat_add(v_startInclusive_1192_, v_startInclusive_1189_);
v___x_1194_ = lean_nat_add(v_startInclusive_1192_, v_endExclusive_1190_);
if (v_isShared_1187_ == 0)
{
v___x_1196_ = v___x_1186_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_fst_1183_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_snd_1184_);
v___x_1196_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1196_);
v___x_1198_ = v___x_1181_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_snd_1201_; lean_object* v_fst_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1222_; 
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg(v___x_1194_, v___x_1193_, v_str_1191_, v___x_1199_, v___x_1198_);
lean_dec(v___x_1193_);
lean_dec(v___x_1194_);
v_snd_1201_ = lean_ctor_get(v___x_1200_, 1);
v_fst_1202_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_snd_1201_);
lean_inc(v_fst_1202_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_snd_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1220_; 
v_snd_1206_ = lean_ctor_get(v_snd_1201_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_snd_1201_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_snd_1201_, 0);
lean_dec(v_unused_1221_);
v___x_1208_ = v_snd_1201_;
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snd_1206_);
lean_dec(v_snd_1201_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_box(v___x_1177_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_snd_1206_);
v___x_1212_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1214_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1212_);
v___x_1214_ = v___x_1204_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_fst_1202_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
size_t v___x_1215_; size_t v___x_1216_; 
v___x_1215_ = ((size_t)1ULL);
v___x_1216_ = lean_usize_add(v_i_1175_, v___x_1215_);
v_i_1175_ = v___x_1216_;
v_b_1176_ = v___x_1214_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_normalizeLabel_spec__1___boxed(lean_object* v_s_1227_, lean_object* v_as_1228_, lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_b_1231_){
_start:
{
size_t v_sz_boxed_1232_; size_t v_i_boxed_1233_; lean_object* v_res_1234_; 
v_sz_boxed_1232_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1233_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_normalizeLabel_spec__1(v_s_1227_, v_as_1228_, v_sz_boxed_1232_, v_i_boxed_1233_, v_b_1231_);
lean_dec_ref(v_as_1228_);
lean_dec_ref(v_s_1227_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_normalizeLabel(lean_object* v_s_1242_, lean_object* v_lines_1243_){
_start:
{
lean_object* v___x_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v_fst_1248_; 
v___x_1244_ = ((lean_object*)(l_Lean_Markdown_normalizeLabel___closed__1));
v_sz_1245_ = lean_array_size(v_lines_1243_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_normalizeLabel_spec__1(v_s_1242_, v_lines_1243_, v_sz_1245_, v___x_1246_, v___x_1244_);
v_fst_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_fst_1248_);
lean_dec_ref(v___x_1247_);
return v_fst_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_normalizeLabel___boxed(lean_object* v_s_1249_, lean_object* v_lines_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Markdown_normalizeLabel(v_s_1249_, v_lines_1250_);
lean_dec_ref(v_lines_1250_);
lean_dec_ref(v_s_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0(lean_object* v___x_1252_, lean_object* v___x_1253_, lean_object* v___x_1254_, lean_object* v___x_1255_, lean_object* v_inst_1256_, lean_object* v_R_1257_, lean_object* v_a_1258_, lean_object* v_b_1259_, lean_object* v_c_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___redArg(v___x_1252_, v___x_1253_, v___x_1255_, v_a_1258_, v_b_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0___boxed(lean_object* v___x_1262_, lean_object* v___x_1263_, lean_object* v___x_1264_, lean_object* v___x_1265_, lean_object* v_inst_1266_, lean_object* v_R_1267_, lean_object* v_a_1268_, lean_object* v_b_1269_, lean_object* v_c_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Markdown_normalizeLabel_spec__0(v___x_1262_, v___x_1263_, v___x_1264_, v___x_1265_, v_inst_1266_, v_R_1267_, v_a_1268_, v_b_1269_, v_c_1270_);
lean_dec_ref(v___x_1265_);
lean_dec_ref(v___x_1264_);
lean_dec(v___x_1263_);
lean_dec(v___x_1262_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_LinkLabel_ofString(lean_object* v_label_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_string_utf8_byte_size(v_label_1272_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_label_1272_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1273_);
lean_ctor_set(v___x_1276_, 1, v___x_1274_);
v___x_1277_ = l_Lean_Markdown_Lines_singleton___redArg(v___x_1276_);
v___x_1278_ = l_Lean_Markdown_normalizeLabel(v___x_1275_, v___x_1277_);
lean_dec_ref(v___x_1277_);
lean_dec_ref_known(v___x_1275_, 3);
return v___x_1278_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Unicode_CaseFolding(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Text(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Lines(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Inline(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Unicode_CaseFolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Lines(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Markdown_instInhabitedExtensions_default = _init_l_Lean_Markdown_instInhabitedExtensions_default();
l_Lean_Markdown_instInhabitedExtensions = _init_l_Lean_Markdown_instInhabitedExtensions();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Inline(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Unicode_CaseFolding(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Text(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Lines(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Inline(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Unicode_CaseFolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Text(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Lines(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Inline(builtin);
}
#ifdef __cplusplus
}
#endif
