// Lean compiler output
// Module: Init.Data.Range.Polymorphic.PRange
// Imports: public import Init.Data.Range.Polymorphic.UpwardEnumerable
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii_decEq___redArg();
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii___redArg();
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_term___x2e_x2e_x2e_x2a___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x2a___closed__0 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x2a___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_...*"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x2a___closed__1 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__1_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x2a___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x2a___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__2_value_aux_0),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 184, 85, 23, 243, 11, 13, 179)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x2a___closed__2 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__2_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x2a___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "...*"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x2a___closed__3 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__3_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x2a___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__3_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x2a___closed__4 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__4_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x2a___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__2_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__4_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x2a___closed__5 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term___x2e_x2e_x2e_x2a = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__5_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term*...*"};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value_aux_0),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 9, 100, 11, 112, 109, 114, 219)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "*...*"};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__2_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__3_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x2a = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__4_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_<...*"};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value_aux_0),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 27, 224, 193, 208, 224, 37, 254)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<...*"};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__2_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value;
LEAN_EXPORT const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x2a = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_...<_"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__0 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value_aux_0),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 56, 180, 150, 42, 67, 215, 61)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__1 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__2 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__3 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "...<"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__4 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__4_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__5 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__6 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__7 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__8 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__9 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__10 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value;
LEAN_EXPORT const lean_object* l_Std_term___x2e_x2e_x2e_x3c__ = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_..._"};
static const lean_object* l_Std_term___x2e_x2e_x2e___00__closed__0 = (const lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__0_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x2e_x2e_x2e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__1_value_aux_0),((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 215, 136, 196, 225, 228, 219, 74)}};
static const lean_object* l_Std_term___x2e_x2e_x2e___00__closed__1 = (const lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__1_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "..."};
static const lean_object* l_Std_term___x2e_x2e_x2e___00__closed__2 = (const lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__2_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__2_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e___00__closed__3 = (const lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__3_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e___00__closed__4 = (const lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__4_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__4_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e___00__closed__5 = (const lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term___x2e_x2e_x2e__ = (const lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__5_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term*...<_"};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 95, 249, 207, 5, 93, 41, 245)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "*...<"};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__2_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__4_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3c__ = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__5_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term*..._"};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e___00__closed__0 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value_aux_0),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 214, 10, 96, 112, 57, 139, 148)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e___00__closed__1 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "*..."};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e___00__closed__2 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__2_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e___00__closed__3 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e___00__closed__4 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__4_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e___00__closed__5 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term_x2a_x2e_x2e_x2e__ = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e___00__closed__5_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term_<...<_"};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value_aux_0),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 24, 184, 113, 209, 224, 82, 248)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<...<"};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__2_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3c__ = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_<..._"};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e___00__closed__0 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value_aux_0),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 200, 25, 103, 90, 101, 53, 48)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e___00__closed__1 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "<..."};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e___00__closed__2 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__2_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e___00__closed__3 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e___00__closed__4 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e___00__closed__5 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term___x3c_x2e_x2e_x2e__ = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_...=_"};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3d___00__closed__0 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 81, 4, 194, 158, 170, 93, 115)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3d___00__closed__1 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value;
static const lean_string_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "...="};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3d___00__closed__2 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__2_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3d___00__closed__3 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3d___00__closed__4 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3d___00__closed__5 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term___x2e_x2e_x2e_x3d__ = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term*...=_"};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 142, 110, 52, 44, 186, 117, 12)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value;
static const lean_string_object l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "*...="};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__2_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value;
static const lean_ctor_object l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__4_value)}};
static const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5 = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term_x2a_x2e_x2e_x2e_x3d__ = (const lean_object*)&l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__5_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term_<...=_"};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value_aux_0),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 72, 254, 139, 229, 96, 28, 211)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value;
static const lean_string_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<...="};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__2_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value;
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value)}};
static const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5 = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_term___x3c_x2e_x2e_x2e_x3d__ = (const lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value_aux_2),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Rcc.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rcc"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(175, 69, 185, 129, 244, 236, 185, 225)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(131, 107, 95, 242, 110, 199, 227, 122)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 238, 58, 56, 209, 114, 29, 228)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(0, 21, 116, 230, 181, 124, 77, 220)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__10_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__11_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__13_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14_value;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Ric.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ric"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(118, 93, 82, 58, 11, 2, 27, 222)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(6, 120, 153, 215, 244, 147, 168, 99)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 67, 230, 246, 155, 76, 10, 120)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(181, 130, 117, 53, 80, 95, 78, 116)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Rci.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rci"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(188, 174, 152, 104, 54, 96, 0, 97)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(116, 248, 156, 94, 192, 235, 212, 242)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(83, 90, 19, 212, 182, 193, 89, 16)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(167, 71, 120, 0, 165, 65, 50, 6)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Rii.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rii"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 86, 88, 80, 224, 91, 82, 111)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 103, 39, 227, 122, 142, 212, 182)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(204, 10, 192, 182, 218, 42, 98, 220)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(100, 56, 191, 92, 38, 6, 135, 82)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Roc.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Roc"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 253, 213, 29, 242, 199, 8, 132)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(135, 0, 201, 39, 192, 159, 244, 192)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(28, 166, 87, 113, 118, 177, 150, 230)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(84, 163, 94, 134, 20, 241, 197, 229)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Roi.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Roi"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 149, 179, 188, 144, 198, 181, 247)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(16, 75, 38, 248, 8, 57, 232, 97)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(95, 65, 216, 85, 31, 94, 16, 225)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(83, 142, 250, 85, 106, 40, 159, 95)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Rco.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rco"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(149, 196, 187, 21, 78, 72, 98, 231)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(17, 46, 121, 249, 21, 194, 251, 19)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(82, 23, 146, 9, 98, 233, 127, 0)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(18, 93, 179, 105, 68, 67, 235, 201)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Rio.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rio"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(238, 197, 64, 120, 99, 67, 210, 243)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(46, 103, 21, 135, 36, 136, 183, 160)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 16, 150, 7, 181, 46, 199, 145)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(13, 133, 49, 73, 31, 216, 201, 63)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Roo.mk"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0_value;
static lean_once_cell_t l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1;
static const lean_string_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Roo"};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(33, 37, 125, 112, 69, 74, 250, 21)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(45, 20, 213, 36, 156, 9, 113, 195)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_0),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 134, 1, 143, 80, 181, 102, 249)}};
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value_aux_1),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(78, 122, 174, 114, 50, 86, 67, 250)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__4_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value;
static const lean_ctor_object l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__5_value),((lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__7_value)}};
static const lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8 = (const lean_object*)&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8_value;
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE___redArg();
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT___redArg();
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE___redArg();
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT___redArg();
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT___redArg();
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT___redArg();
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE___redArg();
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT___redArg();
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_Rii_instMembership___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_instMembership(lean_object*);
LEAN_EXPORT uint8_t l_Std_Rii_instDecidableMem___redArg();
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Rii_instDecidableMem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc_decEq___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_lower_4_; lean_object* v_upper_5_; lean_object* v_lower_6_; lean_object* v_upper_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_lower_4_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_lower_4_);
v_upper_5_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_upper_5_);
lean_dec_ref(v_x_2_);
v_lower_6_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_lower_6_);
v_upper_7_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_upper_7_);
lean_dec_ref(v_x_3_);
lean_inc_ref(v_inst_1_);
v___x_8_ = lean_apply_2(v_inst_1_, v_lower_4_, v_lower_6_);
v___x_9_ = lean_unbox(v___x_8_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
lean_dec(v_upper_7_);
lean_dec(v_upper_5_);
lean_dec_ref(v_inst_1_);
v___x_10_ = lean_unbox(v___x_8_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_apply_2(v_inst_1_, v_upper_5_, v_upper_7_);
v___x_12_ = lean_unbox(v___x_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc_decEq___redArg___boxed(lean_object* v_inst_13_, lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_13_, v_x_14_, v_x_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc_decEq(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_19_, v_x_20_, v_x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc_decEq___boxed(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Std_instDecidableEqRcc_decEq(v_00_u03b1_23_, v_inst_24_, v_x_25_, v_x_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc___redArg(lean_object* v_inst_29_, lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_29_, v_x_30_, v_x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc___redArg___boxed(lean_object* v_inst_33_, lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Std_instDecidableEqRcc___redArg(v_inst_33_, v_x_34_, v_x_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRcc(lean_object* v_00_u03b1_38_, lean_object* v_inst_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_39_, v_x_40_, v_x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc___boxed(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Std_instDecidableEqRcc(v_00_u03b1_43_, v_inst_44_, v_x_45_, v_x_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco_decEq___redArg(lean_object* v_inst_49_, lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_lower_52_; lean_object* v_upper_53_; lean_object* v_lower_54_; lean_object* v_upper_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v_lower_52_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_lower_52_);
v_upper_53_ = lean_ctor_get(v_x_50_, 1);
lean_inc(v_upper_53_);
lean_dec_ref(v_x_50_);
v_lower_54_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_lower_54_);
v_upper_55_ = lean_ctor_get(v_x_51_, 1);
lean_inc(v_upper_55_);
lean_dec_ref(v_x_51_);
lean_inc_ref(v_inst_49_);
v___x_56_ = lean_apply_2(v_inst_49_, v_lower_52_, v_lower_54_);
v___x_57_ = lean_unbox(v___x_56_);
if (v___x_57_ == 0)
{
uint8_t v___x_58_; 
lean_dec(v_upper_55_);
lean_dec(v_upper_53_);
lean_dec_ref(v_inst_49_);
v___x_58_ = lean_unbox(v___x_56_);
return v___x_58_;
}
else
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_apply_2(v_inst_49_, v_upper_53_, v_upper_55_);
v___x_60_ = lean_unbox(v___x_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco_decEq___redArg___boxed(lean_object* v_inst_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_61_, v_x_62_, v_x_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco_decEq(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_67_, v_x_68_, v_x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco_decEq___boxed(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Std_instDecidableEqRco_decEq(v_00_u03b1_71_, v_inst_72_, v_x_73_, v_x_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco___redArg(lean_object* v_inst_77_, lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_77_, v_x_78_, v_x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco___redArg___boxed(lean_object* v_inst_81_, lean_object* v_x_82_, lean_object* v_x_83_){
_start:
{
uint8_t v_res_84_; lean_object* v_r_85_; 
v_res_84_ = l_Std_instDecidableEqRco___redArg(v_inst_81_, v_x_82_, v_x_83_);
v_r_85_ = lean_box(v_res_84_);
return v_r_85_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRco(lean_object* v_00_u03b1_86_, lean_object* v_inst_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_87_, v_x_88_, v_x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco___boxed(lean_object* v_00_u03b1_91_, lean_object* v_inst_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Std_instDecidableEqRco(v_00_u03b1_91_, v_inst_92_, v_x_93_, v_x_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci_decEq___redArg(lean_object* v_inst_97_, lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_apply_2(v_inst_97_, v_x_98_, v_x_99_);
v___x_101_ = lean_unbox(v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci_decEq___redArg___boxed(lean_object* v_inst_102_, lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Std_instDecidableEqRci_decEq___redArg(v_inst_102_, v_x_103_, v_x_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci_decEq(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_apply_2(v_inst_108_, v_x_109_, v_x_110_);
v___x_112_ = lean_unbox(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci_decEq___boxed(lean_object* v_00_u03b1_113_, lean_object* v_inst_114_, lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Std_instDecidableEqRci_decEq(v_00_u03b1_113_, v_inst_114_, v_x_115_, v_x_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci___redArg(lean_object* v_inst_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_apply_2(v_inst_119_, v_x_120_, v_x_121_);
v___x_123_ = lean_unbox(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci___redArg___boxed(lean_object* v_inst_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_instDecidableEqRci___redArg(v_inst_124_, v_x_125_, v_x_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRci(lean_object* v_00_u03b1_129_, lean_object* v_inst_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_apply_2(v_inst_130_, v_x_131_, v_x_132_);
v___x_134_ = lean_unbox(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci___boxed(lean_object* v_00_u03b1_135_, lean_object* v_inst_136_, lean_object* v_x_137_, lean_object* v_x_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Std_instDecidableEqRci(v_00_u03b1_135_, v_inst_136_, v_x_137_, v_x_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc_decEq___redArg(lean_object* v_inst_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
lean_object* v_lower_144_; lean_object* v_upper_145_; lean_object* v_lower_146_; lean_object* v_upper_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v_lower_144_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_lower_144_);
v_upper_145_ = lean_ctor_get(v_x_142_, 1);
lean_inc(v_upper_145_);
lean_dec_ref(v_x_142_);
v_lower_146_ = lean_ctor_get(v_x_143_, 0);
lean_inc(v_lower_146_);
v_upper_147_ = lean_ctor_get(v_x_143_, 1);
lean_inc(v_upper_147_);
lean_dec_ref(v_x_143_);
lean_inc_ref(v_inst_141_);
v___x_148_ = lean_apply_2(v_inst_141_, v_lower_144_, v_lower_146_);
v___x_149_ = lean_unbox(v___x_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
lean_dec(v_upper_147_);
lean_dec(v_upper_145_);
lean_dec_ref(v_inst_141_);
v___x_150_ = lean_unbox(v___x_148_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_apply_2(v_inst_141_, v_upper_145_, v_upper_147_);
v___x_152_ = lean_unbox(v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc_decEq___redArg___boxed(lean_object* v_inst_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_153_, v_x_154_, v_x_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc_decEq(lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_159_, v_x_160_, v_x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc_decEq___boxed(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Std_instDecidableEqRoc_decEq(v_00_u03b1_163_, v_inst_164_, v_x_165_, v_x_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc___redArg(lean_object* v_inst_169_, lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_169_, v_x_170_, v_x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc___redArg___boxed(lean_object* v_inst_173_, lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Std_instDecidableEqRoc___redArg(v_inst_173_, v_x_174_, v_x_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoc(lean_object* v_00_u03b1_178_, lean_object* v_inst_179_, lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_179_, v_x_180_, v_x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc___boxed(lean_object* v_00_u03b1_183_, lean_object* v_inst_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = l_Std_instDecidableEqRoc(v_00_u03b1_183_, v_inst_184_, v_x_185_, v_x_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo_decEq___redArg(lean_object* v_inst_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_lower_192_; lean_object* v_upper_193_; lean_object* v_lower_194_; lean_object* v_upper_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_lower_192_ = lean_ctor_get(v_x_190_, 0);
lean_inc(v_lower_192_);
v_upper_193_ = lean_ctor_get(v_x_190_, 1);
lean_inc(v_upper_193_);
lean_dec_ref(v_x_190_);
v_lower_194_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_lower_194_);
v_upper_195_ = lean_ctor_get(v_x_191_, 1);
lean_inc(v_upper_195_);
lean_dec_ref(v_x_191_);
lean_inc_ref(v_inst_189_);
v___x_196_ = lean_apply_2(v_inst_189_, v_lower_192_, v_lower_194_);
v___x_197_ = lean_unbox(v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
lean_dec(v_upper_195_);
lean_dec(v_upper_193_);
lean_dec_ref(v_inst_189_);
v___x_198_ = lean_unbox(v___x_196_);
return v___x_198_;
}
else
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_apply_2(v_inst_189_, v_upper_193_, v_upper_195_);
v___x_200_ = lean_unbox(v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo_decEq___redArg___boxed(lean_object* v_inst_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_201_, v_x_202_, v_x_203_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo_decEq(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_207_, v_x_208_, v_x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo_decEq___boxed(lean_object* v_00_u03b1_211_, lean_object* v_inst_212_, lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Std_instDecidableEqRoo_decEq(v_00_u03b1_211_, v_inst_212_, v_x_213_, v_x_214_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo___redArg(lean_object* v_inst_217_, lean_object* v_x_218_, lean_object* v_x_219_){
_start:
{
uint8_t v___x_220_; 
v___x_220_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_217_, v_x_218_, v_x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo___redArg___boxed(lean_object* v_inst_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Std_instDecidableEqRoo___redArg(v_inst_221_, v_x_222_, v_x_223_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoo(lean_object* v_00_u03b1_226_, lean_object* v_inst_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
uint8_t v___x_230_; 
v___x_230_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_227_, v_x_228_, v_x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo___boxed(lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Std_instDecidableEqRoo(v_00_u03b1_231_, v_inst_232_, v_x_233_, v_x_234_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi_decEq___redArg(lean_object* v_inst_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_apply_2(v_inst_237_, v_x_238_, v_x_239_);
v___x_241_ = lean_unbox(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi_decEq___redArg___boxed(lean_object* v_inst_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Std_instDecidableEqRoi_decEq___redArg(v_inst_242_, v_x_243_, v_x_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi_decEq(lean_object* v_00_u03b1_247_, lean_object* v_inst_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_apply_2(v_inst_248_, v_x_249_, v_x_250_);
v___x_252_ = lean_unbox(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi_decEq___boxed(lean_object* v_00_u03b1_253_, lean_object* v_inst_254_, lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_instDecidableEqRoi_decEq(v_00_u03b1_253_, v_inst_254_, v_x_255_, v_x_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi___redArg(lean_object* v_inst_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_apply_2(v_inst_259_, v_x_260_, v_x_261_);
v___x_263_ = lean_unbox(v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi___redArg___boxed(lean_object* v_inst_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Std_instDecidableEqRoi___redArg(v_inst_264_, v_x_265_, v_x_266_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRoi(lean_object* v_00_u03b1_269_, lean_object* v_inst_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_apply_2(v_inst_270_, v_x_271_, v_x_272_);
v___x_274_ = lean_unbox(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi___boxed(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_instDecidableEqRoi(v_00_u03b1_275_, v_inst_276_, v_x_277_, v_x_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic_decEq___redArg(lean_object* v_inst_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_apply_2(v_inst_281_, v_x_282_, v_x_283_);
v___x_285_ = lean_unbox(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic_decEq___redArg___boxed(lean_object* v_inst_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_instDecidableEqRic_decEq___redArg(v_inst_286_, v_x_287_, v_x_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic_decEq(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_apply_2(v_inst_292_, v_x_293_, v_x_294_);
v___x_296_ = lean_unbox(v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic_decEq___boxed(lean_object* v_00_u03b1_297_, lean_object* v_inst_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Std_instDecidableEqRic_decEq(v_00_u03b1_297_, v_inst_298_, v_x_299_, v_x_300_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic___redArg(lean_object* v_inst_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = lean_apply_2(v_inst_303_, v_x_304_, v_x_305_);
v___x_307_ = lean_unbox(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic___redArg___boxed(lean_object* v_inst_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Std_instDecidableEqRic___redArg(v_inst_308_, v_x_309_, v_x_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRic(lean_object* v_00_u03b1_313_, lean_object* v_inst_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_apply_2(v_inst_314_, v_x_315_, v_x_316_);
v___x_318_ = lean_unbox(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic___boxed(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_instDecidableEqRic(v_00_u03b1_319_, v_inst_320_, v_x_321_, v_x_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio_decEq___redArg(lean_object* v_inst_325_, lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_apply_2(v_inst_325_, v_x_326_, v_x_327_);
v___x_329_ = lean_unbox(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio_decEq___redArg___boxed(lean_object* v_inst_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Std_instDecidableEqRio_decEq___redArg(v_inst_330_, v_x_331_, v_x_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio_decEq(lean_object* v_00_u03b1_335_, lean_object* v_inst_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_apply_2(v_inst_336_, v_x_337_, v_x_338_);
v___x_340_ = lean_unbox(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio_decEq___boxed(lean_object* v_00_u03b1_341_, lean_object* v_inst_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
uint8_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = l_Std_instDecidableEqRio_decEq(v_00_u03b1_341_, v_inst_342_, v_x_343_, v_x_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio___redArg(lean_object* v_inst_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_apply_2(v_inst_347_, v_x_348_, v_x_349_);
v___x_351_ = lean_unbox(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio___redArg___boxed(lean_object* v_inst_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Std_instDecidableEqRio___redArg(v_inst_352_, v_x_353_, v_x_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRio(lean_object* v_00_u03b1_357_, lean_object* v_inst_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_apply_2(v_inst_358_, v_x_359_, v_x_360_);
v___x_362_ = lean_unbox(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio___boxed(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Std_instDecidableEqRio(v_00_u03b1_363_, v_inst_364_, v_x_365_, v_x_366_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii_decEq___redArg(){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = 1;
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___redArg___boxed(lean_object* v___dummy_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Std_instDecidableEqRii_decEq___redArg();
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii_decEq(lean_object* v_00_u03b1_374_, lean_object* v_inst_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = 1;
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___boxed(lean_object* v_00_u03b1_379_, lean_object* v_inst_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Std_instDecidableEqRii_decEq(v_00_u03b1_379_, v_inst_380_, v_x_381_, v_x_382_);
lean_dec_ref(v_inst_380_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii___redArg(){
_start:
{
uint8_t v___x_386_; 
v___x_386_ = 1;
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii___redArg___boxed(lean_object* v___dummy_387_){
_start:
{
uint8_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Std_instDecidableEqRii___redArg();
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii(lean_object* v_00_u03b1_390_, lean_object* v_inst_391_, lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = 1;
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii___boxed(lean_object* v_00_u03b1_395_, lean_object* v_inst_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Std_instDecidableEqRii(v_00_u03b1_395_, v_inst_396_, v_x_397_, v_x_398_);
lean_dec_ref(v_inst_396_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5));
v___x_610_ = l_String_toRawSubstring_x27(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(lean_object* v_x_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_634_);
v___x_638_ = l_Lean_Syntax_isOfKind(v_x_634_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v_x_634_);
v___x_639_ = lean_box(1);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
lean_ctor_set(v___x_640_, 1, v_a_636_);
return v___x_640_;
}
else
{
lean_object* v_quotContext_641_; lean_object* v_currMacroScope_642_; lean_object* v_ref_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_quotContext_641_ = lean_ctor_get(v_a_635_, 1);
v_currMacroScope_642_ = lean_ctor_get(v_a_635_, 2);
v_ref_643_ = lean_ctor_get(v_a_635_, 5);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = l_Lean_Syntax_getArg(v_x_634_, v___x_644_);
v___x_646_ = lean_unsigned_to_nat(2u);
v___x_647_ = l_Lean_Syntax_getArg(v_x_634_, v___x_646_);
lean_dec(v_x_634_);
v___x_648_ = 0;
v___x_649_ = l_Lean_SourceInfo_fromRef(v_ref_643_, v___x_648_);
v___x_650_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_651_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6);
v___x_652_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9));
lean_inc(v_currMacroScope_642_);
lean_inc(v_quotContext_641_);
v___x_653_ = l_Lean_addMacroScope(v_quotContext_641_, v___x_652_, v_currMacroScope_642_);
v___x_654_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14));
lean_inc_n(v___x_649_, 2);
v___x_655_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_655_, 0, v___x_649_);
lean_ctor_set(v___x_655_, 1, v___x_651_);
lean_ctor_set(v___x_655_, 2, v___x_653_);
lean_ctor_set(v___x_655_, 3, v___x_654_);
v___x_656_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_657_ = l_Lean_Syntax_node2(v___x_649_, v___x_656_, v___x_645_, v___x_647_);
v___x_658_ = l_Lean_Syntax_node2(v___x_649_, v___x_650_, v___x_655_, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_a_636_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(v_x_660_, v_a_661_, v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_663_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0));
v___x_666_ = l_String_toRawSubstring_x27(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(lean_object* v_x_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_686_);
v___x_690_ = l_Lean_Syntax_isOfKind(v_x_686_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_x_686_);
v___x_691_ = lean_box(1);
v___x_692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v_a_688_);
return v___x_692_;
}
else
{
lean_object* v_quotContext_693_; lean_object* v_currMacroScope_694_; lean_object* v_ref_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_quotContext_693_ = lean_ctor_get(v_a_687_, 1);
v_currMacroScope_694_ = lean_ctor_get(v_a_687_, 2);
v_ref_695_ = lean_ctor_get(v_a_687_, 5);
v___x_696_ = lean_unsigned_to_nat(1u);
v___x_697_ = l_Lean_Syntax_getArg(v_x_686_, v___x_696_);
lean_dec(v_x_686_);
v___x_698_ = 0;
v___x_699_ = l_Lean_SourceInfo_fromRef(v_ref_695_, v___x_698_);
v___x_700_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_701_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1);
v___x_702_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3));
lean_inc(v_currMacroScope_694_);
lean_inc(v_quotContext_693_);
v___x_703_ = l_Lean_addMacroScope(v_quotContext_693_, v___x_702_, v_currMacroScope_694_);
v___x_704_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc_n(v___x_699_, 2);
v___x_705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_705_, 0, v___x_699_);
lean_ctor_set(v___x_705_, 1, v___x_701_);
lean_ctor_set(v___x_705_, 2, v___x_703_);
lean_ctor_set(v___x_705_, 3, v___x_704_);
v___x_706_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_707_ = l_Lean_Syntax_node1(v___x_699_, v___x_706_, v___x_697_);
v___x_708_ = l_Lean_Syntax_node2(v___x_699_, v___x_700_, v___x_705_, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_a_688_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(v_x_710_, v_a_711_, v_a_712_);
lean_dec_ref(v_a_711_);
return v_res_713_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0));
v___x_716_ = l_String_toRawSubstring_x27(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(lean_object* v_x_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x2a___closed__2));
lean_inc(v_x_736_);
v___x_740_ = l_Lean_Syntax_isOfKind(v_x_736_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_x_736_);
v___x_741_ = lean_box(1);
v___x_742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v_a_738_);
return v___x_742_;
}
else
{
lean_object* v_quotContext_743_; lean_object* v_currMacroScope_744_; lean_object* v_ref_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_quotContext_743_ = lean_ctor_get(v_a_737_, 1);
v_currMacroScope_744_ = lean_ctor_get(v_a_737_, 2);
v_ref_745_ = lean_ctor_get(v_a_737_, 5);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = l_Lean_Syntax_getArg(v_x_736_, v___x_746_);
lean_dec(v_x_736_);
v___x_748_ = 0;
v___x_749_ = l_Lean_SourceInfo_fromRef(v_ref_745_, v___x_748_);
v___x_750_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_751_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1);
v___x_752_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_744_);
lean_inc(v_quotContext_743_);
v___x_753_ = l_Lean_addMacroScope(v_quotContext_743_, v___x_752_, v_currMacroScope_744_);
v___x_754_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8));
lean_inc_n(v___x_749_, 2);
v___x_755_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_755_, 0, v___x_749_);
lean_ctor_set(v___x_755_, 1, v___x_751_);
lean_ctor_set(v___x_755_, 2, v___x_753_);
lean_ctor_set(v___x_755_, 3, v___x_754_);
v___x_756_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_757_ = l_Lean_Syntax_node1(v___x_749_, v___x_756_, v___x_747_);
v___x_758_ = l_Lean_Syntax_node2(v___x_749_, v___x_750_, v___x_755_, v___x_757_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v_a_738_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(v_x_760_, v_a_761_, v_a_762_);
lean_dec_ref(v_a_761_);
return v_res_763_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0));
v___x_766_ = l_String_toRawSubstring_x27(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(lean_object* v_x_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1));
v___x_790_ = l_Lean_Syntax_isOfKind(v_x_786_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_box(1);
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_a_788_);
return v___x_792_;
}
else
{
lean_object* v_quotContext_793_; lean_object* v_currMacroScope_794_; lean_object* v_ref_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_quotContext_793_ = lean_ctor_get(v_a_787_, 1);
v_currMacroScope_794_ = lean_ctor_get(v_a_787_, 2);
v_ref_795_ = lean_ctor_get(v_a_787_, 5);
v___x_796_ = 0;
v___x_797_ = l_Lean_SourceInfo_fromRef(v_ref_795_, v___x_796_);
v___x_798_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1);
v___x_799_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_794_);
lean_inc(v_quotContext_793_);
v___x_800_ = l_Lean_addMacroScope(v_quotContext_793_, v___x_799_, v_currMacroScope_794_);
v___x_801_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8));
v___x_802_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_802_, 0, v___x_797_);
lean_ctor_set(v___x_802_, 1, v___x_798_);
lean_ctor_set(v___x_802_, 2, v___x_800_);
lean_ctor_set(v___x_802_, 3, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v_a_788_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(v_x_804_, v_a_805_, v_a_806_);
lean_dec_ref(v_a_805_);
return v_res_807_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0));
v___x_810_ = l_String_toRawSubstring_x27(v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(lean_object* v_x_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_830_);
v___x_834_ = l_Lean_Syntax_isOfKind(v_x_830_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v_x_830_);
v___x_835_ = lean_box(1);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_a_832_);
return v___x_836_;
}
else
{
lean_object* v_quotContext_837_; lean_object* v_currMacroScope_838_; lean_object* v_ref_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_quotContext_837_ = lean_ctor_get(v_a_831_, 1);
v_currMacroScope_838_ = lean_ctor_get(v_a_831_, 2);
v_ref_839_ = lean_ctor_get(v_a_831_, 5);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = l_Lean_Syntax_getArg(v_x_830_, v___x_840_);
v___x_842_ = lean_unsigned_to_nat(2u);
v___x_843_ = l_Lean_Syntax_getArg(v_x_830_, v___x_842_);
lean_dec(v_x_830_);
v___x_844_ = 0;
v___x_845_ = l_Lean_SourceInfo_fromRef(v_ref_839_, v___x_844_);
v___x_846_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_847_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1);
v___x_848_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3));
lean_inc(v_currMacroScope_838_);
lean_inc(v_quotContext_837_);
v___x_849_ = l_Lean_addMacroScope(v_quotContext_837_, v___x_848_, v_currMacroScope_838_);
v___x_850_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc_n(v___x_845_, 2);
v___x_851_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_851_, 0, v___x_845_);
lean_ctor_set(v___x_851_, 1, v___x_847_);
lean_ctor_set(v___x_851_, 2, v___x_849_);
lean_ctor_set(v___x_851_, 3, v___x_850_);
v___x_852_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_853_ = l_Lean_Syntax_node2(v___x_845_, v___x_852_, v___x_841_, v___x_843_);
v___x_854_ = l_Lean_Syntax_node2(v___x_845_, v___x_846_, v___x_851_, v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_a_832_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(v_x_856_, v_a_857_, v_a_858_);
lean_dec_ref(v_a_857_);
return v_res_859_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0));
v___x_862_ = l_String_toRawSubstring_x27(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(lean_object* v_x_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1));
lean_inc(v_x_882_);
v___x_886_ = l_Lean_Syntax_isOfKind(v_x_882_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec(v_x_882_);
v___x_887_ = lean_box(1);
v___x_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v_a_884_);
return v___x_888_;
}
else
{
lean_object* v_quotContext_889_; lean_object* v_currMacroScope_890_; lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_quotContext_889_ = lean_ctor_get(v_a_883_, 1);
v_currMacroScope_890_ = lean_ctor_get(v_a_883_, 2);
v_ref_891_ = lean_ctor_get(v_a_883_, 5);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = l_Lean_Syntax_getArg(v_x_882_, v___x_892_);
lean_dec(v_x_882_);
v___x_894_ = 0;
v___x_895_ = l_Lean_SourceInfo_fromRef(v_ref_891_, v___x_894_);
v___x_896_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_897_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1);
v___x_898_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_890_);
lean_inc(v_quotContext_889_);
v___x_899_ = l_Lean_addMacroScope(v_quotContext_889_, v___x_898_, v_currMacroScope_890_);
v___x_900_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8));
lean_inc_n(v___x_895_, 2);
v___x_901_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_901_, 0, v___x_895_);
lean_ctor_set(v___x_901_, 1, v___x_897_);
lean_ctor_set(v___x_901_, 2, v___x_899_);
lean_ctor_set(v___x_901_, 3, v___x_900_);
v___x_902_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_903_ = l_Lean_Syntax_node1(v___x_895_, v___x_902_, v___x_893_);
v___x_904_ = l_Lean_Syntax_node2(v___x_895_, v___x_896_, v___x_901_, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_a_884_);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(v_x_906_, v_a_907_, v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_909_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0));
v___x_912_ = l_String_toRawSubstring_x27(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(lean_object* v_x_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_935_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_932_);
v___x_936_ = l_Lean_Syntax_isOfKind(v_x_932_, v___x_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v_x_932_);
v___x_937_ = lean_box(1);
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_a_934_);
return v___x_938_;
}
else
{
lean_object* v_quotContext_939_; lean_object* v_currMacroScope_940_; lean_object* v_ref_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_quotContext_939_ = lean_ctor_get(v_a_933_, 1);
v_currMacroScope_940_ = lean_ctor_get(v_a_933_, 2);
v_ref_941_ = lean_ctor_get(v_a_933_, 5);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = l_Lean_Syntax_getArg(v_x_932_, v___x_942_);
v___x_944_ = lean_unsigned_to_nat(2u);
v___x_945_ = l_Lean_Syntax_getArg(v_x_932_, v___x_944_);
lean_dec(v_x_932_);
v___x_946_ = 0;
v___x_947_ = l_Lean_SourceInfo_fromRef(v_ref_941_, v___x_946_);
v___x_948_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_949_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_950_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_940_);
lean_inc(v_quotContext_939_);
v___x_951_ = l_Lean_addMacroScope(v_quotContext_939_, v___x_950_, v_currMacroScope_940_);
v___x_952_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_947_, 2);
v___x_953_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_953_, 0, v___x_947_);
lean_ctor_set(v___x_953_, 1, v___x_949_);
lean_ctor_set(v___x_953_, 2, v___x_951_);
lean_ctor_set(v___x_953_, 3, v___x_952_);
v___x_954_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_955_ = l_Lean_Syntax_node2(v___x_947_, v___x_954_, v___x_943_, v___x_945_);
v___x_956_ = l_Lean_Syntax_node2(v___x_947_, v___x_948_, v___x_953_, v___x_955_);
v___x_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_a_934_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(v_x_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(lean_object* v_x_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_962_);
v___x_966_ = l_Lean_Syntax_isOfKind(v_x_962_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_x_962_);
v___x_967_ = lean_box(1);
v___x_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_a_964_);
return v___x_968_;
}
else
{
lean_object* v_quotContext_969_; lean_object* v_currMacroScope_970_; lean_object* v_ref_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_quotContext_969_ = lean_ctor_get(v_a_963_, 1);
v_currMacroScope_970_ = lean_ctor_get(v_a_963_, 2);
v_ref_971_ = lean_ctor_get(v_a_963_, 5);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = l_Lean_Syntax_getArg(v_x_962_, v___x_972_);
v___x_974_ = lean_unsigned_to_nat(2u);
v___x_975_ = l_Lean_Syntax_getArg(v_x_962_, v___x_974_);
lean_dec(v_x_962_);
v___x_976_ = 0;
v___x_977_ = l_Lean_SourceInfo_fromRef(v_ref_971_, v___x_976_);
v___x_978_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_979_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_980_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_970_);
lean_inc(v_quotContext_969_);
v___x_981_ = l_Lean_addMacroScope(v_quotContext_969_, v___x_980_, v_currMacroScope_970_);
v___x_982_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_977_, 2);
v___x_983_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_983_, 0, v___x_977_);
lean_ctor_set(v___x_983_, 1, v___x_979_);
lean_ctor_set(v___x_983_, 2, v___x_981_);
lean_ctor_set(v___x_983_, 3, v___x_982_);
v___x_984_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_985_ = l_Lean_Syntax_node2(v___x_977_, v___x_984_, v___x_973_, v___x_975_);
v___x_986_ = l_Lean_Syntax_node2(v___x_977_, v___x_978_, v___x_983_, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v_a_964_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1___boxed(lean_object* v_x_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(v_x_988_, v_a_989_, v_a_990_);
lean_dec_ref(v_a_989_);
return v_res_991_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0));
v___x_994_ = l_String_toRawSubstring_x27(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(lean_object* v_x_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_1014_);
v___x_1018_ = l_Lean_Syntax_isOfKind(v_x_1014_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v_x_1014_);
v___x_1019_ = lean_box(1);
v___x_1020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_a_1016_);
return v___x_1020_;
}
else
{
lean_object* v_quotContext_1021_; lean_object* v_currMacroScope_1022_; lean_object* v_ref_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_quotContext_1021_ = lean_ctor_get(v_a_1015_, 1);
v_currMacroScope_1022_ = lean_ctor_get(v_a_1015_, 2);
v_ref_1023_ = lean_ctor_get(v_a_1015_, 5);
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = l_Lean_Syntax_getArg(v_x_1014_, v___x_1024_);
lean_dec(v_x_1014_);
v___x_1026_ = 0;
v___x_1027_ = l_Lean_SourceInfo_fromRef(v_ref_1023_, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1029_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1030_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1022_);
lean_inc(v_quotContext_1021_);
v___x_1031_ = l_Lean_addMacroScope(v_quotContext_1021_, v___x_1030_, v_currMacroScope_1022_);
v___x_1032_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1027_, 2);
v___x_1033_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1027_);
lean_ctor_set(v___x_1033_, 1, v___x_1029_);
lean_ctor_set(v___x_1033_, 2, v___x_1031_);
lean_ctor_set(v___x_1033_, 3, v___x_1032_);
v___x_1034_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1035_ = l_Lean_Syntax_node1(v___x_1027_, v___x_1034_, v___x_1025_);
v___x_1036_ = l_Lean_Syntax_node2(v___x_1027_, v___x_1028_, v___x_1033_, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v_a_1016_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(v_x_1038_, v_a_1039_, v_a_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(lean_object* v_x_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_1042_);
v___x_1046_ = l_Lean_Syntax_isOfKind(v_x_1042_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec(v_x_1042_);
v___x_1047_ = lean_box(1);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_a_1044_);
return v___x_1048_;
}
else
{
lean_object* v_quotContext_1049_; lean_object* v_currMacroScope_1050_; lean_object* v_ref_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_quotContext_1049_ = lean_ctor_get(v_a_1043_, 1);
v_currMacroScope_1050_ = lean_ctor_get(v_a_1043_, 2);
v_ref_1051_ = lean_ctor_get(v_a_1043_, 5);
v___x_1052_ = lean_unsigned_to_nat(1u);
v___x_1053_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1052_);
lean_dec(v_x_1042_);
v___x_1054_ = 0;
v___x_1055_ = l_Lean_SourceInfo_fromRef(v_ref_1051_, v___x_1054_);
v___x_1056_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1057_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1058_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1050_);
lean_inc(v_quotContext_1049_);
v___x_1059_ = l_Lean_addMacroScope(v_quotContext_1049_, v___x_1058_, v_currMacroScope_1050_);
v___x_1060_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1055_, 2);
v___x_1061_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1055_);
lean_ctor_set(v___x_1061_, 1, v___x_1057_);
lean_ctor_set(v___x_1061_, 2, v___x_1059_);
lean_ctor_set(v___x_1061_, 3, v___x_1060_);
v___x_1062_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1063_ = l_Lean_Syntax_node1(v___x_1055_, v___x_1062_, v___x_1053_);
v___x_1064_ = l_Lean_Syntax_node2(v___x_1055_, v___x_1056_, v___x_1061_, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_1044_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1___boxed(lean_object* v_x_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(v_x_1066_, v_a_1067_, v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1069_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0));
v___x_1072_ = l_String_toRawSubstring_x27(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(lean_object* v_x_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_1092_);
v___x_1096_ = l_Lean_Syntax_isOfKind(v_x_1092_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec(v_x_1092_);
v___x_1097_ = lean_box(1);
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_a_1094_);
return v___x_1098_;
}
else
{
lean_object* v_quotContext_1099_; lean_object* v_currMacroScope_1100_; lean_object* v_ref_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_quotContext_1099_ = lean_ctor_get(v_a_1093_, 1);
v_currMacroScope_1100_ = lean_ctor_get(v_a_1093_, 2);
v_ref_1101_ = lean_ctor_get(v_a_1093_, 5);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(2u);
v___x_1105_ = l_Lean_Syntax_getArg(v_x_1092_, v___x_1104_);
lean_dec(v_x_1092_);
v___x_1106_ = 0;
v___x_1107_ = l_Lean_SourceInfo_fromRef(v_ref_1101_, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1109_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1110_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1100_);
lean_inc(v_quotContext_1099_);
v___x_1111_ = l_Lean_addMacroScope(v_quotContext_1099_, v___x_1110_, v_currMacroScope_1100_);
v___x_1112_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1107_, 2);
v___x_1113_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1107_);
lean_ctor_set(v___x_1113_, 1, v___x_1109_);
lean_ctor_set(v___x_1113_, 2, v___x_1111_);
lean_ctor_set(v___x_1113_, 3, v___x_1112_);
v___x_1114_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1115_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1114_, v___x_1103_, v___x_1105_);
v___x_1116_ = l_Lean_Syntax_node2(v___x_1107_, v___x_1108_, v___x_1113_, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_a_1094_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(v_x_1118_, v_a_1119_, v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(lean_object* v_x_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_1122_);
v___x_1126_ = l_Lean_Syntax_isOfKind(v_x_1122_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v_x_1122_);
v___x_1127_ = lean_box(1);
v___x_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
lean_ctor_set(v___x_1128_, 1, v_a_1124_);
return v___x_1128_;
}
else
{
lean_object* v_quotContext_1129_; lean_object* v_currMacroScope_1130_; lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_quotContext_1129_ = lean_ctor_get(v_a_1123_, 1);
v_currMacroScope_1130_ = lean_ctor_get(v_a_1123_, 2);
v_ref_1131_ = lean_ctor_get(v_a_1123_, 5);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = l_Lean_Syntax_getArg(v_x_1122_, v___x_1132_);
v___x_1134_ = lean_unsigned_to_nat(2u);
v___x_1135_ = l_Lean_Syntax_getArg(v_x_1122_, v___x_1134_);
lean_dec(v_x_1122_);
v___x_1136_ = 0;
v___x_1137_ = l_Lean_SourceInfo_fromRef(v_ref_1131_, v___x_1136_);
v___x_1138_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1139_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1140_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1130_);
lean_inc(v_quotContext_1129_);
v___x_1141_ = l_Lean_addMacroScope(v_quotContext_1129_, v___x_1140_, v_currMacroScope_1130_);
v___x_1142_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1137_, 2);
v___x_1143_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1137_);
lean_ctor_set(v___x_1143_, 1, v___x_1139_);
lean_ctor_set(v___x_1143_, 2, v___x_1141_);
lean_ctor_set(v___x_1143_, 3, v___x_1142_);
v___x_1144_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1145_ = l_Lean_Syntax_node2(v___x_1137_, v___x_1144_, v___x_1133_, v___x_1135_);
v___x_1146_ = l_Lean_Syntax_node2(v___x_1137_, v___x_1138_, v___x_1143_, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v_a_1124_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1___boxed(lean_object* v_x_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(v_x_1148_, v_a_1149_, v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE___redArg(){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_box(0);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE___redArg___boxed(lean_object* v___dummy_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_Rcc_instMembershipOfLE___redArg();
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_box(0);
return v___x_1158_;
}
}
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1159_, lean_object* v_a_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v_lower_1162_; lean_object* v_upper_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_lower_1162_ = lean_ctor_get(v_r_1159_, 0);
lean_inc(v_lower_1162_);
v_upper_1163_ = lean_ctor_get(v_r_1159_, 1);
lean_inc(v_upper_1163_);
lean_dec_ref(v_r_1159_);
lean_inc_ref(v_inst_1161_);
lean_inc(v_a_1160_);
v___x_1164_ = lean_apply_2(v_inst_1161_, v_lower_1162_, v_a_1160_);
v___x_1165_ = lean_unbox(v___x_1164_);
if (v___x_1165_ == 0)
{
uint8_t v___x_1166_; 
lean_dec(v_upper_1163_);
lean_dec_ref(v_inst_1161_);
lean_dec(v_a_1160_);
v___x_1166_ = lean_unbox(v___x_1164_);
return v___x_1166_;
}
else
{
lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = lean_apply_2(v_inst_1161_, v_a_1160_, v_upper_1163_);
v___x_1168_ = lean_unbox(v___x_1167_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1169_, lean_object* v_a_1170_, lean_object* v_inst_1171_){
_start:
{
uint8_t v_res_1172_; lean_object* v_r_1173_; 
v_res_1172_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1169_, v_a_1170_, v_inst_1171_);
v_r_1173_ = lean_box(v_res_1172_);
return v_r_1173_;
}
}
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1174_, lean_object* v_r_1175_, lean_object* v_a_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1175_, v_a_1176_, v_inst_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1180_, lean_object* v_r_1181_, lean_object* v_a_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_){
_start:
{
uint8_t v_res_1185_; lean_object* v_r_1186_; 
v_res_1185_ = l_Std_Rcc_instDecidableMemOfDecidableLE(v_00_u03b1_1180_, v_r_1181_, v_a_1182_, v_inst_1183_, v_inst_1184_);
v_r_1186_ = lean_box(v_res_1185_);
return v_r_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT___redArg(){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT___redArg___boxed(lean_object* v___dummy_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_Rco_instMembershipOfLEOfLT___redArg();
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_box(0);
return v___x_1194_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1195_, lean_object* v_a_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v_lower_1199_; lean_object* v_upper_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_lower_1199_ = lean_ctor_get(v_r_1195_, 0);
lean_inc(v_lower_1199_);
v_upper_1200_ = lean_ctor_get(v_r_1195_, 1);
lean_inc(v_upper_1200_);
lean_dec_ref(v_r_1195_);
lean_inc(v_a_1196_);
v___x_1201_ = lean_apply_2(v_inst_1197_, v_lower_1199_, v_a_1196_);
v___x_1202_ = lean_unbox(v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; 
lean_dec(v_upper_1200_);
lean_dec_ref(v_inst_1198_);
lean_dec(v_a_1196_);
v___x_1203_ = lean_unbox(v___x_1201_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_apply_2(v_inst_1198_, v_a_1196_, v_upper_1200_);
v___x_1205_ = lean_unbox(v___x_1204_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1206_, lean_object* v_a_1207_, lean_object* v_inst_1208_, lean_object* v_inst_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1206_, v_a_1207_, v_inst_1208_, v_inst_1209_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1212_, lean_object* v_r_1213_, lean_object* v_a_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_, lean_object* v_inst_1218_){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1213_, v_a_1214_, v_inst_1216_, v_inst_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_r_1221_, lean_object* v_a_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_){
_start:
{
uint8_t v_res_1227_; lean_object* v_r_1228_; 
v_res_1227_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1220_, v_r_1221_, v_a_1222_, v_inst_1223_, v_inst_1224_, v_inst_1225_, v_inst_1226_);
v_r_1228_ = lean_box(v_res_1227_);
return v_r_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE___redArg(){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_box(0);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE___redArg___boxed(lean_object* v___dummy_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_Rci_instMembershipOfLE___redArg();
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE(lean_object* v_00_u03b1_1233_, lean_object* v_inst_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_box(0);
return v___x_1235_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1236_, lean_object* v_a_1237_, lean_object* v_inst_1238_){
_start:
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_apply_2(v_inst_1238_, v_r_1236_, v_a_1237_);
v___x_1240_ = lean_unbox(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1241_, lean_object* v_a_1242_, lean_object* v_inst_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Std_Rci_instDecidableMemOfDecidableLE___redArg(v_r_1241_, v_a_1242_, v_inst_1243_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1246_, lean_object* v_r_1247_, lean_object* v_a_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_){
_start:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_apply_2(v_inst_1250_, v_r_1247_, v_a_1248_);
v___x_1252_ = lean_unbox(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_r_1254_, lean_object* v_a_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Std_Rci_instDecidableMemOfDecidableLE(v_00_u03b1_1253_, v_r_1254_, v_a_1255_, v_inst_1256_, v_inst_1257_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT___redArg(){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_box(0);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT___redArg___boxed(lean_object* v___dummy_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Std_Roc_instMembershipOfLEOfLT___redArg();
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_box(0);
return v___x_1267_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1268_, lean_object* v_a_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_){
_start:
{
lean_object* v_lower_1272_; lean_object* v_upper_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_lower_1272_ = lean_ctor_get(v_r_1268_, 0);
lean_inc(v_lower_1272_);
v_upper_1273_ = lean_ctor_get(v_r_1268_, 1);
lean_inc(v_upper_1273_);
lean_dec_ref(v_r_1268_);
lean_inc(v_a_1269_);
v___x_1274_ = lean_apply_2(v_inst_1271_, v_lower_1272_, v_a_1269_);
v___x_1275_ = lean_unbox(v___x_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; 
lean_dec(v_upper_1273_);
lean_dec_ref(v_inst_1270_);
lean_dec(v_a_1269_);
v___x_1276_ = lean_unbox(v___x_1274_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_apply_2(v_inst_1270_, v_a_1269_, v_upper_1273_);
v___x_1278_ = lean_unbox(v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1279_, lean_object* v_a_1280_, lean_object* v_inst_1281_, lean_object* v_inst_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1279_, v_a_1280_, v_inst_1281_, v_inst_1282_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1285_, lean_object* v_r_1286_, lean_object* v_a_1287_, lean_object* v_inst_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1286_, v_a_1287_, v_inst_1289_, v_inst_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1293_, lean_object* v_r_1294_, lean_object* v_a_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1293_, v_r_1294_, v_a_1295_, v_inst_1296_, v_inst_1297_, v_inst_1298_, v_inst_1299_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT___redArg(){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = lean_box(0);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT___redArg___boxed(lean_object* v___dummy_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l_Std_Roo_instMembershipOfLT___redArg();
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT(lean_object* v_00_u03b1_1306_, lean_object* v_inst_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_box(0);
return v___x_1308_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1309_, lean_object* v_a_1310_, lean_object* v_inst_1311_){
_start:
{
lean_object* v_lower_1312_; lean_object* v_upper_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_lower_1312_ = lean_ctor_get(v_r_1309_, 0);
lean_inc(v_lower_1312_);
v_upper_1313_ = lean_ctor_get(v_r_1309_, 1);
lean_inc(v_upper_1313_);
lean_dec_ref(v_r_1309_);
lean_inc_ref(v_inst_1311_);
lean_inc(v_a_1310_);
v___x_1314_ = lean_apply_2(v_inst_1311_, v_lower_1312_, v_a_1310_);
v___x_1315_ = lean_unbox(v___x_1314_);
if (v___x_1315_ == 0)
{
uint8_t v___x_1316_; 
lean_dec(v_upper_1313_);
lean_dec_ref(v_inst_1311_);
lean_dec(v_a_1310_);
v___x_1316_ = lean_unbox(v___x_1314_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = lean_apply_2(v_inst_1311_, v_a_1310_, v_upper_1313_);
v___x_1318_ = lean_unbox(v___x_1317_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1319_, lean_object* v_a_1320_, lean_object* v_inst_1321_){
_start:
{
uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1319_, v_a_1320_, v_inst_1321_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1324_, lean_object* v_r_1325_, lean_object* v_a_1326_, lean_object* v_inst_1327_, lean_object* v_inst_1328_){
_start:
{
uint8_t v___x_1329_; 
v___x_1329_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1325_, v_a_1326_, v_inst_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_r_1331_, lean_object* v_a_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_){
_start:
{
uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_res_1335_ = l_Std_Roo_instDecidableMemOfDecidableLT(v_00_u03b1_1330_, v_r_1331_, v_a_1332_, v_inst_1333_, v_inst_1334_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT___redArg(){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_box(0);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT___redArg___boxed(lean_object* v___dummy_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Std_Roi_instMembershipOfLT___redArg();
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT(lean_object* v_00_u03b1_1341_, lean_object* v_inst_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_box(0);
return v___x_1343_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1344_, lean_object* v_a_1345_, lean_object* v_inst_1346_){
_start:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = lean_apply_2(v_inst_1346_, v_r_1344_, v_a_1345_);
v___x_1348_ = lean_unbox(v___x_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1349_, lean_object* v_a_1350_, lean_object* v_inst_1351_){
_start:
{
uint8_t v_res_1352_; lean_object* v_r_1353_; 
v_res_1352_ = l_Std_Roi_instDecidableMemOfDecidableLT___redArg(v_r_1349_, v_a_1350_, v_inst_1351_);
v_r_1353_ = lean_box(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1354_, lean_object* v_r_1355_, lean_object* v_a_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_){
_start:
{
lean_object* v___x_1359_; uint8_t v___x_1360_; 
v___x_1359_ = lean_apply_2(v_inst_1358_, v_r_1355_, v_a_1356_);
v___x_1360_ = lean_unbox(v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1361_, lean_object* v_r_1362_, lean_object* v_a_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_){
_start:
{
uint8_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l_Std_Roi_instDecidableMemOfDecidableLT(v_00_u03b1_1361_, v_r_1362_, v_a_1363_, v_inst_1364_, v_inst_1365_);
v_r_1367_ = lean_box(v_res_1366_);
return v_r_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE___redArg(){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_box(0);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE___redArg___boxed(lean_object* v___dummy_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Std_Ric_instMembershipOfLE___redArg();
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE(lean_object* v_00_u03b1_1372_, lean_object* v_inst_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_box(0);
return v___x_1374_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1375_, lean_object* v_a_1376_, lean_object* v_inst_1377_){
_start:
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = lean_apply_2(v_inst_1377_, v_a_1376_, v_r_1375_);
v___x_1379_ = lean_unbox(v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1380_, lean_object* v_a_1381_, lean_object* v_inst_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_Std_Ric_instDecidableMemOfDecidableLE___redArg(v_r_1380_, v_a_1381_, v_inst_1382_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1385_, lean_object* v_r_1386_, lean_object* v_a_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_){
_start:
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = lean_apply_2(v_inst_1389_, v_a_1387_, v_r_1386_);
v___x_1391_ = lean_unbox(v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1392_, lean_object* v_r_1393_, lean_object* v_a_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l_Std_Ric_instDecidableMemOfDecidableLE(v_00_u03b1_1392_, v_r_1393_, v_a_1394_, v_inst_1395_, v_inst_1396_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT___redArg(){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_box(0);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT___redArg___boxed(lean_object* v___dummy_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_Rio_instMembershipOfLT___redArg();
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT(lean_object* v_00_u03b1_1403_, lean_object* v_inst_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_box(0);
return v___x_1405_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1406_, lean_object* v_a_1407_, lean_object* v_inst_1408_){
_start:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_apply_2(v_inst_1408_, v_a_1407_, v_r_1406_);
v___x_1410_ = lean_unbox(v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1411_, lean_object* v_a_1412_, lean_object* v_inst_1413_){
_start:
{
uint8_t v_res_1414_; lean_object* v_r_1415_; 
v_res_1414_ = l_Std_Rio_instDecidableMemOfDecidableLT___redArg(v_r_1411_, v_a_1412_, v_inst_1413_);
v_r_1415_ = lean_box(v_res_1414_);
return v_r_1415_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1416_, lean_object* v_r_1417_, lean_object* v_a_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_){
_start:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = lean_apply_2(v_inst_1420_, v_a_1418_, v_r_1417_);
v___x_1422_ = lean_unbox(v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1423_, lean_object* v_r_1424_, lean_object* v_a_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_){
_start:
{
uint8_t v_res_1428_; lean_object* v_r_1429_; 
v_res_1428_ = l_Std_Rio_instDecidableMemOfDecidableLT(v_00_u03b1_1423_, v_r_1424_, v_a_1425_, v_inst_1426_, v_inst_1427_);
v_r_1429_ = lean_box(v_res_1428_);
return v_r_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instMembership___redArg(){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_box(0);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instMembership___redArg___boxed(lean_object* v___dummy_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Std_Rii_instMembership___redArg();
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instMembership(lean_object* v_00_u03b1_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_box(0);
return v___x_1435_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_instDecidableMem___redArg(){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = 1;
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___redArg___boxed(lean_object* v___dummy_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l_Std_Rii_instDecidableMem___redArg();
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_instDecidableMem(lean_object* v_00_u03b1_1441_, lean_object* v_r_1442_, lean_object* v_a_1443_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = 1;
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___boxed(lean_object* v_00_u03b1_1445_, lean_object* v_r_1446_, lean_object* v_a_1447_){
_start:
{
uint8_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l_Std_Rii_instDecidableMem(v_00_u03b1_1445_, v_r_1446_, v_a_1447_);
lean_dec(v_a_1447_);
v_r_1449_ = lean_box(v_res_1448_);
return v_r_1449_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_PRange(builtin);
}
#ifdef __cplusplus
}
#endif
