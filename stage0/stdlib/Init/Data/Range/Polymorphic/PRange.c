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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x2a___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x2a___closed__4_value)}};
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
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__3_value)}};
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
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__8 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__3_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__5_value),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__8_value)}};
static const lean_object* l_Std_term___x2e_x2e_x2e_x3c___00__closed__9 = (const lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value;
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3c___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3c___00__closed__9_value)}};
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
static const lean_ctor_object l_Std_term___x2e_x2e_x2e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e___00__closed__4_value)}};
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
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__4_value)}};
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
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e___00__closed__4_value)}};
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
static const lean_ctor_object l_Std_term___x2e_x2e_x2e_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x2e_x2e_x2e_x3d___00__closed__4_value)}};
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
static const lean_ctor_object l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__4_value)}};
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
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rii_instMembership(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii_decEq(lean_object* v_00_u03b1_369_, lean_object* v_inst_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = 1;
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___boxed(lean_object* v_00_u03b1_374_, lean_object* v_inst_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Std_instDecidableEqRii_decEq(v_00_u03b1_374_, v_inst_375_, v_x_376_, v_x_377_);
lean_dec_ref(v_inst_375_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT uint8_t l_Std_instDecidableEqRii(lean_object* v_00_u03b1_380_, lean_object* v_inst_381_, lean_object* v_x_382_, lean_object* v_x_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = 1;
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii___boxed(lean_object* v_00_u03b1_385_, lean_object* v_inst_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Std_instDecidableEqRii(v_00_u03b1_385_, v_inst_386_, v_x_387_, v_x_388_);
lean_dec_ref(v_inst_386_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5));
v___x_600_ = l_String_toRawSubstring_x27(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(lean_object* v_x_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_624_);
v___x_628_ = l_Lean_Syntax_isOfKind(v_x_624_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec_ref(v_a_625_);
lean_dec(v_x_624_);
v___x_629_ = lean_box(1);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_a_626_);
return v___x_630_;
}
else
{
lean_object* v_quotContext_631_; lean_object* v_currMacroScope_632_; lean_object* v_ref_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_quotContext_631_ = lean_ctor_get(v_a_625_, 1);
lean_inc(v_quotContext_631_);
v_currMacroScope_632_ = lean_ctor_get(v_a_625_, 2);
lean_inc(v_currMacroScope_632_);
v_ref_633_ = lean_ctor_get(v_a_625_, 5);
lean_inc(v_ref_633_);
lean_dec_ref(v_a_625_);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_Lean_Syntax_getArg(v_x_624_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(2u);
v___x_637_ = l_Lean_Syntax_getArg(v_x_624_, v___x_636_);
lean_dec(v_x_624_);
v___x_638_ = 0;
v___x_639_ = l_Lean_SourceInfo_fromRef(v_ref_633_, v___x_638_);
lean_dec(v_ref_633_);
v___x_640_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_641_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6);
v___x_642_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9));
v___x_643_ = l_Lean_addMacroScope(v_quotContext_631_, v___x_642_, v_currMacroScope_632_);
v___x_644_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14));
lean_inc(v___x_639_);
v___x_645_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_645_, 0, v___x_639_);
lean_ctor_set(v___x_645_, 1, v___x_641_);
lean_ctor_set(v___x_645_, 2, v___x_643_);
lean_ctor_set(v___x_645_, 3, v___x_644_);
v___x_646_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_639_);
v___x_647_ = l_Lean_Syntax_node2(v___x_639_, v___x_646_, v___x_635_, v___x_637_);
v___x_648_ = l_Lean_Syntax_node2(v___x_639_, v___x_640_, v___x_645_, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_626_);
return v___x_649_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0));
v___x_652_ = l_String_toRawSubstring_x27(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(lean_object* v_x_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_672_);
v___x_676_ = l_Lean_Syntax_isOfKind(v_x_672_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec_ref(v_a_673_);
lean_dec(v_x_672_);
v___x_677_ = lean_box(1);
v___x_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
lean_ctor_set(v___x_678_, 1, v_a_674_);
return v___x_678_;
}
else
{
lean_object* v_quotContext_679_; lean_object* v_currMacroScope_680_; lean_object* v_ref_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_quotContext_679_ = lean_ctor_get(v_a_673_, 1);
lean_inc(v_quotContext_679_);
v_currMacroScope_680_ = lean_ctor_get(v_a_673_, 2);
lean_inc(v_currMacroScope_680_);
v_ref_681_ = lean_ctor_get(v_a_673_, 5);
lean_inc(v_ref_681_);
lean_dec_ref(v_a_673_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = l_Lean_Syntax_getArg(v_x_672_, v___x_682_);
lean_dec(v_x_672_);
v___x_684_ = 0;
v___x_685_ = l_Lean_SourceInfo_fromRef(v_ref_681_, v___x_684_);
lean_dec(v_ref_681_);
v___x_686_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_687_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1);
v___x_688_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3));
v___x_689_ = l_Lean_addMacroScope(v_quotContext_679_, v___x_688_, v_currMacroScope_680_);
v___x_690_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc(v___x_685_);
v___x_691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_691_, 0, v___x_685_);
lean_ctor_set(v___x_691_, 1, v___x_687_);
lean_ctor_set(v___x_691_, 2, v___x_689_);
lean_ctor_set(v___x_691_, 3, v___x_690_);
v___x_692_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_685_);
v___x_693_ = l_Lean_Syntax_node1(v___x_685_, v___x_692_, v___x_683_);
v___x_694_ = l_Lean_Syntax_node2(v___x_685_, v___x_686_, v___x_691_, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_674_);
return v___x_695_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0));
v___x_698_ = l_String_toRawSubstring_x27(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(lean_object* v_x_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x2a___closed__2));
lean_inc(v_x_718_);
v___x_722_ = l_Lean_Syntax_isOfKind(v_x_718_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec_ref(v_a_719_);
lean_dec(v_x_718_);
v___x_723_ = lean_box(1);
v___x_724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_a_720_);
return v___x_724_;
}
else
{
lean_object* v_quotContext_725_; lean_object* v_currMacroScope_726_; lean_object* v_ref_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_quotContext_725_ = lean_ctor_get(v_a_719_, 1);
lean_inc(v_quotContext_725_);
v_currMacroScope_726_ = lean_ctor_get(v_a_719_, 2);
lean_inc(v_currMacroScope_726_);
v_ref_727_ = lean_ctor_get(v_a_719_, 5);
lean_inc(v_ref_727_);
lean_dec_ref(v_a_719_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = l_Lean_Syntax_getArg(v_x_718_, v___x_728_);
lean_dec(v_x_718_);
v___x_730_ = 0;
v___x_731_ = l_Lean_SourceInfo_fromRef(v_ref_727_, v___x_730_);
lean_dec(v_ref_727_);
v___x_732_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_733_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1);
v___x_734_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3));
v___x_735_ = l_Lean_addMacroScope(v_quotContext_725_, v___x_734_, v_currMacroScope_726_);
v___x_736_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8));
lean_inc(v___x_731_);
v___x_737_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_737_, 0, v___x_731_);
lean_ctor_set(v___x_737_, 1, v___x_733_);
lean_ctor_set(v___x_737_, 2, v___x_735_);
lean_ctor_set(v___x_737_, 3, v___x_736_);
v___x_738_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_731_);
v___x_739_ = l_Lean_Syntax_node1(v___x_731_, v___x_738_, v___x_729_);
v___x_740_ = l_Lean_Syntax_node2(v___x_731_, v___x_732_, v___x_737_, v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_a_720_);
return v___x_741_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0));
v___x_744_ = l_String_toRawSubstring_x27(v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(lean_object* v_x_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1));
v___x_768_ = l_Lean_Syntax_isOfKind(v_x_764_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref(v_a_765_);
v___x_769_ = lean_box(1);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v_a_766_);
return v___x_770_;
}
else
{
lean_object* v_quotContext_771_; lean_object* v_currMacroScope_772_; lean_object* v_ref_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_quotContext_771_ = lean_ctor_get(v_a_765_, 1);
lean_inc(v_quotContext_771_);
v_currMacroScope_772_ = lean_ctor_get(v_a_765_, 2);
lean_inc(v_currMacroScope_772_);
v_ref_773_ = lean_ctor_get(v_a_765_, 5);
lean_inc(v_ref_773_);
lean_dec_ref(v_a_765_);
v___x_774_ = 0;
v___x_775_ = l_Lean_SourceInfo_fromRef(v_ref_773_, v___x_774_);
lean_dec(v_ref_773_);
v___x_776_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1);
v___x_777_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3));
v___x_778_ = l_Lean_addMacroScope(v_quotContext_771_, v___x_777_, v_currMacroScope_772_);
v___x_779_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8));
v___x_780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_780_, 0, v___x_775_);
lean_ctor_set(v___x_780_, 1, v___x_776_);
lean_ctor_set(v___x_780_, 2, v___x_778_);
lean_ctor_set(v___x_780_, 3, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_a_766_);
return v___x_781_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0));
v___x_784_ = l_String_toRawSubstring_x27(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(lean_object* v_x_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_804_);
v___x_808_ = l_Lean_Syntax_isOfKind(v_x_804_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_a_805_);
lean_dec(v_x_804_);
v___x_809_ = lean_box(1);
v___x_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v_a_806_);
return v___x_810_;
}
else
{
lean_object* v_quotContext_811_; lean_object* v_currMacroScope_812_; lean_object* v_ref_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_quotContext_811_ = lean_ctor_get(v_a_805_, 1);
lean_inc(v_quotContext_811_);
v_currMacroScope_812_ = lean_ctor_get(v_a_805_, 2);
lean_inc(v_currMacroScope_812_);
v_ref_813_ = lean_ctor_get(v_a_805_, 5);
lean_inc(v_ref_813_);
lean_dec_ref(v_a_805_);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = l_Lean_Syntax_getArg(v_x_804_, v___x_814_);
v___x_816_ = lean_unsigned_to_nat(2u);
v___x_817_ = l_Lean_Syntax_getArg(v_x_804_, v___x_816_);
lean_dec(v_x_804_);
v___x_818_ = 0;
v___x_819_ = l_Lean_SourceInfo_fromRef(v_ref_813_, v___x_818_);
lean_dec(v_ref_813_);
v___x_820_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_821_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1);
v___x_822_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3));
v___x_823_ = l_Lean_addMacroScope(v_quotContext_811_, v___x_822_, v_currMacroScope_812_);
v___x_824_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc(v___x_819_);
v___x_825_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_825_, 0, v___x_819_);
lean_ctor_set(v___x_825_, 1, v___x_821_);
lean_ctor_set(v___x_825_, 2, v___x_823_);
lean_ctor_set(v___x_825_, 3, v___x_824_);
v___x_826_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_819_);
v___x_827_ = l_Lean_Syntax_node2(v___x_819_, v___x_826_, v___x_815_, v___x_817_);
v___x_828_ = l_Lean_Syntax_node2(v___x_819_, v___x_820_, v___x_825_, v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v_a_806_);
return v___x_829_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0));
v___x_832_ = l_String_toRawSubstring_x27(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(lean_object* v_x_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_855_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1));
lean_inc(v_x_852_);
v___x_856_ = l_Lean_Syntax_isOfKind(v_x_852_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v_a_853_);
lean_dec(v_x_852_);
v___x_857_ = lean_box(1);
v___x_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_a_854_);
return v___x_858_;
}
else
{
lean_object* v_quotContext_859_; lean_object* v_currMacroScope_860_; lean_object* v_ref_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_quotContext_859_ = lean_ctor_get(v_a_853_, 1);
lean_inc(v_quotContext_859_);
v_currMacroScope_860_ = lean_ctor_get(v_a_853_, 2);
lean_inc(v_currMacroScope_860_);
v_ref_861_ = lean_ctor_get(v_a_853_, 5);
lean_inc(v_ref_861_);
lean_dec_ref(v_a_853_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = l_Lean_Syntax_getArg(v_x_852_, v___x_862_);
lean_dec(v_x_852_);
v___x_864_ = 0;
v___x_865_ = l_Lean_SourceInfo_fromRef(v_ref_861_, v___x_864_);
lean_dec(v_ref_861_);
v___x_866_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_867_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1);
v___x_868_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3));
v___x_869_ = l_Lean_addMacroScope(v_quotContext_859_, v___x_868_, v_currMacroScope_860_);
v___x_870_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8));
lean_inc(v___x_865_);
v___x_871_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_871_, 0, v___x_865_);
lean_ctor_set(v___x_871_, 1, v___x_867_);
lean_ctor_set(v___x_871_, 2, v___x_869_);
lean_ctor_set(v___x_871_, 3, v___x_870_);
v___x_872_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_865_);
v___x_873_ = l_Lean_Syntax_node1(v___x_865_, v___x_872_, v___x_863_);
v___x_874_ = l_Lean_Syntax_node2(v___x_865_, v___x_866_, v___x_871_, v___x_873_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v_a_854_);
return v___x_875_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0));
v___x_878_ = l_String_toRawSubstring_x27(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(lean_object* v_x_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_898_);
v___x_902_ = l_Lean_Syntax_isOfKind(v_x_898_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref(v_a_899_);
lean_dec(v_x_898_);
v___x_903_ = lean_box(1);
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v_a_900_);
return v___x_904_;
}
else
{
lean_object* v_quotContext_905_; lean_object* v_currMacroScope_906_; lean_object* v_ref_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_quotContext_905_ = lean_ctor_get(v_a_899_, 1);
lean_inc(v_quotContext_905_);
v_currMacroScope_906_ = lean_ctor_get(v_a_899_, 2);
lean_inc(v_currMacroScope_906_);
v_ref_907_ = lean_ctor_get(v_a_899_, 5);
lean_inc(v_ref_907_);
lean_dec_ref(v_a_899_);
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = l_Lean_Syntax_getArg(v_x_898_, v___x_908_);
v___x_910_ = lean_unsigned_to_nat(2u);
v___x_911_ = l_Lean_Syntax_getArg(v_x_898_, v___x_910_);
lean_dec(v_x_898_);
v___x_912_ = 0;
v___x_913_ = l_Lean_SourceInfo_fromRef(v_ref_907_, v___x_912_);
lean_dec(v_ref_907_);
v___x_914_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_915_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_916_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
v___x_917_ = l_Lean_addMacroScope(v_quotContext_905_, v___x_916_, v_currMacroScope_906_);
v___x_918_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc(v___x_913_);
v___x_919_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_919_, 0, v___x_913_);
lean_ctor_set(v___x_919_, 1, v___x_915_);
lean_ctor_set(v___x_919_, 2, v___x_917_);
lean_ctor_set(v___x_919_, 3, v___x_918_);
v___x_920_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_913_);
v___x_921_ = l_Lean_Syntax_node2(v___x_913_, v___x_920_, v___x_909_, v___x_911_);
v___x_922_ = l_Lean_Syntax_node2(v___x_913_, v___x_914_, v___x_919_, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_a_900_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(lean_object* v_x_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_924_);
v___x_928_ = l_Lean_Syntax_isOfKind(v_x_924_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec_ref(v_a_925_);
lean_dec(v_x_924_);
v___x_929_ = lean_box(1);
v___x_930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v_a_926_);
return v___x_930_;
}
else
{
lean_object* v_quotContext_931_; lean_object* v_currMacroScope_932_; lean_object* v_ref_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_quotContext_931_ = lean_ctor_get(v_a_925_, 1);
lean_inc(v_quotContext_931_);
v_currMacroScope_932_ = lean_ctor_get(v_a_925_, 2);
lean_inc(v_currMacroScope_932_);
v_ref_933_ = lean_ctor_get(v_a_925_, 5);
lean_inc(v_ref_933_);
lean_dec_ref(v_a_925_);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = l_Lean_Syntax_getArg(v_x_924_, v___x_934_);
v___x_936_ = lean_unsigned_to_nat(2u);
v___x_937_ = l_Lean_Syntax_getArg(v_x_924_, v___x_936_);
lean_dec(v_x_924_);
v___x_938_ = 0;
v___x_939_ = l_Lean_SourceInfo_fromRef(v_ref_933_, v___x_938_);
lean_dec(v_ref_933_);
v___x_940_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_941_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_942_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
v___x_943_ = l_Lean_addMacroScope(v_quotContext_931_, v___x_942_, v_currMacroScope_932_);
v___x_944_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc(v___x_939_);
v___x_945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_945_, 0, v___x_939_);
lean_ctor_set(v___x_945_, 1, v___x_941_);
lean_ctor_set(v___x_945_, 2, v___x_943_);
lean_ctor_set(v___x_945_, 3, v___x_944_);
v___x_946_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_939_);
v___x_947_ = l_Lean_Syntax_node2(v___x_939_, v___x_946_, v___x_935_, v___x_937_);
v___x_948_ = l_Lean_Syntax_node2(v___x_939_, v___x_940_, v___x_945_, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v_a_926_);
return v___x_949_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0));
v___x_952_ = l_String_toRawSubstring_x27(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(lean_object* v_x_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_972_);
v___x_976_ = l_Lean_Syntax_isOfKind(v_x_972_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec_ref(v_a_973_);
lean_dec(v_x_972_);
v___x_977_ = lean_box(1);
v___x_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v_a_974_);
return v___x_978_;
}
else
{
lean_object* v_quotContext_979_; lean_object* v_currMacroScope_980_; lean_object* v_ref_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_quotContext_979_ = lean_ctor_get(v_a_973_, 1);
lean_inc(v_quotContext_979_);
v_currMacroScope_980_ = lean_ctor_get(v_a_973_, 2);
lean_inc(v_currMacroScope_980_);
v_ref_981_ = lean_ctor_get(v_a_973_, 5);
lean_inc(v_ref_981_);
lean_dec_ref(v_a_973_);
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = l_Lean_Syntax_getArg(v_x_972_, v___x_982_);
lean_dec(v_x_972_);
v___x_984_ = 0;
v___x_985_ = l_Lean_SourceInfo_fromRef(v_ref_981_, v___x_984_);
lean_dec(v_ref_981_);
v___x_986_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_987_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_988_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
v___x_989_ = l_Lean_addMacroScope(v_quotContext_979_, v___x_988_, v_currMacroScope_980_);
v___x_990_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc(v___x_985_);
v___x_991_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_991_, 0, v___x_985_);
lean_ctor_set(v___x_991_, 1, v___x_987_);
lean_ctor_set(v___x_991_, 2, v___x_989_);
lean_ctor_set(v___x_991_, 3, v___x_990_);
v___x_992_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_985_);
v___x_993_ = l_Lean_Syntax_node1(v___x_985_, v___x_992_, v___x_983_);
v___x_994_ = l_Lean_Syntax_node2(v___x_985_, v___x_986_, v___x_991_, v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_a_974_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(lean_object* v_x_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_996_);
v___x_1000_ = l_Lean_Syntax_isOfKind(v_x_996_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec_ref(v_a_997_);
lean_dec(v_x_996_);
v___x_1001_ = lean_box(1);
v___x_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_a_998_);
return v___x_1002_;
}
else
{
lean_object* v_quotContext_1003_; lean_object* v_currMacroScope_1004_; lean_object* v_ref_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_quotContext_1003_ = lean_ctor_get(v_a_997_, 1);
lean_inc(v_quotContext_1003_);
v_currMacroScope_1004_ = lean_ctor_get(v_a_997_, 2);
lean_inc(v_currMacroScope_1004_);
v_ref_1005_ = lean_ctor_get(v_a_997_, 5);
lean_inc(v_ref_1005_);
lean_dec_ref(v_a_997_);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = l_Lean_Syntax_getArg(v_x_996_, v___x_1006_);
lean_dec(v_x_996_);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_SourceInfo_fromRef(v_ref_1005_, v___x_1008_);
lean_dec(v_ref_1005_);
v___x_1010_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1011_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1012_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
v___x_1013_ = l_Lean_addMacroScope(v_quotContext_1003_, v___x_1012_, v_currMacroScope_1004_);
v___x_1014_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc(v___x_1009_);
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1009_);
lean_ctor_set(v___x_1015_, 1, v___x_1011_);
lean_ctor_set(v___x_1015_, 2, v___x_1013_);
lean_ctor_set(v___x_1015_, 3, v___x_1014_);
v___x_1016_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_1009_);
v___x_1017_ = l_Lean_Syntax_node1(v___x_1009_, v___x_1016_, v___x_1007_);
v___x_1018_ = l_Lean_Syntax_node2(v___x_1009_, v___x_1010_, v___x_1015_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_a_998_);
return v___x_1019_;
}
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0));
v___x_1022_ = l_String_toRawSubstring_x27(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(lean_object* v_x_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_1042_);
v___x_1046_ = l_Lean_Syntax_isOfKind(v_x_1042_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec_ref(v_a_1043_);
lean_dec(v_x_1042_);
v___x_1047_ = lean_box(1);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_a_1044_);
return v___x_1048_;
}
else
{
lean_object* v_quotContext_1049_; lean_object* v_currMacroScope_1050_; lean_object* v_ref_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_quotContext_1049_ = lean_ctor_get(v_a_1043_, 1);
lean_inc(v_quotContext_1049_);
v_currMacroScope_1050_ = lean_ctor_get(v_a_1043_, 2);
lean_inc(v_currMacroScope_1050_);
v_ref_1051_ = lean_ctor_get(v_a_1043_, 5);
lean_inc(v_ref_1051_);
lean_dec_ref(v_a_1043_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1052_);
v___x_1054_ = lean_unsigned_to_nat(2u);
v___x_1055_ = l_Lean_Syntax_getArg(v_x_1042_, v___x_1054_);
lean_dec(v_x_1042_);
v___x_1056_ = 0;
v___x_1057_ = l_Lean_SourceInfo_fromRef(v_ref_1051_, v___x_1056_);
lean_dec(v_ref_1051_);
v___x_1058_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1059_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1060_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
v___x_1061_ = l_Lean_addMacroScope(v_quotContext_1049_, v___x_1060_, v_currMacroScope_1050_);
v___x_1062_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc(v___x_1057_);
v___x_1063_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1057_);
lean_ctor_set(v___x_1063_, 1, v___x_1059_);
lean_ctor_set(v___x_1063_, 2, v___x_1061_);
lean_ctor_set(v___x_1063_, 3, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_1057_);
v___x_1065_ = l_Lean_Syntax_node2(v___x_1057_, v___x_1064_, v___x_1053_, v___x_1055_);
v___x_1066_ = l_Lean_Syntax_node2(v___x_1057_, v___x_1058_, v___x_1063_, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_a_1044_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(lean_object* v_x_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_1068_);
v___x_1072_ = l_Lean_Syntax_isOfKind(v_x_1068_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_dec_ref(v_a_1069_);
lean_dec(v_x_1068_);
v___x_1073_ = lean_box(1);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_1070_);
return v___x_1074_;
}
else
{
lean_object* v_quotContext_1075_; lean_object* v_currMacroScope_1076_; lean_object* v_ref_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_quotContext_1075_ = lean_ctor_get(v_a_1069_, 1);
lean_inc(v_quotContext_1075_);
v_currMacroScope_1076_ = lean_ctor_get(v_a_1069_, 2);
lean_inc(v_currMacroScope_1076_);
v_ref_1077_ = lean_ctor_get(v_a_1069_, 5);
lean_inc(v_ref_1077_);
lean_dec_ref(v_a_1069_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = l_Lean_Syntax_getArg(v_x_1068_, v___x_1078_);
v___x_1080_ = lean_unsigned_to_nat(2u);
v___x_1081_ = l_Lean_Syntax_getArg(v_x_1068_, v___x_1080_);
lean_dec(v_x_1068_);
v___x_1082_ = 0;
v___x_1083_ = l_Lean_SourceInfo_fromRef(v_ref_1077_, v___x_1082_);
lean_dec(v_ref_1077_);
v___x_1084_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1085_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1086_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
v___x_1087_ = l_Lean_addMacroScope(v_quotContext_1075_, v___x_1086_, v_currMacroScope_1076_);
v___x_1088_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc(v___x_1083_);
v___x_1089_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1083_);
lean_ctor_set(v___x_1089_, 1, v___x_1085_);
lean_ctor_set(v___x_1089_, 2, v___x_1087_);
lean_ctor_set(v___x_1089_, 3, v___x_1088_);
v___x_1090_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
lean_inc(v___x_1083_);
v___x_1091_ = l_Lean_Syntax_node2(v___x_1083_, v___x_1090_, v___x_1079_, v___x_1081_);
v___x_1092_ = l_Lean_Syntax_node2(v___x_1083_, v___x_1084_, v___x_1089_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_a_1070_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE(lean_object* v_00_u03b1_1094_, lean_object* v_inst_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_box(0);
return v___x_1096_;
}
}
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1097_, lean_object* v_a_1098_, lean_object* v_inst_1099_){
_start:
{
lean_object* v_lower_1100_; lean_object* v_upper_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_lower_1100_ = lean_ctor_get(v_r_1097_, 0);
lean_inc(v_lower_1100_);
v_upper_1101_ = lean_ctor_get(v_r_1097_, 1);
lean_inc(v_upper_1101_);
lean_dec_ref(v_r_1097_);
lean_inc_ref(v_inst_1099_);
lean_inc(v_a_1098_);
v___x_1102_ = lean_apply_2(v_inst_1099_, v_lower_1100_, v_a_1098_);
v___x_1103_ = lean_unbox(v___x_1102_);
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; 
lean_dec(v_upper_1101_);
lean_dec_ref(v_inst_1099_);
lean_dec(v_a_1098_);
v___x_1104_ = lean_unbox(v___x_1102_);
return v___x_1104_;
}
else
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = lean_apply_2(v_inst_1099_, v_a_1098_, v_upper_1101_);
v___x_1106_ = lean_unbox(v___x_1105_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1107_, lean_object* v_a_1108_, lean_object* v_inst_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1107_, v_a_1108_, v_inst_1109_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1112_, lean_object* v_r_1113_, lean_object* v_a_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1113_, v_a_1114_, v_inst_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_r_1119_, lean_object* v_a_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_){
_start:
{
uint8_t v_res_1123_; lean_object* v_r_1124_; 
v_res_1123_ = l_Std_Rcc_instDecidableMemOfDecidableLE(v_00_u03b1_1118_, v_r_1119_, v_a_1120_, v_inst_1121_, v_inst_1122_);
v_r_1124_ = lean_box(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_box(0);
return v___x_1128_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1129_, lean_object* v_a_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_){
_start:
{
lean_object* v_lower_1133_; lean_object* v_upper_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
v_lower_1133_ = lean_ctor_get(v_r_1129_, 0);
lean_inc(v_lower_1133_);
v_upper_1134_ = lean_ctor_get(v_r_1129_, 1);
lean_inc(v_upper_1134_);
lean_dec_ref(v_r_1129_);
lean_inc(v_a_1130_);
v___x_1135_ = lean_apply_2(v_inst_1131_, v_lower_1133_, v_a_1130_);
v___x_1136_ = lean_unbox(v___x_1135_);
if (v___x_1136_ == 0)
{
uint8_t v___x_1137_; 
lean_dec(v_upper_1134_);
lean_dec_ref(v_inst_1132_);
lean_dec(v_a_1130_);
v___x_1137_ = lean_unbox(v___x_1135_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_apply_2(v_inst_1132_, v_a_1130_, v_upper_1134_);
v___x_1139_ = lean_unbox(v___x_1138_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1140_, lean_object* v_a_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_){
_start:
{
uint8_t v_res_1144_; lean_object* v_r_1145_; 
v_res_1144_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1140_, v_a_1141_, v_inst_1142_, v_inst_1143_);
v_r_1145_ = lean_box(v_res_1144_);
return v_r_1145_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1146_, lean_object* v_r_1147_, lean_object* v_a_1148_, lean_object* v_inst_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1147_, v_a_1148_, v_inst_1150_, v_inst_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_r_1155_, lean_object* v_a_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_){
_start:
{
uint8_t v_res_1161_; lean_object* v_r_1162_; 
v_res_1161_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1154_, v_r_1155_, v_a_1156_, v_inst_1157_, v_inst_1158_, v_inst_1159_, v_inst_1160_);
v_r_1162_ = lean_box(v_res_1161_);
return v_r_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE(lean_object* v_00_u03b1_1163_, lean_object* v_inst_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_box(0);
return v___x_1165_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1166_, lean_object* v_a_1167_, lean_object* v_inst_1168_){
_start:
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = lean_apply_2(v_inst_1168_, v_r_1166_, v_a_1167_);
v___x_1170_ = lean_unbox(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1171_, lean_object* v_a_1172_, lean_object* v_inst_1173_){
_start:
{
uint8_t v_res_1174_; lean_object* v_r_1175_; 
v_res_1174_ = l_Std_Rci_instDecidableMemOfDecidableLE___redArg(v_r_1171_, v_a_1172_, v_inst_1173_);
v_r_1175_ = lean_box(v_res_1174_);
return v_r_1175_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1176_, lean_object* v_r_1177_, lean_object* v_a_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_apply_2(v_inst_1180_, v_r_1177_, v_a_1178_);
v___x_1182_ = lean_unbox(v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1183_, lean_object* v_r_1184_, lean_object* v_a_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Std_Rci_instDecidableMemOfDecidableLE(v_00_u03b1_1183_, v_r_1184_, v_a_1185_, v_inst_1186_, v_inst_1187_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_box(0);
return v___x_1193_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1194_, lean_object* v_a_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v_lower_1198_; lean_object* v_upper_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_lower_1198_ = lean_ctor_get(v_r_1194_, 0);
lean_inc(v_lower_1198_);
v_upper_1199_ = lean_ctor_get(v_r_1194_, 1);
lean_inc(v_upper_1199_);
lean_dec_ref(v_r_1194_);
lean_inc(v_a_1195_);
v___x_1200_ = lean_apply_2(v_inst_1197_, v_lower_1198_, v_a_1195_);
v___x_1201_ = lean_unbox(v___x_1200_);
if (v___x_1201_ == 0)
{
uint8_t v___x_1202_; 
lean_dec(v_upper_1199_);
lean_dec_ref(v_inst_1196_);
lean_dec(v_a_1195_);
v___x_1202_ = lean_unbox(v___x_1200_);
return v___x_1202_;
}
else
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_apply_2(v_inst_1196_, v_a_1195_, v_upper_1199_);
v___x_1204_ = lean_unbox(v___x_1203_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1205_, lean_object* v_a_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1205_, v_a_1206_, v_inst_1207_, v_inst_1208_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1211_, lean_object* v_r_1212_, lean_object* v_a_1213_, lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
uint8_t v___x_1218_; 
v___x_1218_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1212_, v_a_1213_, v_inst_1215_, v_inst_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_r_1220_, lean_object* v_a_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_){
_start:
{
uint8_t v_res_1226_; lean_object* v_r_1227_; 
v_res_1226_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1219_, v_r_1220_, v_a_1221_, v_inst_1222_, v_inst_1223_, v_inst_1224_, v_inst_1225_);
v_r_1227_ = lean_box(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT(lean_object* v_00_u03b1_1228_, lean_object* v_inst_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_box(0);
return v___x_1230_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1231_, lean_object* v_a_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v_lower_1234_; lean_object* v_upper_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_lower_1234_ = lean_ctor_get(v_r_1231_, 0);
lean_inc(v_lower_1234_);
v_upper_1235_ = lean_ctor_get(v_r_1231_, 1);
lean_inc(v_upper_1235_);
lean_dec_ref(v_r_1231_);
lean_inc_ref(v_inst_1233_);
lean_inc(v_a_1232_);
v___x_1236_ = lean_apply_2(v_inst_1233_, v_lower_1234_, v_a_1232_);
v___x_1237_ = lean_unbox(v___x_1236_);
if (v___x_1237_ == 0)
{
uint8_t v___x_1238_; 
lean_dec(v_upper_1235_);
lean_dec_ref(v_inst_1233_);
lean_dec(v_a_1232_);
v___x_1238_ = lean_unbox(v___x_1236_);
return v___x_1238_;
}
else
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_apply_2(v_inst_1233_, v_a_1232_, v_upper_1235_);
v___x_1240_ = lean_unbox(v___x_1239_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1241_, lean_object* v_a_1242_, lean_object* v_inst_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1241_, v_a_1242_, v_inst_1243_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1246_, lean_object* v_r_1247_, lean_object* v_a_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1247_, v_a_1248_, v_inst_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_r_1253_, lean_object* v_a_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Std_Roo_instDecidableMemOfDecidableLT(v_00_u03b1_1252_, v_r_1253_, v_a_1254_, v_inst_1255_, v_inst_1256_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT(lean_object* v_00_u03b1_1259_, lean_object* v_inst_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_box(0);
return v___x_1261_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1262_, lean_object* v_a_1263_, lean_object* v_inst_1264_){
_start:
{
lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1265_ = lean_apply_2(v_inst_1264_, v_r_1262_, v_a_1263_);
v___x_1266_ = lean_unbox(v___x_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1267_, lean_object* v_a_1268_, lean_object* v_inst_1269_){
_start:
{
uint8_t v_res_1270_; lean_object* v_r_1271_; 
v_res_1270_ = l_Std_Roi_instDecidableMemOfDecidableLT___redArg(v_r_1267_, v_a_1268_, v_inst_1269_);
v_r_1271_ = lean_box(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1272_, lean_object* v_r_1273_, lean_object* v_a_1274_, lean_object* v_inst_1275_, lean_object* v_inst_1276_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_apply_2(v_inst_1276_, v_r_1273_, v_a_1274_);
v___x_1278_ = lean_unbox(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1279_, lean_object* v_r_1280_, lean_object* v_a_1281_, lean_object* v_inst_1282_, lean_object* v_inst_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l_Std_Roi_instDecidableMemOfDecidableLT(v_00_u03b1_1279_, v_r_1280_, v_a_1281_, v_inst_1282_, v_inst_1283_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE(lean_object* v_00_u03b1_1286_, lean_object* v_inst_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_box(0);
return v___x_1288_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1289_, lean_object* v_a_1290_, lean_object* v_inst_1291_){
_start:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_apply_2(v_inst_1291_, v_a_1290_, v_r_1289_);
v___x_1293_ = lean_unbox(v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1294_, lean_object* v_a_1295_, lean_object* v_inst_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Std_Ric_instDecidableMemOfDecidableLE___redArg(v_r_1294_, v_a_1295_, v_inst_1296_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1299_, lean_object* v_r_1300_, lean_object* v_a_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_){
_start:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_apply_2(v_inst_1303_, v_a_1301_, v_r_1300_);
v___x_1305_ = lean_unbox(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_r_1307_, lean_object* v_a_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Std_Ric_instDecidableMemOfDecidableLE(v_00_u03b1_1306_, v_r_1307_, v_a_1308_, v_inst_1309_, v_inst_1310_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT(lean_object* v_00_u03b1_1313_, lean_object* v_inst_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1316_, lean_object* v_a_1317_, lean_object* v_inst_1318_){
_start:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = lean_apply_2(v_inst_1318_, v_a_1317_, v_r_1316_);
v___x_1320_ = lean_unbox(v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1321_, lean_object* v_a_1322_, lean_object* v_inst_1323_){
_start:
{
uint8_t v_res_1324_; lean_object* v_r_1325_; 
v_res_1324_ = l_Std_Rio_instDecidableMemOfDecidableLT___redArg(v_r_1321_, v_a_1322_, v_inst_1323_);
v_r_1325_ = lean_box(v_res_1324_);
return v_r_1325_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1326_, lean_object* v_r_1327_, lean_object* v_a_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_){
_start:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = lean_apply_2(v_inst_1330_, v_a_1328_, v_r_1327_);
v___x_1332_ = lean_unbox(v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1333_, lean_object* v_r_1334_, lean_object* v_a_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_){
_start:
{
uint8_t v_res_1338_; lean_object* v_r_1339_; 
v_res_1338_ = l_Std_Rio_instDecidableMemOfDecidableLT(v_00_u03b1_1333_, v_r_1334_, v_a_1335_, v_inst_1336_, v_inst_1337_);
v_r_1339_ = lean_box(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instMembership(lean_object* v_00_u03b1_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_box(0);
return v___x_1341_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_instDecidableMem(lean_object* v_00_u03b1_1342_, lean_object* v_r_1343_, lean_object* v_a_1344_){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = 1;
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___boxed(lean_object* v_00_u03b1_1346_, lean_object* v_r_1347_, lean_object* v_a_1348_){
_start:
{
uint8_t v_res_1349_; lean_object* v_r_1350_; 
v_res_1349_ = l_Std_Rii_instDecidableMem(v_00_u03b1_1346_, v_r_1347_, v_a_1348_);
lean_dec(v_a_1348_);
v_r_1350_ = lean_box(v_res_1349_);
return v_r_1350_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_UpwardEnumerable(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
