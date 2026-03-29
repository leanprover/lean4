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
v_currMacroScope_632_ = lean_ctor_get(v_a_625_, 2);
v_ref_633_ = lean_ctor_get(v_a_625_, 5);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_Lean_Syntax_getArg(v_x_624_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(2u);
v___x_637_ = l_Lean_Syntax_getArg(v_x_624_, v___x_636_);
lean_dec(v_x_624_);
v___x_638_ = 0;
v___x_639_ = l_Lean_SourceInfo_fromRef(v_ref_633_, v___x_638_);
v___x_640_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_641_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6);
v___x_642_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9));
lean_inc(v_currMacroScope_632_);
lean_inc(v_quotContext_631_);
v___x_643_ = l_Lean_addMacroScope(v_quotContext_631_, v___x_642_, v_currMacroScope_632_);
v___x_644_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14));
lean_inc_n(v___x_639_, 2);
v___x_645_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_645_, 0, v___x_639_);
lean_ctor_set(v___x_645_, 1, v___x_641_);
lean_ctor_set(v___x_645_, 2, v___x_643_);
lean_ctor_set(v___x_645_, 3, v___x_644_);
v___x_646_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_647_ = l_Lean_Syntax_node2(v___x_639_, v___x_646_, v___x_635_, v___x_637_);
v___x_648_ = l_Lean_Syntax_node2(v___x_639_, v___x_640_, v___x_645_, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_626_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(v_x_650_, v_a_651_, v_a_652_);
lean_dec_ref(v_a_651_);
return v_res_653_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0));
v___x_656_ = l_String_toRawSubstring_x27(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(lean_object* v_x_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_676_);
v___x_680_ = l_Lean_Syntax_isOfKind(v_x_676_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v_x_676_);
v___x_681_ = lean_box(1);
v___x_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_a_678_);
return v___x_682_;
}
else
{
lean_object* v_quotContext_683_; lean_object* v_currMacroScope_684_; lean_object* v_ref_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_quotContext_683_ = lean_ctor_get(v_a_677_, 1);
v_currMacroScope_684_ = lean_ctor_get(v_a_677_, 2);
v_ref_685_ = lean_ctor_get(v_a_677_, 5);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = l_Lean_Syntax_getArg(v_x_676_, v___x_686_);
lean_dec(v_x_676_);
v___x_688_ = 0;
v___x_689_ = l_Lean_SourceInfo_fromRef(v_ref_685_, v___x_688_);
v___x_690_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_691_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1);
v___x_692_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3));
lean_inc(v_currMacroScope_684_);
lean_inc(v_quotContext_683_);
v___x_693_ = l_Lean_addMacroScope(v_quotContext_683_, v___x_692_, v_currMacroScope_684_);
v___x_694_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc_n(v___x_689_, 2);
v___x_695_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_695_, 0, v___x_689_);
lean_ctor_set(v___x_695_, 1, v___x_691_);
lean_ctor_set(v___x_695_, 2, v___x_693_);
lean_ctor_set(v___x_695_, 3, v___x_694_);
v___x_696_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_697_ = l_Lean_Syntax_node1(v___x_689_, v___x_696_, v___x_687_);
v___x_698_ = l_Lean_Syntax_node2(v___x_689_, v___x_690_, v___x_695_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v_a_678_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(v_x_700_, v_a_701_, v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_703_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0));
v___x_706_ = l_String_toRawSubstring_x27(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(lean_object* v_x_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x2a___closed__2));
lean_inc(v_x_726_);
v___x_730_ = l_Lean_Syntax_isOfKind(v_x_726_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v_x_726_);
v___x_731_ = lean_box(1);
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_a_728_);
return v___x_732_;
}
else
{
lean_object* v_quotContext_733_; lean_object* v_currMacroScope_734_; lean_object* v_ref_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_quotContext_733_ = lean_ctor_get(v_a_727_, 1);
v_currMacroScope_734_ = lean_ctor_get(v_a_727_, 2);
v_ref_735_ = lean_ctor_get(v_a_727_, 5);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = l_Lean_Syntax_getArg(v_x_726_, v___x_736_);
lean_dec(v_x_726_);
v___x_738_ = 0;
v___x_739_ = l_Lean_SourceInfo_fromRef(v_ref_735_, v___x_738_);
v___x_740_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_741_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1);
v___x_742_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_734_);
lean_inc(v_quotContext_733_);
v___x_743_ = l_Lean_addMacroScope(v_quotContext_733_, v___x_742_, v_currMacroScope_734_);
v___x_744_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8));
lean_inc_n(v___x_739_, 2);
v___x_745_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_745_, 0, v___x_739_);
lean_ctor_set(v___x_745_, 1, v___x_741_);
lean_ctor_set(v___x_745_, 2, v___x_743_);
lean_ctor_set(v___x_745_, 3, v___x_744_);
v___x_746_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_747_ = l_Lean_Syntax_node1(v___x_739_, v___x_746_, v___x_737_);
v___x_748_ = l_Lean_Syntax_node2(v___x_739_, v___x_740_, v___x_745_, v___x_747_);
v___x_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_a_728_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(v_x_750_, v_a_751_, v_a_752_);
lean_dec_ref(v_a_751_);
return v_res_753_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0));
v___x_756_ = l_String_toRawSubstring_x27(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(lean_object* v_x_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1));
v___x_780_ = l_Lean_Syntax_isOfKind(v_x_776_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_box(1);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_a_778_);
return v___x_782_;
}
else
{
lean_object* v_quotContext_783_; lean_object* v_currMacroScope_784_; lean_object* v_ref_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_quotContext_783_ = lean_ctor_get(v_a_777_, 1);
v_currMacroScope_784_ = lean_ctor_get(v_a_777_, 2);
v_ref_785_ = lean_ctor_get(v_a_777_, 5);
v___x_786_ = 0;
v___x_787_ = l_Lean_SourceInfo_fromRef(v_ref_785_, v___x_786_);
v___x_788_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1);
v___x_789_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_784_);
lean_inc(v_quotContext_783_);
v___x_790_ = l_Lean_addMacroScope(v_quotContext_783_, v___x_789_, v_currMacroScope_784_);
v___x_791_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8));
v___x_792_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_792_, 0, v___x_787_);
lean_ctor_set(v___x_792_, 1, v___x_788_);
lean_ctor_set(v___x_792_, 2, v___x_790_);
lean_ctor_set(v___x_792_, 3, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_778_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(v_x_794_, v_a_795_, v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_797_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0));
v___x_800_ = l_String_toRawSubstring_x27(v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(lean_object* v_x_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_823_; uint8_t v___x_824_; 
v___x_823_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_820_);
v___x_824_ = l_Lean_Syntax_isOfKind(v_x_820_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_x_820_);
v___x_825_ = lean_box(1);
v___x_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_a_822_);
return v___x_826_;
}
else
{
lean_object* v_quotContext_827_; lean_object* v_currMacroScope_828_; lean_object* v_ref_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_quotContext_827_ = lean_ctor_get(v_a_821_, 1);
v_currMacroScope_828_ = lean_ctor_get(v_a_821_, 2);
v_ref_829_ = lean_ctor_get(v_a_821_, 5);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = l_Lean_Syntax_getArg(v_x_820_, v___x_830_);
v___x_832_ = lean_unsigned_to_nat(2u);
v___x_833_ = l_Lean_Syntax_getArg(v_x_820_, v___x_832_);
lean_dec(v_x_820_);
v___x_834_ = 0;
v___x_835_ = l_Lean_SourceInfo_fromRef(v_ref_829_, v___x_834_);
v___x_836_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_837_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1);
v___x_838_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3));
lean_inc(v_currMacroScope_828_);
lean_inc(v_quotContext_827_);
v___x_839_ = l_Lean_addMacroScope(v_quotContext_827_, v___x_838_, v_currMacroScope_828_);
v___x_840_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc_n(v___x_835_, 2);
v___x_841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_841_, 0, v___x_835_);
lean_ctor_set(v___x_841_, 1, v___x_837_);
lean_ctor_set(v___x_841_, 2, v___x_839_);
lean_ctor_set(v___x_841_, 3, v___x_840_);
v___x_842_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_843_ = l_Lean_Syntax_node2(v___x_835_, v___x_842_, v___x_831_, v___x_833_);
v___x_844_ = l_Lean_Syntax_node2(v___x_835_, v___x_836_, v___x_841_, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_a_822_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(v_x_846_, v_a_847_, v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_849_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0));
v___x_852_ = l_String_toRawSubstring_x27(v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(lean_object* v_x_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1));
lean_inc(v_x_872_);
v___x_876_ = l_Lean_Syntax_isOfKind(v_x_872_, v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
lean_dec(v_x_872_);
v___x_877_ = lean_box(1);
v___x_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v_a_874_);
return v___x_878_;
}
else
{
lean_object* v_quotContext_879_; lean_object* v_currMacroScope_880_; lean_object* v_ref_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_quotContext_879_ = lean_ctor_get(v_a_873_, 1);
v_currMacroScope_880_ = lean_ctor_get(v_a_873_, 2);
v_ref_881_ = lean_ctor_get(v_a_873_, 5);
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = l_Lean_Syntax_getArg(v_x_872_, v___x_882_);
lean_dec(v_x_872_);
v___x_884_ = 0;
v___x_885_ = l_Lean_SourceInfo_fromRef(v_ref_881_, v___x_884_);
v___x_886_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_887_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1);
v___x_888_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_880_);
lean_inc(v_quotContext_879_);
v___x_889_ = l_Lean_addMacroScope(v_quotContext_879_, v___x_888_, v_currMacroScope_880_);
v___x_890_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8));
lean_inc_n(v___x_885_, 2);
v___x_891_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_891_, 0, v___x_885_);
lean_ctor_set(v___x_891_, 1, v___x_887_);
lean_ctor_set(v___x_891_, 2, v___x_889_);
lean_ctor_set(v___x_891_, 3, v___x_890_);
v___x_892_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_893_ = l_Lean_Syntax_node1(v___x_885_, v___x_892_, v___x_883_);
v___x_894_ = l_Lean_Syntax_node2(v___x_885_, v___x_886_, v___x_891_, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v_a_874_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(v_x_896_, v_a_897_, v_a_898_);
lean_dec_ref(v_a_897_);
return v_res_899_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0));
v___x_902_ = l_String_toRawSubstring_x27(v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(lean_object* v_x_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_922_);
v___x_926_ = l_Lean_Syntax_isOfKind(v_x_922_, v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec(v_x_922_);
v___x_927_ = lean_box(1);
v___x_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v_a_924_);
return v___x_928_;
}
else
{
lean_object* v_quotContext_929_; lean_object* v_currMacroScope_930_; lean_object* v_ref_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_quotContext_929_ = lean_ctor_get(v_a_923_, 1);
v_currMacroScope_930_ = lean_ctor_get(v_a_923_, 2);
v_ref_931_ = lean_ctor_get(v_a_923_, 5);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = l_Lean_Syntax_getArg(v_x_922_, v___x_932_);
v___x_934_ = lean_unsigned_to_nat(2u);
v___x_935_ = l_Lean_Syntax_getArg(v_x_922_, v___x_934_);
lean_dec(v_x_922_);
v___x_936_ = 0;
v___x_937_ = l_Lean_SourceInfo_fromRef(v_ref_931_, v___x_936_);
v___x_938_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_939_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_940_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_930_);
lean_inc(v_quotContext_929_);
v___x_941_ = l_Lean_addMacroScope(v_quotContext_929_, v___x_940_, v_currMacroScope_930_);
v___x_942_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_937_, 2);
v___x_943_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_943_, 0, v___x_937_);
lean_ctor_set(v___x_943_, 1, v___x_939_);
lean_ctor_set(v___x_943_, 2, v___x_941_);
lean_ctor_set(v___x_943_, 3, v___x_942_);
v___x_944_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_945_ = l_Lean_Syntax_node2(v___x_937_, v___x_944_, v___x_933_, v___x_935_);
v___x_946_ = l_Lean_Syntax_node2(v___x_937_, v___x_938_, v___x_943_, v___x_945_);
v___x_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_a_924_);
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(v_x_948_, v_a_949_, v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(lean_object* v_x_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_952_);
v___x_956_ = l_Lean_Syntax_isOfKind(v_x_952_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_x_952_);
v___x_957_ = lean_box(1);
v___x_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v_a_954_);
return v___x_958_;
}
else
{
lean_object* v_quotContext_959_; lean_object* v_currMacroScope_960_; lean_object* v_ref_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_quotContext_959_ = lean_ctor_get(v_a_953_, 1);
v_currMacroScope_960_ = lean_ctor_get(v_a_953_, 2);
v_ref_961_ = lean_ctor_get(v_a_953_, 5);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = l_Lean_Syntax_getArg(v_x_952_, v___x_962_);
v___x_964_ = lean_unsigned_to_nat(2u);
v___x_965_ = l_Lean_Syntax_getArg(v_x_952_, v___x_964_);
lean_dec(v_x_952_);
v___x_966_ = 0;
v___x_967_ = l_Lean_SourceInfo_fromRef(v_ref_961_, v___x_966_);
v___x_968_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_969_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_970_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_960_);
lean_inc(v_quotContext_959_);
v___x_971_ = l_Lean_addMacroScope(v_quotContext_959_, v___x_970_, v_currMacroScope_960_);
v___x_972_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_967_, 2);
v___x_973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_973_, 0, v___x_967_);
lean_ctor_set(v___x_973_, 1, v___x_969_);
lean_ctor_set(v___x_973_, 2, v___x_971_);
lean_ctor_set(v___x_973_, 3, v___x_972_);
v___x_974_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_975_ = l_Lean_Syntax_node2(v___x_967_, v___x_974_, v___x_963_, v___x_965_);
v___x_976_ = l_Lean_Syntax_node2(v___x_967_, v___x_968_, v___x_973_, v___x_975_);
v___x_977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v_a_954_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1___boxed(lean_object* v_x_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(v_x_978_, v_a_979_, v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_981_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0));
v___x_984_ = l_String_toRawSubstring_x27(v___x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(lean_object* v_x_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_1004_);
v___x_1008_ = l_Lean_Syntax_isOfKind(v_x_1004_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec(v_x_1004_);
v___x_1009_ = lean_box(1);
v___x_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_a_1006_);
return v___x_1010_;
}
else
{
lean_object* v_quotContext_1011_; lean_object* v_currMacroScope_1012_; lean_object* v_ref_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_quotContext_1011_ = lean_ctor_get(v_a_1005_, 1);
v_currMacroScope_1012_ = lean_ctor_get(v_a_1005_, 2);
v_ref_1013_ = lean_ctor_get(v_a_1005_, 5);
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = l_Lean_Syntax_getArg(v_x_1004_, v___x_1014_);
lean_dec(v_x_1004_);
v___x_1016_ = 0;
v___x_1017_ = l_Lean_SourceInfo_fromRef(v_ref_1013_, v___x_1016_);
v___x_1018_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1019_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1020_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1012_);
lean_inc(v_quotContext_1011_);
v___x_1021_ = l_Lean_addMacroScope(v_quotContext_1011_, v___x_1020_, v_currMacroScope_1012_);
v___x_1022_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1017_, 2);
v___x_1023_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1017_);
lean_ctor_set(v___x_1023_, 1, v___x_1019_);
lean_ctor_set(v___x_1023_, 2, v___x_1021_);
lean_ctor_set(v___x_1023_, 3, v___x_1022_);
v___x_1024_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1025_ = l_Lean_Syntax_node1(v___x_1017_, v___x_1024_, v___x_1015_);
v___x_1026_ = l_Lean_Syntax_node2(v___x_1017_, v___x_1018_, v___x_1023_, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v_a_1006_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(v_x_1028_, v_a_1029_, v_a_1030_);
lean_dec_ref(v_a_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(lean_object* v_x_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_1032_);
v___x_1036_ = l_Lean_Syntax_isOfKind(v_x_1032_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec(v_x_1032_);
v___x_1037_ = lean_box(1);
v___x_1038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_a_1034_);
return v___x_1038_;
}
else
{
lean_object* v_quotContext_1039_; lean_object* v_currMacroScope_1040_; lean_object* v_ref_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_quotContext_1039_ = lean_ctor_get(v_a_1033_, 1);
v_currMacroScope_1040_ = lean_ctor_get(v_a_1033_, 2);
v_ref_1041_ = lean_ctor_get(v_a_1033_, 5);
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = l_Lean_Syntax_getArg(v_x_1032_, v___x_1042_);
lean_dec(v_x_1032_);
v___x_1044_ = 0;
v___x_1045_ = l_Lean_SourceInfo_fromRef(v_ref_1041_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1047_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1048_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1040_);
lean_inc(v_quotContext_1039_);
v___x_1049_ = l_Lean_addMacroScope(v_quotContext_1039_, v___x_1048_, v_currMacroScope_1040_);
v___x_1050_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1045_, 2);
v___x_1051_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1045_);
lean_ctor_set(v___x_1051_, 1, v___x_1047_);
lean_ctor_set(v___x_1051_, 2, v___x_1049_);
lean_ctor_set(v___x_1051_, 3, v___x_1050_);
v___x_1052_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1053_ = l_Lean_Syntax_node1(v___x_1045_, v___x_1052_, v___x_1043_);
v___x_1054_ = l_Lean_Syntax_node2(v___x_1045_, v___x_1046_, v___x_1051_, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v_a_1034_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1___boxed(lean_object* v_x_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(v_x_1056_, v_a_1057_, v_a_1058_);
lean_dec_ref(v_a_1057_);
return v_res_1059_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0));
v___x_1062_ = l_String_toRawSubstring_x27(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(lean_object* v_x_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_1082_);
v___x_1086_ = l_Lean_Syntax_isOfKind(v_x_1082_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_dec(v_x_1082_);
v___x_1087_ = lean_box(1);
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
lean_ctor_set(v___x_1088_, 1, v_a_1084_);
return v___x_1088_;
}
else
{
lean_object* v_quotContext_1089_; lean_object* v_currMacroScope_1090_; lean_object* v_ref_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_quotContext_1089_ = lean_ctor_get(v_a_1083_, 1);
v_currMacroScope_1090_ = lean_ctor_get(v_a_1083_, 2);
v_ref_1091_ = lean_ctor_get(v_a_1083_, 5);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = l_Lean_Syntax_getArg(v_x_1082_, v___x_1092_);
v___x_1094_ = lean_unsigned_to_nat(2u);
v___x_1095_ = l_Lean_Syntax_getArg(v_x_1082_, v___x_1094_);
lean_dec(v_x_1082_);
v___x_1096_ = 0;
v___x_1097_ = l_Lean_SourceInfo_fromRef(v_ref_1091_, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1099_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1100_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1090_);
lean_inc(v_quotContext_1089_);
v___x_1101_ = l_Lean_addMacroScope(v_quotContext_1089_, v___x_1100_, v_currMacroScope_1090_);
v___x_1102_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1097_, 2);
v___x_1103_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1097_);
lean_ctor_set(v___x_1103_, 1, v___x_1099_);
lean_ctor_set(v___x_1103_, 2, v___x_1101_);
lean_ctor_set(v___x_1103_, 3, v___x_1102_);
v___x_1104_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1105_ = l_Lean_Syntax_node2(v___x_1097_, v___x_1104_, v___x_1093_, v___x_1095_);
v___x_1106_ = l_Lean_Syntax_node2(v___x_1097_, v___x_1098_, v___x_1103_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_a_1084_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(v_x_1108_, v_a_1109_, v_a_1110_);
lean_dec_ref(v_a_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(lean_object* v_x_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_1112_);
v___x_1116_ = l_Lean_Syntax_isOfKind(v_x_1112_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v_x_1112_);
v___x_1117_ = lean_box(1);
v___x_1118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_a_1114_);
return v___x_1118_;
}
else
{
lean_object* v_quotContext_1119_; lean_object* v_currMacroScope_1120_; lean_object* v_ref_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_quotContext_1119_ = lean_ctor_get(v_a_1113_, 1);
v_currMacroScope_1120_ = lean_ctor_get(v_a_1113_, 2);
v_ref_1121_ = lean_ctor_get(v_a_1113_, 5);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = l_Lean_Syntax_getArg(v_x_1112_, v___x_1122_);
v___x_1124_ = lean_unsigned_to_nat(2u);
v___x_1125_ = l_Lean_Syntax_getArg(v_x_1112_, v___x_1124_);
lean_dec(v_x_1112_);
v___x_1126_ = 0;
v___x_1127_ = l_Lean_SourceInfo_fromRef(v_ref_1121_, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1129_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1130_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1120_);
lean_inc(v_quotContext_1119_);
v___x_1131_ = l_Lean_addMacroScope(v_quotContext_1119_, v___x_1130_, v_currMacroScope_1120_);
v___x_1132_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1127_, 2);
v___x_1133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1127_);
lean_ctor_set(v___x_1133_, 1, v___x_1129_);
lean_ctor_set(v___x_1133_, 2, v___x_1131_);
lean_ctor_set(v___x_1133_, 3, v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1135_ = l_Lean_Syntax_node2(v___x_1127_, v___x_1134_, v___x_1123_, v___x_1125_);
v___x_1136_ = l_Lean_Syntax_node2(v___x_1127_, v___x_1128_, v___x_1133_, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_a_1114_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1___boxed(lean_object* v_x_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(v_x_1138_, v_a_1139_, v_a_1140_);
lean_dec_ref(v_a_1139_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE(lean_object* v_00_u03b1_1142_, lean_object* v_inst_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
}
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1145_, lean_object* v_a_1146_, lean_object* v_inst_1147_){
_start:
{
lean_object* v_lower_1148_; lean_object* v_upper_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_lower_1148_ = lean_ctor_get(v_r_1145_, 0);
lean_inc(v_lower_1148_);
v_upper_1149_ = lean_ctor_get(v_r_1145_, 1);
lean_inc(v_upper_1149_);
lean_dec_ref(v_r_1145_);
lean_inc_ref(v_inst_1147_);
lean_inc(v_a_1146_);
v___x_1150_ = lean_apply_2(v_inst_1147_, v_lower_1148_, v_a_1146_);
v___x_1151_ = lean_unbox(v___x_1150_);
if (v___x_1151_ == 0)
{
uint8_t v___x_1152_; 
lean_dec(v_upper_1149_);
lean_dec_ref(v_inst_1147_);
lean_dec(v_a_1146_);
v___x_1152_ = lean_unbox(v___x_1150_);
return v___x_1152_;
}
else
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_apply_2(v_inst_1147_, v_a_1146_, v_upper_1149_);
v___x_1154_ = lean_unbox(v___x_1153_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1155_, lean_object* v_a_1156_, lean_object* v_inst_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1155_, v_a_1156_, v_inst_1157_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1160_, lean_object* v_r_1161_, lean_object* v_a_1162_, lean_object* v_inst_1163_, lean_object* v_inst_1164_){
_start:
{
uint8_t v___x_1165_; 
v___x_1165_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1161_, v_a_1162_, v_inst_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1166_, lean_object* v_r_1167_, lean_object* v_a_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l_Std_Rcc_instDecidableMemOfDecidableLE(v_00_u03b1_1166_, v_r_1167_, v_a_1168_, v_inst_1169_, v_inst_1170_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_box(0);
return v___x_1176_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1177_, lean_object* v_a_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v_lower_1181_; lean_object* v_upper_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_lower_1181_ = lean_ctor_get(v_r_1177_, 0);
lean_inc(v_lower_1181_);
v_upper_1182_ = lean_ctor_get(v_r_1177_, 1);
lean_inc(v_upper_1182_);
lean_dec_ref(v_r_1177_);
lean_inc(v_a_1178_);
v___x_1183_ = lean_apply_2(v_inst_1179_, v_lower_1181_, v_a_1178_);
v___x_1184_ = lean_unbox(v___x_1183_);
if (v___x_1184_ == 0)
{
uint8_t v___x_1185_; 
lean_dec(v_upper_1182_);
lean_dec_ref(v_inst_1180_);
lean_dec(v_a_1178_);
v___x_1185_ = lean_unbox(v___x_1183_);
return v___x_1185_;
}
else
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = lean_apply_2(v_inst_1180_, v_a_1178_, v_upper_1182_);
v___x_1187_ = lean_unbox(v___x_1186_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1188_, lean_object* v_a_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_){
_start:
{
uint8_t v_res_1192_; lean_object* v_r_1193_; 
v_res_1192_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1188_, v_a_1189_, v_inst_1190_, v_inst_1191_);
v_r_1193_ = lean_box(v_res_1192_);
return v_r_1193_;
}
}
LEAN_EXPORT uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1194_, lean_object* v_r_1195_, lean_object* v_a_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1195_, v_a_1196_, v_inst_1198_, v_inst_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1202_, lean_object* v_r_1203_, lean_object* v_a_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_inst_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1202_, v_r_1203_, v_a_1204_, v_inst_1205_, v_inst_1206_, v_inst_1207_, v_inst_1208_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE(lean_object* v_00_u03b1_1211_, lean_object* v_inst_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_box(0);
return v___x_1213_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1214_, lean_object* v_a_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1217_ = lean_apply_2(v_inst_1216_, v_r_1214_, v_a_1215_);
v___x_1218_ = lean_unbox(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1219_, lean_object* v_a_1220_, lean_object* v_inst_1221_){
_start:
{
uint8_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Std_Rci_instDecidableMemOfDecidableLE___redArg(v_r_1219_, v_a_1220_, v_inst_1221_);
v_r_1223_ = lean_box(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT uint8_t l_Std_Rci_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1224_, lean_object* v_r_1225_, lean_object* v_a_1226_, lean_object* v_inst_1227_, lean_object* v_inst_1228_){
_start:
{
lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1229_ = lean_apply_2(v_inst_1228_, v_r_1225_, v_a_1226_);
v___x_1230_ = lean_unbox(v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_r_1232_, lean_object* v_a_1233_, lean_object* v_inst_1234_, lean_object* v_inst_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_Std_Rci_instDecidableMemOfDecidableLE(v_00_u03b1_1231_, v_r_1232_, v_a_1233_, v_inst_1234_, v_inst_1235_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_box(0);
return v___x_1241_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1242_, lean_object* v_a_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_){
_start:
{
lean_object* v_lower_1246_; lean_object* v_upper_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_lower_1246_ = lean_ctor_get(v_r_1242_, 0);
lean_inc(v_lower_1246_);
v_upper_1247_ = lean_ctor_get(v_r_1242_, 1);
lean_inc(v_upper_1247_);
lean_dec_ref(v_r_1242_);
lean_inc(v_a_1243_);
v___x_1248_ = lean_apply_2(v_inst_1245_, v_lower_1246_, v_a_1243_);
v___x_1249_ = lean_unbox(v___x_1248_);
if (v___x_1249_ == 0)
{
uint8_t v___x_1250_; 
lean_dec(v_upper_1247_);
lean_dec_ref(v_inst_1244_);
lean_dec(v_a_1243_);
v___x_1250_ = lean_unbox(v___x_1248_);
return v___x_1250_;
}
else
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_apply_2(v_inst_1244_, v_a_1243_, v_upper_1247_);
v___x_1252_ = lean_unbox(v___x_1251_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1253_, lean_object* v_a_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_){
_start:
{
uint8_t v_res_1257_; lean_object* v_r_1258_; 
v_res_1257_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1253_, v_a_1254_, v_inst_1255_, v_inst_1256_);
v_r_1258_ = lean_box(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1259_, lean_object* v_r_1260_, lean_object* v_a_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_inst_1265_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1260_, v_a_1261_, v_inst_1263_, v_inst_1265_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_r_1268_, lean_object* v_a_1269_, lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1267_, v_r_1268_, v_a_1269_, v_inst_1270_, v_inst_1271_, v_inst_1272_, v_inst_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT(lean_object* v_00_u03b1_1276_, lean_object* v_inst_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_box(0);
return v___x_1278_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1279_, lean_object* v_a_1280_, lean_object* v_inst_1281_){
_start:
{
lean_object* v_lower_1282_; lean_object* v_upper_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_lower_1282_ = lean_ctor_get(v_r_1279_, 0);
lean_inc(v_lower_1282_);
v_upper_1283_ = lean_ctor_get(v_r_1279_, 1);
lean_inc(v_upper_1283_);
lean_dec_ref(v_r_1279_);
lean_inc_ref(v_inst_1281_);
lean_inc(v_a_1280_);
v___x_1284_ = lean_apply_2(v_inst_1281_, v_lower_1282_, v_a_1280_);
v___x_1285_ = lean_unbox(v___x_1284_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; 
lean_dec(v_upper_1283_);
lean_dec_ref(v_inst_1281_);
lean_dec(v_a_1280_);
v___x_1286_ = lean_unbox(v___x_1284_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_apply_2(v_inst_1281_, v_a_1280_, v_upper_1283_);
v___x_1288_ = lean_unbox(v___x_1287_);
return v___x_1288_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1289_, lean_object* v_a_1290_, lean_object* v_inst_1291_){
_start:
{
uint8_t v_res_1292_; lean_object* v_r_1293_; 
v_res_1292_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1289_, v_a_1290_, v_inst_1291_);
v_r_1293_ = lean_box(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT uint8_t l_Std_Roo_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1294_, lean_object* v_r_1295_, lean_object* v_a_1296_, lean_object* v_inst_1297_, lean_object* v_inst_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1295_, v_a_1296_, v_inst_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1300_, lean_object* v_r_1301_, lean_object* v_a_1302_, lean_object* v_inst_1303_, lean_object* v_inst_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Std_Roo_instDecidableMemOfDecidableLT(v_00_u03b1_1300_, v_r_1301_, v_a_1302_, v_inst_1303_, v_inst_1304_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT(lean_object* v_00_u03b1_1307_, lean_object* v_inst_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_box(0);
return v___x_1309_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1310_, lean_object* v_a_1311_, lean_object* v_inst_1312_){
_start:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_apply_2(v_inst_1312_, v_r_1310_, v_a_1311_);
v___x_1314_ = lean_unbox(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1315_, lean_object* v_a_1316_, lean_object* v_inst_1317_){
_start:
{
uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_res_1318_ = l_Std_Roi_instDecidableMemOfDecidableLT___redArg(v_r_1315_, v_a_1316_, v_inst_1317_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT uint8_t l_Std_Roi_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1320_, lean_object* v_r_1321_, lean_object* v_a_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_){
_start:
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_apply_2(v_inst_1324_, v_r_1321_, v_a_1322_);
v___x_1326_ = lean_unbox(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_r_1328_, lean_object* v_a_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_){
_start:
{
uint8_t v_res_1332_; lean_object* v_r_1333_; 
v_res_1332_ = l_Std_Roi_instDecidableMemOfDecidableLT(v_00_u03b1_1327_, v_r_1328_, v_a_1329_, v_inst_1330_, v_inst_1331_);
v_r_1333_ = lean_box(v_res_1332_);
return v_r_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE(lean_object* v_00_u03b1_1334_, lean_object* v_inst_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_box(0);
return v___x_1336_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1337_, lean_object* v_a_1338_, lean_object* v_inst_1339_){
_start:
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = lean_apply_2(v_inst_1339_, v_a_1338_, v_r_1337_);
v___x_1341_ = lean_unbox(v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1342_, lean_object* v_a_1343_, lean_object* v_inst_1344_){
_start:
{
uint8_t v_res_1345_; lean_object* v_r_1346_; 
v_res_1345_ = l_Std_Ric_instDecidableMemOfDecidableLE___redArg(v_r_1342_, v_a_1343_, v_inst_1344_);
v_r_1346_ = lean_box(v_res_1345_);
return v_r_1346_;
}
}
LEAN_EXPORT uint8_t l_Std_Ric_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1347_, lean_object* v_r_1348_, lean_object* v_a_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_){
_start:
{
lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1352_ = lean_apply_2(v_inst_1351_, v_a_1349_, v_r_1348_);
v___x_1353_ = lean_unbox(v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_r_1355_, lean_object* v_a_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_){
_start:
{
uint8_t v_res_1359_; lean_object* v_r_1360_; 
v_res_1359_ = l_Std_Ric_instDecidableMemOfDecidableLE(v_00_u03b1_1354_, v_r_1355_, v_a_1356_, v_inst_1357_, v_inst_1358_);
v_r_1360_ = lean_box(v_res_1359_);
return v_r_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT(lean_object* v_00_u03b1_1361_, lean_object* v_inst_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_box(0);
return v___x_1363_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1364_, lean_object* v_a_1365_, lean_object* v_inst_1366_){
_start:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = lean_apply_2(v_inst_1366_, v_a_1365_, v_r_1364_);
v___x_1368_ = lean_unbox(v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1369_, lean_object* v_a_1370_, lean_object* v_inst_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Std_Rio_instDecidableMemOfDecidableLT___redArg(v_r_1369_, v_a_1370_, v_inst_1371_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT uint8_t l_Std_Rio_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1374_, lean_object* v_r_1375_, lean_object* v_a_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_){
_start:
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = lean_apply_2(v_inst_1378_, v_a_1376_, v_r_1375_);
v___x_1380_ = lean_unbox(v___x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_r_1382_, lean_object* v_a_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l_Std_Rio_instDecidableMemOfDecidableLT(v_00_u03b1_1381_, v_r_1382_, v_a_1383_, v_inst_1384_, v_inst_1385_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instMembership(lean_object* v_00_u03b1_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_box(0);
return v___x_1389_;
}
}
LEAN_EXPORT uint8_t l_Std_Rii_instDecidableMem(lean_object* v_00_u03b1_1390_, lean_object* v_r_1391_, lean_object* v_a_1392_){
_start:
{
uint8_t v___x_1393_; 
v___x_1393_ = 1;
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_r_1395_, lean_object* v_a_1396_){
_start:
{
uint8_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l_Std_Rii_instDecidableMem(v_00_u03b1_1394_, v_r_1395_, v_a_1396_);
lean_dec(v_a_1396_);
v_r_1398_ = lean_box(v_res_1397_);
return v_r_1398_;
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
