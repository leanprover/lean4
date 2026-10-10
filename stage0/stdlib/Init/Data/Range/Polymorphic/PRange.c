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
uint8_t l_Std_instDecidableEqRcc_decEq___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_){
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
LEAN_EXPORT void l_Std_instDecidableEqRcc_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_x_3_ = stack[2].m_obj;
uint8_t v_res_13_;
v_res_13_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_1_, v_x_2_, v_x_3_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc_decEq___redArg___boxed(lean_object* v_inst_14_, lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_14_, v_x_15_, v_x_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
uint8_t l_Std_instDecidableEqRcc_decEq(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_20_, v_x_21_, v_x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRcc_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_20_ = stack[1].m_obj;
lean_object* v_x_21_ = stack[2].m_obj;
lean_object* v_x_22_ = stack[3].m_obj;
uint8_t v_res_24_;
v_res_24_ = l_Std_instDecidableEqRcc_decEq(lean_box(0), v_inst_20_, v_x_21_, v_x_22_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc_decEq___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Std_instDecidableEqRcc_decEq(v_00_u03b1_25_, v_inst_26_, v_x_27_, v_x_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
uint8_t l_Std_instDecidableEqRcc___redArg(lean_object* v_inst_31_, lean_object* v_x_32_, lean_object* v_x_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_31_, v_x_32_, v_x_33_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRcc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_31_ = stack[0].m_obj;
lean_object* v_x_32_ = stack[1].m_obj;
lean_object* v_x_33_ = stack[2].m_obj;
uint8_t v_res_35_;
v_res_35_ = l_Std_instDecidableEqRcc___redArg(v_inst_31_, v_x_32_, v_x_33_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc___redArg___boxed(lean_object* v_inst_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_Std_instDecidableEqRcc___redArg(v_inst_36_, v_x_37_, v_x_38_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
uint8_t l_Std_instDecidableEqRcc(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = l_Std_instDecidableEqRcc_decEq___redArg(v_inst_42_, v_x_43_, v_x_44_);
return v___x_45_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_42_ = stack[1].m_obj;
lean_object* v_x_43_ = stack[2].m_obj;
lean_object* v_x_44_ = stack[3].m_obj;
uint8_t v_res_46_;
v_res_46_ = l_Std_instDecidableEqRcc(lean_box(0), v_inst_42_, v_x_43_, v_x_44_);
stack->m_num = v_res_46_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRcc___boxed(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Std_instDecidableEqRcc(v_00_u03b1_47_, v_inst_48_, v_x_49_, v_x_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
uint8_t l_Std_instDecidableEqRco_decEq___redArg(lean_object* v_inst_53_, lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_lower_56_; lean_object* v_upper_57_; lean_object* v_lower_58_; lean_object* v_upper_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_lower_56_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_lower_56_);
v_upper_57_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_upper_57_);
lean_dec_ref(v_x_54_);
v_lower_58_ = lean_ctor_get(v_x_55_, 0);
lean_inc(v_lower_58_);
v_upper_59_ = lean_ctor_get(v_x_55_, 1);
lean_inc(v_upper_59_);
lean_dec_ref(v_x_55_);
lean_inc_ref(v_inst_53_);
v___x_60_ = lean_apply_2(v_inst_53_, v_lower_56_, v_lower_58_);
v___x_61_ = lean_unbox(v___x_60_);
if (v___x_61_ == 0)
{
uint8_t v___x_62_; 
lean_dec(v_upper_59_);
lean_dec(v_upper_57_);
lean_dec_ref(v_inst_53_);
v___x_62_ = lean_unbox(v___x_60_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = lean_apply_2(v_inst_53_, v_upper_57_, v_upper_59_);
v___x_64_ = lean_unbox(v___x_63_);
return v___x_64_;
}
}
}
LEAN_EXPORT void l_Std_instDecidableEqRco_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_53_ = stack[0].m_obj;
lean_object* v_x_54_ = stack[1].m_obj;
lean_object* v_x_55_ = stack[2].m_obj;
uint8_t v_res_65_;
v_res_65_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_53_, v_x_54_, v_x_55_);
stack->m_num = v_res_65_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco_decEq___redArg___boxed(lean_object* v_inst_66_, lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_66_, v_x_67_, v_x_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
uint8_t l_Std_instDecidableEqRco_decEq(lean_object* v_00_u03b1_71_, lean_object* v_inst_72_, lean_object* v_x_73_, lean_object* v_x_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_72_, v_x_73_, v_x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRco_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_72_ = stack[1].m_obj;
lean_object* v_x_73_ = stack[2].m_obj;
lean_object* v_x_74_ = stack[3].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_Std_instDecidableEqRco_decEq(lean_box(0), v_inst_72_, v_x_73_, v_x_74_);
stack->m_num = v_res_76_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco_decEq___boxed(lean_object* v_00_u03b1_77_, lean_object* v_inst_78_, lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_instDecidableEqRco_decEq(v_00_u03b1_77_, v_inst_78_, v_x_79_, v_x_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
uint8_t l_Std_instDecidableEqRco___redArg(lean_object* v_inst_83_, lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v___x_86_; 
v___x_86_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_83_, v_x_84_, v_x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRco___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_83_ = stack[0].m_obj;
lean_object* v_x_84_ = stack[1].m_obj;
lean_object* v_x_85_ = stack[2].m_obj;
uint8_t v_res_87_;
v_res_87_ = l_Std_instDecidableEqRco___redArg(v_inst_83_, v_x_84_, v_x_85_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco___redArg___boxed(lean_object* v_inst_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Std_instDecidableEqRco___redArg(v_inst_88_, v_x_89_, v_x_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
uint8_t l_Std_instDecidableEqRco(lean_object* v_00_u03b1_93_, lean_object* v_inst_94_, lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = l_Std_instDecidableEqRco_decEq___redArg(v_inst_94_, v_x_95_, v_x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRco_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_94_ = stack[1].m_obj;
lean_object* v_x_95_ = stack[2].m_obj;
lean_object* v_x_96_ = stack[3].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_Std_instDecidableEqRco(lean_box(0), v_inst_94_, v_x_95_, v_x_96_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRco___boxed(lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_instDecidableEqRco(v_00_u03b1_99_, v_inst_100_, v_x_101_, v_x_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
uint8_t l_Std_instDecidableEqRci_decEq___redArg(lean_object* v_inst_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = lean_apply_2(v_inst_105_, v_x_106_, v_x_107_);
v___x_109_ = lean_unbox(v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRci_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_105_ = stack[0].m_obj;
lean_object* v_x_106_ = stack[1].m_obj;
lean_object* v_x_107_ = stack[2].m_obj;
uint8_t v_res_110_;
v_res_110_ = l_Std_instDecidableEqRci_decEq___redArg(v_inst_105_, v_x_106_, v_x_107_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci_decEq___redArg___boxed(lean_object* v_inst_111_, lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_instDecidableEqRci_decEq___redArg(v_inst_111_, v_x_112_, v_x_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
uint8_t l_Std_instDecidableEqRci_decEq(lean_object* v_00_u03b1_116_, lean_object* v_inst_117_, lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_apply_2(v_inst_117_, v_x_118_, v_x_119_);
v___x_121_ = lean_unbox(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRci_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_117_ = stack[1].m_obj;
lean_object* v_x_118_ = stack[2].m_obj;
lean_object* v_x_119_ = stack[3].m_obj;
uint8_t v_res_122_;
v_res_122_ = l_Std_instDecidableEqRci_decEq(lean_box(0), v_inst_117_, v_x_118_, v_x_119_);
stack->m_num = v_res_122_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci_decEq___boxed(lean_object* v_00_u03b1_123_, lean_object* v_inst_124_, lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_instDecidableEqRci_decEq(v_00_u03b1_123_, v_inst_124_, v_x_125_, v_x_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
uint8_t l_Std_instDecidableEqRci___redArg(lean_object* v_inst_129_, lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_apply_2(v_inst_129_, v_x_130_, v_x_131_);
v___x_133_ = lean_unbox(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRci___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_129_ = stack[0].m_obj;
lean_object* v_x_130_ = stack[1].m_obj;
lean_object* v_x_131_ = stack[2].m_obj;
uint8_t v_res_134_;
v_res_134_ = l_Std_instDecidableEqRci___redArg(v_inst_129_, v_x_130_, v_x_131_);
stack->m_num = v_res_134_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci___redArg___boxed(lean_object* v_inst_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_instDecidableEqRci___redArg(v_inst_135_, v_x_136_, v_x_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
uint8_t l_Std_instDecidableEqRci(lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = lean_apply_2(v_inst_141_, v_x_142_, v_x_143_);
v___x_145_ = lean_unbox(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRci_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_141_ = stack[1].m_obj;
lean_object* v_x_142_ = stack[2].m_obj;
lean_object* v_x_143_ = stack[3].m_obj;
uint8_t v_res_146_;
v_res_146_ = l_Std_instDecidableEqRci(lean_box(0), v_inst_141_, v_x_142_, v_x_143_);
stack->m_num = v_res_146_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRci___boxed(lean_object* v_00_u03b1_147_, lean_object* v_inst_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_instDecidableEqRci(v_00_u03b1_147_, v_inst_148_, v_x_149_, v_x_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
uint8_t l_Std_instDecidableEqRoc_decEq___redArg(lean_object* v_inst_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_lower_156_; lean_object* v_upper_157_; lean_object* v_lower_158_; lean_object* v_upper_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_lower_156_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_lower_156_);
v_upper_157_ = lean_ctor_get(v_x_154_, 1);
lean_inc(v_upper_157_);
lean_dec_ref(v_x_154_);
v_lower_158_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_lower_158_);
v_upper_159_ = lean_ctor_get(v_x_155_, 1);
lean_inc(v_upper_159_);
lean_dec_ref(v_x_155_);
lean_inc_ref(v_inst_153_);
v___x_160_ = lean_apply_2(v_inst_153_, v_lower_156_, v_lower_158_);
v___x_161_ = lean_unbox(v___x_160_);
if (v___x_161_ == 0)
{
uint8_t v___x_162_; 
lean_dec(v_upper_159_);
lean_dec(v_upper_157_);
lean_dec_ref(v_inst_153_);
v___x_162_ = lean_unbox(v___x_160_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_apply_2(v_inst_153_, v_upper_157_, v_upper_159_);
v___x_164_ = lean_unbox(v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoc_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_153_ = stack[0].m_obj;
lean_object* v_x_154_ = stack[1].m_obj;
lean_object* v_x_155_ = stack[2].m_obj;
uint8_t v_res_165_;
v_res_165_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_153_, v_x_154_, v_x_155_);
stack->m_num = v_res_165_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc_decEq___redArg___boxed(lean_object* v_inst_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_166_, v_x_167_, v_x_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
uint8_t l_Std_instDecidableEqRoc_decEq(lean_object* v_00_u03b1_171_, lean_object* v_inst_172_, lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_172_, v_x_173_, v_x_174_);
return v___x_175_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoc_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_172_ = stack[1].m_obj;
lean_object* v_x_173_ = stack[2].m_obj;
lean_object* v_x_174_ = stack[3].m_obj;
uint8_t v_res_176_;
v_res_176_ = l_Std_instDecidableEqRoc_decEq(lean_box(0), v_inst_172_, v_x_173_, v_x_174_);
stack->m_num = v_res_176_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc_decEq___boxed(lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_instDecidableEqRoc_decEq(v_00_u03b1_177_, v_inst_178_, v_x_179_, v_x_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l_Std_instDecidableEqRoc___redArg(lean_object* v_inst_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
uint8_t v___x_186_; 
v___x_186_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_183_, v_x_184_, v_x_185_);
return v___x_186_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_183_ = stack[0].m_obj;
lean_object* v_x_184_ = stack[1].m_obj;
lean_object* v_x_185_ = stack[2].m_obj;
uint8_t v_res_187_;
v_res_187_ = l_Std_instDecidableEqRoc___redArg(v_inst_183_, v_x_184_, v_x_185_);
stack->m_num = v_res_187_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc___redArg___boxed(lean_object* v_inst_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Std_instDecidableEqRoc___redArg(v_inst_188_, v_x_189_, v_x_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
uint8_t l_Std_instDecidableEqRoc(lean_object* v_00_u03b1_193_, lean_object* v_inst_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
uint8_t v___x_197_; 
v___x_197_ = l_Std_instDecidableEqRoc_decEq___redArg(v_inst_194_, v_x_195_, v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoc_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_194_ = stack[1].m_obj;
lean_object* v_x_195_ = stack[2].m_obj;
lean_object* v_x_196_ = stack[3].m_obj;
uint8_t v_res_198_;
v_res_198_ = l_Std_instDecidableEqRoc(lean_box(0), v_inst_194_, v_x_195_, v_x_196_);
stack->m_num = v_res_198_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoc___boxed(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_, lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Std_instDecidableEqRoc(v_00_u03b1_199_, v_inst_200_, v_x_201_, v_x_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
uint8_t l_Std_instDecidableEqRoo_decEq___redArg(lean_object* v_inst_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v_lower_208_; lean_object* v_upper_209_; lean_object* v_lower_210_; lean_object* v_upper_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_lower_208_ = lean_ctor_get(v_x_206_, 0);
lean_inc(v_lower_208_);
v_upper_209_ = lean_ctor_get(v_x_206_, 1);
lean_inc(v_upper_209_);
lean_dec_ref(v_x_206_);
v_lower_210_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_lower_210_);
v_upper_211_ = lean_ctor_get(v_x_207_, 1);
lean_inc(v_upper_211_);
lean_dec_ref(v_x_207_);
lean_inc_ref(v_inst_205_);
v___x_212_ = lean_apply_2(v_inst_205_, v_lower_208_, v_lower_210_);
v___x_213_ = lean_unbox(v___x_212_);
if (v___x_213_ == 0)
{
uint8_t v___x_214_; 
lean_dec(v_upper_211_);
lean_dec(v_upper_209_);
lean_dec_ref(v_inst_205_);
v___x_214_ = lean_unbox(v___x_212_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_apply_2(v_inst_205_, v_upper_209_, v_upper_211_);
v___x_216_ = lean_unbox(v___x_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoo_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_205_ = stack[0].m_obj;
lean_object* v_x_206_ = stack[1].m_obj;
lean_object* v_x_207_ = stack[2].m_obj;
uint8_t v_res_217_;
v_res_217_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_205_, v_x_206_, v_x_207_);
stack->m_num = v_res_217_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo_decEq___redArg___boxed(lean_object* v_inst_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_218_, v_x_219_, v_x_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
uint8_t l_Std_instDecidableEqRoo_decEq(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
uint8_t v___x_227_; 
v___x_227_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_224_, v_x_225_, v_x_226_);
return v___x_227_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoo_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_224_ = stack[1].m_obj;
lean_object* v_x_225_ = stack[2].m_obj;
lean_object* v_x_226_ = stack[3].m_obj;
uint8_t v_res_228_;
v_res_228_ = l_Std_instDecidableEqRoo_decEq(lean_box(0), v_inst_224_, v_x_225_, v_x_226_);
stack->m_num = v_res_228_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo_decEq___boxed(lean_object* v_00_u03b1_229_, lean_object* v_inst_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l_Std_instDecidableEqRoo_decEq(v_00_u03b1_229_, v_inst_230_, v_x_231_, v_x_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
uint8_t l_Std_instDecidableEqRoo___redArg(lean_object* v_inst_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_235_, v_x_236_, v_x_237_);
return v___x_238_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoo___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_235_ = stack[0].m_obj;
lean_object* v_x_236_ = stack[1].m_obj;
lean_object* v_x_237_ = stack[2].m_obj;
uint8_t v_res_239_;
v_res_239_ = l_Std_instDecidableEqRoo___redArg(v_inst_235_, v_x_236_, v_x_237_);
stack->m_num = v_res_239_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo___redArg___boxed(lean_object* v_inst_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_instDecidableEqRoo___redArg(v_inst_240_, v_x_241_, v_x_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
uint8_t l_Std_instDecidableEqRoo(lean_object* v_00_u03b1_245_, lean_object* v_inst_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = l_Std_instDecidableEqRoo_decEq___redArg(v_inst_246_, v_x_247_, v_x_248_);
return v___x_249_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoo_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_246_ = stack[1].m_obj;
lean_object* v_x_247_ = stack[2].m_obj;
lean_object* v_x_248_ = stack[3].m_obj;
uint8_t v_res_250_;
v_res_250_ = l_Std_instDecidableEqRoo(lean_box(0), v_inst_246_, v_x_247_, v_x_248_);
stack->m_num = v_res_250_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoo___boxed(lean_object* v_00_u03b1_251_, lean_object* v_inst_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Std_instDecidableEqRoo(v_00_u03b1_251_, v_inst_252_, v_x_253_, v_x_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
uint8_t l_Std_instDecidableEqRoi_decEq___redArg(lean_object* v_inst_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_apply_2(v_inst_257_, v_x_258_, v_x_259_);
v___x_261_ = lean_unbox(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoi_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_257_ = stack[0].m_obj;
lean_object* v_x_258_ = stack[1].m_obj;
lean_object* v_x_259_ = stack[2].m_obj;
uint8_t v_res_262_;
v_res_262_ = l_Std_instDecidableEqRoi_decEq___redArg(v_inst_257_, v_x_258_, v_x_259_);
stack->m_num = v_res_262_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi_decEq___redArg___boxed(lean_object* v_inst_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Std_instDecidableEqRoi_decEq___redArg(v_inst_263_, v_x_264_, v_x_265_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
uint8_t l_Std_instDecidableEqRoi_decEq(lean_object* v_00_u03b1_268_, lean_object* v_inst_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_apply_2(v_inst_269_, v_x_270_, v_x_271_);
v___x_273_ = lean_unbox(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoi_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_269_ = stack[1].m_obj;
lean_object* v_x_270_ = stack[2].m_obj;
lean_object* v_x_271_ = stack[3].m_obj;
uint8_t v_res_274_;
v_res_274_ = l_Std_instDecidableEqRoi_decEq(lean_box(0), v_inst_269_, v_x_270_, v_x_271_);
stack->m_num = v_res_274_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi_decEq___boxed(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Std_instDecidableEqRoi_decEq(v_00_u03b1_275_, v_inst_276_, v_x_277_, v_x_278_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
uint8_t l_Std_instDecidableEqRoi___redArg(lean_object* v_inst_281_, lean_object* v_x_282_, lean_object* v_x_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_apply_2(v_inst_281_, v_x_282_, v_x_283_);
v___x_285_ = lean_unbox(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoi___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_281_ = stack[0].m_obj;
lean_object* v_x_282_ = stack[1].m_obj;
lean_object* v_x_283_ = stack[2].m_obj;
uint8_t v_res_286_;
v_res_286_ = l_Std_instDecidableEqRoi___redArg(v_inst_281_, v_x_282_, v_x_283_);
stack->m_num = v_res_286_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi___redArg___boxed(lean_object* v_inst_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_instDecidableEqRoi___redArg(v_inst_287_, v_x_288_, v_x_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
uint8_t l_Std_instDecidableEqRoi(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_apply_2(v_inst_293_, v_x_294_, v_x_295_);
v___x_297_ = lean_unbox(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRoi_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_293_ = stack[1].m_obj;
lean_object* v_x_294_ = stack[2].m_obj;
lean_object* v_x_295_ = stack[3].m_obj;
uint8_t v_res_298_;
v_res_298_ = l_Std_instDecidableEqRoi(lean_box(0), v_inst_293_, v_x_294_, v_x_295_);
stack->m_num = v_res_298_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRoi___boxed(lean_object* v_00_u03b1_299_, lean_object* v_inst_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Std_instDecidableEqRoi(v_00_u03b1_299_, v_inst_300_, v_x_301_, v_x_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
uint8_t l_Std_instDecidableEqRic_decEq___redArg(lean_object* v_inst_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_apply_2(v_inst_305_, v_x_306_, v_x_307_);
v___x_309_ = lean_unbox(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRic_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_305_ = stack[0].m_obj;
lean_object* v_x_306_ = stack[1].m_obj;
lean_object* v_x_307_ = stack[2].m_obj;
uint8_t v_res_310_;
v_res_310_ = l_Std_instDecidableEqRic_decEq___redArg(v_inst_305_, v_x_306_, v_x_307_);
stack->m_num = v_res_310_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic_decEq___redArg___boxed(lean_object* v_inst_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_res_314_; lean_object* v_r_315_; 
v_res_314_ = l_Std_instDecidableEqRic_decEq___redArg(v_inst_311_, v_x_312_, v_x_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
uint8_t l_Std_instDecidableEqRic_decEq(lean_object* v_00_u03b1_316_, lean_object* v_inst_317_, lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_apply_2(v_inst_317_, v_x_318_, v_x_319_);
v___x_321_ = lean_unbox(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRic_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_317_ = stack[1].m_obj;
lean_object* v_x_318_ = stack[2].m_obj;
lean_object* v_x_319_ = stack[3].m_obj;
uint8_t v_res_322_;
v_res_322_ = l_Std_instDecidableEqRic_decEq(lean_box(0), v_inst_317_, v_x_318_, v_x_319_);
stack->m_num = v_res_322_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic_decEq___boxed(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Std_instDecidableEqRic_decEq(v_00_u03b1_323_, v_inst_324_, v_x_325_, v_x_326_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
uint8_t l_Std_instDecidableEqRic___redArg(lean_object* v_inst_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_apply_2(v_inst_329_, v_x_330_, v_x_331_);
v___x_333_ = lean_unbox(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRic___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_329_ = stack[0].m_obj;
lean_object* v_x_330_ = stack[1].m_obj;
lean_object* v_x_331_ = stack[2].m_obj;
uint8_t v_res_334_;
v_res_334_ = l_Std_instDecidableEqRic___redArg(v_inst_329_, v_x_330_, v_x_331_);
stack->m_num = v_res_334_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic___redArg___boxed(lean_object* v_inst_335_, lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
uint8_t v_res_338_; lean_object* v_r_339_; 
v_res_338_ = l_Std_instDecidableEqRic___redArg(v_inst_335_, v_x_336_, v_x_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
uint8_t l_Std_instDecidableEqRic(lean_object* v_00_u03b1_340_, lean_object* v_inst_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_apply_2(v_inst_341_, v_x_342_, v_x_343_);
v___x_345_ = lean_unbox(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRic_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_341_ = stack[1].m_obj;
lean_object* v_x_342_ = stack[2].m_obj;
lean_object* v_x_343_ = stack[3].m_obj;
uint8_t v_res_346_;
v_res_346_ = l_Std_instDecidableEqRic(lean_box(0), v_inst_341_, v_x_342_, v_x_343_);
stack->m_num = v_res_346_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRic___boxed(lean_object* v_00_u03b1_347_, lean_object* v_inst_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_instDecidableEqRic(v_00_u03b1_347_, v_inst_348_, v_x_349_, v_x_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
uint8_t l_Std_instDecidableEqRio_decEq___redArg(lean_object* v_inst_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = lean_apply_2(v_inst_353_, v_x_354_, v_x_355_);
v___x_357_ = lean_unbox(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRio_decEq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_353_ = stack[0].m_obj;
lean_object* v_x_354_ = stack[1].m_obj;
lean_object* v_x_355_ = stack[2].m_obj;
uint8_t v_res_358_;
v_res_358_ = l_Std_instDecidableEqRio_decEq___redArg(v_inst_353_, v_x_354_, v_x_355_);
stack->m_num = v_res_358_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio_decEq___redArg___boxed(lean_object* v_inst_359_, lean_object* v_x_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_instDecidableEqRio_decEq___redArg(v_inst_359_, v_x_360_, v_x_361_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
uint8_t l_Std_instDecidableEqRio_decEq(lean_object* v_00_u03b1_364_, lean_object* v_inst_365_, lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_apply_2(v_inst_365_, v_x_366_, v_x_367_);
v___x_369_ = lean_unbox(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRio_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_365_ = stack[1].m_obj;
lean_object* v_x_366_ = stack[2].m_obj;
lean_object* v_x_367_ = stack[3].m_obj;
uint8_t v_res_370_;
v_res_370_ = l_Std_instDecidableEqRio_decEq(lean_box(0), v_inst_365_, v_x_366_, v_x_367_);
stack->m_num = v_res_370_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio_decEq___boxed(lean_object* v_00_u03b1_371_, lean_object* v_inst_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Std_instDecidableEqRio_decEq(v_00_u03b1_371_, v_inst_372_, v_x_373_, v_x_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
uint8_t l_Std_instDecidableEqRio___redArg(lean_object* v_inst_377_, lean_object* v_x_378_, lean_object* v_x_379_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_apply_2(v_inst_377_, v_x_378_, v_x_379_);
v___x_381_ = lean_unbox(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRio___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_377_ = stack[0].m_obj;
lean_object* v_x_378_ = stack[1].m_obj;
lean_object* v_x_379_ = stack[2].m_obj;
uint8_t v_res_382_;
v_res_382_ = l_Std_instDecidableEqRio___redArg(v_inst_377_, v_x_378_, v_x_379_);
stack->m_num = v_res_382_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio___redArg___boxed(lean_object* v_inst_383_, lean_object* v_x_384_, lean_object* v_x_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Std_instDecidableEqRio___redArg(v_inst_383_, v_x_384_, v_x_385_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
uint8_t l_Std_instDecidableEqRio(lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_apply_2(v_inst_389_, v_x_390_, v_x_391_);
v___x_393_ = lean_unbox(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRio_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_389_ = stack[1].m_obj;
lean_object* v_x_390_ = stack[2].m_obj;
lean_object* v_x_391_ = stack[3].m_obj;
uint8_t v_res_394_;
v_res_394_ = l_Std_instDecidableEqRio(lean_box(0), v_inst_389_, v_x_390_, v_x_391_);
stack->m_num = v_res_394_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRio___boxed(lean_object* v_00_u03b1_395_, lean_object* v_inst_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Std_instDecidableEqRio(v_00_u03b1_395_, v_inst_396_, v_x_397_, v_x_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
uint8_t l_Std_instDecidableEqRii_decEq___redArg(){
_start:
{
uint8_t v___x_402_; 
v___x_402_ = 1;
return v___x_402_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRii_decEq___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_403_;
v_res_403_ = l_Std_instDecidableEqRii_decEq___redArg();
stack->m_num = v_res_403_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___redArg___boxed(lean_object* v___dummy_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Std_instDecidableEqRii_decEq___redArg();
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
uint8_t l_Std_instDecidableEqRii_decEq(lean_object* v_00_u03b1_407_, lean_object* v_inst_408_, lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = 1;
return v___x_411_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRii_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_408_ = stack[1].m_obj;
lean_object* v_x_409_ = stack[2].m_obj;
lean_object* v_x_410_ = stack[3].m_obj;
uint8_t v_res_412_;
v_res_412_ = l_Std_instDecidableEqRii_decEq(lean_box(0), v_inst_408_, v_x_409_, v_x_410_);
stack->m_num = v_res_412_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii_decEq___boxed(lean_object* v_00_u03b1_413_, lean_object* v_inst_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Std_instDecidableEqRii_decEq(v_00_u03b1_413_, v_inst_414_, v_x_415_, v_x_416_);
lean_dec_ref(v_inst_414_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
uint8_t l_Std_instDecidableEqRii___redArg(){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = 1;
return v___x_420_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRii___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_421_;
v_res_421_ = l_Std_instDecidableEqRii___redArg();
stack->m_num = v_res_421_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii___redArg___boxed(lean_object* v___dummy_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = l_Std_instDecidableEqRii___redArg();
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
uint8_t l_Std_instDecidableEqRii(lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = 1;
return v___x_429_;
}
}
LEAN_EXPORT void l_Std_instDecidableEqRii_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_426_ = stack[1].m_obj;
lean_object* v_x_427_ = stack[2].m_obj;
lean_object* v_x_428_ = stack[3].m_obj;
uint8_t v_res_430_;
v_res_430_ = l_Std_instDecidableEqRii(lean_box(0), v_inst_426_, v_x_427_, v_x_428_);
stack->m_num = v_res_430_;
}
LEAN_EXPORT lean_object* l_Std_instDecidableEqRii___boxed(lean_object* v_00_u03b1_431_, lean_object* v_inst_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Std_instDecidableEqRii(v_00_u03b1_431_, v_inst_432_, v_x_433_, v_x_434_);
lean_dec_ref(v_inst_432_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__5));
v___x_646_ = l_String_toRawSubstring_x27(v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(lean_object* v_x_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_670_);
v___x_674_ = l_Lean_Syntax_isOfKind(v_x_670_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v_x_670_);
v___x_675_ = lean_box(1);
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v_a_672_);
return v___x_676_;
}
else
{
lean_object* v_quotContext_677_; lean_object* v_currMacroScope_678_; lean_object* v_ref_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_quotContext_677_ = lean_ctor_get(v_a_671_, 1);
v_currMacroScope_678_ = lean_ctor_get(v_a_671_, 2);
v_ref_679_ = lean_ctor_get(v_a_671_, 5);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = l_Lean_Syntax_getArg(v_x_670_, v___x_680_);
v___x_682_ = lean_unsigned_to_nat(2u);
v___x_683_ = l_Lean_Syntax_getArg(v_x_670_, v___x_682_);
lean_dec(v_x_670_);
v___x_684_ = 0;
v___x_685_ = l_Lean_SourceInfo_fromRef(v_ref_679_, v___x_684_);
v___x_686_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_687_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__6);
v___x_688_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__9));
lean_inc(v_currMacroScope_678_);
lean_inc(v_quotContext_677_);
v___x_689_ = l_Lean_addMacroScope(v_quotContext_677_, v___x_688_, v_currMacroScope_678_);
v___x_690_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__14));
lean_inc_n(v___x_685_, 2);
v___x_691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_691_, 0, v___x_685_);
lean_ctor_set(v___x_691_, 1, v___x_687_);
lean_ctor_set(v___x_691_, 2, v___x_689_);
lean_ctor_set(v___x_691_, 3, v___x_690_);
v___x_692_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_693_ = l_Lean_Syntax_node2(v___x_685_, v___x_692_, v___x_681_, v___x_683_);
v___x_694_ = l_Lean_Syntax_node2(v___x_685_, v___x_686_, v___x_691_, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_672_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1(v_x_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_a_697_);
return v_res_699_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__0));
v___x_702_ = l_String_toRawSubstring_x27(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(lean_object* v_x_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_725_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_722_);
v___x_726_ = l_Lean_Syntax_isOfKind(v_x_722_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec(v_x_722_);
v___x_727_ = lean_box(1);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v_a_724_);
return v___x_728_;
}
else
{
lean_object* v_quotContext_729_; lean_object* v_currMacroScope_730_; lean_object* v_ref_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_quotContext_729_ = lean_ctor_get(v_a_723_, 1);
v_currMacroScope_730_ = lean_ctor_get(v_a_723_, 2);
v_ref_731_ = lean_ctor_get(v_a_723_, 5);
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = l_Lean_Syntax_getArg(v_x_722_, v___x_732_);
lean_dec(v_x_722_);
v___x_734_ = 0;
v___x_735_ = l_Lean_SourceInfo_fromRef(v_ref_731_, v___x_734_);
v___x_736_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_737_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__1);
v___x_738_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__3));
lean_inc(v_currMacroScope_730_);
lean_inc(v_quotContext_729_);
v___x_739_ = l_Lean_addMacroScope(v_quotContext_729_, v___x_738_, v_currMacroScope_730_);
v___x_740_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc_n(v___x_735_, 2);
v___x_741_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_741_, 0, v___x_735_);
lean_ctor_set(v___x_741_, 1, v___x_737_);
lean_ctor_set(v___x_741_, 2, v___x_739_);
lean_ctor_set(v___x_741_, 3, v___x_740_);
v___x_742_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_743_ = l_Lean_Syntax_node1(v___x_735_, v___x_742_, v___x_733_);
v___x_744_ = l_Lean_Syntax_node2(v___x_735_, v___x_736_, v___x_741_, v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v_a_724_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3d____1(v_x_746_, v_a_747_, v_a_748_);
lean_dec_ref(v_a_747_);
return v_res_749_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__0));
v___x_752_ = l_String_toRawSubstring_x27(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(lean_object* v_x_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x2a___closed__2));
lean_inc(v_x_772_);
v___x_776_ = l_Lean_Syntax_isOfKind(v_x_772_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec(v_x_772_);
v___x_777_ = lean_box(1);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v_a_774_);
return v___x_778_;
}
else
{
lean_object* v_quotContext_779_; lean_object* v_currMacroScope_780_; lean_object* v_ref_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_quotContext_779_ = lean_ctor_get(v_a_773_, 1);
v_currMacroScope_780_ = lean_ctor_get(v_a_773_, 2);
v_ref_781_ = lean_ctor_get(v_a_773_, 5);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = l_Lean_Syntax_getArg(v_x_772_, v___x_782_);
lean_dec(v_x_772_);
v___x_784_ = 0;
v___x_785_ = l_Lean_SourceInfo_fromRef(v_ref_781_, v___x_784_);
v___x_786_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_787_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__1);
v___x_788_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_780_);
lean_inc(v_quotContext_779_);
v___x_789_ = l_Lean_addMacroScope(v_quotContext_779_, v___x_788_, v_currMacroScope_780_);
v___x_790_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___closed__8));
lean_inc_n(v___x_785_, 2);
v___x_791_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_791_, 0, v___x_785_);
lean_ctor_set(v___x_791_, 1, v___x_787_);
lean_ctor_set(v___x_791_, 2, v___x_789_);
lean_ctor_set(v___x_791_, 3, v___x_790_);
v___x_792_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_793_ = l_Lean_Syntax_node1(v___x_785_, v___x_792_, v___x_783_);
v___x_794_ = l_Lean_Syntax_node2(v___x_785_, v___x_786_, v___x_791_, v___x_793_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_a_774_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x2a__1(v_x_796_, v_a_797_, v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_799_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__0));
v___x_802_ = l_String_toRawSubstring_x27(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(lean_object* v_x_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x2a___closed__1));
v___x_826_ = l_Lean_Syntax_isOfKind(v_x_822_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_box(1);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_a_824_);
return v___x_828_;
}
else
{
lean_object* v_quotContext_829_; lean_object* v_currMacroScope_830_; lean_object* v_ref_831_; uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_quotContext_829_ = lean_ctor_get(v_a_823_, 1);
v_currMacroScope_830_ = lean_ctor_get(v_a_823_, 2);
v_ref_831_ = lean_ctor_get(v_a_823_, 5);
v___x_832_ = 0;
v___x_833_ = l_Lean_SourceInfo_fromRef(v_ref_831_, v___x_832_);
v___x_834_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__1);
v___x_835_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_830_);
lean_inc(v_quotContext_829_);
v___x_836_ = l_Lean_addMacroScope(v_quotContext_829_, v___x_835_, v_currMacroScope_830_);
v___x_837_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___closed__8));
v___x_838_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_838_, 0, v___x_833_);
lean_ctor_set(v___x_838_, 1, v___x_834_);
lean_ctor_set(v___x_838_, 2, v___x_836_);
lean_ctor_set(v___x_838_, 3, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_a_824_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x2a__1(v_x_840_, v_a_841_, v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_843_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__0));
v___x_846_ = l_String_toRawSubstring_x27(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(lean_object* v_x_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_869_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3d___00__closed__1));
lean_inc(v_x_866_);
v___x_870_ = l_Lean_Syntax_isOfKind(v_x_866_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_x_866_);
v___x_871_ = lean_box(1);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v_a_868_);
return v___x_872_;
}
else
{
lean_object* v_quotContext_873_; lean_object* v_currMacroScope_874_; lean_object* v_ref_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_quotContext_873_ = lean_ctor_get(v_a_867_, 1);
v_currMacroScope_874_ = lean_ctor_get(v_a_867_, 2);
v_ref_875_ = lean_ctor_get(v_a_867_, 5);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_Syntax_getArg(v_x_866_, v___x_876_);
v___x_878_ = lean_unsigned_to_nat(2u);
v___x_879_ = l_Lean_Syntax_getArg(v_x_866_, v___x_878_);
lean_dec(v_x_866_);
v___x_880_ = 0;
v___x_881_ = l_Lean_SourceInfo_fromRef(v_ref_875_, v___x_880_);
v___x_882_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_883_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__1);
v___x_884_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__3));
lean_inc(v_currMacroScope_874_);
lean_inc(v_quotContext_873_);
v___x_885_ = l_Lean_addMacroScope(v_quotContext_873_, v___x_884_, v_currMacroScope_874_);
v___x_886_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___closed__8));
lean_inc_n(v___x_881_, 2);
v___x_887_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_887_, 0, v___x_881_);
lean_ctor_set(v___x_887_, 1, v___x_883_);
lean_ctor_set(v___x_887_, 2, v___x_885_);
lean_ctor_set(v___x_887_, 3, v___x_886_);
v___x_888_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_889_ = l_Lean_Syntax_node2(v___x_881_, v___x_888_, v___x_877_, v___x_879_);
v___x_890_ = l_Lean_Syntax_node2(v___x_881_, v___x_882_, v___x_887_, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_a_868_);
return v___x_891_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1___boxed(lean_object* v_x_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3d____1(v_x_892_, v_a_893_, v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_895_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__0));
v___x_898_ = l_String_toRawSubstring_x27(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(lean_object* v_x_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x2a___closed__1));
lean_inc(v_x_918_);
v___x_922_ = l_Lean_Syntax_isOfKind(v_x_918_, v___x_921_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_x_918_);
v___x_923_ = lean_box(1);
v___x_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v_a_920_);
return v___x_924_;
}
else
{
lean_object* v_quotContext_925_; lean_object* v_currMacroScope_926_; lean_object* v_ref_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_quotContext_925_ = lean_ctor_get(v_a_919_, 1);
v_currMacroScope_926_ = lean_ctor_get(v_a_919_, 2);
v_ref_927_ = lean_ctor_get(v_a_919_, 5);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l_Lean_Syntax_getArg(v_x_918_, v___x_928_);
lean_dec(v_x_918_);
v___x_930_ = 0;
v___x_931_ = l_Lean_SourceInfo_fromRef(v_ref_927_, v___x_930_);
v___x_932_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_933_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__1);
v___x_934_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__3));
lean_inc(v_currMacroScope_926_);
lean_inc(v_quotContext_925_);
v___x_935_ = l_Lean_addMacroScope(v_quotContext_925_, v___x_934_, v_currMacroScope_926_);
v___x_936_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___closed__8));
lean_inc_n(v___x_931_, 2);
v___x_937_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_937_, 0, v___x_931_);
lean_ctor_set(v___x_937_, 1, v___x_933_);
lean_ctor_set(v___x_937_, 2, v___x_935_);
lean_ctor_set(v___x_937_, 3, v___x_936_);
v___x_938_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_939_ = l_Lean_Syntax_node1(v___x_931_, v___x_938_, v___x_929_);
v___x_940_ = l_Lean_Syntax_node2(v___x_931_, v___x_932_, v___x_937_, v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v_a_920_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1___boxed(lean_object* v_x_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x2a__1(v_x_942_, v_a_943_, v_a_944_);
lean_dec_ref(v_a_943_);
return v_res_945_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__0));
v___x_948_ = l_String_toRawSubstring_x27(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(lean_object* v_x_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_968_);
v___x_972_ = l_Lean_Syntax_isOfKind(v_x_968_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_x_968_);
v___x_973_ = lean_box(1);
v___x_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v_a_970_);
return v___x_974_;
}
else
{
lean_object* v_quotContext_975_; lean_object* v_currMacroScope_976_; lean_object* v_ref_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_quotContext_975_ = lean_ctor_get(v_a_969_, 1);
v_currMacroScope_976_ = lean_ctor_get(v_a_969_, 2);
v_ref_977_ = lean_ctor_get(v_a_969_, 5);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = l_Lean_Syntax_getArg(v_x_968_, v___x_978_);
v___x_980_ = lean_unsigned_to_nat(2u);
v___x_981_ = l_Lean_Syntax_getArg(v_x_968_, v___x_980_);
lean_dec(v_x_968_);
v___x_982_ = 0;
v___x_983_ = l_Lean_SourceInfo_fromRef(v_ref_977_, v___x_982_);
v___x_984_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_985_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_986_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_976_);
lean_inc(v_quotContext_975_);
v___x_987_ = l_Lean_addMacroScope(v_quotContext_975_, v___x_986_, v_currMacroScope_976_);
v___x_988_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_983_, 2);
v___x_989_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_989_, 0, v___x_983_);
lean_ctor_set(v___x_989_, 1, v___x_985_);
lean_ctor_set(v___x_989_, 2, v___x_987_);
lean_ctor_set(v___x_989_, 3, v___x_988_);
v___x_990_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_991_ = l_Lean_Syntax_node2(v___x_983_, v___x_990_, v___x_979_, v___x_981_);
v___x_992_ = l_Lean_Syntax_node2(v___x_983_, v___x_984_, v___x_989_, v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v_a_970_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1(v_x_994_, v_a_995_, v_a_996_);
lean_dec_ref(v_a_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(lean_object* v_x_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Std_term___x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_998_);
v___x_1002_ = l_Lean_Syntax_isOfKind(v_x_998_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v_x_998_);
v___x_1003_ = lean_box(1);
v___x_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_a_1000_);
return v___x_1004_;
}
else
{
lean_object* v_quotContext_1005_; lean_object* v_currMacroScope_1006_; lean_object* v_ref_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_quotContext_1005_ = lean_ctor_get(v_a_999_, 1);
v_currMacroScope_1006_ = lean_ctor_get(v_a_999_, 2);
v_ref_1007_ = lean_ctor_get(v_a_999_, 5);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = l_Lean_Syntax_getArg(v_x_998_, v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(2u);
v___x_1011_ = l_Lean_Syntax_getArg(v_x_998_, v___x_1010_);
lean_dec(v_x_998_);
v___x_1012_ = 0;
v___x_1013_ = l_Lean_SourceInfo_fromRef(v_ref_1007_, v___x_1012_);
v___x_1014_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1015_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__1);
v___x_1016_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1006_);
lean_inc(v_quotContext_1005_);
v___x_1017_ = l_Lean_addMacroScope(v_quotContext_1005_, v___x_1016_, v_currMacroScope_1006_);
v___x_1018_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1013_, 2);
v___x_1019_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1013_);
lean_ctor_set(v___x_1019_, 1, v___x_1015_);
lean_ctor_set(v___x_1019_, 2, v___x_1017_);
lean_ctor_set(v___x_1019_, 3, v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1021_ = l_Lean_Syntax_node2(v___x_1013_, v___x_1020_, v___x_1009_, v___x_1011_);
v___x_1022_ = l_Lean_Syntax_node2(v___x_1013_, v___x_1014_, v___x_1019_, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v_a_1000_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1___boxed(lean_object* v_x_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e____1(v_x_1024_, v_a_1025_, v_a_1026_);
lean_dec_ref(v_a_1025_);
return v_res_1027_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__0));
v___x_1030_ = l_String_toRawSubstring_x27(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(lean_object* v_x_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_1050_);
v___x_1054_ = l_Lean_Syntax_isOfKind(v_x_1050_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
lean_dec(v_x_1050_);
v___x_1055_ = lean_box(1);
v___x_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_a_1052_);
return v___x_1056_;
}
else
{
lean_object* v_quotContext_1057_; lean_object* v_currMacroScope_1058_; lean_object* v_ref_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_quotContext_1057_ = lean_ctor_get(v_a_1051_, 1);
v_currMacroScope_1058_ = lean_ctor_get(v_a_1051_, 2);
v_ref_1059_ = lean_ctor_get(v_a_1051_, 5);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = l_Lean_Syntax_getArg(v_x_1050_, v___x_1060_);
lean_dec(v_x_1050_);
v___x_1062_ = 0;
v___x_1063_ = l_Lean_SourceInfo_fromRef(v_ref_1059_, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1065_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1066_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1058_);
lean_inc(v_quotContext_1057_);
v___x_1067_ = l_Lean_addMacroScope(v_quotContext_1057_, v___x_1066_, v_currMacroScope_1058_);
v___x_1068_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1063_, 2);
v___x_1069_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1063_);
lean_ctor_set(v___x_1069_, 1, v___x_1065_);
lean_ctor_set(v___x_1069_, 2, v___x_1067_);
lean_ctor_set(v___x_1069_, 3, v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1071_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1070_, v___x_1061_);
v___x_1072_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1064_, v___x_1069_, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_a_1052_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1(v_x_1074_, v_a_1075_, v_a_1076_);
lean_dec_ref(v_a_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(lean_object* v_x_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Std_term_x2a_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_1078_);
v___x_1082_ = l_Lean_Syntax_isOfKind(v_x_1078_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec(v_x_1078_);
v___x_1083_ = lean_box(1);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1080_);
return v___x_1084_;
}
else
{
lean_object* v_quotContext_1085_; lean_object* v_currMacroScope_1086_; lean_object* v_ref_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_quotContext_1085_ = lean_ctor_get(v_a_1079_, 1);
v_currMacroScope_1086_ = lean_ctor_get(v_a_1079_, 2);
v_ref_1087_ = lean_ctor_get(v_a_1079_, 5);
v___x_1088_ = lean_unsigned_to_nat(1u);
v___x_1089_ = l_Lean_Syntax_getArg(v_x_1078_, v___x_1088_);
lean_dec(v_x_1078_);
v___x_1090_ = 0;
v___x_1091_ = l_Lean_SourceInfo_fromRef(v_ref_1087_, v___x_1090_);
v___x_1092_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1093_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1094_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1086_);
lean_inc(v_quotContext_1085_);
v___x_1095_ = l_Lean_addMacroScope(v_quotContext_1085_, v___x_1094_, v_currMacroScope_1086_);
v___x_1096_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1091_, 2);
v___x_1097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1091_);
lean_ctor_set(v___x_1097_, 1, v___x_1093_);
lean_ctor_set(v___x_1097_, 2, v___x_1095_);
lean_ctor_set(v___x_1097_, 3, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1099_ = l_Lean_Syntax_node1(v___x_1091_, v___x_1098_, v___x_1089_);
v___x_1100_ = l_Lean_Syntax_node2(v___x_1091_, v___x_1092_, v___x_1097_, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_a_1080_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1___boxed(lean_object* v_x_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term_x2a_x2e_x2e_x2e____1(v_x_1102_, v_a_1103_, v_a_1104_);
lean_dec_ref(v_a_1103_);
return v_res_1105_;
}
}
static lean_object* _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__0));
v___x_1108_ = l_String_toRawSubstring_x27(v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(lean_object* v_x_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e_x3c___00__closed__1));
lean_inc(v_x_1128_);
v___x_1132_ = l_Lean_Syntax_isOfKind(v_x_1128_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec(v_x_1128_);
v___x_1133_ = lean_box(1);
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_a_1130_);
return v___x_1134_;
}
else
{
lean_object* v_quotContext_1135_; lean_object* v_currMacroScope_1136_; lean_object* v_ref_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_quotContext_1135_ = lean_ctor_get(v_a_1129_, 1);
v_currMacroScope_1136_ = lean_ctor_get(v_a_1129_, 2);
v_ref_1137_ = lean_ctor_get(v_a_1129_, 5);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = l_Lean_Syntax_getArg(v_x_1128_, v___x_1138_);
v___x_1140_ = lean_unsigned_to_nat(2u);
v___x_1141_ = l_Lean_Syntax_getArg(v_x_1128_, v___x_1140_);
lean_dec(v_x_1128_);
v___x_1142_ = 0;
v___x_1143_ = l_Lean_SourceInfo_fromRef(v_ref_1137_, v___x_1142_);
v___x_1144_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1145_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1146_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1136_);
lean_inc(v_quotContext_1135_);
v___x_1147_ = l_Lean_addMacroScope(v_quotContext_1135_, v___x_1146_, v_currMacroScope_1136_);
v___x_1148_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1143_, 2);
v___x_1149_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1143_);
lean_ctor_set(v___x_1149_, 1, v___x_1145_);
lean_ctor_set(v___x_1149_, 2, v___x_1147_);
lean_ctor_set(v___x_1149_, 3, v___x_1148_);
v___x_1150_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1151_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1150_, v___x_1139_, v___x_1141_);
v___x_1152_ = l_Lean_Syntax_node2(v___x_1143_, v___x_1144_, v___x_1149_, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v_a_1130_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___boxed(lean_object* v_x_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1(v_x_1154_, v_a_1155_, v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(lean_object* v_x_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Std_term___x3c_x2e_x2e_x2e___00__closed__1));
lean_inc(v_x_1158_);
v___x_1162_ = l_Lean_Syntax_isOfKind(v_x_1158_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_x_1158_);
v___x_1163_ = lean_box(1);
v___x_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v_a_1160_);
return v___x_1164_;
}
else
{
lean_object* v_quotContext_1165_; lean_object* v_currMacroScope_1166_; lean_object* v_ref_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_quotContext_1165_ = lean_ctor_get(v_a_1159_, 1);
v_currMacroScope_1166_ = lean_ctor_get(v_a_1159_, 2);
v_ref_1167_ = lean_ctor_get(v_a_1159_, 5);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = l_Lean_Syntax_getArg(v_x_1158_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(2u);
v___x_1171_ = l_Lean_Syntax_getArg(v_x_1158_, v___x_1170_);
lean_dec(v_x_1158_);
v___x_1172_ = 0;
v___x_1173_ = l_Lean_SourceInfo_fromRef(v_ref_1167_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__4));
v___x_1175_ = lean_obj_once(&l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1, &l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1_once, _init_l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__1);
v___x_1176_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__3));
lean_inc(v_currMacroScope_1166_);
lean_inc(v_quotContext_1165_);
v___x_1177_ = l_Lean_addMacroScope(v_quotContext_1165_, v___x_1176_, v_currMacroScope_1166_);
v___x_1178_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e_x3c____1___closed__8));
lean_inc_n(v___x_1173_, 2);
v___x_1179_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1173_);
lean_ctor_set(v___x_1179_, 1, v___x_1175_);
lean_ctor_set(v___x_1179_, 2, v___x_1177_);
lean_ctor_set(v___x_1179_, 3, v___x_1178_);
v___x_1180_ = ((lean_object*)(l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x2e_x2e_x2e_x3d____1___closed__16));
v___x_1181_ = l_Lean_Syntax_node2(v___x_1173_, v___x_1180_, v___x_1169_, v___x_1171_);
v___x_1182_ = l_Lean_Syntax_node2(v___x_1173_, v___x_1174_, v___x_1179_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v_a_1160_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1___boxed(lean_object* v_x_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std___aux__Init__Data__Range__Polymorphic__PRange______macroRules__Std__term___x3c_x2e_x2e_x2e____1(v_x_1184_, v_a_1185_, v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1187_;
}
}
lean_object* l_Std_Rcc_instMembershipOfLE___redArg(){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_box(0);
return v___x_1189_;
}
}
LEAN_EXPORT void l_Std_Rcc_instMembershipOfLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1190_;
v_res_1190_ = l_Std_Rcc_instMembershipOfLE___redArg();
stack->m_obj
 = v_res_1190_;
}
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE___redArg___boxed(lean_object* v___dummy_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Std_Rcc_instMembershipOfLE___redArg();
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Rcc_instMembershipOfLE(lean_object* v_00_u03b1_1193_, lean_object* v_inst_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_box(0);
return v___x_1195_;
}
}
uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1196_, lean_object* v_a_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v_lower_1199_; lean_object* v_upper_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_lower_1199_ = lean_ctor_get(v_r_1196_, 0);
lean_inc(v_lower_1199_);
v_upper_1200_ = lean_ctor_get(v_r_1196_, 1);
lean_inc(v_upper_1200_);
lean_dec_ref(v_r_1196_);
lean_inc_ref(v_inst_1198_);
lean_inc(v_a_1197_);
v___x_1201_ = lean_apply_2(v_inst_1198_, v_lower_1199_, v_a_1197_);
v___x_1202_ = lean_unbox(v___x_1201_);
if (v___x_1202_ == 0)
{
uint8_t v___x_1203_; 
lean_dec(v_upper_1200_);
lean_dec_ref(v_inst_1198_);
lean_dec(v_a_1197_);
v___x_1203_ = lean_unbox(v___x_1201_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_apply_2(v_inst_1198_, v_a_1197_, v_upper_1200_);
v___x_1205_ = lean_unbox(v___x_1204_);
return v___x_1205_;
}
}
}
LEAN_EXPORT void l_Std_Rcc_instDecidableMemOfDecidableLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1196_ = stack[0].m_obj;
lean_object* v_a_1197_ = stack[1].m_obj;
lean_object* v_inst_1198_ = stack[2].m_obj;
uint8_t v_res_1206_;
v_res_1206_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1196_, v_a_1197_, v_inst_1198_);
stack->m_num = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1207_, lean_object* v_a_1208_, lean_object* v_inst_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1207_, v_a_1208_, v_inst_1209_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
uint8_t l_Std_Rcc_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1212_, lean_object* v_r_1213_, lean_object* v_a_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = l_Std_Rcc_instDecidableMemOfDecidableLE___redArg(v_r_1213_, v_a_1214_, v_inst_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT void l_Std_Rcc_instDecidableMemOfDecidableLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1213_ = stack[1].m_obj;
lean_object* v_a_1214_ = stack[2].m_obj;
lean_object* v_inst_1215_ = stack[3].m_obj;
lean_object* v_inst_1216_ = stack[4].m_obj;
uint8_t v_res_1218_;
v_res_1218_ = l_Std_Rcc_instDecidableMemOfDecidableLE(lean_box(0), v_r_1213_, v_a_1214_, v_inst_1215_, v_inst_1216_);
stack->m_num = v_res_1218_;
}
LEAN_EXPORT lean_object* l_Std_Rcc_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_r_1220_, lean_object* v_a_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_){
_start:
{
uint8_t v_res_1224_; lean_object* v_r_1225_; 
v_res_1224_ = l_Std_Rcc_instDecidableMemOfDecidableLE(v_00_u03b1_1219_, v_r_1220_, v_a_1221_, v_inst_1222_, v_inst_1223_);
v_r_1225_ = lean_box(v_res_1224_);
return v_r_1225_;
}
}
lean_object* l_Std_Rco_instMembershipOfLEOfLT___redArg(){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_box(0);
return v___x_1227_;
}
}
LEAN_EXPORT void l_Std_Rco_instMembershipOfLEOfLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1228_;
v_res_1228_ = l_Std_Rco_instMembershipOfLEOfLT___redArg();
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT___redArg___boxed(lean_object* v___dummy_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Std_Rco_instMembershipOfLEOfLT___redArg();
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Rco_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_box(0);
return v___x_1234_;
}
}
uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1235_, lean_object* v_a_1236_, lean_object* v_inst_1237_, lean_object* v_inst_1238_){
_start:
{
lean_object* v_lower_1239_; lean_object* v_upper_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_lower_1239_ = lean_ctor_get(v_r_1235_, 0);
lean_inc(v_lower_1239_);
v_upper_1240_ = lean_ctor_get(v_r_1235_, 1);
lean_inc(v_upper_1240_);
lean_dec_ref(v_r_1235_);
lean_inc(v_a_1236_);
v___x_1241_ = lean_apply_2(v_inst_1237_, v_lower_1239_, v_a_1236_);
v___x_1242_ = lean_unbox(v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
lean_dec(v_upper_1240_);
lean_dec_ref(v_inst_1238_);
lean_dec(v_a_1236_);
v___x_1243_ = lean_unbox(v___x_1241_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = lean_apply_2(v_inst_1238_, v_a_1236_, v_upper_1240_);
v___x_1245_ = lean_unbox(v___x_1244_);
return v___x_1245_;
}
}
}
LEAN_EXPORT void l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1235_ = stack[0].m_obj;
lean_object* v_a_1236_ = stack[1].m_obj;
lean_object* v_inst_1237_ = stack[2].m_obj;
lean_object* v_inst_1238_ = stack[3].m_obj;
uint8_t v_res_1246_;
v_res_1246_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1235_, v_a_1236_, v_inst_1237_, v_inst_1238_);
stack->m_num = v_res_1246_;
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1247_, lean_object* v_a_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1247_, v_a_1248_, v_inst_1249_, v_inst_1250_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
uint8_t l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1253_, lean_object* v_r_1254_, lean_object* v_a_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_){
_start:
{
uint8_t v___x_1260_; 
v___x_1260_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1254_, v_a_1255_, v_inst_1257_, v_inst_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT void l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1254_ = stack[1].m_obj;
lean_object* v_a_1255_ = stack[2].m_obj;
lean_object* v_inst_1256_ = stack[3].m_obj;
lean_object* v_inst_1257_ = stack[4].m_obj;
lean_object* v_inst_1258_ = stack[5].m_obj;
lean_object* v_inst_1259_ = stack[6].m_obj;
uint8_t v_res_1261_;
v_res_1261_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(lean_box(0), v_r_1254_, v_a_1255_, v_inst_1256_, v_inst_1257_, v_inst_1258_, v_inst_1259_);
stack->m_num = v_res_1261_;
}
LEAN_EXPORT lean_object* l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1262_, lean_object* v_r_1263_, lean_object* v_a_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Std_Rco_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1262_, v_r_1263_, v_a_1264_, v_inst_1265_, v_inst_1266_, v_inst_1267_, v_inst_1268_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
lean_object* l_Std_Rci_instMembershipOfLE___redArg(){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_box(0);
return v___x_1272_;
}
}
LEAN_EXPORT void l_Std_Rci_instMembershipOfLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1273_;
v_res_1273_ = l_Std_Rci_instMembershipOfLE___redArg();
stack->m_obj
 = v_res_1273_;
}
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE___redArg___boxed(lean_object* v___dummy_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_Rci_instMembershipOfLE___redArg();
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Rci_instMembershipOfLE(lean_object* v_00_u03b1_1276_, lean_object* v_inst_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_box(0);
return v___x_1278_;
}
}
uint8_t l_Std_Rci_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1279_, lean_object* v_a_1280_, lean_object* v_inst_1281_){
_start:
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = lean_apply_2(v_inst_1281_, v_r_1279_, v_a_1280_);
v___x_1283_ = lean_unbox(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT void l_Std_Rci_instDecidableMemOfDecidableLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1279_ = stack[0].m_obj;
lean_object* v_a_1280_ = stack[1].m_obj;
lean_object* v_inst_1281_ = stack[2].m_obj;
uint8_t v_res_1284_;
v_res_1284_ = l_Std_Rci_instDecidableMemOfDecidableLE___redArg(v_r_1279_, v_a_1280_, v_inst_1281_);
stack->m_num = v_res_1284_;
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1285_, lean_object* v_a_1286_, lean_object* v_inst_1287_){
_start:
{
uint8_t v_res_1288_; lean_object* v_r_1289_; 
v_res_1288_ = l_Std_Rci_instDecidableMemOfDecidableLE___redArg(v_r_1285_, v_a_1286_, v_inst_1287_);
v_r_1289_ = lean_box(v_res_1288_);
return v_r_1289_;
}
}
uint8_t l_Std_Rci_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1290_, lean_object* v_r_1291_, lean_object* v_a_1292_, lean_object* v_inst_1293_, lean_object* v_inst_1294_){
_start:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = lean_apply_2(v_inst_1294_, v_r_1291_, v_a_1292_);
v___x_1296_ = lean_unbox(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT void l_Std_Rci_instDecidableMemOfDecidableLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1291_ = stack[1].m_obj;
lean_object* v_a_1292_ = stack[2].m_obj;
lean_object* v_inst_1293_ = stack[3].m_obj;
lean_object* v_inst_1294_ = stack[4].m_obj;
uint8_t v_res_1297_;
v_res_1297_ = l_Std_Rci_instDecidableMemOfDecidableLE(lean_box(0), v_r_1291_, v_a_1292_, v_inst_1293_, v_inst_1294_);
stack->m_num = v_res_1297_;
}
LEAN_EXPORT lean_object* l_Std_Rci_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1298_, lean_object* v_r_1299_, lean_object* v_a_1300_, lean_object* v_inst_1301_, lean_object* v_inst_1302_){
_start:
{
uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = l_Std_Rci_instDecidableMemOfDecidableLE(v_00_u03b1_1298_, v_r_1299_, v_a_1300_, v_inst_1301_, v_inst_1302_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
lean_object* l_Std_Roc_instMembershipOfLEOfLT___redArg(){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
}
LEAN_EXPORT void l_Std_Roc_instMembershipOfLEOfLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1307_;
v_res_1307_ = l_Std_Roc_instMembershipOfLEOfLT___redArg();
stack->m_obj
 = v_res_1307_;
}
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT___redArg___boxed(lean_object* v___dummy_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_Roc_instMembershipOfLEOfLT___redArg();
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_Roc_instMembershipOfLEOfLT(lean_object* v_00_u03b1_1310_, lean_object* v_inst_1311_, lean_object* v_inst_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
}
uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(lean_object* v_r_1314_, lean_object* v_a_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_){
_start:
{
lean_object* v_lower_1318_; lean_object* v_upper_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_lower_1318_ = lean_ctor_get(v_r_1314_, 0);
lean_inc(v_lower_1318_);
v_upper_1319_ = lean_ctor_get(v_r_1314_, 1);
lean_inc(v_upper_1319_);
lean_dec_ref(v_r_1314_);
lean_inc(v_a_1315_);
v___x_1320_ = lean_apply_2(v_inst_1317_, v_lower_1318_, v_a_1315_);
v___x_1321_ = lean_unbox(v___x_1320_);
if (v___x_1321_ == 0)
{
uint8_t v___x_1322_; 
lean_dec(v_upper_1319_);
lean_dec_ref(v_inst_1316_);
lean_dec(v_a_1315_);
v___x_1322_ = lean_unbox(v___x_1320_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = lean_apply_2(v_inst_1316_, v_a_1315_, v_upper_1319_);
v___x_1324_ = lean_unbox(v___x_1323_);
return v___x_1324_;
}
}
}
LEAN_EXPORT void l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1314_ = stack[0].m_obj;
lean_object* v_a_1315_ = stack[1].m_obj;
lean_object* v_inst_1316_ = stack[2].m_obj;
lean_object* v_inst_1317_ = stack[3].m_obj;
uint8_t v_res_1325_;
v_res_1325_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1314_, v_a_1315_, v_inst_1316_, v_inst_1317_);
stack->m_num = v_res_1325_;
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg___boxed(lean_object* v_r_1326_, lean_object* v_a_1327_, lean_object* v_inst_1328_, lean_object* v_inst_1329_){
_start:
{
uint8_t v_res_1330_; lean_object* v_r_1331_; 
v_res_1330_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1326_, v_a_1327_, v_inst_1328_, v_inst_1329_);
v_r_1331_ = lean_box(v_res_1330_);
return v_r_1331_;
}
}
uint8_t l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(lean_object* v_00_u03b1_1332_, lean_object* v_r_1333_, lean_object* v_a_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___redArg(v_r_1333_, v_a_1334_, v_inst_1336_, v_inst_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT void l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1333_ = stack[1].m_obj;
lean_object* v_a_1334_ = stack[2].m_obj;
lean_object* v_inst_1335_ = stack[3].m_obj;
lean_object* v_inst_1336_ = stack[4].m_obj;
lean_object* v_inst_1337_ = stack[5].m_obj;
lean_object* v_inst_1338_ = stack[6].m_obj;
uint8_t v_res_1340_;
v_res_1340_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(lean_box(0), v_r_1333_, v_a_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_);
stack->m_num = v_res_1340_;
}
LEAN_EXPORT lean_object* l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_r_1342_, lean_object* v_a_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_){
_start:
{
uint8_t v_res_1348_; lean_object* v_r_1349_; 
v_res_1348_ = l_Std_Roc_instDecidableMemOfDecidableLEOfDecidableLT(v_00_u03b1_1341_, v_r_1342_, v_a_1343_, v_inst_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_);
v_r_1349_ = lean_box(v_res_1348_);
return v_r_1349_;
}
}
lean_object* l_Std_Roo_instMembershipOfLT___redArg(){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_box(0);
return v___x_1351_;
}
}
LEAN_EXPORT void l_Std_Roo_instMembershipOfLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1352_;
v_res_1352_ = l_Std_Roo_instMembershipOfLT___redArg();
stack->m_obj
 = v_res_1352_;
}
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT___redArg___boxed(lean_object* v___dummy_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Std_Roo_instMembershipOfLT___redArg();
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Roo_instMembershipOfLT(lean_object* v_00_u03b1_1355_, lean_object* v_inst_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_box(0);
return v___x_1357_;
}
}
uint8_t l_Std_Roo_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1358_, lean_object* v_a_1359_, lean_object* v_inst_1360_){
_start:
{
lean_object* v_lower_1361_; lean_object* v_upper_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_lower_1361_ = lean_ctor_get(v_r_1358_, 0);
lean_inc(v_lower_1361_);
v_upper_1362_ = lean_ctor_get(v_r_1358_, 1);
lean_inc(v_upper_1362_);
lean_dec_ref(v_r_1358_);
lean_inc_ref(v_inst_1360_);
lean_inc(v_a_1359_);
v___x_1363_ = lean_apply_2(v_inst_1360_, v_lower_1361_, v_a_1359_);
v___x_1364_ = lean_unbox(v___x_1363_);
if (v___x_1364_ == 0)
{
uint8_t v___x_1365_; 
lean_dec(v_upper_1362_);
lean_dec_ref(v_inst_1360_);
lean_dec(v_a_1359_);
v___x_1365_ = lean_unbox(v___x_1363_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_apply_2(v_inst_1360_, v_a_1359_, v_upper_1362_);
v___x_1367_ = lean_unbox(v___x_1366_);
return v___x_1367_;
}
}
}
LEAN_EXPORT void l_Std_Roo_instDecidableMemOfDecidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1358_ = stack[0].m_obj;
lean_object* v_a_1359_ = stack[1].m_obj;
lean_object* v_inst_1360_ = stack[2].m_obj;
uint8_t v_res_1368_;
v_res_1368_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1358_, v_a_1359_, v_inst_1360_);
stack->m_num = v_res_1368_;
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1369_, lean_object* v_a_1370_, lean_object* v_inst_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1369_, v_a_1370_, v_inst_1371_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
uint8_t l_Std_Roo_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1374_, lean_object* v_r_1375_, lean_object* v_a_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = l_Std_Roo_instDecidableMemOfDecidableLT___redArg(v_r_1375_, v_a_1376_, v_inst_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT void l_Std_Roo_instDecidableMemOfDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1375_ = stack[1].m_obj;
lean_object* v_a_1376_ = stack[2].m_obj;
lean_object* v_inst_1377_ = stack[3].m_obj;
lean_object* v_inst_1378_ = stack[4].m_obj;
uint8_t v_res_1380_;
v_res_1380_ = l_Std_Roo_instDecidableMemOfDecidableLT(lean_box(0), v_r_1375_, v_a_1376_, v_inst_1377_, v_inst_1378_);
stack->m_num = v_res_1380_;
}
LEAN_EXPORT lean_object* l_Std_Roo_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_r_1382_, lean_object* v_a_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l_Std_Roo_instDecidableMemOfDecidableLT(v_00_u03b1_1381_, v_r_1382_, v_a_1383_, v_inst_1384_, v_inst_1385_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
lean_object* l_Std_Roi_instMembershipOfLT___redArg(){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_box(0);
return v___x_1389_;
}
}
LEAN_EXPORT void l_Std_Roi_instMembershipOfLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1390_;
v_res_1390_ = l_Std_Roi_instMembershipOfLT___redArg();
stack->m_obj
 = v_res_1390_;
}
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT___redArg___boxed(lean_object* v___dummy_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_Roi_instMembershipOfLT___redArg();
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_Roi_instMembershipOfLT(lean_object* v_00_u03b1_1393_, lean_object* v_inst_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_box(0);
return v___x_1395_;
}
}
uint8_t l_Std_Roi_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1396_, lean_object* v_a_1397_, lean_object* v_inst_1398_){
_start:
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_apply_2(v_inst_1398_, v_r_1396_, v_a_1397_);
v___x_1400_ = lean_unbox(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT void l_Std_Roi_instDecidableMemOfDecidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1396_ = stack[0].m_obj;
lean_object* v_a_1397_ = stack[1].m_obj;
lean_object* v_inst_1398_ = stack[2].m_obj;
uint8_t v_res_1401_;
v_res_1401_ = l_Std_Roi_instDecidableMemOfDecidableLT___redArg(v_r_1396_, v_a_1397_, v_inst_1398_);
stack->m_num = v_res_1401_;
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1402_, lean_object* v_a_1403_, lean_object* v_inst_1404_){
_start:
{
uint8_t v_res_1405_; lean_object* v_r_1406_; 
v_res_1405_ = l_Std_Roi_instDecidableMemOfDecidableLT___redArg(v_r_1402_, v_a_1403_, v_inst_1404_);
v_r_1406_ = lean_box(v_res_1405_);
return v_r_1406_;
}
}
uint8_t l_Std_Roi_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1407_, lean_object* v_r_1408_, lean_object* v_a_1409_, lean_object* v_inst_1410_, lean_object* v_inst_1411_){
_start:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1412_ = lean_apply_2(v_inst_1411_, v_r_1408_, v_a_1409_);
v___x_1413_ = lean_unbox(v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT void l_Std_Roi_instDecidableMemOfDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1408_ = stack[1].m_obj;
lean_object* v_a_1409_ = stack[2].m_obj;
lean_object* v_inst_1410_ = stack[3].m_obj;
lean_object* v_inst_1411_ = stack[4].m_obj;
uint8_t v_res_1414_;
v_res_1414_ = l_Std_Roi_instDecidableMemOfDecidableLT(lean_box(0), v_r_1408_, v_a_1409_, v_inst_1410_, v_inst_1411_);
stack->m_num = v_res_1414_;
}
LEAN_EXPORT lean_object* l_Std_Roi_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_r_1416_, lean_object* v_a_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_){
_start:
{
uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_res_1420_ = l_Std_Roi_instDecidableMemOfDecidableLT(v_00_u03b1_1415_, v_r_1416_, v_a_1417_, v_inst_1418_, v_inst_1419_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
lean_object* l_Std_Ric_instMembershipOfLE___redArg(){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_box(0);
return v___x_1423_;
}
}
LEAN_EXPORT void l_Std_Ric_instMembershipOfLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1424_;
v_res_1424_ = l_Std_Ric_instMembershipOfLE___redArg();
stack->m_obj
 = v_res_1424_;
}
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE___redArg___boxed(lean_object* v___dummy_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Std_Ric_instMembershipOfLE___redArg();
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Ric_instMembershipOfLE(lean_object* v_00_u03b1_1427_, lean_object* v_inst_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
}
uint8_t l_Std_Ric_instDecidableMemOfDecidableLE___redArg(lean_object* v_r_1430_, lean_object* v_a_1431_, lean_object* v_inst_1432_){
_start:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = lean_apply_2(v_inst_1432_, v_a_1431_, v_r_1430_);
v___x_1434_ = lean_unbox(v___x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT void l_Std_Ric_instDecidableMemOfDecidableLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1430_ = stack[0].m_obj;
lean_object* v_a_1431_ = stack[1].m_obj;
lean_object* v_inst_1432_ = stack[2].m_obj;
uint8_t v_res_1435_;
v_res_1435_ = l_Std_Ric_instDecidableMemOfDecidableLE___redArg(v_r_1430_, v_a_1431_, v_inst_1432_);
stack->m_num = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___redArg___boxed(lean_object* v_r_1436_, lean_object* v_a_1437_, lean_object* v_inst_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l_Std_Ric_instDecidableMemOfDecidableLE___redArg(v_r_1436_, v_a_1437_, v_inst_1438_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
uint8_t l_Std_Ric_instDecidableMemOfDecidableLE(lean_object* v_00_u03b1_1441_, lean_object* v_r_1442_, lean_object* v_a_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_){
_start:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_apply_2(v_inst_1445_, v_a_1443_, v_r_1442_);
v___x_1447_ = lean_unbox(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT void l_Std_Ric_instDecidableMemOfDecidableLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1442_ = stack[1].m_obj;
lean_object* v_a_1443_ = stack[2].m_obj;
lean_object* v_inst_1444_ = stack[3].m_obj;
lean_object* v_inst_1445_ = stack[4].m_obj;
uint8_t v_res_1448_;
v_res_1448_ = l_Std_Ric_instDecidableMemOfDecidableLE(lean_box(0), v_r_1442_, v_a_1443_, v_inst_1444_, v_inst_1445_);
stack->m_num = v_res_1448_;
}
LEAN_EXPORT lean_object* l_Std_Ric_instDecidableMemOfDecidableLE___boxed(lean_object* v_00_u03b1_1449_, lean_object* v_r_1450_, lean_object* v_a_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_){
_start:
{
uint8_t v_res_1454_; lean_object* v_r_1455_; 
v_res_1454_ = l_Std_Ric_instDecidableMemOfDecidableLE(v_00_u03b1_1449_, v_r_1450_, v_a_1451_, v_inst_1452_, v_inst_1453_);
v_r_1455_ = lean_box(v_res_1454_);
return v_r_1455_;
}
}
lean_object* l_Std_Rio_instMembershipOfLT___redArg(){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_box(0);
return v___x_1457_;
}
}
LEAN_EXPORT void l_Std_Rio_instMembershipOfLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1458_;
v_res_1458_ = l_Std_Rio_instMembershipOfLT___redArg();
stack->m_obj
 = v_res_1458_;
}
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT___redArg___boxed(lean_object* v___dummy_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_Rio_instMembershipOfLT___redArg();
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Std_Rio_instMembershipOfLT(lean_object* v_00_u03b1_1461_, lean_object* v_inst_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_box(0);
return v___x_1463_;
}
}
uint8_t l_Std_Rio_instDecidableMemOfDecidableLT___redArg(lean_object* v_r_1464_, lean_object* v_a_1465_, lean_object* v_inst_1466_){
_start:
{
lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1467_ = lean_apply_2(v_inst_1466_, v_a_1465_, v_r_1464_);
v___x_1468_ = lean_unbox(v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT void l_Std_Rio_instDecidableMemOfDecidableLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1464_ = stack[0].m_obj;
lean_object* v_a_1465_ = stack[1].m_obj;
lean_object* v_inst_1466_ = stack[2].m_obj;
uint8_t v_res_1469_;
v_res_1469_ = l_Std_Rio_instDecidableMemOfDecidableLT___redArg(v_r_1464_, v_a_1465_, v_inst_1466_);
stack->m_num = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___redArg___boxed(lean_object* v_r_1470_, lean_object* v_a_1471_, lean_object* v_inst_1472_){
_start:
{
uint8_t v_res_1473_; lean_object* v_r_1474_; 
v_res_1473_ = l_Std_Rio_instDecidableMemOfDecidableLT___redArg(v_r_1470_, v_a_1471_, v_inst_1472_);
v_r_1474_ = lean_box(v_res_1473_);
return v_r_1474_;
}
}
uint8_t l_Std_Rio_instDecidableMemOfDecidableLT(lean_object* v_00_u03b1_1475_, lean_object* v_r_1476_, lean_object* v_a_1477_, lean_object* v_inst_1478_, lean_object* v_inst_1479_){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = lean_apply_2(v_inst_1479_, v_a_1477_, v_r_1476_);
v___x_1481_ = lean_unbox(v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT void l_Std_Rio_instDecidableMemOfDecidableLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1476_ = stack[1].m_obj;
lean_object* v_a_1477_ = stack[2].m_obj;
lean_object* v_inst_1478_ = stack[3].m_obj;
lean_object* v_inst_1479_ = stack[4].m_obj;
uint8_t v_res_1482_;
v_res_1482_ = l_Std_Rio_instDecidableMemOfDecidableLT(lean_box(0), v_r_1476_, v_a_1477_, v_inst_1478_, v_inst_1479_);
stack->m_num = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Std_Rio_instDecidableMemOfDecidableLT___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_r_1484_, lean_object* v_a_1485_, lean_object* v_inst_1486_, lean_object* v_inst_1487_){
_start:
{
uint8_t v_res_1488_; lean_object* v_r_1489_; 
v_res_1488_ = l_Std_Rio_instDecidableMemOfDecidableLT(v_00_u03b1_1483_, v_r_1484_, v_a_1485_, v_inst_1486_, v_inst_1487_);
v_r_1489_ = lean_box(v_res_1488_);
return v_r_1489_;
}
}
lean_object* l_Std_Rii_instMembership___redArg(){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_box(0);
return v___x_1491_;
}
}
LEAN_EXPORT void l_Std_Rii_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1492_;
v_res_1492_ = l_Std_Rii_instMembership___redArg();
stack->m_obj
 = v_res_1492_;
}
LEAN_EXPORT lean_object* l_Std_Rii_instMembership___redArg___boxed(lean_object* v___dummy_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Std_Rii_instMembership___redArg();
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_Rii_instMembership(lean_object* v_00_u03b1_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_box(0);
return v___x_1496_;
}
}
uint8_t l_Std_Rii_instDecidableMem___redArg(){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = 1;
return v___x_1498_;
}
}
LEAN_EXPORT void l_Std_Rii_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_1499_;
v_res_1499_ = l_Std_Rii_instDecidableMem___redArg();
stack->m_num = v_res_1499_;
}
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___redArg___boxed(lean_object* v___dummy_1500_){
_start:
{
uint8_t v_res_1501_; lean_object* v_r_1502_; 
v_res_1501_ = l_Std_Rii_instDecidableMem___redArg();
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
uint8_t l_Std_Rii_instDecidableMem(lean_object* v_00_u03b1_1503_, lean_object* v_r_1504_, lean_object* v_a_1505_){
_start:
{
uint8_t v___x_1506_; 
v___x_1506_ = 1;
return v___x_1506_;
}
}
LEAN_EXPORT void l_Std_Rii_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1504_ = stack[1].m_obj;
lean_object* v_a_1505_ = stack[2].m_obj;
uint8_t v_res_1507_;
v_res_1507_ = l_Std_Rii_instDecidableMem(lean_box(0), v_r_1504_, v_a_1505_);
stack->m_num = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Std_Rii_instDecidableMem___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_r_1509_, lean_object* v_a_1510_){
_start:
{
uint8_t v_res_1511_; lean_object* v_r_1512_; 
v_res_1511_ = l_Std_Rii_instDecidableMem(v_00_u03b1_1508_, v_r_1509_, v_a_1510_);
lean_dec(v_a_1510_);
v_r_1512_ = lean_box(v_res_1511_);
return v_r_1512_;
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
