// Lean compiler output
// Module: Lean.AutoDecl
// Imports: public import Lean.Structure public import Lean.CoreM
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
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
extern lean_object* l_Lean_belowSuffix;
extern lean_object* l_Lean_brecOnSuffix;
extern lean_object* l_Lean_recOnSuffix;
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_functor"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "functor_unfold"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ndrecOn"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionType"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ctorElim"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ctorElimType"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "below_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "brecOn_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "grind_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unsafe_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45;
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; uint8_t v___x_6_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
v___x_6_ = lean_string_dec_eq(v_a_1_, v_head_4_);
if (v___x_6_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0___boxed(lean_object* v_a_8_, lean_object* v_x_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_a_8_, v_x_9_);
lean_dec(v_x_9_);
lean_dec_ref(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20));
v___x_52_ = l_Lean_belowSuffix;
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21);
v___x_55_ = l_Lean_brecOnSuffix;
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22);
v___x_58_ = l_Lean_recOnSuffix;
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23);
v___x_61_ = l_Lean_casesOnSuffix;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25));
v___x_65_ = lean_string_utf8_byte_size(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27));
v___x_68_ = lean_string_utf8_byte_size(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38));
v___x_90_ = lean_string_utf8_byte_size(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40));
v___x_93_ = lean_string_utf8_byte_size(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42));
v___x_96_ = lean_string_utf8_byte_size(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44));
v___x_99_ = lean_string_utf8_byte_size(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object* v_decl_100_, lean_object* v_a_101_){
_start:
{
uint8_t v___x_103_; uint8_t v___x_104_; 
v___x_103_ = l_Lean_Name_hasMacroScopes(v_decl_100_);
v___x_104_ = 1;
if (v___x_103_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = l_Lean_Name_isInternal(v_decl_100_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v_env_107_; uint8_t v___x_108_; 
v___x_106_ = lean_st_ref_get(v_a_101_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref_n(v_env_107_, 2);
lean_dec(v___x_106_);
lean_inc(v_decl_100_);
v___x_108_ = lean_is_reserved_name(v_env_107_, v_decl_100_);
if (v___x_108_ == 0)
{
if (lean_obj_tag(v_decl_100_) == 1)
{
lean_object* v_pre_109_; lean_object* v_str_110_; uint8_t v___y_112_; lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_254_; 
v_pre_109_ = lean_ctor_get(v_decl_100_, 0);
lean_inc_n(v_pre_109_, 2);
v_str_110_ = lean_ctor_get(v_decl_100_, 1);
lean_inc_ref(v_str_110_);
lean_dec_ref_known(v_decl_100_, 2);
v___x_160_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_pre_109_, v_a_101_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_254_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_254_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_254_;
goto v_resetjp_162_;
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0));
v___x_114_ = l_Lean_Name_str___override(v_pre_109_, v___x_113_);
lean_inc(v___x_114_);
lean_inc_ref(v_env_107_);
v___x_115_ = l_Lean_Environment_find_x3f(v_env_107_, v___x_114_, v___y_112_);
if (lean_obj_tag(v___x_115_) == 1)
{
lean_object* v_val_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_157_; 
v_val_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_157_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_157_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_val_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_157_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
if (lean_obj_tag(v_val_116_) == 5)
{
lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_151_; 
lean_del_object(v___x_118_);
v_isSharedCheck_151_ = !lean_is_exclusive(v_val_116_);
if (v_isSharedCheck_151_ == 0)
{
lean_object* v_unused_152_; 
v_unused_152_ = lean_ctor_get(v_val_116_, 0);
lean_dec(v_unused_152_);
v___x_121_ = v_val_116_;
v_isShared_122_ = v_isSharedCheck_151_;
goto v_resetjp_120_;
}
else
{
lean_dec(v_val_116_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_151_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1));
v___x_124_ = lean_string_dec_eq(v_str_110_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = l_Lean_casesOnSuffix;
v___x_126_ = lean_string_dec_eq(v_str_110_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2));
v___x_128_ = lean_string_dec_eq(v_str_110_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = l_Lean_Name_str___override(v___x_114_, v_str_110_);
v___x_130_ = l_Lean_Environment_isConstructor(v_env_107_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_box(v___x_108_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 0);
lean_ctor_set(v___x_121_, 0, v___x_131_);
v___x_133_ = v___x_121_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
else
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_box(v___x_104_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 0);
lean_ctor_set(v___x_121_, 0, v___x_135_);
v___x_137_ = v___x_121_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_object* v___x_139_; lean_object* v___x_141_; 
lean_dec(v___x_114_);
lean_dec_ref(v_str_110_);
lean_dec_ref(v_env_107_);
v___x_139_ = lean_box(v___x_104_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 0);
lean_ctor_set(v___x_121_, 0, v___x_139_);
v___x_141_ = v___x_121_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec(v___x_114_);
lean_dec_ref(v_str_110_);
lean_dec_ref(v_env_107_);
v___x_143_ = lean_box(v___x_104_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 0);
lean_ctor_set(v___x_121_, 0, v___x_143_);
v___x_145_ = v___x_121_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_dec(v___x_114_);
lean_dec_ref(v_str_110_);
lean_dec_ref(v_env_107_);
v___x_147_ = lean_box(v___x_104_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 0);
lean_ctor_set(v___x_121_, 0, v___x_147_);
v___x_149_ = v___x_121_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_155_; 
lean_dec(v_val_116_);
lean_dec(v___x_114_);
lean_dec_ref(v_str_110_);
lean_dec_ref(v_env_107_);
v___x_153_ = lean_box(v___x_108_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 0);
lean_ctor_set(v___x_118_, 0, v___x_153_);
v___x_155_ = v___x_118_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v___x_115_);
lean_dec(v___x_114_);
lean_dec_ref(v_str_110_);
lean_dec_ref(v_env_107_);
v___x_158_ = lean_box(v___x_108_);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
v_resetjp_162_:
{
uint8_t v___y_166_; uint8_t v___y_181_; uint8_t v___y_191_; uint8_t v___y_210_; uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_a_161_);
lean_dec(v_a_161_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_244_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44));
v___x_245_ = lean_string_utf8_byte_size(v_str_110_);
v___x_246_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45);
v___x_247_ = lean_nat_dec_le(v___x_246_, v___x_245_);
if (v___x_247_ == 0)
{
goto v___jp_234_;
}
else
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_string_memcmp(v_str_110_, v___x_244_, v___x_248_, v___x_248_, v___x_246_);
if (v___x_249_ == 0)
{
goto v___jp_234_;
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_250_ = lean_box(v___x_104_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_252_ = lean_box(v___x_104_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
v___jp_165_:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24);
v___x_168_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_str_110_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
lean_inc_ref(v_str_110_);
v___x_170_ = l_Lean_Name_str___override(v___x_169_, v_str_110_);
lean_inc(v_pre_109_);
lean_inc_ref(v_env_107_);
v___x_171_ = l_Lean_isSubobjectField_x3f(v_env_107_, v_pre_109_, v___x_170_);
if (lean_obj_tag(v___x_171_) == 1)
{
lean_object* v___x_172_; lean_object* v___x_174_; 
lean_dec_ref_known(v___x_171_, 1);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_172_ = lean_box(v___x_104_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_172_);
v___x_174_ = v___x_163_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_dec(v___x_171_);
lean_del_object(v___x_163_);
v___y_112_ = v___y_166_;
goto v___jp_111_;
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_178_; 
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_176_ = lean_box(v___x_104_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_176_);
v___x_178_ = v___x_163_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
v___jp_180_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_182_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25));
v___x_183_ = lean_string_utf8_byte_size(v_str_110_);
v___x_184_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26);
v___x_185_ = lean_nat_dec_le(v___x_184_, v___x_183_);
if (v___x_185_ == 0)
{
v___y_166_ = v___y_181_;
goto v___jp_165_;
}
else
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_string_memcmp(v_str_110_, v___x_182_, v___x_186_, v___x_186_, v___x_184_);
if (v___x_187_ == 0)
{
v___y_166_ = v___y_181_;
goto v___jp_165_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_188_ = lean_box(v___x_104_);
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
return v___x_189_;
}
}
}
v___jp_190_:
{
lean_object* v___x_192_; 
lean_inc(v_pre_109_);
lean_inc_ref(v_env_107_);
v___x_192_ = l_Lean_Environment_find_x3f(v_env_107_, v_pre_109_, v___y_191_);
if (lean_obj_tag(v___x_192_) == 1)
{
lean_object* v_val_193_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_192_, 1);
if (lean_obj_tag(v_val_193_) == 5)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_207_; 
v_isSharedCheck_207_ = !lean_is_exclusive(v_val_193_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_val_193_, 0);
lean_dec(v_unused_208_);
v___x_195_ = v_val_193_;
v_isShared_196_ = v_isSharedCheck_207_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_val_193_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_207_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_197_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27));
v___x_198_ = lean_string_utf8_byte_size(v_str_110_);
v___x_199_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28);
v___x_200_ = lean_nat_dec_le(v___x_199_, v___x_198_);
if (v___x_200_ == 0)
{
lean_del_object(v___x_195_);
v___y_181_ = v___y_191_;
goto v___jp_180_;
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_string_memcmp(v_str_110_, v___x_197_, v___x_201_, v___x_201_, v___x_199_);
if (v___x_202_ == 0)
{
lean_del_object(v___x_195_);
v___y_181_ = v___y_191_;
goto v___jp_180_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_203_ = lean_box(v___x_104_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 0);
lean_ctor_set(v___x_195_, 0, v___x_203_);
v___x_205_ = v___x_195_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
else
{
lean_dec(v_val_193_);
lean_del_object(v___x_163_);
v___y_112_ = v___y_191_;
goto v___jp_111_;
}
}
else
{
lean_dec(v___x_192_);
lean_del_object(v___x_163_);
v___y_112_ = v___y_191_;
goto v___jp_111_;
}
}
v___jp_209_:
{
uint8_t v___x_211_; 
lean_inc(v_pre_109_);
lean_inc_ref(v_env_107_);
v___x_211_ = l_Lean_Environment_isConstructor(v_env_107_, v_pre_109_);
if (v___x_211_ == 0)
{
v___y_191_ = v___y_210_;
goto v___jp_190_;
}
else
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37));
v___x_213_ = l_List_elem___at___00Lean_isAutoDeclOrPrivate__Internal_spec__0(v_str_110_, v___x_212_);
if (v___x_213_ == 0)
{
v___y_191_ = v___x_213_;
goto v___jp_190_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_214_ = lean_box(v___x_104_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
}
v___jp_216_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_217_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38));
v___x_218_ = lean_string_utf8_byte_size(v_str_110_);
v___x_219_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39);
v___x_220_ = lean_nat_dec_le(v___x_219_, v___x_218_);
if (v___x_220_ == 0)
{
v___y_210_ = v___x_220_;
goto v___jp_209_;
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_string_memcmp(v_str_110_, v___x_217_, v___x_221_, v___x_221_, v___x_219_);
if (v___x_222_ == 0)
{
v___y_210_ = v___x_222_;
goto v___jp_209_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_223_ = lean_box(v___x_104_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
v___jp_225_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_226_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40));
v___x_227_ = lean_string_utf8_byte_size(v_str_110_);
v___x_228_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41);
v___x_229_ = lean_nat_dec_le(v___x_228_, v___x_227_);
if (v___x_229_ == 0)
{
goto v___jp_216_;
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_string_memcmp(v_str_110_, v___x_226_, v___x_230_, v___x_230_, v___x_228_);
if (v___x_231_ == 0)
{
goto v___jp_216_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_232_ = lean_box(v___x_104_);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
v___jp_234_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42));
v___x_236_ = lean_string_utf8_byte_size(v_str_110_);
v___x_237_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43);
v___x_238_ = lean_nat_dec_le(v___x_237_, v___x_236_);
if (v___x_238_ == 0)
{
goto v___jp_225_;
}
else
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_string_memcmp(v_str_110_, v___x_235_, v___x_239_, v___x_239_, v___x_237_);
if (v___x_240_ == 0)
{
goto v___jp_225_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
lean_del_object(v___x_163_);
lean_dec_ref(v_str_110_);
lean_dec(v_pre_109_);
lean_dec_ref(v_env_107_);
v___x_241_ = lean_box(v___x_104_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
}
}
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref(v_env_107_);
lean_dec(v_decl_100_);
v___x_255_ = lean_box(v___x_108_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v_env_107_);
lean_dec(v_decl_100_);
v___x_257_ = lean_box(v___x_104_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_decl_100_);
v___x_259_ = lean_box(v___x_104_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_dec(v_decl_100_);
v___x_261_ = lean_box(v___x_104_);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___boxed(lean_object* v_decl_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_263_, v_a_264_);
lean_dec(v_a_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal(lean_object* v_decl_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_267_, v_a_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___boxed(lean_object* v_decl_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_isAutoDeclOrPrivate__Internal(v_decl_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_276_;
}
}
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_AutoDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AutoDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_AutoDecl(builtin);
}
#ifdef __cplusplus
}
#endif
