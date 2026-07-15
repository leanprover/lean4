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
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t lean_is_reserved_name(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
uint8_t l_Lean_Environment_isConstructor(lean_object*, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_belowSuffix;
extern lean_object* l_Lean_brecOnSuffix;
extern lean_object* l_Lean_recOnSuffix;
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_functor"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "functor_unfold"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ndrecOn"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "noConfusionType"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "noConfusion"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ctorElim"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ctorElimType"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__11_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__13_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__10_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__14_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__9_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__15_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__8_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__16_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__17_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__6_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__18_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__5_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__19_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__4_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__20_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "below_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "brecOn_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__33_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__34_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__32_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__35_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__31_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__36_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37_value;
static const lean_ctor_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__30_value),((lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__37_value)}};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38_value;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "grind_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unsafe_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "match_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44;
static const lean_string_object l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proof_"};
static const lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45 = (const lean_object*)&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45_value;
static lean_once_cell_t l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__46;
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___f_5_; 
v___x_4_ = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
v___f_5_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_5_, 0, v___x_4_);
return v___f_5_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__21));
v___x_43_ = l_Lean_belowSuffix;
v___x_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23(void){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__22);
v___x_46_ = l_Lean_brecOnSuffix;
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__23);
v___x_49_ = l_Lean_recOnSuffix;
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__24);
v___x_52_ = l_Lean_casesOnSuffix;
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26));
v___x_56_ = lean_string_utf8_byte_size(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28));
v___x_59_ = lean_string_utf8_byte_size(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39));
v___x_81_ = lean_string_utf8_byte_size(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41));
v___x_84_ = lean_string_utf8_byte_size(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43));
v___x_87_ = lean_string_utf8_byte_size(v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__46(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45));
v___x_90_ = lean_string_utf8_byte_size(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object* v_decl_91_, lean_object* v_a_92_){
_start:
{
uint8_t v___x_94_; uint8_t v___x_95_; 
v___x_94_ = l_Lean_Name_hasMacroScopes(v_decl_91_);
v___x_95_ = 1;
if (v___x_94_ == 0)
{
uint8_t v___x_96_; 
v___x_96_ = l_Lean_Name_isInternal(v_decl_91_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v_env_98_; uint8_t v___x_99_; 
v___x_97_ = lean_st_ref_get(v_a_92_);
v_env_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref_n(v_env_98_, 2);
lean_dec(v___x_97_);
lean_inc(v_decl_91_);
v___x_99_ = lean_is_reserved_name(v_env_98_, v_decl_91_);
if (v___x_99_ == 0)
{
if (lean_obj_tag(v_decl_91_) == 1)
{
lean_object* v_pre_100_; lean_object* v_str_101_; uint8_t v___y_103_; lean_object* v___x_151_; lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_246_; 
v_pre_100_ = lean_ctor_get(v_decl_91_, 0);
lean_inc_n(v_pre_100_, 2);
v_str_101_ = lean_ctor_get(v_decl_91_, 1);
lean_inc_ref(v_str_101_);
lean_dec_ref_known(v_decl_91_, 2);
v___x_151_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_pre_100_, v_a_92_);
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_246_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_246_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_246_;
goto v_resetjp_153_;
}
v___jp_102_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__0));
v___x_105_ = l_Lean_Name_str___override(v_pre_100_, v___x_104_);
lean_inc(v___x_105_);
lean_inc_ref(v_env_98_);
v___x_106_ = l_Lean_Environment_find_x3f(v_env_98_, v___x_105_, v___y_103_);
if (lean_obj_tag(v___x_106_) == 1)
{
lean_object* v_val_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_148_; 
v_val_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_148_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_148_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_val_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_148_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
if (lean_obj_tag(v_val_107_) == 5)
{
lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_142_; 
lean_del_object(v___x_109_);
v_isSharedCheck_142_ = !lean_is_exclusive(v_val_107_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v_val_107_, 0);
lean_dec(v_unused_143_);
v___x_112_ = v_val_107_;
v_isShared_113_ = v_isSharedCheck_142_;
goto v_resetjp_111_;
}
else
{
lean_dec(v_val_107_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_142_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_114_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__1));
v___x_115_ = lean_string_dec_eq(v_str_101_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = l_Lean_casesOnSuffix;
v___x_117_ = lean_string_dec_eq(v_str_101_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__2));
v___x_119_ = lean_string_dec_eq(v_str_101_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Name_str___override(v___x_105_, v_str_101_);
v___x_121_ = l_Lean_Environment_isConstructor(v_env_98_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_box(v___x_99_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_122_);
v___x_124_ = v___x_112_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
else
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_126_);
v___x_128_ = v___x_112_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_132_; 
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_130_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_130_);
v___x_132_ = v___x_112_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_134_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_134_);
v___x_136_ = v___x_112_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
else
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_138_ = lean_box(v___x_95_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 0);
lean_ctor_set(v___x_112_, 0, v___x_138_);
v___x_140_ = v___x_112_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec(v_val_107_);
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_144_ = lean_box(v___x_99_);
if (v_isShared_110_ == 0)
{
lean_ctor_set_tag(v___x_109_, 0);
lean_ctor_set(v___x_109_, 0, v___x_144_);
v___x_146_ = v___x_109_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec(v___x_106_);
lean_dec(v___x_105_);
lean_dec_ref(v_str_101_);
lean_dec_ref(v_env_98_);
v___x_149_ = lean_box(v___x_99_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
v_resetjp_153_:
{
uint8_t v___y_157_; uint8_t v___y_173_; uint8_t v___y_183_; uint8_t v___x_235_; 
v___x_235_ = lean_unbox(v_a_152_);
lean_dec(v_a_152_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_236_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__45));
v___x_237_ = lean_string_utf8_byte_size(v_str_101_);
v___x_238_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__46, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__46_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__46);
v___x_239_ = lean_nat_dec_le(v___x_238_, v___x_237_);
if (v___x_239_ == 0)
{
goto v___jp_226_;
}
else
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_string_memcmp(v_str_101_, v___x_236_, v___x_240_, v___x_240_, v___x_238_);
if (v___x_241_ == 0)
{
goto v___jp_226_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_242_ = lean_box(v___x_95_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_244_ = lean_box(v___x_95_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
v___jp_156_:
{
lean_object* v___f_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___f_158_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3);
v___x_159_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__25);
lean_inc_ref(v_str_101_);
v___x_160_ = l_List_elem___redArg(v___f_158_, v_str_101_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_box(0);
lean_inc_ref(v_str_101_);
v___x_162_ = l_Lean_Name_str___override(v___x_161_, v_str_101_);
lean_inc(v_pre_100_);
lean_inc_ref(v_env_98_);
v___x_163_ = l_Lean_isSubobjectField_x3f(v_env_98_, v_pre_100_, v___x_162_);
if (lean_obj_tag(v___x_163_) == 1)
{
lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec_ref_known(v___x_163_, 1);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_164_ = lean_box(v___x_95_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_164_);
v___x_166_ = v___x_154_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_dec(v___x_163_);
lean_del_object(v___x_154_);
v___y_103_ = v___y_157_;
goto v___jp_102_;
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_170_; 
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_168_ = lean_box(v___x_95_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_168_);
v___x_170_ = v___x_154_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
v___jp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_174_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__26));
v___x_175_ = lean_string_utf8_byte_size(v_str_101_);
v___x_176_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__27);
v___x_177_ = lean_nat_dec_le(v___x_176_, v___x_175_);
if (v___x_177_ == 0)
{
v___y_157_ = v___y_173_;
goto v___jp_156_;
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_string_memcmp(v_str_101_, v___x_174_, v___x_178_, v___x_178_, v___x_176_);
if (v___x_179_ == 0)
{
v___y_157_ = v___y_173_;
goto v___jp_156_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_180_ = lean_box(v___x_95_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
v___jp_182_:
{
if (v___y_183_ == 0)
{
lean_object* v___x_184_; 
lean_inc(v_pre_100_);
lean_inc_ref(v_env_98_);
v___x_184_ = l_Lean_Environment_find_x3f(v_env_98_, v_pre_100_, v___y_183_);
if (lean_obj_tag(v___x_184_) == 1)
{
lean_object* v_val_185_; 
v_val_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_val_185_);
lean_dec_ref_known(v___x_184_, 1);
if (lean_obj_tag(v_val_185_) == 5)
{
lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_199_; 
v_isSharedCheck_199_ = !lean_is_exclusive(v_val_185_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_val_185_, 0);
lean_dec(v_unused_200_);
v___x_187_ = v_val_185_;
v_isShared_188_ = v_isSharedCheck_199_;
goto v_resetjp_186_;
}
else
{
lean_dec(v_val_185_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_199_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_189_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__28));
v___x_190_ = lean_string_utf8_byte_size(v_str_101_);
v___x_191_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__29);
v___x_192_ = lean_nat_dec_le(v___x_191_, v___x_190_);
if (v___x_192_ == 0)
{
lean_del_object(v___x_187_);
v___y_173_ = v___y_183_;
goto v___jp_172_;
}
else
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_string_memcmp(v_str_101_, v___x_189_, v___x_193_, v___x_193_, v___x_191_);
if (v___x_194_ == 0)
{
lean_del_object(v___x_187_);
v___y_173_ = v___y_183_;
goto v___jp_172_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_195_ = lean_box(v___x_95_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 0);
lean_ctor_set(v___x_187_, 0, v___x_195_);
v___x_197_ = v___x_187_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
else
{
lean_dec(v_val_185_);
lean_del_object(v___x_154_);
v___y_103_ = v___y_183_;
goto v___jp_102_;
}
}
else
{
lean_dec(v___x_184_);
lean_del_object(v___x_154_);
v___y_103_ = v___y_183_;
goto v___jp_102_;
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_201_ = lean_box(v___x_95_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
v___jp_203_:
{
uint8_t v___x_204_; 
lean_inc(v_pre_100_);
lean_inc_ref(v_env_98_);
v___x_204_ = l_Lean_Environment_isConstructor(v_env_98_, v_pre_100_);
if (v___x_204_ == 0)
{
v___y_183_ = v___x_204_;
goto v___jp_182_;
}
else
{
lean_object* v___f_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___f_205_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__3);
v___x_206_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__38));
lean_inc_ref(v_str_101_);
v___x_207_ = l_List_elem___redArg(v___f_205_, v_str_101_, v___x_206_);
v___y_183_ = v___x_207_;
goto v___jp_182_;
}
}
v___jp_208_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_209_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__39));
v___x_210_ = lean_string_utf8_byte_size(v_str_101_);
v___x_211_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__40);
v___x_212_ = lean_nat_dec_le(v___x_211_, v___x_210_);
if (v___x_212_ == 0)
{
goto v___jp_203_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_string_memcmp(v_str_101_, v___x_209_, v___x_213_, v___x_213_, v___x_211_);
if (v___x_214_ == 0)
{
goto v___jp_203_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_215_ = lean_box(v___x_95_);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
}
v___jp_217_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_218_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__41));
v___x_219_ = lean_string_utf8_byte_size(v_str_101_);
v___x_220_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__42);
v___x_221_ = lean_nat_dec_le(v___x_220_, v___x_219_);
if (v___x_221_ == 0)
{
goto v___jp_208_;
}
else
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_string_memcmp(v_str_101_, v___x_218_, v___x_222_, v___x_222_, v___x_220_);
if (v___x_223_ == 0)
{
goto v___jp_208_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_224_ = lean_box(v___x_95_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
}
v___jp_226_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_227_ = ((lean_object*)(l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__43));
v___x_228_ = lean_string_utf8_byte_size(v_str_101_);
v___x_229_ = lean_obj_once(&l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44, &l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44_once, _init_l_Lean_isAutoDeclOrPrivate__Internal___redArg___closed__44);
v___x_230_ = lean_nat_dec_le(v___x_229_, v___x_228_);
if (v___x_230_ == 0)
{
goto v___jp_217_;
}
else
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_string_memcmp(v_str_101_, v___x_227_, v___x_231_, v___x_231_, v___x_229_);
if (v___x_232_ == 0)
{
goto v___jp_217_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_del_object(v___x_154_);
lean_dec_ref(v_str_101_);
lean_dec(v_pre_100_);
lean_dec_ref(v_env_98_);
v___x_233_ = lean_box(v___x_95_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_env_98_);
lean_dec(v_decl_91_);
v___x_247_ = lean_box(v___x_99_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v_env_98_);
lean_dec(v_decl_91_);
v___x_249_ = lean_box(v___x_95_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_decl_91_);
v___x_251_ = lean_box(v___x_95_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_decl_91_);
v___x_253_ = lean_box(v___x_95_);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg___boxed(lean_object* v_decl_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_255_, v_a_256_);
lean_dec(v_a_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal(lean_object* v_decl_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_decl_259_, v_a_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAutoDeclOrPrivate__Internal___boxed(lean_object* v_decl_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_isAutoDeclOrPrivate__Internal(v_decl_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
return v_res_268_;
}
}
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
