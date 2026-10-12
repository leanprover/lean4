// Lean compiler output
// Module: Lean.Data.Html.Spec
// Imports: public import Init.Prelude import Init.Data.String.Modify import Init.Data.Array.BinSearch
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT uint8_t l_Lean_Html_isControl(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Html_isControl___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Html_isAsciiWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_isAsciiWhitespace___closed__0 = (const lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__0_value;
static const lean_ctor_object l_Lean_Html_isAsciiWhitespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__0_value)}};
static const lean_object* l_Lean_Html_isAsciiWhitespace___closed__1 = (const lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__1_value;
static const lean_ctor_object l_Lean_Html_isAsciiWhitespace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(12) << 1) | 1)),((lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__1_value)}};
static const lean_object* l_Lean_Html_isAsciiWhitespace___closed__2 = (const lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__2_value;
static const lean_ctor_object l_Lean_Html_isAsciiWhitespace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__2_value)}};
static const lean_object* l_Lean_Html_isAsciiWhitespace___closed__3 = (const lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__3_value;
static const lean_ctor_object l_Lean_Html_isAsciiWhitespace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__3_value)}};
static const lean_object* l_Lean_Html_isAsciiWhitespace___closed__4 = (const lean_object*)&l_Lean_Html_isAsciiWhitespace___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_Html_isAsciiWhitespace(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Html_isAsciiWhitespace___boxed(lean_object*);
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1114111) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__0 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__0_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1114110) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__0_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__1 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__1_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1048575) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__1_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__2 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__2_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1048574) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__2_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__3 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__3_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(983039) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__3_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__4 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__4_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(983038) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__4_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__5 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__5_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(917503) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__5_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__6 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__6_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(917502) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__6_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__7 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__7_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(851967) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__7_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__8 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__8_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(851966) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__8_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__9 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__9_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(786431) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__9_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__10 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__10_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(786430) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__10_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__11 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__11_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(720895) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__11_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__12 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__12_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(720894) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__12_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__13 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__13_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(655359) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__13_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__14 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__14_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(655358) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__14_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__15 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__15_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(589823) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__15_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__16 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__16_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(589822) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__16_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__17 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__17_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(524287) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__17_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__18 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__18_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(524286) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__18_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__19 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__19_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(458751) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__19_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__20 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__20_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(458750) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__20_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__21 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__21_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(393215) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__21_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__22 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__22_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(393214) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__22_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__23 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__23_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(327679) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__23_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__24 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__24_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(327678) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__24_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__25 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__25_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(262143) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__25_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__26 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__26_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(262142) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__26_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__27 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__27_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(196607) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__27_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__28 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__28_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(196606) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__28_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__29 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__29_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(131071) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__29_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__30 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__30_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(131070) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__30_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__31 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__31_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(65535) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__31_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__32 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__32_value;
static const lean_ctor_object l_Lean_Html_isNonCharacter___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(65534) << 1) | 1)),((lean_object*)&l_Lean_Html_isNonCharacter___closed__32_value)}};
static const lean_object* l_Lean_Html_isNonCharacter___closed__33 = (const lean_object*)&l_Lean_Html_isNonCharacter___closed__33_value;
LEAN_EXPORT uint8_t l_Lean_Html_isNonCharacter(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Html_isNonCharacter___boxed(lean_object*);
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "area"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "base"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "br"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__2_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "col"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__3 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__3_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "embed"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__4 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__4_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "hr"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__5 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__5_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "img"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__6 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__6_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "input"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__7 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__7_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__8 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__8_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__9 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__9_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__10 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__10_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__11 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__11_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "track"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__12 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__12_value;
static const lean_string_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "wbr"};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__13 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__13_value;
static const lean_array_object l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*14, .m_other = 0, .m_tag = 246}, .m_size = 14, .m_capacity = 14, .m_data = {((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__0_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__1_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__2_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__3_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__4_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__5_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__6_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__7_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__8_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__9_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__10_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__11_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__12_value),((lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__13_value)}};
static const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__14 = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__14_value;
LEAN_EXPORT const lean_object* l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements = (const lean_object*)&l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements___closed__14_value;
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lean_Html_isVoidElement_spec__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Html_isVoidElement___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_isVoidElement___closed__0;
static lean_once_cell_t l_Lean_Html_isVoidElement___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Html_isVoidElement___closed__1;
static lean_once_cell_t l_Lean_Html_isVoidElement___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Html_isVoidElement___closed__2;
static lean_once_cell_t l_Lean_Html_isVoidElement___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_Html_isVoidElement___closed__3;
LEAN_EXPORT uint8_t l_Lean_Html_isVoidElement(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_isVoidElement___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Html_isControl(uint32_t v_c_1_){
_start:
{
lean_object* v_n_2_; lean_object* v___x_3_; uint8_t v___x_4_; 
v_n_2_ = lean_uint32_to_nat(v_c_1_);
v___x_3_ = lean_unsigned_to_nat(31u);
v___x_4_ = lean_nat_dec_le(v_n_2_, v___x_3_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(127u);
v___x_6_ = lean_nat_dec_le(v___x_5_, v_n_2_);
if (v___x_6_ == 0)
{
lean_dec(v_n_2_);
return v___x_6_;
}
else
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(159u);
v___x_8_ = lean_nat_dec_le(v_n_2_, v___x_7_);
lean_dec(v_n_2_);
return v___x_8_;
}
}
else
{
lean_dec(v_n_2_);
return v___x_4_;
}
}
}
LEAN_EXPORT void l_Lean_Html_isControl_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
uint8_t v_res_9_;
v_res_9_ = l_Lean_Html_isControl(v_c_1_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Html_isControl___boxed(lean_object* v_c_10_){
_start:
{
uint32_t v_c_boxed_11_; uint8_t v_res_12_; lean_object* v_r_13_; 
v_c_boxed_11_ = lean_unbox_uint32(v_c_10_);
lean_dec(v_c_10_);
v_res_12_ = l_Lean_Html_isControl(v_c_boxed_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
uint8_t l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(lean_object* v_a_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
uint8_t v___x_16_; 
v___x_16_ = 0;
return v___x_16_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; uint8_t v___x_19_; 
v_head_17_ = lean_ctor_get(v_x_15_, 0);
v_tail_18_ = lean_ctor_get(v_x_15_, 1);
v___x_19_ = lean_nat_dec_eq(v_a_14_, v_head_17_);
if (v___x_19_ == 0)
{
v_x_15_ = v_tail_18_;
goto _start;
}
else
{
return v___x_19_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_14_ = stack[0].m_obj;
lean_object* v_x_15_ = stack[1].m_obj;
uint8_t v_res_21_;
v_res_21_ = l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(v_a_14_, v_x_15_);
stack->m_num = v_res_21_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0___boxed(lean_object* v_a_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(v_a_22_, v_x_23_);
lean_dec(v_x_23_);
lean_dec(v_a_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
uint8_t l_Lean_Html_isAsciiWhitespace(uint32_t v_c_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_42_ = lean_uint32_to_nat(v_c_41_);
v___x_43_ = ((lean_object*)(l_Lean_Html_isAsciiWhitespace___closed__4));
v___x_44_ = l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(v___x_42_, v___x_43_);
lean_dec(v___x_42_);
return v___x_44_;
}
}
LEAN_EXPORT void l_Lean_Html_isAsciiWhitespace_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_41_ = stack[0].m_num;
uint8_t v_res_45_;
v_res_45_ = l_Lean_Html_isAsciiWhitespace(v_c_41_);
stack->m_num = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Html_isAsciiWhitespace___boxed(lean_object* v_c_46_){
_start:
{
uint32_t v_c_boxed_47_; uint8_t v_res_48_; lean_object* v_r_49_; 
v_c_boxed_47_ = lean_unbox_uint32(v_c_46_);
lean_dec(v_c_46_);
v_res_48_ = l_Lean_Html_isAsciiWhitespace(v_c_boxed_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
uint8_t l_Lean_Html_isNonCharacter(uint32_t v_c_152_){
_start:
{
lean_object* v_n_153_; lean_object* v___x_157_; uint8_t v___x_158_; 
v_n_153_ = lean_uint32_to_nat(v_c_152_);
v___x_157_ = lean_unsigned_to_nat(64976u);
v___x_158_ = lean_nat_dec_le(v___x_157_, v_n_153_);
if (v___x_158_ == 0)
{
goto v___jp_154_;
}
else
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(65007u);
v___x_160_ = lean_nat_dec_le(v_n_153_, v___x_159_);
if (v___x_160_ == 0)
{
goto v___jp_154_;
}
else
{
lean_dec(v_n_153_);
return v___x_160_;
}
}
v___jp_154_:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Html_isNonCharacter___closed__33));
v___x_156_ = l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(v_n_153_, v___x_155_);
lean_dec(v_n_153_);
return v___x_156_;
}
}
}
LEAN_EXPORT void l_Lean_Html_isNonCharacter_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_152_ = stack[0].m_num;
uint8_t v_res_161_;
v_res_161_ = l_Lean_Html_isNonCharacter(v_c_152_);
stack->m_num = v_res_161_;
}
LEAN_EXPORT lean_object* l_Lean_Html_isNonCharacter___boxed(lean_object* v_c_162_){
_start:
{
uint32_t v_c_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_c_boxed_163_ = lean_unbox_uint32(v_c_162_);
lean_dec(v_c_162_);
v_res_164_ = l_Lean_Html_isNonCharacter(v_c_boxed_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lean_Html_isVoidElement_spec__0(lean_object* v_s_211_, lean_object* v_p_212_){
_start:
{
uint32_t v___y_214_; lean_object* v___x_219_; uint8_t v_decide_220_; 
v___x_219_ = lean_string_utf8_byte_size(v_s_211_);
v_decide_220_ = lean_nat_dec_eq(v_p_212_, v___x_219_);
if (v_decide_220_ == 0)
{
uint32_t v___x_221_; uint32_t v___x_222_; uint8_t v___x_223_; 
v___x_221_ = lean_string_utf8_get_fast(v_s_211_, v_p_212_);
v___x_222_ = 65;
v___x_223_ = lean_uint32_dec_le(v___x_222_, v___x_221_);
if (v___x_223_ == 0)
{
v___y_214_ = v___x_221_;
goto v___jp_213_;
}
else
{
uint32_t v___x_224_; uint8_t v___x_225_; 
v___x_224_ = 90;
v___x_225_ = lean_uint32_dec_le(v___x_221_, v___x_224_);
if (v___x_225_ == 0)
{
v___y_214_ = v___x_221_;
goto v___jp_213_;
}
else
{
uint32_t v___x_226_; uint32_t v___x_227_; 
v___x_226_ = 32;
v___x_227_ = lean_uint32_add(v___x_221_, v___x_226_);
v___y_214_ = v___x_227_;
goto v___jp_213_;
}
}
}
else
{
lean_dec(v_p_212_);
return v_s_211_;
}
v___jp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
lean_inc(v_p_212_);
v___x_215_ = lean_string_utf8_set(v_s_211_, v_p_212_, v___y_214_);
v___x_216_ = l_Char_utf8Size(v___y_214_);
v___x_217_ = lean_nat_add(v_p_212_, v___x_216_);
lean_dec(v___x_216_);
lean_dec(v_p_212_);
v_s_211_ = v___x_215_;
v_p_212_ = v___x_217_;
goto _start;
}
}
}
uint8_t l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(lean_object* v___y_228_, lean_object* v_as_229_, lean_object* v_k_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_m_235_; lean_object* v_a_236_; uint8_t v___x_237_; 
v___x_233_ = lean_nat_add(v_x_231_, v_x_232_);
v___x_234_ = lean_unsigned_to_nat(1u);
v_m_235_ = lean_nat_shiftr(v___x_233_, v___x_234_);
lean_dec(v___x_233_);
v_a_236_ = lean_array_fget_borrowed(v_as_229_, v_m_235_);
v___x_237_ = lean_string_dec_lt(v_a_236_, v_k_230_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; uint8_t v___x_239_; 
lean_dec(v_x_232_);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_string_dec_lt(v_k_230_, v_a_236_);
if (v___x_239_ == 0)
{
uint8_t v___x_240_; 
lean_dec(v_m_235_);
lean_dec(v_x_231_);
v___x_240_ = lean_nat_dec_le(v___x_238_, v___y_228_);
return v___x_240_;
}
else
{
uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_eq(v_m_235_, v___x_238_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_nat_sub(v_m_235_, v___x_234_);
lean_dec(v_m_235_);
v___x_243_ = lean_nat_dec_lt(v___x_242_, v_x_231_);
if (v___x_243_ == 0)
{
v_x_232_ = v___x_242_;
goto _start;
}
else
{
lean_dec(v___x_242_);
lean_dec(v_x_231_);
return v___x_241_;
}
}
else
{
lean_dec(v_m_235_);
lean_dec(v_x_231_);
return v___x_237_;
}
}
}
else
{
lean_object* v___x_245_; uint8_t v___x_246_; 
lean_dec(v_x_231_);
v___x_245_ = lean_nat_add(v_m_235_, v___x_234_);
lean_dec(v_m_235_);
v___x_246_ = lean_nat_dec_le(v___x_245_, v_x_232_);
if (v___x_246_ == 0)
{
lean_dec(v___x_245_);
lean_dec(v_x_232_);
return v___x_246_;
}
else
{
v_x_231_ = v___x_245_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_228_ = stack[0].m_obj;
lean_object* v_as_229_ = stack[1].m_obj;
lean_object* v_k_230_ = stack[2].m_obj;
lean_object* v_x_231_ = stack[3].m_obj;
lean_object* v_x_232_ = stack[4].m_obj;
uint8_t v_res_248_;
v_res_248_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(v___y_228_, v_as_229_, v_k_230_, v_x_231_, v_x_232_);
stack->m_num = v_res_248_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg___boxed(lean_object* v___y_249_, lean_object* v_as_250_, lean_object* v_k_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(v___y_249_, v_as_250_, v_k_251_, v_x_252_, v_x_253_);
lean_dec_ref(v_k_251_);
lean_dec_ref(v_as_250_);
lean_dec(v___y_249_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
static lean_object* _init_l_Lean_Html_isVoidElement___closed__0(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements));
v___x_257_ = lean_array_get_size(v___x_256_);
return v___x_257_;
}
}
static uint8_t _init_l_Lean_Html_isVoidElement___closed__1(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__0, &l_Lean_Html_isVoidElement___closed__0_once, _init_l_Lean_Html_isVoidElement___closed__0);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_nat_dec_lt(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Html_isVoidElement___closed__2(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__0, &l_Lean_Html_isVoidElement___closed__0_once, _init_l_Lean_Html_isVoidElement___closed__0);
v___x_263_ = lean_nat_sub(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static uint8_t _init_l_Lean_Html_isVoidElement___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__2, &l_Lean_Html_isVoidElement___closed__2_once, _init_l_Lean_Html_isVoidElement___closed__2);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_nat_dec_le(v___x_265_, v___x_264_);
return v___x_266_;
}
}
uint8_t l_Lean_Html_isVoidElement(lean_object* v_tagName_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements));
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_uint8_once(&l_Lean_Html_isVoidElement___closed__1, &l_Lean_Html_isVoidElement___closed__1_once, _init_l_Lean_Html_isVoidElement___closed__1);
if (v___x_270_ == 0)
{
lean_dec_ref(v_tagName_267_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__2, &l_Lean_Html_isVoidElement___closed__2_once, _init_l_Lean_Html_isVoidElement___closed__2);
v___x_272_ = lean_uint8_once(&l_Lean_Html_isVoidElement___closed__3, &l_Lean_Html_isVoidElement___closed__3_once, _init_l_Lean_Html_isVoidElement___closed__3);
if (v___x_272_ == 0)
{
lean_dec_ref(v_tagName_267_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_String_mapAux___at___00Lean_Html_isVoidElement_spec__0(v_tagName_267_, v___x_269_);
v___x_274_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(v___x_271_, v___x_268_, v___x_273_, v___x_269_, v___x_271_);
lean_dec_ref(v___x_273_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT void l_Lean_Html_isVoidElement_0interp(lean_interpreter_value* stack)
{
lean_object* v_tagName_267_ = stack[0].m_obj;
uint8_t v_res_275_;
v_res_275_ = l_Lean_Html_isVoidElement(v_tagName_267_);
stack->m_num = v_res_275_;
}
LEAN_EXPORT lean_object* l_Lean_Html_isVoidElement___boxed(lean_object* v_tagName_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Lean_Html_isVoidElement(v_tagName_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
uint8_t l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1(lean_object* v___y_279_, lean_object* v_as_280_, lean_object* v_k_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(v___y_279_, v_as_280_, v_k_281_, v_x_282_, v_x_283_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_279_ = stack[0].m_obj;
lean_object* v_as_280_ = stack[1].m_obj;
lean_object* v_k_281_ = stack[2].m_obj;
lean_object* v_x_282_ = stack[3].m_obj;
lean_object* v_x_283_ = stack[4].m_obj;
uint8_t v_res_286_;
v_res_286_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1(v___y_279_, v_as_280_, v_k_281_, v_x_282_, v_x_283_, lean_box(0));
stack->m_num = v_res_286_;
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___boxed(lean_object* v___y_287_, lean_object* v_as_288_, lean_object* v_k_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
uint8_t v_res_293_; lean_object* v_r_294_; 
v_res_293_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1(v___y_287_, v_as_288_, v_k_289_, v_x_290_, v_x_291_, v_x_292_);
lean_dec_ref(v_k_289_);
lean_dec_ref(v_as_288_);
lean_dec(v___y_287_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_BinSearch(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Html_Spec(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Html_Spec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_Array_BinSearch(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_Spec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_BinSearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Html_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Html_Spec(builtin);
}
#ifdef __cplusplus
}
#endif
