// Lean compiler output
// Module: Lean.Data.Html.Spec
// Imports: public import Init.Prelude import Init.Data.String.Modify import Init.Data.Array.BinSearch import Init.Data.String.Compare
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Html_isControl(uint32_t v_c_1_){
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
LEAN_EXPORT lean_object* l_Lean_Html_isControl___boxed(lean_object* v_c_9_){
_start:
{
uint32_t v_c_boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_c_boxed_10_ = lean_unbox_uint32(v_c_9_);
lean_dec(v_c_9_);
v_res_11_ = l_Lean_Html_isControl(v_c_boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(lean_object* v_a_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
uint8_t v___x_15_; 
v___x_15_ = 0;
return v___x_15_;
}
else
{
lean_object* v_head_16_; lean_object* v_tail_17_; uint8_t v___x_18_; 
v_head_16_ = lean_ctor_get(v_x_14_, 0);
v_tail_17_ = lean_ctor_get(v_x_14_, 1);
v___x_18_ = lean_nat_dec_eq(v_a_13_, v_head_16_);
if (v___x_18_ == 0)
{
v_x_14_ = v_tail_17_;
goto _start;
}
else
{
return v___x_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0___boxed(lean_object* v_a_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(v_a_20_, v_x_21_);
lean_dec(v_x_21_);
lean_dec(v_a_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_isAsciiWhitespace(uint32_t v_c_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_40_ = lean_uint32_to_nat(v_c_39_);
v___x_41_ = ((lean_object*)(l_Lean_Html_isAsciiWhitespace___closed__4));
v___x_42_ = l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(v___x_40_, v___x_41_);
lean_dec(v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_isAsciiWhitespace___boxed(lean_object* v_c_43_){
_start:
{
uint32_t v_c_boxed_44_; uint8_t v_res_45_; lean_object* v_r_46_; 
v_c_boxed_44_ = lean_unbox_uint32(v_c_43_);
lean_dec(v_c_43_);
v_res_45_ = l_Lean_Html_isAsciiWhitespace(v_c_boxed_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_isNonCharacter(uint32_t v_c_149_){
_start:
{
lean_object* v_n_150_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_n_150_ = lean_uint32_to_nat(v_c_149_);
v___x_154_ = lean_unsigned_to_nat(64976u);
v___x_155_ = lean_nat_dec_le(v___x_154_, v_n_150_);
if (v___x_155_ == 0)
{
goto v___jp_151_;
}
else
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(65007u);
v___x_157_ = lean_nat_dec_le(v_n_150_, v___x_156_);
if (v___x_157_ == 0)
{
goto v___jp_151_;
}
else
{
lean_dec(v_n_150_);
return v___x_157_;
}
}
v___jp_151_:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Html_isNonCharacter___closed__33));
v___x_153_ = l_List_elem___at___00Lean_Html_isAsciiWhitespace_spec__0(v_n_150_, v___x_152_);
lean_dec(v_n_150_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_isNonCharacter___boxed(lean_object* v_c_158_){
_start:
{
uint32_t v_c_boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_c_boxed_159_ = lean_unbox_uint32(v_c_158_);
lean_dec(v_c_158_);
v_res_160_ = l_Lean_Html_isNonCharacter(v_c_boxed_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00Lean_Html_isVoidElement_spec__0(lean_object* v_s_207_, lean_object* v_p_208_){
_start:
{
lean_object* v___y_210_; lean_object* v___y_211_; uint32_t v___y_215_; lean_object* v___x_227_; uint8_t v_decide_228_; 
v___x_227_ = lean_string_utf8_byte_size(v_s_207_);
v_decide_228_ = lean_nat_dec_eq(v_p_208_, v___x_227_);
if (v_decide_228_ == 0)
{
uint32_t v___x_229_; uint32_t v___x_230_; uint8_t v___x_231_; 
v___x_229_ = lean_string_utf8_get_fast(v_s_207_, v_p_208_);
v___x_230_ = 65;
v___x_231_ = lean_uint32_dec_le(v___x_230_, v___x_229_);
if (v___x_231_ == 0)
{
v___y_215_ = v___x_229_;
goto v___jp_214_;
}
else
{
uint32_t v___x_232_; uint8_t v___x_233_; 
v___x_232_ = 90;
v___x_233_ = lean_uint32_dec_le(v___x_229_, v___x_232_);
if (v___x_233_ == 0)
{
v___y_215_ = v___x_229_;
goto v___jp_214_;
}
else
{
uint32_t v___x_234_; uint32_t v___x_235_; 
v___x_234_ = 32;
v___x_235_ = lean_uint32_add(v___x_229_, v___x_234_);
v___y_215_ = v___x_235_;
goto v___jp_214_;
}
}
}
else
{
lean_dec(v_p_208_);
return v_s_207_;
}
v___jp_209_:
{
lean_object* v___x_212_; 
v___x_212_ = lean_nat_add(v_p_208_, v___y_211_);
lean_dec(v_p_208_);
v_s_207_ = v___y_210_;
v_p_208_ = v___x_212_;
goto _start;
}
v___jp_214_:
{
lean_object* v___x_216_; uint32_t v___x_217_; uint8_t v___x_218_; 
lean_inc(v_p_208_);
v___x_216_ = lean_string_utf8_set(v_s_207_, v_p_208_, v___y_215_);
v___x_217_ = 127;
v___x_218_ = lean_uint32_dec_le(v___y_215_, v___x_217_);
if (v___x_218_ == 0)
{
uint32_t v___x_219_; uint8_t v___x_220_; 
v___x_219_ = 2047;
v___x_220_ = lean_uint32_dec_le(v___y_215_, v___x_219_);
if (v___x_220_ == 0)
{
uint32_t v___x_221_; uint8_t v___x_222_; 
v___x_221_ = 65535;
v___x_222_ = lean_uint32_dec_le(v___y_215_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(4u);
v___y_210_ = v___x_216_;
v___y_211_ = v___x_223_;
goto v___jp_209_;
}
else
{
lean_object* v___x_224_; 
v___x_224_ = lean_unsigned_to_nat(3u);
v___y_210_ = v___x_216_;
v___y_211_ = v___x_224_;
goto v___jp_209_;
}
}
else
{
lean_object* v___x_225_; 
v___x_225_ = lean_unsigned_to_nat(2u);
v___y_210_ = v___x_216_;
v___y_211_ = v___x_225_;
goto v___jp_209_;
}
}
else
{
lean_object* v___x_226_; 
v___x_226_ = lean_unsigned_to_nat(1u);
v___y_210_ = v___x_216_;
v___y_211_ = v___x_226_;
goto v___jp_209_;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(lean_object* v___y_236_, lean_object* v_as_237_, lean_object* v_k_238_, lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v_m_243_; lean_object* v_a_244_; uint8_t v___x_245_; 
v___x_241_ = lean_nat_add(v_x_239_, v_x_240_);
v___x_242_ = lean_unsigned_to_nat(1u);
v_m_243_ = lean_nat_shiftr(v___x_241_, v___x_242_);
lean_dec(v___x_241_);
v_a_244_ = lean_array_fget_borrowed(v_as_237_, v_m_243_);
v___x_245_ = lean_string_dec_lt(v_a_244_, v_k_238_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
lean_dec(v_x_240_);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_string_dec_lt(v_k_238_, v_a_244_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
lean_dec(v_m_243_);
lean_dec(v_x_239_);
v___x_248_ = lean_nat_dec_le(v___x_246_, v___y_236_);
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = lean_nat_dec_eq(v_m_243_, v___x_246_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_nat_sub(v_m_243_, v___x_242_);
lean_dec(v_m_243_);
v___x_251_ = lean_nat_dec_lt(v___x_250_, v_x_239_);
if (v___x_251_ == 0)
{
v_x_240_ = v___x_250_;
goto _start;
}
else
{
lean_dec(v___x_250_);
lean_dec(v_x_239_);
return v___x_249_;
}
}
else
{
lean_dec(v_m_243_);
lean_dec(v_x_239_);
return v___x_245_;
}
}
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; 
lean_dec(v_x_239_);
v___x_253_ = lean_nat_add(v_m_243_, v___x_242_);
lean_dec(v_m_243_);
v___x_254_ = lean_nat_dec_le(v___x_253_, v_x_240_);
if (v___x_254_ == 0)
{
lean_dec(v___x_253_);
lean_dec(v_x_240_);
return v___x_254_;
}
else
{
v_x_239_ = v___x_253_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg___boxed(lean_object* v___y_256_, lean_object* v_as_257_, lean_object* v_k_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(v___y_256_, v_as_257_, v_k_258_, v_x_259_, v_x_260_);
lean_dec_ref(v_k_258_);
lean_dec_ref(v_as_257_);
lean_dec(v___y_256_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
static lean_object* _init_l_Lean_Html_isVoidElement___closed__0(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements));
v___x_264_ = lean_array_get_size(v___x_263_);
return v___x_264_;
}
}
static uint8_t _init_l_Lean_Html_isVoidElement___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__0, &l_Lean_Html_isVoidElement___closed__0_once, _init_l_Lean_Html_isVoidElement___closed__0);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_nat_dec_lt(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_Html_isVoidElement___closed__2(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__0, &l_Lean_Html_isVoidElement___closed__0_once, _init_l_Lean_Html_isVoidElement___closed__0);
v___x_270_ = lean_nat_sub(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static uint8_t _init_l_Lean_Html_isVoidElement___closed__3(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__2, &l_Lean_Html_isVoidElement___closed__2_once, _init_l_Lean_Html_isVoidElement___closed__2);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_nat_dec_le(v___x_272_, v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT uint8_t l_Lean_Html_isVoidElement(lean_object* v_tagName_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_275_ = ((lean_object*)(l___private_Lean_Data_Html_Spec_0__Lean_Html_voidElements));
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_uint8_once(&l_Lean_Html_isVoidElement___closed__1, &l_Lean_Html_isVoidElement___closed__1_once, _init_l_Lean_Html_isVoidElement___closed__1);
if (v___x_277_ == 0)
{
lean_dec_ref(v_tagName_274_);
return v___x_277_;
}
else
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_obj_once(&l_Lean_Html_isVoidElement___closed__2, &l_Lean_Html_isVoidElement___closed__2_once, _init_l_Lean_Html_isVoidElement___closed__2);
v___x_279_ = lean_uint8_once(&l_Lean_Html_isVoidElement___closed__3, &l_Lean_Html_isVoidElement___closed__3_once, _init_l_Lean_Html_isVoidElement___closed__3);
if (v___x_279_ == 0)
{
lean_dec_ref(v_tagName_274_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = l_String_mapAux___at___00Lean_Html_isVoidElement_spec__0(v_tagName_274_, v___x_276_);
v___x_281_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(v___x_278_, v___x_275_, v___x_280_, v___x_276_, v___x_278_);
lean_dec_ref(v___x_280_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Html_isVoidElement___boxed(lean_object* v_tagName_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l_Lean_Html_isVoidElement(v_tagName_282_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1(lean_object* v___y_285_, lean_object* v_as_286_, lean_object* v_k_287_, lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___redArg(v___y_285_, v_as_286_, v_k_287_, v_x_288_, v_x_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1___boxed(lean_object* v___y_292_, lean_object* v_as_293_, lean_object* v_k_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Array_binSearchAux___at___00Lean_Html_isVoidElement_spec__1(v___y_292_, v_as_293_, v_k_294_, v_x_295_, v_x_296_, v_x_297_);
lean_dec_ref(v_k_294_);
lean_dec_ref(v_as_293_);
lean_dec(v___y_292_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_BinSearch(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Compare(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Compare(builtin);
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
lean_object* initialize_Init_Data_String_Compare(uint8_t builtin);
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
res = initialize_Init_Data_String_Compare(builtin);
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
