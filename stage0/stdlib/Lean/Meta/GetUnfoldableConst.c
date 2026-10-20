// Lean compiler output
// Module: Lean.Meta.GetUnfoldableConst
// Imports: public import Lean.Meta.Basic public import Lean.Meta.Match.MatchPatternAttr
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
uint8_t l_Lean_hasMatchPatternAttribute(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_recordUnfoldAxiom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__0_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__2 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__2_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__3 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__3_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__4 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__4_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__5 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__5_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Zero"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__6 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__6_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__7 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__7_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__6_value),LEAN_SCALAR_PTR_LITERAL(192, 171, 244, 106, 217, 72, 118, 253)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__7_value),LEAN_SCALAR_PTR_LITERAL(172, 37, 33, 120, 251, 36, 203, 36)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__8 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__8_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "One"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__9 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__9_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__10 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__10_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__9_value),LEAN_SCALAR_PTR_LITERAL(19, 85, 184, 168, 121, 55, 74, 19)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__10_value),LEAN_SCALAR_PTR_LITERAL(31, 134, 200, 93, 163, 253, 252, 128)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__11 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__11_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "decEq"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__12 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value),LEAN_SCALAR_PTR_LITERAL(173, 33, 189, 14, 17, 44, 93, 202)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__13 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__13_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__14 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__14_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value),LEAN_SCALAR_PTR_LITERAL(13, 188, 70, 193, 211, 173, 121, 176)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__15 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__15_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__16 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__16_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__16_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__17 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__17_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofNatAux"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__18 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__18_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__16_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__18_value),LEAN_SCALAR_PTR_LITERAL(116, 234, 215, 212, 41, 156, 42, 184)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__19 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__19_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__20 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__20_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__20_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value),LEAN_SCALAR_PTR_LITERAL(84, 207, 54, 232, 73, 134, 242, 60)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__21 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__21_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__22 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__22_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hasDecEq"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__23 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__23_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__22_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__23_value),LEAN_SCALAR_PTR_LITERAL(159, 74, 159, 113, 169, 254, 60, 207)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__24 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__24_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__25 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__25_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__25_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 21, 77, 8, 216, 186, 116, 67)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__26 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__26_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__27 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__27_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__27_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 212, 171, 80, 86, 90, 103, 206)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__28 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__28_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__27_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 235, 10, 182, 21, 156, 243)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__29 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__29_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__30 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__30_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__30_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(23, 109, 23, 47, 202, 202, 227, 131)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__31 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__31_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__30_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value),LEAN_SCALAR_PTR_LITERAL(84, 139, 186, 14, 71, 124, 11, 146)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__32 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__32_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__33 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__33_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__33_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__34_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 73, 218, 73, 188, 181, 30, 93)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__34 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__34_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__33_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value),LEAN_SCALAR_PTR_LITERAL(224, 170, 234, 202, 62, 31, 245, 181)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__35 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__35_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__36 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__36_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__36_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 45, 252, 130, 147, 16, 202, 24)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__37 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__37_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__36_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__12_value),LEAN_SCALAR_PTR_LITERAL(152, 6, 142, 135, 217, 150, 112, 208)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__38 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__38_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__39 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__39_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__40 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__40_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__39_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__40_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__41 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__41_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mod"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__42 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__42_value;
static const lean_string_object l_Lean_Meta_canUnfoldAtMatcher___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mod"};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__43 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__43_value;
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__42_value),LEAN_SCALAR_PTR_LITERAL(141, 157, 192, 123, 66, 123, 34, 2)}};
static const lean_ctor_object l_Lean_Meta_canUnfoldAtMatcher___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__43_value),LEAN_SCALAR_PTR_LITERAL(26, 140, 125, 94, 9, 215, 242, 2)}};
static const lean_object* l_Lean_Meta_canUnfoldAtMatcher___closed__44 = (const lean_object*)&l_Lean_Meta_canUnfoldAtMatcher___closed__44_value;
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_getReducibilityStatusCore(v_env_5_, v_declName_1_);
v___x_7_ = lean_box(v___x_6_);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg___boxed(lean_object* v_declName_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(lean_object* v_declName_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_13_, v___y_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___boxed(lean_object* v_declName_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(v_declName_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(lean_object* v_declName_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_43_; 
v___x_27_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_23_, v___y_25_);
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_43_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
uint8_t v___x_32_; 
v___x_32_ = lean_unbox(v_a_28_);
lean_dec(v_a_28_);
if (v___x_32_ == 2)
{
uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_33_ = 1;
v___x_34_ = lean_box(v___x_33_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_34_);
v___x_36_ = v___x_30_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
else
{
uint8_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_38_ = 0;
v___x_39_ = lean_box(v___x_38_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_39_);
v___x_41_ = v___x_30_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0___boxed(lean_object* v_declName_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(v_declName_44_, v___y_45_, v___y_46_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault(lean_object* v_cfg_49_, lean_object* v_info_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
uint8_t v_transparency_54_; 
v_transparency_54_ = lean_ctor_get_uint8(v_cfg_49_, 9);
switch(v_transparency_54_)
{
case 4:
{
uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = 0;
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
case 0:
{
uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = 1;
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
case 1:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = l_Lean_ConstantInfo_name(v_info_50_);
v___x_62_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(v___x_61_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_78_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
uint8_t v___x_67_; 
v___x_67_ = lean_unbox(v_a_63_);
lean_dec(v_a_63_);
if (v___x_67_ == 0)
{
uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = 1;
v___x_69_ = lean_box(v___x_68_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_69_);
v___x_71_ = v___x_65_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
else
{
uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_73_ = 0;
v___x_74_ = lean_box(v___x_73_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_74_);
v___x_76_ = v___x_65_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
else
{
return v___x_62_;
}
}
default: 
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_120_; 
v___x_79_ = l_Lean_ConstantInfo_name(v_info_50_);
v___x_80_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v___x_79_, v_a_52_);
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_120_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_120_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_120_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
uint8_t v___x_85_; uint8_t v___x_86_; uint8_t v___x_87_; uint8_t v___x_88_; 
v___x_85_ = 0;
v___x_86_ = lean_unbox(v_a_81_);
v___x_87_ = l_Lean_instBEqReducibilityStatus_beq(v___x_86_, v___x_85_);
v___x_88_ = 1;
if (v___x_87_ == 0)
{
uint8_t v___x_107_; uint8_t v___x_108_; uint8_t v___x_109_; 
v___x_107_ = 4;
v___x_108_ = lean_unbox(v_a_81_);
v___x_109_ = l_Lean_instBEqReducibilityStatus_beq(v___x_108_, v___x_107_);
if (v___x_109_ == 0)
{
goto v___jp_89_;
}
else
{
uint8_t v___x_110_; uint8_t v___x_111_; 
v___x_110_ = 3;
v___x_111_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_54_, v___x_110_);
if (v___x_111_ == 0)
{
uint8_t v___x_112_; uint8_t v___x_113_; 
v___x_112_ = 5;
v___x_113_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_54_, v___x_112_);
if (v___x_113_ == 0)
{
goto v___jp_89_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_del_object(v___x_83_);
lean_dec(v_a_81_);
v___x_114_ = lean_box(v___x_88_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_del_object(v___x_83_);
lean_dec(v_a_81_);
v___x_116_ = lean_box(v___x_88_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_83_);
lean_dec(v_a_81_);
v___x_118_ = lean_box(v___x_88_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
v___jp_89_:
{
uint8_t v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; 
v___x_90_ = 3;
v___x_91_ = lean_unbox(v_a_81_);
lean_dec(v_a_81_);
v___x_92_ = l_Lean_instBEqReducibilityStatus_beq(v___x_91_, v___x_90_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_box(v___x_87_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_93_);
v___x_95_ = v___x_83_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
uint8_t v___x_97_; uint8_t v___x_98_; 
v___x_97_ = 5;
v___x_98_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_54_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_box(v___x_98_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_99_);
v___x_101_ = v___x_83_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
else
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_box(v___x_88_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_103_);
v___x_105_ = v___x_83_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault___boxed(lean_object* v_cfg_121_, lean_object* v_info_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Meta_canUnfoldDefault(v_cfg_121_, v_info_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec_ref(v_info_122_);
lean_dec_ref(v_cfg_121_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher(lean_object* v_cfg_213_, lean_object* v_info_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_canUnfoldDefault(v_cfg_213_, v_info_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_363_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_363_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_363_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_363_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; uint8_t v___x_224_; 
v___x_223_ = 1;
v___x_224_ = lean_unbox(v_a_219_);
lean_dec(v_a_219_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v_env_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_225_ = lean_st_ref_get(v_a_216_);
v_env_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_env_226_);
lean_dec(v___x_225_);
v___x_227_ = l_Lean_ConstantInfo_name(v_info_214_);
lean_inc(v___x_227_);
v___x_228_ = l_Lean_hasMatchPatternAttribute(v_env_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__2));
v___x_230_ = lean_name_eq(v___x_227_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__5));
v___x_232_ = lean_name_eq(v___x_227_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__8));
v___x_234_ = lean_name_eq(v___x_227_, v___x_233_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__11));
v___x_236_ = lean_name_eq(v___x_227_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__13));
v___x_238_ = lean_name_eq(v___x_227_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__15));
v___x_240_ = lean_name_eq(v___x_227_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__17));
v___x_242_ = lean_name_eq(v___x_227_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__19));
v___x_244_ = lean_name_eq(v___x_227_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__21));
v___x_246_ = lean_name_eq(v___x_227_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__24));
v___x_248_ = lean_name_eq(v___x_227_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__26));
v___x_250_ = lean_name_eq(v___x_227_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__28));
v___x_252_ = lean_name_eq(v___x_227_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__29));
v___x_254_ = lean_name_eq(v___x_227_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__31));
v___x_256_ = lean_name_eq(v___x_227_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__32));
v___x_258_ = lean_name_eq(v___x_227_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__34));
v___x_260_ = lean_name_eq(v___x_227_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__35));
v___x_262_ = lean_name_eq(v___x_227_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__37));
v___x_264_ = lean_name_eq(v___x_227_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__38));
v___x_266_ = lean_name_eq(v___x_227_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__41));
v___x_268_ = lean_name_eq(v___x_227_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_269_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__44));
v___x_270_ = lean_name_eq(v___x_227_, v___x_269_);
lean_dec(v___x_227_);
v___x_271_ = lean_box(v___x_270_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_271_);
v___x_273_ = v___x_221_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_277_; 
lean_dec(v___x_227_);
v___x_275_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_275_);
v___x_277_ = v___x_221_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec(v___x_227_);
v___x_279_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_279_);
v___x_281_ = v___x_221_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_285_; 
lean_dec(v___x_227_);
v___x_283_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_283_);
v___x_285_ = v___x_221_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
lean_object* v___x_287_; lean_object* v___x_289_; 
lean_dec(v___x_227_);
v___x_287_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_287_);
v___x_289_ = v___x_221_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec(v___x_227_);
v___x_291_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_291_);
v___x_293_ = v___x_221_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_object* v___x_295_; lean_object* v___x_297_; 
lean_dec(v___x_227_);
v___x_295_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_295_);
v___x_297_ = v___x_221_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v___x_299_; lean_object* v___x_301_; 
lean_dec(v___x_227_);
v___x_299_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_299_);
v___x_301_ = v___x_221_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_305_; 
lean_dec(v___x_227_);
v___x_303_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_303_);
v___x_305_ = v___x_221_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_309_; 
lean_dec(v___x_227_);
v___x_307_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_307_);
v___x_309_ = v___x_221_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v___x_227_);
v___x_311_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_311_);
v___x_313_ = v___x_221_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec(v___x_227_);
v___x_315_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_315_);
v___x_317_ = v___x_221_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_321_; 
lean_dec(v___x_227_);
v___x_319_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_319_);
v___x_321_ = v___x_221_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec(v___x_227_);
v___x_323_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_323_);
v___x_325_ = v___x_221_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec(v___x_227_);
v___x_327_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_327_);
v___x_329_ = v___x_221_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec(v___x_227_);
v___x_331_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_331_);
v___x_333_ = v___x_221_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_337_; 
lean_dec(v___x_227_);
v___x_335_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_335_);
v___x_337_ = v___x_221_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec(v___x_227_);
v___x_339_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_339_);
v___x_341_ = v___x_221_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_dec(v___x_227_);
v___x_343_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_343_);
v___x_345_ = v___x_221_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
lean_dec(v___x_227_);
v___x_347_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_347_);
v___x_349_ = v___x_221_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec(v___x_227_);
v___x_351_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_351_);
v___x_353_ = v___x_221_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_dec(v___x_227_);
v___x_355_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_355_);
v___x_357_ = v___x_221_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_box(v___x_223_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_359_);
v___x_361_ = v___x_221_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object* v_cfg_364_, lean_object* v_info_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_canUnfoldAtMatcher(v_cfg_364_, v_info_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec_ref(v_info_365_);
lean_dec_ref(v_cfg_364_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg(lean_object* v_info_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_customCanUnfoldPredicate_x3f_375_; lean_object* v___x_376_; 
v_customCanUnfoldPredicate_x3f_375_ = lean_ctor_get(v_a_371_, 6);
v___x_376_ = l_Lean_Meta_Context_config(v_a_371_);
if (lean_obj_tag(v_customCanUnfoldPredicate_x3f_375_) == 0)
{
uint8_t v_canUnfoldPredicateConfig_377_; 
v_canUnfoldPredicateConfig_377_ = lean_ctor_get_uint8(v___x_376_, 19);
if (v_canUnfoldPredicateConfig_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_canUnfoldDefault(v___x_376_, v_info_370_, v_a_372_, v_a_373_);
lean_dec_ref(v_info_370_);
lean_dec_ref(v___x_376_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_canUnfoldAtMatcher(v___x_376_, v_info_370_, v_a_372_, v_a_373_);
lean_dec_ref(v_info_370_);
lean_dec_ref(v___x_376_);
return v___x_379_;
}
}
else
{
lean_object* v_val_380_; lean_object* v___x_381_; 
v_val_380_ = lean_ctor_get(v_customCanUnfoldPredicate_x3f_375_, 0);
lean_inc(v_val_380_);
lean_inc(v_a_373_);
lean_inc_ref(v_a_372_);
v___x_381_ = lean_apply_5(v_val_380_, v___x_376_, v_info_370_, v_a_372_, v_a_373_, lean_box(0));
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg___boxed(lean_object* v_info_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_canUnfold___redArg(v_info_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec_ref(v_a_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold(lean_object* v_info_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_canUnfold___redArg(v_info_388_, v_a_389_, v_a_391_, v_a_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object* v_info_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_canUnfold(v_info_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; lean_object* v_env_409_; uint8_t v___x_410_; lean_object* v_env_411_; lean_object* v___x_412_; lean_object* v_toCold_413_; lean_object* v_mctx_414_; lean_object* v_lctx_415_; lean_object* v_options_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_408_ = lean_st_ref_get(v___y_406_);
v_env_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc_ref(v_env_409_);
lean_dec(v___x_408_);
v___x_410_ = 0;
v_env_411_ = l_Lean_Environment_setRecordingDeps(v_env_409_, v___x_410_);
v___x_412_ = lean_st_ref_get(v___y_404_);
v_toCold_413_ = lean_ctor_get(v___y_405_, 0);
v_mctx_414_ = lean_ctor_get(v___x_412_, 0);
lean_inc_ref(v_mctx_414_);
lean_dec(v___x_412_);
v_lctx_415_ = lean_ctor_get(v___y_403_, 2);
v_options_416_ = lean_ctor_get(v_toCold_413_, 2);
lean_inc_ref(v_options_416_);
lean_inc_ref(v_lctx_415_);
v___x_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_417_, 0, v_env_411_);
lean_ctor_set(v___x_417_, 1, v_mctx_414_);
lean_ctor_set(v___x_417_, 2, v_lctx_415_);
lean_ctor_set(v___x_417_, 3, v_options_416_);
v___x_418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v_msgData_402_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_ref_433_; lean_object* v___x_434_; lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v_ref_433_ = lean_ctor_get(v___y_430_, 2);
v___x_434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_inc(v_ref_433_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v_ref_433_);
lean_ctor_set(v___x_439_, 1, v_a_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 1);
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_msg_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_451_, lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_toCold_458_; lean_object* v_currRecDepth_459_; lean_object* v_ref_460_; uint16_t v_optionFlags_461_; uint8_t v_suppressElabErrors_462_; uint8_t v_isRecordingDeps_463_; lean_object* v_ref_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_toCold_458_ = lean_ctor_get(v___y_455_, 0);
v_currRecDepth_459_ = lean_ctor_get(v___y_455_, 1);
v_ref_460_ = lean_ctor_get(v___y_455_, 2);
v_optionFlags_461_ = lean_ctor_get_uint16(v___y_455_, sizeof(void*)*3);
v_suppressElabErrors_462_ = lean_ctor_get_uint8(v___y_455_, sizeof(void*)*3 + 2);
v_isRecordingDeps_463_ = lean_ctor_get_uint8(v___y_455_, sizeof(void*)*3 + 3);
v_ref_464_ = l_Lean_replaceRef(v_ref_451_, v_ref_460_);
lean_inc(v_currRecDepth_459_);
lean_inc_ref(v_toCold_458_);
v___x_465_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_465_, 0, v_toCold_458_);
lean_ctor_set(v___x_465_, 1, v_currRecDepth_459_);
lean_ctor_set(v___x_465_, 2, v_ref_464_);
lean_ctor_set_uint16(v___x_465_, sizeof(void*)*3, v_optionFlags_461_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*3 + 2, v_suppressElabErrors_462_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*3 + 3, v_isRecordingDeps_463_);
v___x_466_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_452_, v___y_453_, v___y_454_, v___x_465_, v___y_456_);
lean_dec_ref_known(v___x_465_, 3);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_467_, v_msg_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v_ref_467_);
return v_res_474_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_479_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_ctor_set(v___x_481_, 3, v___x_480_);
lean_ctor_set(v___x_481_, 4, v___x_479_);
lean_ctor_set(v___x_481_, 5, v___x_479_);
lean_ctor_set(v___x_481_, 6, v___x_479_);
lean_ctor_set(v___x_481_, 7, v___x_479_);
lean_ctor_set(v___x_481_, 8, v___x_479_);
lean_ctor_set(v___x_481_, 9, v___x_479_);
lean_ctor_set(v___x_481_, 10, v___x_479_);
lean_ctor_set(v___x_481_, 11, v___x_478_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(32u);
v___x_483_ = lean_mk_empty_array_with_capacity(v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_485_ = ((size_t)5ULL);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_unsigned_to_nat(32u);
v___x_488_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_489_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_490_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_486_);
lean_ctor_set(v___x_490_, 3, v___x_486_);
lean_ctor_set_usize(v___x_490_, 4, v___x_485_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_box(1);
v___x_492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_493_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_491_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_516_, lean_object* v_declHint_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_env_522_; uint8_t v___x_523_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_st_ref_get(v___y_518_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_env_522_);
lean_dec(v___x_521_);
v___x_523_ = l_Lean_Name_isAnonymous(v_declHint_517_);
if (v___x_523_ == 0)
{
uint8_t v_isExporting_524_; 
v_isExporting_524_ = lean_ctor_get_uint8(v_env_522_, sizeof(void*)*13);
if (v_isExporting_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v_env_522_);
lean_dec(v_declHint_517_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_msg_516_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; uint8_t v___x_527_; 
lean_inc_ref(v_env_522_);
v___x_526_ = l_Lean_Environment_setExporting(v_env_522_, v___x_523_);
lean_inc(v_declHint_517_);
lean_inc_ref(v___x_526_);
v___x_527_ = l_Lean_Environment_contains(v___x_526_, v_declHint_517_, v_isExporting_524_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_526_);
lean_dec_ref(v_env_522_);
lean_dec(v_declHint_517_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_msg_516_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_c_534_; lean_object* v___x_535_; 
v___x_529_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_530_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_531_ = l_Lean_Options_empty;
v___x_532_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_532_, 0, v___x_526_);
lean_ctor_set(v___x_532_, 1, v___x_529_);
lean_ctor_set(v___x_532_, 2, v___x_530_);
lean_ctor_set(v___x_532_, 3, v___x_531_);
lean_inc(v_declHint_517_);
v___x_533_ = l_Lean_MessageData_ofConstName(v_declHint_517_, v___x_523_);
v_c_534_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_534_, 0, v___x_532_);
lean_ctor_set(v_c_534_, 1, v___x_533_);
v___x_535_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_522_, v_declHint_517_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v_env_522_);
lean_dec(v_declHint_517_);
v___x_536_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_c_534_);
v___x_538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = l_Lean_MessageData_note(v___x_539_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v_msg_516_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v_val_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_577_; 
v_val_543_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_577_ == 0)
{
v___x_545_ = v___x_535_;
v_isShared_546_ = v_isSharedCheck_577_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_val_543_);
lean_dec(v___x_535_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_577_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v_moduleNames_548_; lean_object* v_mod_549_; uint8_t v___x_550_; 
v___x_547_ = l_Lean_Environment_header(v_env_522_);
lean_dec_ref(v_env_522_);
v_moduleNames_548_ = lean_ctor_get(v___x_547_, 4);
lean_inc_ref(v_moduleNames_548_);
lean_dec_ref(v___x_547_);
v_mod_549_ = lean_array_get(v___x_520_, v_moduleNames_548_, v_val_543_);
lean_dec(v_val_543_);
lean_dec_ref(v_moduleNames_548_);
v___x_550_ = l_Lean_isPrivateName(v_declHint_517_);
lean_dec(v_declHint_517_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set(v___x_552_, 1, v_c_534_);
v___x_553_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = l_Lean_MessageData_ofName(v_mod_549_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15);
v___x_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l_Lean_MessageData_note(v___x_558_);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v_msg_516_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 0);
lean_ctor_set(v___x_545_, 0, v___x_560_);
v___x_562_ = v___x_545_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
lean_ctor_set(v___x_565_, 1, v_c_534_);
v___x_566_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = l_Lean_MessageData_ofName(v_mod_549_);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19);
v___x_571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_MessageData_note(v___x_571_);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v_msg_516_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 0);
lean_ctor_set(v___x_545_, 0, v___x_573_);
v___x_575_ = v___x_545_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_578_; 
lean_dec_ref(v_env_522_);
lean_dec(v_declHint_517_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_msg_516_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_579_, lean_object* v_declHint_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_579_, v_declHint_580_, v___y_581_);
lean_dec(v___y_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(lean_object* v_msg_584_, lean_object* v_declHint_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_601_; 
v___x_591_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_584_, v_declHint_585_, v___y_589_);
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_601_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_596_ = l_Lean_unknownIdentifierMessageTag;
v___x_597_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v_a_592_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_597_);
v___x_599_ = v___x_594_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_602_, lean_object* v_declHint_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_602_, v_declHint_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(lean_object* v_ref_610_, lean_object* v_msg_611_, lean_object* v_declHint_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v___x_618_; lean_object* v_a_619_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_611_, v_declHint_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
v___x_620_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_610_, v_a_619_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_ref_621_, lean_object* v_msg_622_, lean_object* v_declHint_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_621_, v_msg_622_, v_declHint_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v_ref_621_);
return v_res_629_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2));
v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(lean_object* v_ref_636_, lean_object* v_constName_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_643_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1);
v___x_644_ = 0;
lean_inc(v_constName_637_);
v___x_645_ = l_Lean_MessageData_ofConstName(v_constName_637_, v___x_644_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_643_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_636_, v___x_648_, v_constName_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___boxed(lean_object* v_ref_650_, lean_object* v_constName_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_650_, v_constName_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v_ref_650_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object* v_constName_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; lean_object* v_env_665_; uint8_t v___x_666_; lean_object* v___x_667_; 
v___x_664_ = lean_st_ref_get(v_a_662_);
v_env_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref(v_env_665_);
lean_dec(v___x_664_);
v___x_666_ = 0;
lean_inc(v_constName_658_);
v___x_667_ = l_Lean_Environment_findAsync_x3f(v_env_665_, v_constName_658_, v___x_666_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_constName_658_);
v_val_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_701_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_701_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_val_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_701_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
uint8_t v_kind_672_; 
v_kind_672_ = lean_ctor_get_uint8(v_val_668_, sizeof(void*)*3);
if (v_kind_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_668_);
lean_inc_ref(v___x_673_);
v___x_674_ = l_Lean_Meta_canUnfold___redArg(v___x_673_, v_a_659_, v_a_661_, v_a_662_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_690_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_690_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_690_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
uint8_t v___x_679_; 
v___x_679_ = lean_unbox(v_a_675_);
lean_dec(v_a_675_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_682_; 
lean_dec_ref(v___x_673_);
lean_del_object(v___x_670_);
v___x_680_ = lean_box(0);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
lean_object* v___x_685_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_673_);
v___x_685_ = v___x_670_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_673_);
v___x_685_ = v_reuseFailAlloc_689_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_687_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_685_);
v___x_687_ = v___x_677_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v___x_673_);
lean_del_object(v___x_670_);
v_a_691_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_674_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_674_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_del_object(v___x_670_);
lean_dec(v_val_668_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
else
{
lean_object* v_ref_702_; lean_object* v___x_703_; 
lean_dec(v___x_667_);
v_ref_702_ = lean_ctor_get(v_a_661_, 2);
v___x_703_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_702_, v_constName_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object* v_constName_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_getUnfoldableConst_x3f(v_constName_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(lean_object* v_00_u03b1_711_, lean_object* v_ref_712_, lean_object* v_constName_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_712_, v_constName_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___boxed(lean_object* v_00_u03b1_720_, lean_object* v_ref_721_, lean_object* v_constName_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(v_00_u03b1_720_, v_ref_721_, v_constName_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v_ref_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(lean_object* v_00_u03b1_729_, lean_object* v_ref_730_, lean_object* v_msg_731_, lean_object* v_declHint_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_730_, v_msg_731_, v_declHint_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_739_, lean_object* v_ref_740_, lean_object* v_msg_741_, lean_object* v_declHint_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(v_00_u03b1_739_, v_ref_740_, v_msg_741_, v_declHint_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v_ref_740_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_msg_749_, lean_object* v_declHint_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_749_, v_declHint_750_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msg_757_, lean_object* v_declHint_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(v_msg_757_, v_declHint_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_765_, lean_object* v_ref_766_, lean_object* v_msg_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_766_, v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_774_, lean_object* v_ref_775_, lean_object* v_msg_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(v_00_u03b1_774_, v_ref_775_, v_msg_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v_ref_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_791_, lean_object* v_msg_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_791_, v_msg_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object* v_constName_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_808_; lean_object* v_env_809_; uint8_t v___x_810_; lean_object* v___x_811_; 
v___x_808_ = lean_st_ref_get(v_a_803_);
v_env_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc_ref(v_env_809_);
lean_dec(v___x_808_);
v___x_810_ = 0;
lean_inc(v_constName_799_);
v___x_811_ = l_Lean_Environment_find_x3f(v_env_809_, v_constName_799_, v___x_810_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_812_);
switch(lean_obj_tag(v_val_812_))
{
case 2:
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref_known(v___x_811_, 1);
lean_dec(v_constName_799_);
v_isSharedCheck_820_ = !lean_is_exclusive(v_val_812_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_val_812_, 0);
lean_dec(v_unused_821_);
v___x_814_ = v_val_812_;
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
else
{
lean_dec(v_val_812_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_820_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_box(0);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
case 1:
{
lean_object* v___x_822_; 
lean_dec(v_constName_799_);
v___x_822_ = l_Lean_Meta_canUnfold___redArg(v_val_812_, v_a_800_, v_a_802_, v_a_803_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_835_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_835_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_835_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_835_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___x_827_; 
v___x_827_ = lean_unbox(v_a_823_);
lean_dec(v_a_823_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec_ref_known(v___x_811_, 1);
v___x_828_ = lean_box(0);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_828_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v___x_833_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_811_);
v___x_833_ = v___x_825_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_811_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref_known(v___x_811_, 1);
v_a_836_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_822_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_822_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
case 0:
{
lean_object* v___x_844_; 
lean_dec_ref_known(v_val_812_, 1);
lean_dec_ref_known(v___x_811_, 1);
v___x_844_ = l_Lean_Meta_recordUnfoldAxiom___redArg(v_constName_799_, v_a_801_, v_a_802_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v___x_844_, 0);
lean_dec(v_unused_853_);
v___x_846_ = v___x_844_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_dec(v___x_844_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_850_ = v___x_846_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_844_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_844_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
default: 
{
lean_dec_ref_known(v___x_811_, 1);
lean_dec(v_val_812_);
lean_dec(v_constName_799_);
goto v___jp_805_;
}
}
}
else
{
lean_dec(v___x_811_);
lean_dec(v_constName_799_);
goto v___jp_805_;
}
v___jp_805_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object* v_constName_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_getUnfoldableConstNoEx_x3f(v_constName_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
return v_res_868_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatchPatternAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatchPatternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GetUnfoldableConst(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchPatternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_GetUnfoldableConst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_GetUnfoldableConst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_GetUnfoldableConst(builtin);
}
#ifdef __cplusplus
}
#endif
