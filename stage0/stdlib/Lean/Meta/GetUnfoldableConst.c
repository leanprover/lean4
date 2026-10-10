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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__27;
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
lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_9_;
v_res_9_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_1_, v___y_2_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg___boxed(lean_object* v_declName_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_10_, v___y_11_);
lean_dec(v___y_11_);
return v_res_13_;
}
}
lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(lean_object* v_declName_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_14_, v___y_16_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_14_ = stack[0].m_obj;
lean_object* v___y_15_ = stack[1].m_obj;
lean_object* v___y_16_ = stack[2].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(v_declName_14_, v___y_15_, v___y_16_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___boxed(lean_object* v_declName_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(v_declName_20_, v___y_21_, v___y_22_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_24_;
}
}
lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(lean_object* v_declName_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_29_; lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_45_; 
v___x_29_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_25_, v___y_27_);
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_45_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_45_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
uint8_t v___x_34_; 
v___x_34_ = lean_unbox(v_a_30_);
lean_dec(v_a_30_);
if (v___x_34_ == 2)
{
uint8_t v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_35_ = 1;
v___x_36_ = lean_box(v___x_35_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_36_);
v___x_38_ = v___x_32_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
else
{
uint8_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_40_ = 0;
v___x_41_ = lean_box(v___x_40_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_41_);
v___x_43_ = v___x_32_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_25_ = stack[0].m_obj;
lean_object* v___y_26_ = stack[1].m_obj;
lean_object* v___y_27_ = stack[2].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(v_declName_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0___boxed(lean_object* v_declName_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(v_declName_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
return v_res_51_;
}
}
lean_object* l_Lean_Meta_canUnfoldDefault(lean_object* v_cfg_52_, lean_object* v_info_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
uint8_t v_transparency_57_; 
v_transparency_57_ = lean_ctor_get_uint8(v_cfg_52_, 9);
switch(v_transparency_57_)
{
case 4:
{
uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = 0;
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
case 0:
{
uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = 1;
v___x_62_ = lean_box(v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
case 1:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = l_Lean_ConstantInfo_name(v_info_53_);
v___x_65_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(v___x_64_, v_a_54_, v_a_55_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_81_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_81_ == 0)
{
v___x_68_ = v___x_65_;
v_isShared_69_ = v_isSharedCheck_81_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_dec(v___x_65_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_81_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
uint8_t v___x_70_; 
v___x_70_ = lean_unbox(v_a_66_);
lean_dec(v_a_66_);
if (v___x_70_ == 0)
{
uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_74_; 
v___x_71_ = 1;
v___x_72_ = lean_box(v___x_71_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_72_);
v___x_74_ = v___x_68_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v___x_72_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
else
{
uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_76_ = 0;
v___x_77_ = lean_box(v___x_76_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_77_);
v___x_79_ = v___x_68_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
else
{
return v___x_65_;
}
}
default: 
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_122_; 
v___x_82_ = l_Lean_ConstantInfo_name(v_info_53_);
v___x_83_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v___x_82_, v_a_55_);
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_122_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_122_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_122_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint8_t v___x_88_; uint8_t v___x_89_; uint8_t v___x_90_; uint8_t v___x_91_; uint8_t v___y_93_; uint8_t v___y_103_; 
v___x_88_ = 0;
v___x_89_ = lean_unbox(v_a_84_);
v___x_90_ = l_Lean_instBEqReducibilityStatus_beq(v___x_89_, v___x_88_);
v___x_91_ = 1;
if (v___x_90_ == 0)
{
uint8_t v___x_111_; uint8_t v___x_112_; uint8_t v___x_113_; 
v___x_111_ = 4;
v___x_112_ = lean_unbox(v_a_84_);
v___x_113_ = l_Lean_instBEqReducibilityStatus_beq(v___x_112_, v___x_111_);
if (v___x_113_ == 0)
{
v___y_103_ = v___x_90_;
goto v___jp_102_;
}
else
{
uint8_t v___x_114_; uint8_t v___x_115_; 
v___x_114_ = 3;
v___x_115_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_57_, v___x_114_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; uint8_t v___x_117_; 
v___x_116_ = 5;
v___x_117_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_57_, v___x_116_);
v___y_103_ = v___x_117_;
goto v___jp_102_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_86_);
lean_dec(v_a_84_);
v___x_118_ = lean_box(v___x_91_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_del_object(v___x_86_);
lean_dec(v_a_84_);
v___x_120_ = lean_box(v___x_91_);
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
v___jp_92_:
{
if (v___y_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_94_ = lean_box(v___y_93_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_94_);
v___x_96_ = v___x_86_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
else
{
lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_98_ = lean_box(v___x_91_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_98_);
v___x_100_ = v___x_86_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
v___jp_102_:
{
if (v___y_103_ == 0)
{
uint8_t v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; 
v___x_104_ = 3;
v___x_105_ = lean_unbox(v_a_84_);
lean_dec(v_a_84_);
v___x_106_ = l_Lean_instBEqReducibilityStatus_beq(v___x_105_, v___x_104_);
if (v___x_106_ == 0)
{
v___y_93_ = v___x_90_;
goto v___jp_92_;
}
else
{
uint8_t v___x_107_; uint8_t v___x_108_; 
v___x_107_ = 5;
v___x_108_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_57_, v___x_107_);
v___y_93_ = v___x_108_;
goto v___jp_92_;
}
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_del_object(v___x_86_);
lean_dec(v_a_84_);
v___x_109_ = lean_box(v___x_91_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_canUnfoldDefault_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_52_ = stack[0].m_obj;
lean_object* v_info_53_ = stack[1].m_obj;
lean_object* v_a_54_ = stack[2].m_obj;
lean_object* v_a_55_ = stack[3].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_Lean_Meta_canUnfoldDefault(v_cfg_52_, v_info_53_, v_a_54_, v_a_55_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldDefault___boxed(lean_object* v_cfg_124_, lean_object* v_info_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Meta_canUnfoldDefault(v_cfg_124_, v_info_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
lean_dec_ref(v_info_125_);
lean_dec_ref(v_cfg_124_);
return v_res_129_;
}
}
lean_object* l_Lean_Meta_canUnfoldAtMatcher(lean_object* v_cfg_216_, lean_object* v_info_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_canUnfoldDefault(v_cfg_216_, v_info_217_, v_a_218_, v_a_219_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_366_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_366_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_366_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_366_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint8_t v___x_226_; uint8_t v___x_227_; 
v___x_226_ = 1;
v___x_227_ = lean_unbox(v_a_222_);
lean_dec(v_a_222_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v_env_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_228_ = lean_st_ref_get(v_a_219_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = l_Lean_ConstantInfo_name(v_info_217_);
lean_inc(v___x_230_);
v___x_231_ = l_Lean_hasMatchPatternAttribute(v_env_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__2));
v___x_233_ = lean_name_eq(v___x_230_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__5));
v___x_235_ = lean_name_eq(v___x_230_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__8));
v___x_237_ = lean_name_eq(v___x_230_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__11));
v___x_239_ = lean_name_eq(v___x_230_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__13));
v___x_241_ = lean_name_eq(v___x_230_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__15));
v___x_243_ = lean_name_eq(v___x_230_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__17));
v___x_245_ = lean_name_eq(v___x_230_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__19));
v___x_247_ = lean_name_eq(v___x_230_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__21));
v___x_249_ = lean_name_eq(v___x_230_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__24));
v___x_251_ = lean_name_eq(v___x_230_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__26));
v___x_253_ = lean_name_eq(v___x_230_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__28));
v___x_255_ = lean_name_eq(v___x_230_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__29));
v___x_257_ = lean_name_eq(v___x_230_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__31));
v___x_259_ = lean_name_eq(v___x_230_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__32));
v___x_261_ = lean_name_eq(v___x_230_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__34));
v___x_263_ = lean_name_eq(v___x_230_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__35));
v___x_265_ = lean_name_eq(v___x_230_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__37));
v___x_267_ = lean_name_eq(v___x_230_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__38));
v___x_269_ = lean_name_eq(v___x_230_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__41));
v___x_271_ = lean_name_eq(v___x_230_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_272_ = ((lean_object*)(l_Lean_Meta_canUnfoldAtMatcher___closed__44));
v___x_273_ = lean_name_eq(v___x_230_, v___x_272_);
lean_dec(v___x_230_);
v___x_274_ = lean_box(v___x_273_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_274_);
v___x_276_ = v___x_224_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec(v___x_230_);
v___x_278_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_278_);
v___x_280_ = v___x_224_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec(v___x_230_);
v___x_282_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_282_);
v___x_284_ = v___x_224_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_288_; 
lean_dec(v___x_230_);
v___x_286_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_286_);
v___x_288_ = v___x_224_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_292_; 
lean_dec(v___x_230_);
v___x_290_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_290_);
v___x_292_ = v___x_224_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_296_; 
lean_dec(v___x_230_);
v___x_294_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_294_);
v___x_296_ = v___x_224_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_300_; 
lean_dec(v___x_230_);
v___x_298_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_298_);
v___x_300_ = v___x_224_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_304_; 
lean_dec(v___x_230_);
v___x_302_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_302_);
v___x_304_ = v___x_224_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_308_; 
lean_dec(v___x_230_);
v___x_306_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_306_);
v___x_308_ = v___x_224_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_312_; 
lean_dec(v___x_230_);
v___x_310_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_310_);
v___x_312_ = v___x_224_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_316_; 
lean_dec(v___x_230_);
v___x_314_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_314_);
v___x_316_ = v___x_224_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_320_; 
lean_dec(v___x_230_);
v___x_318_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_318_);
v___x_320_ = v___x_224_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_324_; 
lean_dec(v___x_230_);
v___x_322_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_322_);
v___x_324_ = v___x_224_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec(v___x_230_);
v___x_326_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_326_);
v___x_328_ = v___x_224_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_332_; 
lean_dec(v___x_230_);
v___x_330_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_330_);
v___x_332_ = v___x_224_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_336_; 
lean_dec(v___x_230_);
v___x_334_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_334_);
v___x_336_ = v___x_224_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_340_; 
lean_dec(v___x_230_);
v___x_338_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_338_);
v___x_340_ = v___x_224_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_344_; 
lean_dec(v___x_230_);
v___x_342_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_342_);
v___x_344_ = v___x_224_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_348_; 
lean_dec(v___x_230_);
v___x_346_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_346_);
v___x_348_ = v___x_224_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_352_; 
lean_dec(v___x_230_);
v___x_350_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_350_);
v___x_352_ = v___x_224_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_356_; 
lean_dec(v___x_230_);
v___x_354_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_354_);
v___x_356_ = v___x_224_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_360_; 
lean_dec(v___x_230_);
v___x_358_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_358_);
v___x_360_ = v___x_224_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_box(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_362_);
v___x_364_ = v___x_224_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
return v___x_221_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_canUnfoldAtMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_216_ = stack[0].m_obj;
lean_object* v_info_217_ = stack[1].m_obj;
lean_object* v_a_218_ = stack[2].m_obj;
lean_object* v_a_219_ = stack[3].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Meta_canUnfoldAtMatcher(v_cfg_216_, v_info_217_, v_a_218_, v_a_219_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object* v_cfg_368_, lean_object* v_info_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_canUnfoldAtMatcher(v_cfg_368_, v_info_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec_ref(v_info_369_);
lean_dec_ref(v_cfg_368_);
return v_res_373_;
}
}
lean_object* l_Lean_Meta_canUnfold___redArg(lean_object* v_info_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_customCanUnfoldPredicate_x3f_379_; lean_object* v___x_380_; 
v_customCanUnfoldPredicate_x3f_379_ = lean_ctor_get(v_a_375_, 6);
v___x_380_ = l_Lean_Meta_Context_config(v_a_375_);
if (lean_obj_tag(v_customCanUnfoldPredicate_x3f_379_) == 0)
{
uint8_t v_canUnfoldPredicateConfig_381_; 
v_canUnfoldPredicateConfig_381_ = lean_ctor_get_uint8(v___x_380_, 19);
if (v_canUnfoldPredicateConfig_381_ == 0)
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_canUnfoldDefault(v___x_380_, v_info_374_, v_a_376_, v_a_377_);
lean_dec_ref(v_info_374_);
lean_dec_ref(v___x_380_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_canUnfoldAtMatcher(v___x_380_, v_info_374_, v_a_376_, v_a_377_);
lean_dec_ref(v_info_374_);
lean_dec_ref(v___x_380_);
return v___x_383_;
}
}
else
{
lean_object* v_val_384_; lean_object* v___x_385_; 
v_val_384_ = lean_ctor_get(v_customCanUnfoldPredicate_x3f_379_, 0);
lean_inc(v_val_384_);
lean_inc(v_a_377_);
lean_inc_ref(v_a_376_);
v___x_385_ = lean_apply_5(v_val_384_, v___x_380_, v_info_374_, v_a_376_, v_a_377_, lean_box(0));
return v___x_385_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_canUnfold___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_374_ = stack[0].m_obj;
lean_object* v_a_375_ = stack[1].m_obj;
lean_object* v_a_376_ = stack[2].m_obj;
lean_object* v_a_377_ = stack[3].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_Meta_canUnfold___redArg(v_info_374_, v_a_375_, v_a_376_, v_a_377_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___redArg___boxed(lean_object* v_info_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_canUnfold___redArg(v_info_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_392_;
}
}
lean_object* l_Lean_Meta_canUnfold(lean_object* v_info_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_canUnfold___redArg(v_info_393_, v_a_394_, v_a_396_, v_a_397_);
return v___x_399_;
}
}
LEAN_EXPORT void l_Lean_Meta_canUnfold_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_393_ = stack[0].m_obj;
lean_object* v_a_394_ = stack[1].m_obj;
lean_object* v_a_395_ = stack[2].m_obj;
lean_object* v_a_396_ = stack[3].m_obj;
lean_object* v_a_397_ = stack[4].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Meta_canUnfold(v_info_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_canUnfold___boxed(lean_object* v_info_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Meta_canUnfold(v_info_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
return v_res_407_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_msgData_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; lean_object* v_env_415_; uint8_t v___x_416_; lean_object* v_env_417_; lean_object* v___x_418_; lean_object* v_toCold_419_; lean_object* v_mctx_420_; lean_object* v_lctx_421_; lean_object* v_options_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_414_ = lean_st_ref_get(v___y_412_);
v_env_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_env_415_);
lean_dec(v___x_414_);
v___x_416_ = 0;
v_env_417_ = l_Lean_Environment_setRecordingDeps(v_env_415_, v___x_416_);
v___x_418_ = lean_st_ref_get(v___y_410_);
v_toCold_419_ = lean_ctor_get(v___y_411_, 0);
v_mctx_420_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_mctx_420_);
lean_dec(v___x_418_);
v_lctx_421_ = lean_ctor_get(v___y_409_, 2);
v_options_422_ = lean_ctor_get(v_toCold_419_, 2);
lean_inc_ref(v_options_422_);
lean_inc_ref(v_lctx_421_);
v___x_423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_423_, 0, v_env_417_);
lean_ctor_set(v___x_423_, 1, v_mctx_420_);
lean_ctor_set(v___x_423_, 2, v_lctx_421_);
lean_ctor_set(v___x_423_, 3, v_options_422_);
v___x_424_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v_msgData_408_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_408_ = stack[0].m_obj;
lean_object* v___y_409_ = stack[1].m_obj;
lean_object* v___y_410_ = stack[2].m_obj;
lean_object* v___y_411_ = stack[3].m_obj;
lean_object* v___y_412_ = stack[4].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(lean_object* v_msgData_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_433_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_ref_440_; lean_object* v___x_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_ref_440_ = lean_ctor_get(v___y_437_, 2);
v___x_441_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_448_; 
lean_inc(v_ref_440_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_ref_440_);
lean_ctor_set(v___x_446_, 1, v_a_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 1);
lean_ctor_set(v___x_444_, 0, v___x_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_434_ = stack[0].m_obj;
lean_object* v___y_435_ = stack[1].m_obj;
lean_object* v___y_436_ = stack[2].m_obj;
lean_object* v___y_437_ = stack[3].m_obj;
lean_object* v___y_438_ = stack[4].m_obj;
lean_object* v_res_451_;
v_res_451_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
return v_res_458_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_toCold_466_; lean_object* v_currRecDepth_467_; lean_object* v_ref_468_; uint16_t v_optionFlags_469_; uint8_t v_suppressElabErrors_470_; uint8_t v_isRecordingDeps_471_; lean_object* v_ref_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_toCold_466_ = lean_ctor_get(v___y_463_, 0);
v_currRecDepth_467_ = lean_ctor_get(v___y_463_, 1);
v_ref_468_ = lean_ctor_get(v___y_463_, 2);
v_optionFlags_469_ = lean_ctor_get_uint16(v___y_463_, sizeof(void*)*3);
v_suppressElabErrors_470_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*3 + 2);
v_isRecordingDeps_471_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*3 + 3);
v_ref_472_ = l_Lean_replaceRef(v_ref_459_, v_ref_468_);
lean_inc(v_currRecDepth_467_);
lean_inc_ref(v_toCold_466_);
v___x_473_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_473_, 0, v_toCold_466_);
lean_ctor_set(v___x_473_, 1, v_currRecDepth_467_);
lean_ctor_set(v___x_473_, 2, v_ref_472_);
lean_ctor_set_uint16(v___x_473_, sizeof(void*)*3, v_optionFlags_469_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*3 + 2, v_suppressElabErrors_470_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*3 + 3, v_isRecordingDeps_471_);
v___x_474_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_460_, v___y_461_, v___y_462_, v___x_473_, v___y_464_);
lean_dec_ref_known(v___x_473_, 3);
return v___x_474_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_459_ = stack[0].m_obj;
lean_object* v_msg_460_ = stack[1].m_obj;
lean_object* v___y_461_ = stack[2].m_obj;
lean_object* v___y_462_ = stack[3].m_obj;
lean_object* v___y_463_ = stack[4].m_obj;
lean_object* v___y_464_ = stack[5].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_459_, v_msg_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_476_, lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_476_, v_msg_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v_ref_476_);
return v_res_483_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_488_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
lean_ctor_set(v___x_490_, 2, v___x_489_);
lean_ctor_set(v___x_490_, 3, v___x_489_);
lean_ctor_set(v___x_490_, 4, v___x_488_);
lean_ctor_set(v___x_490_, 5, v___x_488_);
lean_ctor_set(v___x_490_, 6, v___x_488_);
lean_ctor_set(v___x_490_, 7, v___x_488_);
lean_ctor_set(v___x_490_, 8, v___x_488_);
lean_ctor_set(v___x_490_, 9, v___x_488_);
lean_ctor_set(v___x_490_, 10, v___x_488_);
lean_ctor_set(v___x_490_, 11, v___x_487_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(32u);
v___x_492_ = lean_mk_empty_array_with_capacity(v___x_491_);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_494_ = ((size_t)5ULL);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_unsigned_to_nat(32u);
v___x_497_ = lean_mk_empty_array_with_capacity(v___x_496_);
v___x_498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
v___x_499_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
lean_ctor_set(v___x_499_, 2, v___x_495_);
lean_ctor_set(v___x_499_, 3, v___x_495_);
lean_ctor_set_usize(v___x_499_, 4, v___x_494_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = lean_box(1);
v___x_501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4);
v___x_502_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
v___x_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
lean_ctor_set(v___x_503_, 2, v___x_500_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14));
v___x_518_ = l_Lean_stringToMessageData(v___x_517_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18));
v___x_524_ = l_Lean_stringToMessageData(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__21(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__20));
v___x_527_ = l_Lean_stringToMessageData(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__23(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__22));
v___x_530_ = l_Lean_stringToMessageData(v___x_529_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__25(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__24));
v___x_533_ = l_Lean_stringToMessageData(v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__27(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__26));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msg_537_, lean_object* v_declHint_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_env_543_; uint8_t v___x_544_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_st_ref_get(v___y_539_);
v_env_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc_ref(v_env_543_);
lean_dec(v___x_542_);
v___x_544_ = l_Lean_Name_isAnonymous(v_declHint_538_);
if (v___x_544_ == 0)
{
uint8_t v_isExporting_545_; 
v_isExporting_545_ = lean_ctor_get_uint8(v_env_543_, sizeof(void*)*13);
if (v_isExporting_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec_ref(v_env_543_);
lean_dec(v_declHint_538_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v_msg_537_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; uint8_t v___x_548_; 
lean_inc_ref(v_env_543_);
v___x_547_ = l_Lean_Environment_setExporting(v_env_543_, v___x_544_);
lean_inc(v_declHint_538_);
lean_inc_ref(v___x_547_);
v___x_548_ = l_Lean_Environment_contains(v___x_547_, v_declHint_538_, v_isExporting_545_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
lean_dec_ref(v___x_547_);
lean_dec_ref(v_env_543_);
lean_dec(v_declHint_538_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v_msg_537_);
return v___x_549_;
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_c_555_; lean_object* v___x_556_; 
v___x_550_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5);
v___x_552_ = l_Lean_Options_empty;
v___x_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_553_, 0, v___x_547_);
lean_ctor_set(v___x_553_, 1, v___x_550_);
lean_ctor_set(v___x_553_, 2, v___x_551_);
lean_ctor_set(v___x_553_, 3, v___x_552_);
lean_inc(v_declHint_538_);
v___x_554_ = l_Lean_MessageData_ofConstName(v_declHint_538_, v___x_544_);
v_c_555_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_555_, 0, v___x_553_);
lean_ctor_set(v_c_555_, 1, v___x_554_);
v___x_556_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_543_, v_declHint_538_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec_ref(v_env_543_);
lean_dec(v_declHint_538_);
v___x_557_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
v___x_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v_c_555_);
v___x_559_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_MessageData_note(v___x_560_);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v_msg_537_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
else
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_620_; 
v_val_564_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_620_ == 0)
{
v___x_566_ = v___x_556_;
v_isShared_567_ = v_isSharedCheck_620_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v___x_556_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_620_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v_modules_569_; lean_object* v_moduleNames_570_; lean_object* v_mod_571_; uint8_t v___y_573_; uint8_t v___x_603_; 
v___x_568_ = l_Lean_Environment_header(v_env_543_);
lean_dec_ref(v_env_543_);
v_modules_569_ = lean_ctor_get(v___x_568_, 3);
lean_inc_ref(v_modules_569_);
v_moduleNames_570_ = lean_ctor_get(v___x_568_, 4);
lean_inc_ref(v_moduleNames_570_);
lean_dec_ref(v___x_568_);
v_mod_571_ = lean_array_get(v___x_541_, v_moduleNames_570_, v_val_564_);
lean_dec_ref(v_moduleNames_570_);
v___x_603_ = l_Lean_isPrivateName(v_declHint_538_);
lean_dec(v_declHint_538_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_modules_569_);
v___x_605_ = lean_nat_dec_lt(v_val_564_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec_ref(v_modules_569_);
lean_dec(v_val_564_);
v___y_573_ = v___x_603_;
goto v___jp_572_;
}
else
{
lean_object* v___x_606_; lean_object* v_toImport_607_; uint8_t v_isExported_608_; 
v___x_606_ = lean_array_fget(v_modules_569_, v_val_564_);
lean_dec(v_val_564_);
lean_dec_ref(v_modules_569_);
v_toImport_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc_ref(v_toImport_607_);
lean_dec(v___x_606_);
v_isExported_608_ = lean_ctor_get_uint8(v_toImport_607_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_607_);
v___y_573_ = v_isExported_608_;
goto v___jp_572_;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec_ref(v_modules_569_);
lean_del_object(v___x_566_);
lean_dec(v_val_564_);
v___x_609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v_c_555_);
v___x_611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__25);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_Lean_MessageData_ofName(v_mod_571_);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__27);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_MessageData_note(v___x_616_);
v___x_618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_618_, 0, v_msg_537_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
v___jp_572_:
{
if (v___y_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_574_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_c_555_);
v___x_576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_MessageData_ofName(v_mod_571_);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_MessageData_note(v___x_581_);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v_msg_537_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 0);
lean_ctor_set(v___x_566_, 0, v___x_583_);
v___x_585_ = v___x_566_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
lean_ctor_set(v___x_588_, 1, v_c_555_);
v___x_589_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_MessageData_ofName(v_mod_571_);
lean_inc_ref(v___x_591_);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__21);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___x_591_);
v___x_596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__23);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_MessageData_note(v___x_597_);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v_msg_537_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 0);
lean_ctor_set(v___x_566_, 0, v___x_599_);
v___x_601_ = v___x_566_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref(v_env_543_);
lean_dec(v_declHint_538_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v_msg_537_);
return v___x_621_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_537_ = stack[0].m_obj;
lean_object* v_declHint_538_ = stack[1].m_obj;
lean_object* v___y_539_ = stack[2].m_obj;
lean_object* v_res_622_;
v_res_622_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_537_, v_declHint_538_, v___y_539_);
stack->m_obj
 = v_res_622_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msg_623_, lean_object* v_declHint_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_623_, v_declHint_624_, v___y_625_);
lean_dec(v___y_625_);
return v_res_627_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(lean_object* v_msg_628_, lean_object* v_declHint_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_645_; 
v___x_635_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_628_, v_declHint_629_, v___y_633_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_645_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_640_ = l_Lean_unknownIdentifierMessageTag;
v___x_641_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v_a_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_628_ = stack[0].m_obj;
lean_object* v_declHint_629_ = stack[1].m_obj;
lean_object* v___y_630_ = stack[2].m_obj;
lean_object* v___y_631_ = stack[3].m_obj;
lean_object* v___y_632_ = stack[4].m_obj;
lean_object* v___y_633_ = stack[5].m_obj;
lean_object* v_res_646_;
v_res_646_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_628_, v_declHint_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_647_, lean_object* v_declHint_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_647_, v_declHint_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(lean_object* v_ref_655_, lean_object* v_msg_656_, lean_object* v_declHint_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_665_; 
v___x_663_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_656_, v_declHint_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref(v___x_663_);
v___x_665_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_655_, v_a_664_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
return v___x_665_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_655_ = stack[0].m_obj;
lean_object* v_msg_656_ = stack[1].m_obj;
lean_object* v_declHint_657_ = stack[2].m_obj;
lean_object* v___y_658_ = stack[3].m_obj;
lean_object* v___y_659_ = stack[4].m_obj;
lean_object* v___y_660_ = stack[5].m_obj;
lean_object* v___y_661_ = stack[6].m_obj;
lean_object* v_res_666_;
v_res_666_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_655_, v_msg_656_, v_declHint_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
stack->m_obj
 = v_res_666_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_ref_667_, lean_object* v_msg_668_, lean_object* v_declHint_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_667_, v_msg_668_, v_declHint_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v_ref_667_);
return v_res_675_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(lean_object* v_ref_682_, lean_object* v_constName_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_689_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1);
v___x_690_ = 0;
lean_inc(v_constName_683_);
v___x_691_ = l_Lean_MessageData_ofConstName(v_constName_683_, v___x_690_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_689_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_682_, v___x_694_, v_constName_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_695_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_682_ = stack[0].m_obj;
lean_object* v_constName_683_ = stack[1].m_obj;
lean_object* v___y_684_ = stack[2].m_obj;
lean_object* v___y_685_ = stack[3].m_obj;
lean_object* v___y_686_ = stack[4].m_obj;
lean_object* v___y_687_ = stack[5].m_obj;
lean_object* v_res_696_;
v_res_696_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_682_, v_constName_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___boxed(lean_object* v_ref_697_, lean_object* v_constName_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_697_, v_constName_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v_ref_697_);
return v_res_704_;
}
}
lean_object* l_Lean_Meta_getUnfoldableConst_x3f(lean_object* v_constName_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_711_; lean_object* v_env_712_; uint8_t v___x_713_; lean_object* v___x_714_; 
v___x_711_ = lean_st_ref_get(v_a_709_);
v_env_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc_ref(v_env_712_);
lean_dec(v___x_711_);
v___x_713_ = 0;
lean_inc(v_constName_705_);
v___x_714_ = l_Lean_Environment_findAsync_x3f(v_env_712_, v_constName_705_, v___x_713_);
if (lean_obj_tag(v___x_714_) == 1)
{
lean_object* v_val_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_constName_705_);
v_val_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_748_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_748_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_val_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_748_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
uint8_t v_kind_719_; 
v_kind_719_ = lean_ctor_get_uint8(v_val_715_, sizeof(void*)*3);
if (v_kind_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_715_);
lean_inc_ref(v___x_720_);
v___x_721_ = l_Lean_Meta_canUnfold___redArg(v___x_720_, v_a_706_, v_a_708_, v_a_709_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_737_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_737_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_737_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
uint8_t v___x_726_; 
v___x_726_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_729_; 
lean_dec_ref(v___x_720_);
lean_del_object(v___x_717_);
v___x_727_ = lean_box(0);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_727_);
v___x_729_ = v___x_724_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_object* v___x_732_; 
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_720_);
v___x_732_ = v___x_717_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_720_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_732_);
v___x_734_ = v___x_724_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_720_);
lean_del_object(v___x_717_);
v_a_738_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_721_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_721_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_717_);
lean_dec(v_val_715_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
}
else
{
lean_object* v_ref_749_; lean_object* v___x_750_; 
lean_dec(v___x_714_);
v_ref_749_ = lean_ctor_get(v_a_708_, 2);
v___x_750_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_749_, v_constName_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
return v___x_750_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getUnfoldableConst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_705_ = stack[0].m_obj;
lean_object* v_a_706_ = stack[1].m_obj;
lean_object* v_a_707_ = stack[2].m_obj;
lean_object* v_a_708_ = stack[3].m_obj;
lean_object* v_a_709_ = stack[4].m_obj;
lean_object* v_res_751_;
v_res_751_ = l_Lean_Meta_getUnfoldableConst_x3f(v_constName_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
stack->m_obj
 = v_res_751_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConst_x3f___boxed(lean_object* v_constName_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Meta_getUnfoldableConst_x3f(v_constName_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_758_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(lean_object* v_00_u03b1_759_, lean_object* v_ref_760_, lean_object* v_constName_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_760_, v_constName_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v___x_767_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_760_ = stack[1].m_obj;
lean_object* v_constName_761_ = stack[2].m_obj;
lean_object* v___y_762_ = stack[3].m_obj;
lean_object* v___y_763_ = stack[4].m_obj;
lean_object* v___y_764_ = stack[5].m_obj;
lean_object* v___y_765_ = stack[6].m_obj;
lean_object* v_res_768_;
v_res_768_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(lean_box(0), v_ref_760_, v_constName_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___boxed(lean_object* v_00_u03b1_769_, lean_object* v_ref_770_, lean_object* v_constName_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(v_00_u03b1_769_, v_ref_770_, v_constName_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v_ref_770_);
return v_res_777_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(lean_object* v_00_u03b1_778_, lean_object* v_ref_779_, lean_object* v_msg_780_, lean_object* v_declHint_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_779_, v_msg_780_, v_declHint_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_787_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_779_ = stack[1].m_obj;
lean_object* v_msg_780_ = stack[2].m_obj;
lean_object* v_declHint_781_ = stack[3].m_obj;
lean_object* v___y_782_ = stack[4].m_obj;
lean_object* v___y_783_ = stack[5].m_obj;
lean_object* v___y_784_ = stack[6].m_obj;
lean_object* v___y_785_ = stack[7].m_obj;
lean_object* v_res_788_;
v_res_788_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(lean_box(0), v_ref_779_, v_msg_780_, v_declHint_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_789_, lean_object* v_ref_790_, lean_object* v_msg_791_, lean_object* v_declHint_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(v_00_u03b1_789_, v_ref_790_, v_msg_791_, v_declHint_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v_ref_790_);
return v_res_798_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_msg_799_, lean_object* v_declHint_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_799_, v_declHint_800_, v___y_804_);
return v___x_806_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_799_ = stack[0].m_obj;
lean_object* v_declHint_800_ = stack[1].m_obj;
lean_object* v___y_801_ = stack[2].m_obj;
lean_object* v___y_802_ = stack[3].m_obj;
lean_object* v___y_803_ = stack[4].m_obj;
lean_object* v___y_804_ = stack[5].m_obj;
lean_object* v_res_807_;
v_res_807_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(v_msg_799_, v_declHint_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
stack->m_obj
 = v_res_807_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msg_808_, lean_object* v_declHint_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(v_msg_808_, v_declHint_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_815_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_816_, lean_object* v_ref_817_, lean_object* v_msg_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_817_, v_msg_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
return v___x_824_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_817_ = stack[1].m_obj;
lean_object* v_msg_818_ = stack[2].m_obj;
lean_object* v___y_819_ = stack[3].m_obj;
lean_object* v___y_820_ = stack[4].m_obj;
lean_object* v___y_821_ = stack[5].m_obj;
lean_object* v___y_822_ = stack[6].m_obj;
lean_object* v_res_825_;
v_res_825_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(lean_box(0), v_ref_817_, v_msg_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_826_, lean_object* v_ref_827_, lean_object* v_msg_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(v_00_u03b1_826_, v_ref_827_, v_msg_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v_ref_827_);
return v_res_834_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b1_835_, lean_object* v_msg_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_836_ = stack[1].m_obj;
lean_object* v___y_837_ = stack[2].m_obj;
lean_object* v___y_838_ = stack[3].m_obj;
lean_object* v___y_839_ = stack[4].m_obj;
lean_object* v___y_840_ = stack[5].m_obj;
lean_object* v_res_843_;
v_res_843_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(lean_box(0), v_msg_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_00_u03b1_844_, lean_object* v_msg_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_844_, v_msg_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f(lean_object* v_constName_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_861_; lean_object* v_env_862_; uint8_t v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_st_ref_get(v_a_856_);
v_env_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_env_862_);
lean_dec(v___x_861_);
v___x_863_ = 0;
lean_inc(v_constName_852_);
v___x_864_ = l_Lean_Environment_find_x3f(v_env_862_, v_constName_852_, v___x_863_);
if (lean_obj_tag(v___x_864_) == 1)
{
lean_object* v_val_865_; 
v_val_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_val_865_);
switch(lean_obj_tag(v_val_865_))
{
case 2:
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref_known(v___x_864_, 1);
lean_dec(v_constName_852_);
v_isSharedCheck_873_ = !lean_is_exclusive(v_val_865_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v_val_865_, 0);
lean_dec(v_unused_874_);
v___x_867_ = v_val_865_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_val_865_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 0);
lean_ctor_set(v___x_867_, 0, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
case 1:
{
lean_object* v___x_875_; 
lean_dec(v_constName_852_);
v___x_875_ = l_Lean_Meta_canUnfold___redArg(v_val_865_, v_a_853_, v_a_855_, v_a_856_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_888_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_888_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_888_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
uint8_t v___x_880_; 
v___x_880_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; lean_object* v___x_883_; 
lean_dec_ref_known(v___x_864_, 1);
v___x_881_ = lean_box(0);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_881_);
v___x_883_ = v___x_878_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
lean_object* v___x_886_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_864_);
v___x_886_ = v___x_878_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_864_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref_known(v___x_864_, 1);
v_a_889_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_875_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_875_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
case 0:
{
lean_object* v___x_897_; 
lean_dec_ref_known(v_val_865_, 1);
lean_dec_ref_known(v___x_864_, 1);
v___x_897_ = l_Lean_Meta_recordUnfoldAxiom___redArg(v_constName_852_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_897_, 0);
lean_dec(v_unused_906_);
v___x_899_ = v___x_897_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_dec(v___x_897_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_907_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_897_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_897_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
default: 
{
lean_dec_ref_known(v___x_864_, 1);
lean_dec(v_val_865_);
lean_dec(v_constName_852_);
goto v___jp_858_;
}
}
}
else
{
lean_dec(v___x_864_);
lean_dec(v_constName_852_);
goto v___jp_858_;
}
v___jp_858_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(0);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getUnfoldableConstNoEx_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_852_ = stack[0].m_obj;
lean_object* v_a_853_ = stack[1].m_obj;
lean_object* v_a_854_ = stack[2].m_obj;
lean_object* v_a_855_ = stack[3].m_obj;
lean_object* v_a_856_ = stack[4].m_obj;
lean_object* v_res_915_;
v_res_915_ = l_Lean_Meta_getUnfoldableConstNoEx_x3f(v_constName_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
stack->m_obj
 = v_res_915_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(lean_object* v_constName_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_getUnfoldableConstNoEx_x3f(v_constName_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_922_;
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
