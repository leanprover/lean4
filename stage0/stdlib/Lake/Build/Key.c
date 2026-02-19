// Lean compiler output
// Module: Lake.Build.Key
// Imports: public import Init.Data.Order import Lake.Util.Name import Init.Data.String.Search import Init.Data.Iterators.Consumers
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
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lake_instInhabitedBuildKey_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedBuildKey_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedBuildKey_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedBuildKey_default = (const lean_object*)&l_Lake_instInhabitedBuildKey_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedBuildKey = (const lean_object*)&l_Lake_instInhabitedBuildKey_default___closed__0_value;
static const lean_string_object l_Lake_instReprBuildKey_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.BuildKey.module"};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__0 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__1 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__1_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__2 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__2_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_instReprBuildKey_repr___closed__3;
static lean_object* l_Lake_instReprBuildKey_repr___closed__4;
static const lean_string_object l_Lake_instReprBuildKey_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lake.BuildKey.package"};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__5 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__5_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__5_value)}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__6 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__7 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__7_value;
static const lean_string_object l_Lake_instReprBuildKey_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.BuildKey.packageModule"};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__8 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__8_value)}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__9 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__9_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__10 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__10_value;
static const lean_string_object l_Lake_instReprBuildKey_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lake.BuildKey.packageTarget"};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__11 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__11_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__11_value)}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__12 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__12_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__13 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__13_value;
static const lean_string_object l_Lake_instReprBuildKey_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lake.BuildKey.facet"};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__14 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__14_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__14_value)}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__15 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__15_value;
static const lean_ctor_object l_Lake_instReprBuildKey_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprBuildKey_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprBuildKey_repr___closed__16 = (const lean_object*)&l_Lake_instReprBuildKey_repr___closed__16_value;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprBuildKey_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprBuildKey___closed__0 = (const lean_object*)&l_Lake_instReprBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprBuildKey = (const lean_object*)&l_Lake_instReprBuildKey___closed__0_value;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static uint64_t l_Lake_instHashableBuildKey_hash___closed__0;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static uint64_t l_Lake_instHashableBuildKey_hash___closed__1;
static uint64_t l_Lake_instHashableBuildKey_hash___closed__2;
LEAN_EXPORT uint64_t l_Lake_instHashableBuildKey_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey_hash___boxed(lean_object*);
static const lean_closure_object l_Lake_instHashableBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instHashableBuildKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instHashableBuildKey___closed__0 = (const lean_object*)&l_Lake_instHashableBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instHashableBuildKey = (const lean_object*)&l_Lake_instHashableBuildKey___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object*);
static const lean_closure_object l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PartialBuildKey_mk___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PartialBuildKey_instCoeBuildKey___closed__0 = (const lean_object*)&l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instCoeBuildKey = (const lean_object*)&l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instRepr___private__1 = (const lean_object*)&l_Lake_instReprBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instRepr = (const lean_object*)&l_Lake_instReprBuildKey___closed__0_value;
static const lean_ctor_object l_Lake_PartialBuildKey_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_PartialBuildKey_instInhabited___closed__0 = (const lean_object*)&l_Lake_PartialBuildKey_instInhabited___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instInhabited = (const lean_object*)&l_Lake_PartialBuildKey_instInhabited___closed__0_value;
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1;
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "ill-formed target: default package targets are not supported in partial build keys"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed target: too many '/'"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2;
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "ill-formed target: expected module name after '+'"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PartialBuildKey_instInhabited___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value;
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value;
static lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object*);
static const lean_string_object l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed target: empty facet"};
static const lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0 = (const lean_object*)&l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value;
static const lean_ctor_object l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value)}};
static const lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1 = (const lean_object*)&l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object*, lean_object*);
static lean_object* l_Lake_PartialBuildKey_parse___closed__0;
static const lean_string_object l_Lake_PartialBuildKey_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.Build.Key"};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__1 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__1_value;
static const lean_string_object l_Lake_PartialBuildKey_parse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lake.PartialBuildKey.parse"};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__2 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__2_value;
static const lean_string_object l_Lake_PartialBuildKey_parse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__3 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__3_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PartialBuildKey_parse___closed__4;
static const lean_string_object l_Lake_PartialBuildKey_parse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed target: empty string"};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__5 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__5_value;
static const lean_ctor_object l_Lake_PartialBuildKey_parse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_PartialBuildKey_parse___closed__5_value)}};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__6 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object*);
static const lean_string_object l_Lake_PartialBuildKey_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "/+"};
static const lean_object* l_Lake_PartialBuildKey_toString___closed__0 = (const lean_object*)&l_Lake_PartialBuildKey_toString___closed__0_value;
static const lean_string_object l_Lake_PartialBuildKey_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_PartialBuildKey_toString___closed__1 = (const lean_object*)&l_Lake_PartialBuildKey_toString___closed__1_value;
static const lean_string_object l_Lake_PartialBuildKey_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_PartialBuildKey_toString___closed__2 = (const lean_object*)&l_Lake_PartialBuildKey_toString___closed__2_value;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
static const lean_closure_object l_Lake_PartialBuildKey_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PartialBuildKey_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PartialBuildKey_instToString___closed__0 = (const lean_object*)&l_Lake_PartialBuildKey_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instToString = (const lean_object*)&l_Lake_PartialBuildKey_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* l_Lake_Name_eraseHead(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
static const lean_closure_object l_Lake_BuildKey_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildKey_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildKey_instToString___closed__0 = (const lean_object*)&l_Lake_BuildKey_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildKey_instToString = (const lean_object*)&l_Lake_BuildKey_instToString___closed__0_value;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildKey_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
case 3:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_BuildKey_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_BuildKey_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildKey_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildKey_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildKey_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildKey_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildKey_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildKey_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildKey_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildKey_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildKey_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildKey_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_instReprBuildKey_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprBuildKey_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_14 = lean_unsigned_to_nat(1024u);
x_15 = lean_nat_dec_le(x_14, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lake_instReprBuildKey_repr___closed__3;
x_4 = x_16;
goto block_13;
}
else
{
lean_object* x_17; 
x_17 = l_Lake_instReprBuildKey_repr___closed__4;
x_4 = x_17;
goto block_13;
}
block_13:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__2));
x_6 = lean_unsigned_to_nat(1024u);
x_7 = l_Lean_Name_reprPrec(x_3, x_6);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_29; uint8_t x_30; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec_ref(x_1);
x_29 = lean_unsigned_to_nat(1024u);
x_30 = lean_nat_dec_le(x_29, x_2);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lake_instReprBuildKey_repr___closed__3;
x_19 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
x_32 = l_Lake_instReprBuildKey_repr___closed__4;
x_19 = x_32;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__7));
x_21 = lean_unsigned_to_nat(1024u);
x_22 = l_Lean_Name_reprPrec(x_18, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = 0;
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_27 = l_Repr_addAppParen(x_26, x_2);
return x_27;
}
}
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_50; uint8_t x_51; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_35 = x_1;
} else {
 lean_dec_ref(x_1);
 x_35 = lean_box(0);
}
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lake_instReprBuildKey_repr___closed__3;
x_36 = x_52;
goto block_49;
}
else
{
lean_object* x_53; 
x_53 = l_Lake_instReprBuildKey_repr___closed__4;
x_36 = x_53;
goto block_49;
}
block_49:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_box(1);
x_38 = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__10));
x_39 = lean_unsigned_to_nat(1024u);
x_40 = l_Lean_Name_reprPrec(x_33, x_39);
if (lean_is_scalar(x_35)) {
 x_41 = lean_alloc_ctor(5, 2, 0);
} else {
 x_41 = x_35;
 lean_ctor_set_tag(x_41, 5);
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = l_Lean_Name_reprPrec(x_34, x_39);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
x_46 = 0;
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = l_Repr_addAppParen(x_47, x_2);
return x_48;
}
}
case 3:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_71; uint8_t x_72; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_56 = x_1;
} else {
 lean_dec_ref(x_1);
 x_56 = lean_box(0);
}
x_71 = lean_unsigned_to_nat(1024u);
x_72 = lean_nat_dec_le(x_71, x_2);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Lake_instReprBuildKey_repr___closed__3;
x_57 = x_73;
goto block_70;
}
else
{
lean_object* x_74; 
x_74 = l_Lake_instReprBuildKey_repr___closed__4;
x_57 = x_74;
goto block_70;
}
block_70:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_box(1);
x_59 = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__13));
x_60 = lean_unsigned_to_nat(1024u);
x_61 = l_Lean_Name_reprPrec(x_54, x_60);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(5, 2, 0);
} else {
 x_62 = x_56;
 lean_ctor_set_tag(x_62, 5);
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
x_64 = l_Lean_Name_reprPrec(x_55, x_60);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
x_67 = 0;
x_68 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = l_Repr_addAppParen(x_68, x_2);
return x_69;
}
}
default: 
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_92; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_77 = x_1;
} else {
 lean_dec_ref(x_1);
 x_77 = lean_box(0);
}
x_78 = lean_unsigned_to_nat(1024u);
x_92 = lean_nat_dec_le(x_78, x_2);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = l_Lake_instReprBuildKey_repr___closed__3;
x_79 = x_93;
goto block_91;
}
else
{
lean_object* x_94; 
x_94 = l_Lake_instReprBuildKey_repr___closed__4;
x_79 = x_94;
goto block_91;
}
block_91:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_box(1);
x_81 = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__16));
x_82 = l_Lake_instReprBuildKey_repr(x_75, x_78);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(5, 2, 0);
} else {
 x_83 = x_77;
 lean_ctor_set_tag(x_83, 5);
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_85 = l_Lean_Name_reprPrec(x_76, x_78);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
x_88 = 0;
x_89 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = l_Repr_addAppParen(x_89, x_2);
return x_90;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instReprBuildKey_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_name_eq(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_name_eq(x_11, x_13);
if (x_15 == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_name_eq(x_12, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_name_eq(x_18, x_20);
if (x_22 == 0)
{
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_name_eq(x_19, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
default: 
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = l_Lake_instDecidableEqBuildKey_decEq(x_25, x_27);
if (x_29 == 0)
{
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_name_eq(x_26, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableEqBuildKey_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_instDecidableEqBuildKey_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableEqBuildKey(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint64_t _init_l_Lake_instHashableBuildKey_hash___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_instHashableBuildKey_hash___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lake_instHashableBuildKey_hash___closed__0;
x_2 = 0;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lake_instHashableBuildKey_hash___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lake_instHashableBuildKey_hash___closed__0;
x_2 = 1;
x_3 = lean_uint64_mix_hash(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashableBuildKey_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = 0;
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_4; 
x_4 = l_Lake_instHashableBuildKey_hash___closed__1;
return x_4;
}
else
{
uint64_t x_5; uint64_t x_6; 
x_5 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_6 = lean_uint64_mix_hash(x_3, x_5);
return x_6;
}
}
case 1:
{
lean_object* x_7; uint64_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
if (lean_obj_tag(x_7) == 0)
{
uint64_t x_9; 
x_9 = l_Lake_instHashableBuildKey_hash___closed__2;
return x_9;
}
else
{
uint64_t x_10; uint64_t x_11; 
x_10 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
x_11 = lean_uint64_mix_hash(x_8, x_10);
return x_11;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = 2;
if (lean_obj_tag(x_12) == 0)
{
uint64_t x_22; 
x_22 = l_Lake_instHashableBuildKey_hash___closed__0;
x_15 = x_22;
goto block_21;
}
else
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_12, sizeof(void*)*2);
x_15 = x_23;
goto block_21;
}
block_21:
{
uint64_t x_16; 
x_16 = lean_uint64_mix_hash(x_14, x_15);
if (lean_obj_tag(x_13) == 0)
{
uint64_t x_17; uint64_t x_18; 
x_17 = l_Lake_instHashableBuildKey_hash___closed__0;
x_18 = lean_uint64_mix_hash(x_16, x_17);
return x_18;
}
else
{
uint64_t x_19; uint64_t x_20; 
x_19 = lean_ctor_get_uint64(x_13, sizeof(void*)*2);
x_20 = lean_uint64_mix_hash(x_16, x_19);
return x_20;
}
}
}
case 3:
{
lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = 3;
if (lean_obj_tag(x_24) == 0)
{
uint64_t x_34; 
x_34 = l_Lake_instHashableBuildKey_hash___closed__0;
x_27 = x_34;
goto block_33;
}
else
{
uint64_t x_35; 
x_35 = lean_ctor_get_uint64(x_24, sizeof(void*)*2);
x_27 = x_35;
goto block_33;
}
block_33:
{
uint64_t x_28; 
x_28 = lean_uint64_mix_hash(x_26, x_27);
if (lean_obj_tag(x_25) == 0)
{
uint64_t x_29; uint64_t x_30; 
x_29 = l_Lake_instHashableBuildKey_hash___closed__0;
x_30 = lean_uint64_mix_hash(x_28, x_29);
return x_30;
}
else
{
uint64_t x_31; uint64_t x_32; 
x_31 = lean_ctor_get_uint64(x_25, sizeof(void*)*2);
x_32 = lean_uint64_mix_hash(x_28, x_31);
return x_32;
}
}
}
default: 
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_38 = 4;
x_39 = l_Lake_instHashableBuildKey_hash(x_36);
x_40 = lean_uint64_mix_hash(x_38, x_39);
if (lean_obj_tag(x_37) == 0)
{
uint64_t x_41; uint64_t x_42; 
x_41 = l_Lake_instHashableBuildKey_hash___closed__0;
x_42 = lean_uint64_mix_hash(x_40, x_41);
return x_42;
}
else
{
uint64_t x_43; uint64_t x_44; 
x_43 = lean_ctor_get_uint64(x_37, sizeof(void*)*2);
x_44 = lean_uint64_mix_hash(x_40, x_43);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_instHashableBuildKey_hash(x_1);
lean_dec_ref(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PartialBuildKey_mk(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_20 = lean_nat_sub(x_5, x_4);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
x_24 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1;
x_25 = lean_nat_dec_le(x_24, x_20);
lean_dec(x_20);
if (x_25 == 0)
{
x_6 = x_22;
goto block_19;
}
else
{
uint8_t x_26; 
x_26 = lean_string_memcmp(x_3, x_23, x_4, x_21, x_24);
x_6 = x_26;
goto block_19;
}
}
else
{
lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_1);
x_27 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3));
return x_27;
}
block_19:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_string_utf8_extract(x_3, x_4, x_5);
x_8 = l_Lake_stringToLegalOrSimpleName(x_7);
x_9 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_String_Slice_Pos_nextn(x_2, x_12, x_11);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_13);
x_15 = lean_string_utf8_extract(x_3, x_14, x_5);
lean_dec(x_14);
x_16 = l_Lake_stringToLegalOrSimpleName(x_15);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_nat_sub(x_17, x_16);
x_19 = lean_nat_dec_eq(x_15, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_20 = 47;
x_21 = lean_string_utf8_get_fast(x_1, x_15);
x_22 = lean_uint32_dec_eq(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_string_utf8_next_fast(x_1, x_15);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_23);
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_string_utf8_next_fast(x_1, x_15);
x_26 = lean_nat_sub(x_25, x_15);
x_27 = lean_nat_add(x_15, x_26);
lean_dec(x_26);
x_28 = l_String_Slice_subslice_x21(x_2, x_14, x_15);
lean_inc(x_27);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_6 = x_4;
x_7 = x_29;
x_8 = x_30;
goto block_12;
}
}
else
{
lean_object* x_31; 
lean_free_object(x_4);
lean_dec(x_15);
x_31 = lean_box(1);
lean_inc(x_3);
x_6 = x_31;
x_7 = x_14;
x_8 = x_3;
goto block_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_nat_sub(x_35, x_34);
x_37 = lean_nat_dec_eq(x_33, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint32_t x_38; uint32_t x_39; uint8_t x_40; 
x_38 = 47;
x_39 = lean_string_utf8_get_fast(x_1, x_33);
x_40 = lean_uint32_dec_eq(x_39, x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_string_utf8_next_fast(x_1, x_33);
lean_dec(x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_41);
x_4 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_string_utf8_next_fast(x_1, x_33);
x_45 = lean_nat_sub(x_44, x_33);
x_46 = lean_nat_add(x_33, x_45);
lean_dec(x_45);
x_47 = l_String_Slice_subslice_x21(x_2, x_32, x_33);
lean_inc(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec_ref(x_47);
x_6 = x_48;
x_7 = x_49;
x_8 = x_50;
goto block_12;
}
}
else
{
lean_object* x_51; 
lean_dec(x_33);
x_51 = lean_box(1);
lean_inc(x_3);
x_6 = x_51;
x_7 = x_32;
x_8 = x_3;
goto block_12;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_array_push(x_5, x_9);
x_4 = x_6;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object* x_1) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(x_6);
x_8 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2;
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(x_1, x_6, x_5, x_7, x_8);
lean_dec_ref(x_6);
x_10 = lean_array_to_list(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_46; uint8_t x_47; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_ctor_get(x_11, 2);
x_46 = lean_nat_sub(x_18, x_17);
x_47 = lean_nat_dec_eq(x_46, x_4);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
x_49 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7;
x_50 = lean_nat_dec_le(x_49, x_46);
lean_dec(x_46);
if (x_50 == 0)
{
x_19 = x_47;
goto block_45;
}
else
{
uint8_t x_51; 
x_51 = lean_string_memcmp(x_16, x_48, x_17, x_4, x_49);
x_19 = x_51;
goto block_45;
}
}
else
{
lean_object* x_52; 
lean_dec(x_46);
lean_dec(x_11);
x_52 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return x_52;
}
block_45:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
x_21 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1;
x_22 = lean_nat_sub(x_18, x_17);
x_23 = lean_nat_dec_le(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
goto block_15;
}
else
{
uint8_t x_24; 
x_24 = lean_string_memcmp(x_16, x_20, x_17, x_4, x_21);
if (x_24 == 0)
{
goto block_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_String_Slice_Pos_nextn(x_11, x_4, x_25);
lean_dec(x_11);
x_27 = lean_nat_add(x_17, x_26);
lean_dec(x_26);
lean_dec(x_17);
x_28 = lean_nat_sub(x_18, x_27);
x_29 = lean_nat_dec_eq(x_28, x_4);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_string_utf8_extract(x_16, x_27, x_18);
lean_dec(x_18);
lean_dec(x_27);
lean_dec_ref(x_16);
x_31 = l_Lake_stringToLegalOrSimpleName(x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec_ref(x_16);
x_34 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_String_Slice_Pos_nextn(x_11, x_4, x_35);
lean_dec(x_11);
x_37 = lean_nat_add(x_17, x_36);
lean_dec(x_36);
lean_dec(x_17);
x_38 = lean_nat_sub(x_18, x_37);
x_39 = lean_nat_dec_eq(x_38, x_4);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_string_utf8_extract(x_16, x_37, x_18);
lean_dec(x_18);
lean_dec(x_37);
lean_dec_ref(x_16);
x_41 = l_Lake_stringToLegalOrSimpleName(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_37);
lean_dec(x_18);
lean_dec_ref(x_16);
x_44 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return x_44;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_dec_ref(x_12);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_66 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_11, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_11, 2);
lean_inc(x_68);
x_69 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
x_70 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7;
x_71 = lean_nat_sub(x_68, x_67);
x_72 = lean_nat_dec_le(x_70, x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_11);
x_55 = x_66;
x_56 = x_67;
x_57 = x_68;
goto block_65;
}
else
{
uint8_t x_73; 
x_73 = lean_string_memcmp(x_66, x_69, x_67, x_4, x_70);
if (x_73 == 0)
{
lean_dec(x_11);
x_55 = x_66;
x_56 = x_67;
x_57 = x_68;
goto block_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = l_String_Slice_Pos_nextn(x_11, x_4, x_74);
lean_dec(x_11);
x_76 = lean_nat_add(x_67, x_75);
lean_dec(x_75);
lean_dec(x_67);
x_55 = x_66;
x_56 = x_76;
x_57 = x_68;
goto block_65;
}
}
}
else
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_11);
goto block_3;
}
block_65:
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_nat_sub(x_57, x_56);
x_59 = lean_nat_dec_eq(x_58, x_4);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_string_utf8_extract(x_55, x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
x_61 = l_Lake_stringToLegalOrSimpleName(x_60);
x_62 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(x_61, x_53);
lean_dec(x_53);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_55);
x_63 = lean_box(0);
x_64 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(x_63, x_53);
lean_dec(x_53);
return x_64;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(x_13, x_11);
lean_dec(x_11);
return x_14;
}
}
else
{
lean_dec(x_10);
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1));
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_panic_fn(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_nat_sub(x_18, x_17);
x_20 = lean_nat_dec_eq(x_16, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_21 = 58;
x_22 = lean_string_utf8_get_fast(x_1, x_16);
x_23 = lean_uint32_dec_eq(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_string_utf8_next_fast(x_1, x_16);
lean_dec(x_16);
lean_ctor_set(x_4, 1, x_24);
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_string_utf8_next_fast(x_1, x_16);
x_27 = lean_nat_sub(x_26, x_16);
x_28 = lean_nat_add(x_16, x_27);
lean_dec(x_27);
x_29 = l_String_Slice_subslice_x21(x_2, x_15, x_16);
lean_inc(x_28);
lean_ctor_set(x_4, 1, x_28);
lean_ctor_set(x_4, 0, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_6 = x_4;
x_7 = x_30;
x_8 = x_31;
goto block_13;
}
}
else
{
lean_object* x_32; 
lean_free_object(x_4);
lean_dec(x_16);
x_32 = lean_box(1);
lean_inc(x_3);
x_6 = x_32;
x_7 = x_15;
x_8 = x_3;
goto block_13;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_nat_sub(x_36, x_35);
x_38 = lean_nat_dec_eq(x_34, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint32_t x_39; uint32_t x_40; uint8_t x_41; 
x_39 = 58;
x_40 = lean_string_utf8_get_fast(x_1, x_34);
x_41 = lean_uint32_dec_eq(x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_string_utf8_next_fast(x_1, x_34);
lean_dec(x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_4 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_string_utf8_next_fast(x_1, x_34);
x_46 = lean_nat_sub(x_45, x_34);
x_47 = lean_nat_add(x_34, x_46);
lean_dec(x_46);
x_48 = l_String_Slice_subslice_x21(x_2, x_33, x_34);
lean_inc(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec_ref(x_48);
x_6 = x_49;
x_7 = x_50;
x_8 = x_51;
goto block_13;
}
}
else
{
lean_object* x_52; 
lean_dec(x_34);
x_52 = lean_box(1);
lean_inc(x_3);
x_6 = x_52;
x_7 = x_33;
x_8 = x_3;
goto block_13;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = l_String_Slice_toString(x_9);
lean_dec_ref(x_9);
x_11 = lean_array_push(x_5, x_10);
x_4 = x_6;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_string_utf8_byte_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lake_stringToLegalOrSimpleName(x_5);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_1);
x_1 = x_2;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_12; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_string_utf8_byte_size(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lake_stringToLegalOrSimpleName(x_13);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_1 = x_19;
x_2 = x_14;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_21 = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return x_21;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(65u);
x_4 = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
x_5 = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
x_6 = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(x_5);
x_7 = l_Lake_PartialBuildKey_parse___closed__0;
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(x_1, x_5, x_2, x_6, x_7);
lean_dec_ref(x_5);
x_9 = lean_array_to_list(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lake_PartialBuildKey_parse___closed__4;
x_11 = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec_ref(x_9);
x_14 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(x_15, x_13);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 2:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_inc(x_2);
return x_2;
}
}
default: 
{
lean_inc(x_1);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
x_4 = 1;
x_5 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
x_11 = 1;
x_12 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_8, x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
x_18 = 1;
x_19 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_15, x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec_ref(x_19);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = 1;
x_22 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_16, x_21);
x_23 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_15, x_21);
x_26 = lean_string_append(x_24, x_25);
lean_dec_ref(x_25);
return x_26;
}
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec_ref(x_1);
x_29 = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; lean_object* x_31; 
x_30 = 1;
x_31 = l_Lean_Name_toString(x_28, x_30);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = 1;
x_33 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_29, x_32);
x_34 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_28, x_32);
x_37 = lean_string_append(x_35, x_36);
lean_dec_ref(x_36);
return x_37;
}
}
default: 
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_dec_ref(x_1);
x_40 = l_Lean_Name_isAnonymous(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = l_Lake_PartialBuildKey_toString(x_38);
x_42 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
x_43 = lean_string_append(x_41, x_42);
x_44 = 1;
x_45 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_39, x_44);
x_46 = lean_string_append(x_43, x_45);
lean_dec_ref(x_45);
return x_46;
}
else
{
lean_dec(x_39);
x_1 = x_38;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
x_4 = 1;
x_5 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_4);
x_6 = lean_string_append(x_3, x_5);
lean_dec_ref(x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
x_9 = l_Lean_Name_getPrefix(x_7);
lean_dec(x_7);
x_10 = 1;
x_11 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_9, x_10);
x_12 = lean_string_append(x_8, x_11);
lean_dec_ref(x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec_ref(x_1);
x_15 = l_Lean_Name_getPrefix(x_13);
lean_dec(x_13);
x_16 = 1;
x_17 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_15, x_16);
x_18 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_14, x_16);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
return x_21;
}
case 3:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = l_Lean_Name_getPrefix(x_22);
lean_dec(x_22);
x_25 = 1;
x_26 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_24, x_25);
x_27 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_23, x_25);
x_30 = lean_string_append(x_28, x_29);
lean_dec_ref(x_29);
return x_30;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec_ref(x_1);
x_33 = l_Lake_BuildKey_toString(x_31);
x_34 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lake_Name_eraseHead(x_32);
x_37 = 1;
x_38 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_36, x_37);
x_39 = lean_string_append(x_35, x_38);
lean_dec_ref(x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = 1;
x_14 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_12, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = l_Lean_Name_getPrefix(x_15);
lean_dec(x_15);
x_17 = 1;
x_18 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_16, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec_ref(x_1);
x_21 = l_Lake_BuildKey_toSimpleString(x_19);
x_22 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Lake_Name_eraseHead(x_20);
x_25 = 1;
x_26 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_24, x_25);
x_27 = lean_string_append(x_23, x_26);
lean_dec_ref(x_26);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec_ref(x_1);
x_2 = x_28;
x_3 = x_29;
goto block_11;
}
}
block_11:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Name_getPrefix(x_2);
lean_dec(x_2);
x_5 = 1;
x_6 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_4, x_5);
x_7 = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_3, x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec_ref(x_9);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_7; 
x_7 = 2;
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_8, x_9);
return x_10;
}
default: 
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
case 3:
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_15, x_17);
if (x_18 == 1)
{
uint8_t x_19; 
x_19 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_14, x_16);
return x_19;
}
else
{
return x_18;
}
}
default: 
{
uint8_t x_20; 
x_20 = 2;
return x_20;
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
case 3:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_22, x_24);
if (x_26 == 1)
{
uint8_t x_27; 
x_27 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_23, x_25);
return x_27;
}
else
{
return x_26;
}
}
default: 
{
uint8_t x_28; 
x_28 = 2;
return x_28;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
x_33 = l_Lake_BuildKey_quickCmp(x_29, x_31);
if (x_33 == 1)
{
uint8_t x_34; 
x_34 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_30, x_32);
return x_34;
}
else
{
return x_33;
}
}
else
{
uint8_t x_35; 
x_35 = 2;
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_BuildKey_quickCmp(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
case 3:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_apply_2(x_5, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec_ref(x_1);
x_19 = lean_apply_2(x_6, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_apply_2(x_3, x_9, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_apply_2(x_4, x_12, x_13);
return x_14;
}
default: 
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_apply_4(x_5, x_1, lean_box(0), lean_box(0), lean_box(0));
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = lean_apply_2(x_4, x_10, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = lean_apply_2(x_5, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_apply_4(x_6, x_2, lean_box(0), lean_box(0), lean_box(0));
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(x_1);
x_7 = lean_apply_2(x_3, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(x_2);
x_8 = lean_apply_2(x_4, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_2(x_3, x_8, x_9);
return x_10;
}
default: 
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_apply_3(x_4, x_1, lean_box(0), lean_box(0));
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_apply_2(x_4, x_9, x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_apply_3(x_5, x_2, lean_box(0), lean_box(0));
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_2(x_3, x_1, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_apply_2(x_3, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_apply_2(x_4, x_2, lean_box(0));
return x_8;
}
}
}
lean_object* initialize_Init_Data_Order(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Key(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instReprBuildKey_repr___closed__3 = _init_l_Lake_instReprBuildKey_repr___closed__3();
lean_mark_persistent(l_Lake_instReprBuildKey_repr___closed__3);
l_Lake_instReprBuildKey_repr___closed__4 = _init_l_Lake_instReprBuildKey_repr___closed__4();
lean_mark_persistent(l_Lake_instReprBuildKey_repr___closed__4);
l_Lake_instHashableBuildKey_hash___closed__0 = _init_l_Lake_instHashableBuildKey_hash___closed__0();
l_Lake_instHashableBuildKey_hash___closed__1 = _init_l_Lake_instHashableBuildKey_hash___closed__1();
l_Lake_instHashableBuildKey_hash___closed__2 = _init_l_Lake_instHashableBuildKey_hash___closed__2();
l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1 = _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1();
lean_mark_persistent(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2 = _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2();
lean_mark_persistent(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2);
l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7 = _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7();
lean_mark_persistent(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
l_Lake_PartialBuildKey_parse___closed__0 = _init_l_Lake_PartialBuildKey_parse___closed__0();
lean_mark_persistent(l_Lake_PartialBuildKey_parse___closed__0);
l_Lake_PartialBuildKey_parse___closed__4 = _init_l_Lake_PartialBuildKey_parse___closed__4();
lean_mark_persistent(l_Lake_PartialBuildKey_parse___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
