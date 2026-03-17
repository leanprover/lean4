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
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lake_Name_eraseHead(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_instReprBuildKey_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBuildKey_repr___closed__3;
static lean_once_cell_t l_Lake_instReprBuildKey_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprBuildKey_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprBuildKey___closed__0 = (const lean_object*)&l_Lake_instReprBuildKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprBuildKey = (const lean_object*)&l_Lake_instReprBuildKey___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instHashableBuildKey_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_instHashableBuildKey_hash___closed__0;
static lean_once_cell_t l_Lake_instHashableBuildKey_hash___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lake_instHashableBuildKey_hash___closed__1;
static lean_once_cell_t l_Lake_instHashableBuildKey_hash___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1;
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "ill-formed target: default package targets are not supported in partial build keys"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed target: too many '/'"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value;
static const lean_array_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2_value;
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "ill-formed target: expected module name after '+'"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PartialBuildKey_instInhabited___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value;
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value;
static lean_once_cell_t l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object*);
static const lean_string_object l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0 = (const lean_object*)&l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed target: empty facet"};
static const lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0 = (const lean_object*)&l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value;
static const lean_ctor_object l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value)}};
static const lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1 = (const lean_object*)&l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object*, lean_object*);
static const lean_array_object l_Lake_PartialBuildKey_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__0 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__0_value;
static const lean_string_object l_Lake_PartialBuildKey_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.Build.Key"};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__1 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__1_value;
static const lean_string_object l_Lake_PartialBuildKey_parse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lake.PartialBuildKey.parse"};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__2 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__2_value;
static const lean_string_object l_Lake_PartialBuildKey_parse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lake_PartialBuildKey_parse___closed__3 = (const lean_object*)&l_Lake_PartialBuildKey_parse___closed__3_value;
static lean_once_cell_t l_Lake_PartialBuildKey_parse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
static const lean_closure_object l_Lake_PartialBuildKey_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_PartialBuildKey_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PartialBuildKey_instToString___closed__0 = (const lean_object*)&l_Lake_PartialBuildKey_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instToString = (const lean_object*)&l_Lake_PartialBuildKey_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object*);
static const lean_closure_object l_Lake_BuildKey_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildKey_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildKey_instToString___closed__0 = (const lean_object*)&l_Lake_BuildKey_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildKey_instToString = (const lean_object*)&l_Lake_BuildKey_instToString___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lake_BuildKey_ctorIdx(v_x_7_);
lean_dec_ref(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___redArg(lean_object* v_t_9_, lean_object* v_k_10_){
_start:
{
switch(lean_obj_tag(v_t_9_))
{
case 2:
{
lean_object* v_package_11_; lean_object* v_module_12_; lean_object* v___x_13_; 
v_package_11_ = lean_ctor_get(v_t_9_, 0);
lean_inc(v_package_11_);
v_module_12_ = lean_ctor_get(v_t_9_, 1);
lean_inc(v_module_12_);
lean_dec_ref(v_t_9_);
v___x_13_ = lean_apply_2(v_k_10_, v_package_11_, v_module_12_);
return v___x_13_;
}
case 3:
{
lean_object* v_package_14_; lean_object* v_target_15_; lean_object* v___x_16_; 
v_package_14_ = lean_ctor_get(v_t_9_, 0);
lean_inc(v_package_14_);
v_target_15_ = lean_ctor_get(v_t_9_, 1);
lean_inc(v_target_15_);
lean_dec_ref(v_t_9_);
v___x_16_ = lean_apply_2(v_k_10_, v_package_14_, v_target_15_);
return v___x_16_;
}
case 4:
{
lean_object* v_target_17_; lean_object* v_facet_18_; lean_object* v___x_19_; 
v_target_17_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_target_17_);
v_facet_18_ = lean_ctor_get(v_t_9_, 1);
lean_inc(v_facet_18_);
lean_dec_ref(v_t_9_);
v___x_19_ = lean_apply_2(v_k_10_, v_target_17_, v_facet_18_);
return v___x_19_;
}
default: 
{
lean_object* v_module_20_; lean_object* v___x_21_; 
v_module_20_ = lean_ctor_get(v_t_9_, 0);
lean_inc(v_module_20_);
lean_dec_ref(v_t_9_);
v___x_21_ = lean_apply_1(v_k_10_, v_module_20_);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lake_BuildKey_ctorElim___redArg(v_t_24_, v_k_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___boxed(lean_object* v_motive_28_, lean_object* v_ctorIdx_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_k_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lake_BuildKey_ctorElim(v_motive_28_, v_ctorIdx_29_, v_t_30_, v_h_31_, v_k_32_);
lean_dec(v_ctorIdx_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim___redArg(lean_object* v_t_34_, lean_object* v_module_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lake_BuildKey_ctorElim___redArg(v_t_34_, v_module_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_module_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lake_BuildKey_ctorElim___redArg(v_t_38_, v_module_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim___redArg(lean_object* v_t_42_, lean_object* v_package_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lake_BuildKey_ctorElim___redArg(v_t_42_, v_package_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_package_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lake_BuildKey_ctorElim___redArg(v_t_46_, v_package_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim___redArg(lean_object* v_t_50_, lean_object* v_packageModule_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lake_BuildKey_ctorElim___redArg(v_t_50_, v_packageModule_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim(lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_packageModule_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lake_BuildKey_ctorElim___redArg(v_t_54_, v_packageModule_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim___redArg(lean_object* v_t_58_, lean_object* v_packageTarget_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lake_BuildKey_ctorElim___redArg(v_t_58_, v_packageTarget_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_packageTarget_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lake_BuildKey_ctorElim___redArg(v_t_62_, v_packageTarget_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim___redArg(lean_object* v_t_66_, lean_object* v_facet_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lake_BuildKey_ctorElim___redArg(v_t_66_, v_facet_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_facet_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lake_BuildKey_ctorElim___redArg(v_t_70_, v_facet_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lake_instReprBuildKey_repr___closed__3(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(2u);
v___x_85_ = lean_nat_to_int(v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Lake_instReprBuildKey_repr___closed__4(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_to_int(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr(lean_object* v_x_112_, lean_object* v_prec_113_){
_start:
{
switch(lean_obj_tag(v_x_112_))
{
case 0:
{
lean_object* v_module_114_; lean_object* v___y_116_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_module_114_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_module_114_);
lean_dec_ref(v_x_112_);
v___x_125_ = lean_unsigned_to_nat(1024u);
v___x_126_ = lean_nat_dec_le(v___x_125_, v_prec_113_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_116_ = v___x_127_;
goto v___jp_115_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_116_ = v___x_128_;
goto v___jp_115_;
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_117_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__2));
v___x_118_ = lean_unsigned_to_nat(1024u);
v___x_119_ = l_Lean_Name_reprPrec(v_module_114_, v___x_118_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_117_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___y_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = 0;
v___x_123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_122_);
v___x_124_ = l_Repr_addAppParen(v___x_123_, v_prec_113_);
return v___x_124_;
}
}
case 1:
{
lean_object* v_package_129_; lean_object* v___y_131_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_package_129_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_package_129_);
lean_dec_ref(v_x_112_);
v___x_140_ = lean_unsigned_to_nat(1024u);
v___x_141_ = lean_nat_dec_le(v___x_140_, v_prec_113_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_131_ = v___x_142_;
goto v___jp_130_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_131_ = v___x_143_;
goto v___jp_130_;
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_132_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__7));
v___x_133_ = lean_unsigned_to_nat(1024u);
v___x_134_ = l_Lean_Name_reprPrec(v_package_129_, v___x_133_);
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_132_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_136_, 0, v___y_131_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = 0;
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_137_);
v___x_139_ = l_Repr_addAppParen(v___x_138_, v_prec_113_);
return v___x_139_;
}
}
case 2:
{
lean_object* v_package_144_; lean_object* v_module_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_169_; 
v_package_144_ = lean_ctor_get(v_x_112_, 0);
v_module_145_ = lean_ctor_get(v_x_112_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_169_ == 0)
{
v___x_147_ = v_x_112_;
v_isShared_148_ = v_isSharedCheck_169_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_module_145_);
lean_inc(v_package_144_);
lean_dec(v_x_112_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_169_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___y_150_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1024u);
v___x_166_ = lean_nat_dec_le(v___x_165_, v_prec_113_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_150_ = v___x_167_;
goto v___jp_149_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_150_ = v___x_168_;
goto v___jp_149_;
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_151_ = lean_box(1);
v___x_152_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__10));
v___x_153_ = lean_unsigned_to_nat(1024u);
v___x_154_ = l_Lean_Name_reprPrec(v_package_144_, v___x_153_);
if (v_isShared_148_ == 0)
{
lean_ctor_set_tag(v___x_147_, 5);
lean_ctor_set(v___x_147_, 1, v___x_154_);
lean_ctor_set(v___x_147_, 0, v___x_152_);
v___x_156_ = v___x_147_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v___x_154_);
v___x_156_ = v_reuseFailAlloc_164_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_151_);
v___x_158_ = l_Lean_Name_reprPrec(v_module_145_, v___x_153_);
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_160_, 0, v___y_150_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = 0;
v___x_162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_161_);
v___x_163_ = l_Repr_addAppParen(v___x_162_, v_prec_113_);
return v___x_163_;
}
}
}
}
case 3:
{
lean_object* v_package_170_; lean_object* v_target_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_195_; 
v_package_170_ = lean_ctor_get(v_x_112_, 0);
v_target_171_ = lean_ctor_get(v_x_112_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_195_ == 0)
{
v___x_173_ = v_x_112_;
v_isShared_174_ = v_isSharedCheck_195_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_target_171_);
lean_inc(v_package_170_);
lean_dec(v_x_112_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_195_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___y_176_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(1024u);
v___x_192_ = lean_nat_dec_le(v___x_191_, v_prec_113_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_176_ = v___x_193_;
goto v___jp_175_;
}
else
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_176_ = v___x_194_;
goto v___jp_175_;
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_177_ = lean_box(1);
v___x_178_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__13));
v___x_179_ = lean_unsigned_to_nat(1024u);
v___x_180_ = l_Lean_Name_reprPrec(v_package_170_, v___x_179_);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 5);
lean_ctor_set(v___x_173_, 1, v___x_180_);
lean_ctor_set(v___x_173_, 0, v___x_178_);
v___x_182_ = v___x_173_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_190_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_177_);
v___x_184_ = l_Lean_Name_reprPrec(v_target_171_, v___x_179_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_186_, 0, v___y_176_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = 0;
v___x_188_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set_uint8(v___x_188_, sizeof(void*)*1, v___x_187_);
v___x_189_ = l_Repr_addAppParen(v___x_188_, v_prec_113_);
return v___x_189_;
}
}
}
}
default: 
{
lean_object* v_target_196_; lean_object* v_facet_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_220_; 
v_target_196_ = lean_ctor_get(v_x_112_, 0);
v_facet_197_ = lean_ctor_get(v_x_112_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_220_ == 0)
{
v___x_199_ = v_x_112_;
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_facet_197_);
lean_inc(v_target_196_);
lean_dec(v_x_112_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___y_203_; uint8_t v___x_217_; 
v___x_201_ = lean_unsigned_to_nat(1024u);
v___x_217_ = lean_nat_dec_le(v___x_201_, v_prec_113_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_203_ = v___x_218_;
goto v___jp_202_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_203_ = v___x_219_;
goto v___jp_202_;
}
v___jp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_204_ = lean_box(1);
v___x_205_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__16));
v___x_206_ = l_Lake_instReprBuildKey_repr(v_target_196_, v___x_201_);
if (v_isShared_200_ == 0)
{
lean_ctor_set_tag(v___x_199_, 5);
lean_ctor_set(v___x_199_, 1, v___x_206_);
lean_ctor_set(v___x_199_, 0, v___x_205_);
v___x_208_ = v___x_199_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_206_);
v___x_208_ = v_reuseFailAlloc_216_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_204_);
v___x_210_ = l_Lean_Name_reprPrec(v_facet_197_, v___x_201_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___y_203_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = 0;
v___x_214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_213_);
v___x_215_ = l_Repr_addAppParen(v___x_214_, v_prec_113_);
return v___x_215_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr___boxed(lean_object* v_x_221_, lean_object* v_prec_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lake_instReprBuildKey_repr(v_x_221_, v_prec_222_);
lean_dec(v_prec_222_);
return v_res_223_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
switch(lean_obj_tag(v_x_226_))
{
case 0:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v_module_228_; lean_object* v_module_229_; uint8_t v___x_230_; 
v_module_228_ = lean_ctor_get(v_x_226_, 0);
v_module_229_ = lean_ctor_get(v_x_227_, 0);
v___x_230_ = lean_name_eq(v_module_228_, v_module_229_);
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
}
case 1:
{
if (lean_obj_tag(v_x_227_) == 1)
{
lean_object* v_package_232_; lean_object* v_package_233_; uint8_t v___x_234_; 
v_package_232_ = lean_ctor_get(v_x_226_, 0);
v_package_233_ = lean_ctor_get(v_x_227_, 0);
v___x_234_ = lean_name_eq(v_package_232_, v_package_233_);
return v___x_234_;
}
else
{
uint8_t v___x_235_; 
v___x_235_ = 0;
return v___x_235_;
}
}
case 2:
{
if (lean_obj_tag(v_x_227_) == 2)
{
lean_object* v_package_236_; lean_object* v_module_237_; lean_object* v_package_238_; lean_object* v_module_239_; uint8_t v___x_240_; 
v_package_236_ = lean_ctor_get(v_x_226_, 0);
v_module_237_ = lean_ctor_get(v_x_226_, 1);
v_package_238_ = lean_ctor_get(v_x_227_, 0);
v_module_239_ = lean_ctor_get(v_x_227_, 1);
v___x_240_ = lean_name_eq(v_package_236_, v_package_238_);
if (v___x_240_ == 0)
{
return v___x_240_;
}
else
{
uint8_t v___x_241_; 
v___x_241_ = lean_name_eq(v_module_237_, v_module_239_);
return v___x_241_;
}
}
else
{
uint8_t v___x_242_; 
v___x_242_ = 0;
return v___x_242_;
}
}
case 3:
{
if (lean_obj_tag(v_x_227_) == 3)
{
lean_object* v_package_243_; lean_object* v_target_244_; lean_object* v_package_245_; lean_object* v_target_246_; uint8_t v___x_247_; 
v_package_243_ = lean_ctor_get(v_x_226_, 0);
v_target_244_ = lean_ctor_get(v_x_226_, 1);
v_package_245_ = lean_ctor_get(v_x_227_, 0);
v_target_246_ = lean_ctor_get(v_x_227_, 1);
v___x_247_ = lean_name_eq(v_package_243_, v_package_245_);
if (v___x_247_ == 0)
{
return v___x_247_;
}
else
{
uint8_t v___x_248_; 
v___x_248_ = lean_name_eq(v_target_244_, v_target_246_);
return v___x_248_;
}
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
}
default: 
{
if (lean_obj_tag(v_x_227_) == 4)
{
lean_object* v_target_250_; lean_object* v_facet_251_; lean_object* v_target_252_; lean_object* v_facet_253_; uint8_t v_inst_254_; 
v_target_250_ = lean_ctor_get(v_x_226_, 0);
v_facet_251_ = lean_ctor_get(v_x_226_, 1);
v_target_252_ = lean_ctor_get(v_x_227_, 0);
v_facet_253_ = lean_ctor_get(v_x_227_, 1);
v_inst_254_ = l_Lake_instDecidableEqBuildKey_decEq(v_target_250_, v_target_252_);
if (v_inst_254_ == 0)
{
return v_inst_254_;
}
else
{
uint8_t v___x_255_; 
v___x_255_ = lean_name_eq(v_facet_251_, v_facet_253_);
return v___x_255_;
}
}
else
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey_decEq___boxed(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_257_, v_x_258_);
lean_dec_ref(v_x_258_);
lean_dec_ref(v_x_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildKey(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
uint8_t v___x_263_; 
v___x_263_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_261_, v_x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Lake_instDecidableEqBuildKey(v_x_264_, v_x_265_);
lean_dec_ref(v_x_265_);
lean_dec_ref(v_x_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
static uint64_t _init_l_Lake_instHashableBuildKey_hash___closed__0(void){
_start:
{
lean_object* v___x_268_; uint64_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1723u);
v___x_269_ = lean_uint64_of_nat(v___x_268_);
return v___x_269_;
}
}
static uint64_t _init_l_Lake_instHashableBuildKey_hash___closed__1(void){
_start:
{
uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; 
v___x_270_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
v___x_271_ = 0ULL;
v___x_272_ = lean_uint64_mix_hash(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static uint64_t _init_l_Lake_instHashableBuildKey_hash___closed__2(void){
_start:
{
uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; 
v___x_273_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
v___x_274_ = 1ULL;
v___x_275_ = lean_uint64_mix_hash(v___x_274_, v___x_273_);
return v___x_275_;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashableBuildKey_hash(lean_object* v_x_276_){
_start:
{
switch(lean_obj_tag(v_x_276_))
{
case 0:
{
lean_object* v_module_277_; uint64_t v___x_278_; 
v_module_277_ = lean_ctor_get(v_x_276_, 0);
v___x_278_ = 0ULL;
if (lean_obj_tag(v_module_277_) == 0)
{
uint64_t v___x_279_; 
v___x_279_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__1, &l_Lake_instHashableBuildKey_hash___closed__1_once, _init_l_Lake_instHashableBuildKey_hash___closed__1);
return v___x_279_;
}
else
{
uint64_t v_hash_280_; uint64_t v___x_281_; 
v_hash_280_ = lean_ctor_get_uint64(v_module_277_, sizeof(void*)*2);
v___x_281_ = lean_uint64_mix_hash(v___x_278_, v_hash_280_);
return v___x_281_;
}
}
case 1:
{
lean_object* v_package_282_; uint64_t v___x_283_; 
v_package_282_ = lean_ctor_get(v_x_276_, 0);
v___x_283_ = 1ULL;
if (lean_obj_tag(v_package_282_) == 0)
{
uint64_t v___x_284_; 
v___x_284_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__2, &l_Lake_instHashableBuildKey_hash___closed__2_once, _init_l_Lake_instHashableBuildKey_hash___closed__2);
return v___x_284_;
}
else
{
uint64_t v_hash_285_; uint64_t v___x_286_; 
v_hash_285_ = lean_ctor_get_uint64(v_package_282_, sizeof(void*)*2);
v___x_286_ = lean_uint64_mix_hash(v___x_283_, v_hash_285_);
return v___x_286_;
}
}
case 2:
{
lean_object* v_package_287_; lean_object* v_module_288_; uint64_t v___x_289_; uint64_t v___y_291_; 
v_package_287_ = lean_ctor_get(v_x_276_, 0);
v_module_288_ = lean_ctor_get(v_x_276_, 1);
v___x_289_ = 2ULL;
if (lean_obj_tag(v_package_287_) == 0)
{
uint64_t v___x_297_; 
v___x_297_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
v___y_291_ = v___x_297_;
goto v___jp_290_;
}
else
{
uint64_t v_hash_298_; 
v_hash_298_ = lean_ctor_get_uint64(v_package_287_, sizeof(void*)*2);
v___y_291_ = v_hash_298_;
goto v___jp_290_;
}
v___jp_290_:
{
uint64_t v___x_292_; 
v___x_292_ = lean_uint64_mix_hash(v___x_289_, v___y_291_);
if (lean_obj_tag(v_module_288_) == 0)
{
uint64_t v___x_293_; uint64_t v___x_294_; 
v___x_293_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
v___x_294_ = lean_uint64_mix_hash(v___x_292_, v___x_293_);
return v___x_294_;
}
else
{
uint64_t v_hash_295_; uint64_t v___x_296_; 
v_hash_295_ = lean_ctor_get_uint64(v_module_288_, sizeof(void*)*2);
v___x_296_ = lean_uint64_mix_hash(v___x_292_, v_hash_295_);
return v___x_296_;
}
}
}
case 3:
{
lean_object* v_package_299_; lean_object* v_target_300_; uint64_t v___x_301_; uint64_t v___y_303_; 
v_package_299_ = lean_ctor_get(v_x_276_, 0);
v_target_300_ = lean_ctor_get(v_x_276_, 1);
v___x_301_ = 3ULL;
if (lean_obj_tag(v_package_299_) == 0)
{
uint64_t v___x_309_; 
v___x_309_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
v___y_303_ = v___x_309_;
goto v___jp_302_;
}
else
{
uint64_t v_hash_310_; 
v_hash_310_ = lean_ctor_get_uint64(v_package_299_, sizeof(void*)*2);
v___y_303_ = v_hash_310_;
goto v___jp_302_;
}
v___jp_302_:
{
uint64_t v___x_304_; 
v___x_304_ = lean_uint64_mix_hash(v___x_301_, v___y_303_);
if (lean_obj_tag(v_target_300_) == 0)
{
uint64_t v___x_305_; uint64_t v___x_306_; 
v___x_305_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
v___x_306_ = lean_uint64_mix_hash(v___x_304_, v___x_305_);
return v___x_306_;
}
else
{
uint64_t v_hash_307_; uint64_t v___x_308_; 
v_hash_307_ = lean_ctor_get_uint64(v_target_300_, sizeof(void*)*2);
v___x_308_ = lean_uint64_mix_hash(v___x_304_, v_hash_307_);
return v___x_308_;
}
}
}
default: 
{
lean_object* v_target_311_; lean_object* v_facet_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v___x_315_; 
v_target_311_ = lean_ctor_get(v_x_276_, 0);
v_facet_312_ = lean_ctor_get(v_x_276_, 1);
v___x_313_ = 4ULL;
v___x_314_ = l_Lake_instHashableBuildKey_hash(v_target_311_);
v___x_315_ = lean_uint64_mix_hash(v___x_313_, v___x_314_);
if (lean_obj_tag(v_facet_312_) == 0)
{
uint64_t v___x_316_; uint64_t v___x_317_; 
v___x_316_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
v___x_317_ = lean_uint64_mix_hash(v___x_315_, v___x_316_);
return v___x_317_;
}
else
{
uint64_t v_hash_318_; uint64_t v___x_319_; 
v_hash_318_ = lean_ctor_get_uint64(v_facet_312_, sizeof(void*)*2);
v___x_319_ = lean_uint64_mix_hash(v___x_315_, v_hash_318_);
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey_hash___boxed(lean_object* v_x_320_){
_start:
{
uint64_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Lake_instHashableBuildKey_hash(v_x_320_);
lean_dec_ref(v_x_320_);
v_r_322_ = lean_box_uint64(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object* v_key_325_){
_start:
{
lean_inc_ref(v_key_325_);
return v_key_325_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object* v_key_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lake_PartialBuildKey_mk(v_key_326_);
lean_dec_ref(v_key_326_);
return v_res_327_;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_337_ = lean_string_utf8_byte_size(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* v_pkg_341_, lean_object* v_target_342_){
_start:
{
lean_object* v_str_343_; lean_object* v_startInclusive_344_; lean_object* v_endExclusive_345_; uint8_t v___y_347_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_str_343_ = lean_ctor_get(v_target_342_, 0);
v_startInclusive_344_ = lean_ctor_get(v_target_342_, 1);
v_endExclusive_345_ = lean_ctor_get(v_target_342_, 2);
v___x_360_ = lean_nat_sub(v_endExclusive_345_, v_startInclusive_344_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_363_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_364_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_365_ = lean_nat_dec_le(v___x_364_, v___x_360_);
lean_dec(v___x_360_);
if (v___x_365_ == 0)
{
v___y_347_ = v___x_362_;
goto v___jp_346_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = lean_string_memcmp(v_str_343_, v___x_363_, v_startInclusive_344_, v___x_361_, v___x_364_);
v___y_347_ = v___x_366_;
goto v___jp_346_;
}
}
else
{
lean_object* v___x_367_; 
lean_dec(v___x_360_);
lean_dec(v_pkg_341_);
v___x_367_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3));
return v___x_367_;
}
v___jp_346_:
{
if (v___y_347_ == 0)
{
lean_object* v___x_348_; lean_object* v_target_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_348_ = lean_string_utf8_extract(v_str_343_, v_startInclusive_344_, v_endExclusive_345_);
v_target_349_ = l_Lake_stringToLegalOrSimpleName(v___x_348_);
v___x_350_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_350_, 0, v_pkg_341_);
lean_ctor_set(v___x_350_, 1, v_target_349_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_target_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_String_Slice_Pos_nextn(v_target_342_, v___x_353_, v___x_352_);
v___x_355_ = lean_nat_add(v_startInclusive_344_, v___x_354_);
lean_dec(v___x_354_);
v___x_356_ = lean_string_utf8_extract(v_str_343_, v___x_355_, v_endExclusive_345_);
lean_dec(v___x_355_);
v_target_357_ = l_Lake_stringToLegalOrSimpleName(v___x_356_);
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v_pkg_341_);
lean_ctor_set(v___x_358_, 1, v_target_357_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* v_pkg_368_, lean_object* v_target_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v_pkg_368_, v_target_369_);
lean_dec_ref(v_target_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* v_s_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* v_s_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_375_);
lean_dec_ref(v_s_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* v_s_377_, lean_object* v___x_378_, lean_object* v___x_379_, lean_object* v_a_380_, lean_object* v_b_381_){
_start:
{
lean_object* v_it_383_; lean_object* v_startInclusive_384_; lean_object* v_endExclusive_385_; 
if (lean_obj_tag(v_a_380_) == 0)
{
lean_object* v_currPos_389_; lean_object* v_searcher_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_416_; 
v_currPos_389_ = lean_ctor_get(v_a_380_, 0);
v_searcher_390_ = lean_ctor_get(v_a_380_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_416_ == 0)
{
v___x_392_ = v_a_380_;
v_isShared_393_ = v_isSharedCheck_416_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_searcher_390_);
lean_inc(v_currPos_389_);
lean_dec(v_a_380_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_416_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_startInclusive_394_; lean_object* v_endExclusive_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_startInclusive_394_ = lean_ctor_get(v___x_378_, 1);
v_endExclusive_395_ = lean_ctor_get(v___x_378_, 2);
v___x_396_ = lean_nat_sub(v_endExclusive_395_, v_startInclusive_394_);
v___x_397_ = lean_nat_dec_eq(v_searcher_390_, v___x_396_);
lean_dec(v___x_396_);
if (v___x_397_ == 0)
{
uint32_t v___x_398_; uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = 47;
v___x_399_ = lean_string_utf8_get_fast(v_s_377_, v_searcher_390_);
v___x_400_ = lean_uint32_dec_eq(v___x_399_, v___x_398_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_string_utf8_next_fast(v_s_377_, v_searcher_390_);
lean_dec(v_searcher_390_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_401_);
v___x_403_ = v___x_392_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_currPos_389_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_405_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
v_a_380_ = v___x_403_;
goto _start;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_slice_409_; lean_object* v_nextIt_411_; 
v___x_406_ = lean_string_utf8_next_fast(v_s_377_, v_searcher_390_);
v___x_407_ = lean_nat_sub(v___x_406_, v_searcher_390_);
v___x_408_ = lean_nat_add(v_searcher_390_, v___x_407_);
lean_dec(v___x_407_);
v_slice_409_ = l_String_Slice_subslice_x21(v___x_378_, v_currPos_389_, v_searcher_390_);
lean_inc(v___x_408_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v___x_408_);
lean_ctor_set(v___x_392_, 0, v___x_408_);
v_nextIt_411_ = v___x_392_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_408_);
v_nextIt_411_ = v_reuseFailAlloc_414_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v_startInclusive_412_; lean_object* v_endExclusive_413_; 
v_startInclusive_412_ = lean_ctor_get(v_slice_409_, 0);
lean_inc(v_startInclusive_412_);
v_endExclusive_413_ = lean_ctor_get(v_slice_409_, 1);
lean_inc(v_endExclusive_413_);
lean_dec_ref(v_slice_409_);
v_it_383_ = v_nextIt_411_;
v_startInclusive_384_ = v_startInclusive_412_;
v_endExclusive_385_ = v_endExclusive_413_;
goto v___jp_382_;
}
}
}
else
{
lean_object* v___x_415_; 
lean_del_object(v___x_392_);
lean_dec(v_searcher_390_);
v___x_415_ = lean_box(1);
lean_inc(v___x_379_);
v_it_383_ = v___x_415_;
v_startInclusive_384_ = v_currPos_389_;
v_endExclusive_385_ = v___x_379_;
goto v___jp_382_;
}
}
}
else
{
lean_dec(v___x_379_);
lean_dec_ref(v_s_377_);
return v_b_381_;
}
v___jp_382_:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
lean_inc_ref(v_s_377_);
v___x_386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_386_, 0, v_s_377_);
lean_ctor_set(v___x_386_, 1, v_startInclusive_384_);
lean_ctor_set(v___x_386_, 2, v_endExclusive_385_);
v___x_387_ = lean_array_push(v_b_381_, v___x_386_);
v_a_380_ = v_it_383_;
v_b_381_ = v___x_387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object* v_s_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_417_, v___x_418_, v___x_419_, v_a_420_, v_b_421_);
lean_dec_ref(v___x_418_);
return v_res_422_;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_435_ = lean_string_utf8_byte_size(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object* v_s_436_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_string_utf8_byte_size(v_s_436_);
lean_inc_ref(v_s_436_);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v_s_436_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_440_);
v___x_442_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v___x_441_);
v___x_443_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2));
v___x_444_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_436_, v___x_441_, v___x_440_, v___x_442_, v___x_443_);
lean_dec_ref(v___x_441_);
v___x_445_ = lean_array_to_list(v___x_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_head_446_; lean_object* v_tail_447_; 
v_head_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_head_446_);
v_tail_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_tail_447_);
lean_dec_ref(v___x_445_);
if (lean_obj_tag(v_tail_447_) == 0)
{
lean_object* v_str_451_; lean_object* v_startInclusive_452_; lean_object* v_endExclusive_453_; uint8_t v___y_455_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_str_451_ = lean_ctor_get(v_head_446_, 0);
v_startInclusive_452_ = lean_ctor_get(v_head_446_, 1);
v_endExclusive_453_ = lean_ctor_get(v_head_446_, 2);
v___x_481_ = lean_nat_sub(v_endExclusive_453_, v_startInclusive_452_);
v___x_482_ = lean_nat_dec_eq(v___x_481_, v___x_439_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_484_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
v___x_485_ = lean_nat_dec_le(v___x_484_, v___x_481_);
lean_dec(v___x_481_);
if (v___x_485_ == 0)
{
v___y_455_ = v___x_482_;
goto v___jp_454_;
}
else
{
uint8_t v___x_486_; 
v___x_486_ = lean_string_memcmp(v_str_451_, v___x_483_, v_startInclusive_452_, v___x_439_, v___x_484_);
v___y_455_ = v___x_486_;
goto v___jp_454_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec(v___x_481_);
lean_dec(v_head_446_);
v___x_487_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return v___x_487_;
}
v___jp_454_:
{
if (v___y_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_456_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_457_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_458_ = lean_nat_sub(v_endExclusive_453_, v_startInclusive_452_);
v___x_459_ = lean_nat_dec_le(v___x_457_, v___x_458_);
lean_dec(v___x_458_);
if (v___x_459_ == 0)
{
goto v___jp_448_;
}
else
{
uint8_t v___x_460_; 
v___x_460_ = lean_string_memcmp(v_str_451_, v___x_456_, v_startInclusive_452_, v___x_439_, v___x_457_);
if (v___x_460_ == 0)
{
goto v___jp_448_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
lean_inc(v_endExclusive_453_);
lean_inc(v_startInclusive_452_);
lean_inc_ref(v_str_451_);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = l_String_Slice_Pos_nextn(v_head_446_, v___x_439_, v___x_461_);
lean_dec(v_head_446_);
v___x_463_ = lean_nat_add(v_startInclusive_452_, v___x_462_);
lean_dec(v___x_462_);
lean_dec(v_startInclusive_452_);
v___x_464_ = lean_nat_sub(v_endExclusive_453_, v___x_463_);
v___x_465_ = lean_nat_dec_eq(v___x_464_, v___x_439_);
lean_dec(v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = lean_string_utf8_extract(v_str_451_, v___x_463_, v_endExclusive_453_);
lean_dec(v_endExclusive_453_);
lean_dec(v___x_463_);
lean_dec_ref(v_str_451_);
v___x_467_ = l_Lake_stringToLegalOrSimpleName(v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v___x_463_);
lean_dec(v_endExclusive_453_);
lean_dec_ref(v_str_451_);
v___x_470_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
lean_inc(v_endExclusive_453_);
lean_inc(v_startInclusive_452_);
lean_inc_ref(v_str_451_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = l_String_Slice_Pos_nextn(v_head_446_, v___x_439_, v___x_471_);
lean_dec(v_head_446_);
v___x_473_ = lean_nat_add(v_startInclusive_452_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v_startInclusive_452_);
v___x_474_ = lean_nat_sub(v_endExclusive_453_, v___x_473_);
v___x_475_ = lean_nat_dec_eq(v___x_474_, v___x_439_);
lean_dec(v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_476_ = lean_string_utf8_extract(v_str_451_, v___x_473_, v_endExclusive_453_);
lean_dec(v_endExclusive_453_);
lean_dec(v___x_473_);
lean_dec_ref(v_str_451_);
v___x_477_ = l_Lake_stringToLegalOrSimpleName(v___x_476_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; 
lean_dec(v___x_473_);
lean_dec(v_endExclusive_453_);
lean_dec_ref(v_str_451_);
v___x_480_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return v___x_480_;
}
}
}
}
else
{
lean_object* v_head_488_; lean_object* v_tail_489_; lean_object* v_str_491_; lean_object* v_startInclusive_492_; lean_object* v_endExclusive_493_; 
v_head_488_ = lean_ctor_get(v_tail_447_, 0);
lean_inc(v_head_488_);
v_tail_489_ = lean_ctor_get(v_tail_447_, 1);
lean_inc(v_tail_489_);
lean_dec_ref(v_tail_447_);
if (lean_obj_tag(v_tail_489_) == 0)
{
lean_object* v_str_501_; lean_object* v_startInclusive_502_; lean_object* v_endExclusive_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_str_501_ = lean_ctor_get(v_head_446_, 0);
lean_inc_ref(v_str_501_);
v_startInclusive_502_ = lean_ctor_get(v_head_446_, 1);
lean_inc(v_startInclusive_502_);
v_endExclusive_503_ = lean_ctor_get(v_head_446_, 2);
lean_inc(v_endExclusive_503_);
v___x_504_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_505_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
v___x_506_ = lean_nat_sub(v_endExclusive_503_, v_startInclusive_502_);
v___x_507_ = lean_nat_dec_le(v___x_505_, v___x_506_);
lean_dec(v___x_506_);
if (v___x_507_ == 0)
{
lean_dec(v_head_446_);
v_str_491_ = v_str_501_;
v_startInclusive_492_ = v_startInclusive_502_;
v_endExclusive_493_ = v_endExclusive_503_;
goto v___jp_490_;
}
else
{
uint8_t v___x_508_; 
v___x_508_ = lean_string_memcmp(v_str_501_, v___x_504_, v_startInclusive_502_, v___x_439_, v___x_505_);
if (v___x_508_ == 0)
{
lean_dec(v_head_446_);
v_str_491_ = v_str_501_;
v_startInclusive_492_ = v_startInclusive_502_;
v_endExclusive_493_ = v_endExclusive_503_;
goto v___jp_490_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = l_String_Slice_Pos_nextn(v_head_446_, v___x_439_, v___x_509_);
lean_dec(v_head_446_);
v___x_511_ = lean_nat_add(v_startInclusive_502_, v___x_510_);
lean_dec(v___x_510_);
lean_dec(v_startInclusive_502_);
v_str_491_ = v_str_501_;
v_startInclusive_492_ = v___x_511_;
v_endExclusive_493_ = v_endExclusive_503_;
goto v___jp_490_;
}
}
}
else
{
lean_dec(v_tail_489_);
lean_dec(v_head_488_);
lean_dec(v_head_446_);
goto v___jp_437_;
}
v___jp_490_:
{
lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_494_ = lean_nat_sub(v_endExclusive_493_, v_startInclusive_492_);
v___x_495_ = lean_nat_dec_eq(v___x_494_, v___x_439_);
lean_dec(v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_string_utf8_extract(v_str_491_, v_startInclusive_492_, v_endExclusive_493_);
lean_dec(v_endExclusive_493_);
lean_dec(v_startInclusive_492_);
lean_dec_ref(v_str_491_);
v___x_497_ = l_Lake_stringToLegalOrSimpleName(v___x_496_);
v___x_498_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_497_, v_head_488_);
lean_dec(v_head_488_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v_endExclusive_493_);
lean_dec(v_startInclusive_492_);
lean_dec_ref(v_str_491_);
v___x_499_ = lean_box(0);
v___x_500_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_499_, v_head_488_);
lean_dec(v_head_488_);
return v___x_500_;
}
}
}
v___jp_448_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_box(0);
v___x_450_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_449_, v_head_446_);
lean_dec(v_head_446_);
return v___x_450_;
}
}
else
{
lean_dec(v___x_445_);
goto v___jp_437_;
}
v___jp_437_:
{
lean_object* v___x_438_; 
v___x_438_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1));
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* v_s_512_, lean_object* v___x_513_, lean_object* v___x_514_, lean_object* v_inst_515_, lean_object* v_R_516_, lean_object* v_a_517_, lean_object* v_b_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_512_, v___x_513_, v___x_514_, v_a_517_, v_b_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* v_s_520_, lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v_inst_523_, lean_object* v_R_524_, lean_object* v_a_525_, lean_object* v_b_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_520_, v___x_521_, v___x_522_, v_inst_523_, v_R_524_, v_a_525_, v_b_526_);
lean_dec_ref(v___x_521_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_530_);
lean_dec_ref(v_s_530_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___x_536_ = lean_panic_fn(v___x_535_, v_msg_533_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_537_, lean_object* v___x_538_, lean_object* v___x_539_, lean_object* v_a_540_, lean_object* v_b_541_){
_start:
{
lean_object* v_it_543_; lean_object* v_startInclusive_544_; lean_object* v_endExclusive_545_; 
if (lean_obj_tag(v_a_540_) == 0)
{
lean_object* v_currPos_550_; lean_object* v_searcher_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_577_; 
v_currPos_550_ = lean_ctor_get(v_a_540_, 0);
v_searcher_551_ = lean_ctor_get(v_a_540_, 1);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_577_ == 0)
{
v___x_553_ = v_a_540_;
v_isShared_554_ = v_isSharedCheck_577_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_searcher_551_);
lean_inc(v_currPos_550_);
lean_dec(v_a_540_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_577_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_startInclusive_555_; lean_object* v_endExclusive_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_startInclusive_555_ = lean_ctor_get(v___x_538_, 1);
v_endExclusive_556_ = lean_ctor_get(v___x_538_, 2);
v___x_557_ = lean_nat_sub(v_endExclusive_556_, v_startInclusive_555_);
v___x_558_ = lean_nat_dec_eq(v_searcher_551_, v___x_557_);
lean_dec(v___x_557_);
if (v___x_558_ == 0)
{
uint32_t v___x_559_; uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = 58;
v___x_560_ = lean_string_utf8_get_fast(v_s_537_, v_searcher_551_);
v___x_561_ = lean_uint32_dec_eq(v___x_560_, v___x_559_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_562_ = lean_string_utf8_next_fast(v_s_537_, v_searcher_551_);
lean_dec(v_searcher_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_562_);
v___x_564_ = v___x_553_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_currPos_550_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v_a_540_ = v___x_564_;
goto _start;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_slice_570_; lean_object* v_nextIt_572_; 
v___x_567_ = lean_string_utf8_next_fast(v_s_537_, v_searcher_551_);
v___x_568_ = lean_nat_sub(v___x_567_, v_searcher_551_);
v___x_569_ = lean_nat_add(v_searcher_551_, v___x_568_);
lean_dec(v___x_568_);
v_slice_570_ = l_String_Slice_subslice_x21(v___x_538_, v_currPos_550_, v_searcher_551_);
lean_inc(v___x_569_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_569_);
lean_ctor_set(v___x_553_, 0, v___x_569_);
v_nextIt_572_ = v___x_553_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_569_);
v_nextIt_572_ = v_reuseFailAlloc_575_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v_startInclusive_573_; lean_object* v_endExclusive_574_; 
v_startInclusive_573_ = lean_ctor_get(v_slice_570_, 0);
lean_inc(v_startInclusive_573_);
v_endExclusive_574_ = lean_ctor_get(v_slice_570_, 1);
lean_inc(v_endExclusive_574_);
lean_dec_ref(v_slice_570_);
v_it_543_ = v_nextIt_572_;
v_startInclusive_544_ = v_startInclusive_573_;
v_endExclusive_545_ = v_endExclusive_574_;
goto v___jp_542_;
}
}
}
else
{
lean_object* v___x_576_; 
lean_del_object(v___x_553_);
lean_dec(v_searcher_551_);
v___x_576_ = lean_box(1);
lean_inc(v___x_539_);
v_it_543_ = v___x_576_;
v_startInclusive_544_ = v_currPos_550_;
v_endExclusive_545_ = v___x_539_;
goto v___jp_542_;
}
}
}
else
{
lean_dec(v___x_539_);
lean_dec_ref(v_s_537_);
return v_b_541_;
}
v___jp_542_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
lean_inc_ref(v_s_537_);
v___x_546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_546_, 0, v_s_537_);
lean_ctor_set(v___x_546_, 1, v_startInclusive_544_);
lean_ctor_set(v___x_546_, 2, v_endExclusive_545_);
v___x_547_ = l_String_Slice_toString(v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = lean_array_push(v_b_541_, v___x_547_);
v_a_540_ = v_it_543_;
v_b_541_ = v___x_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v_a_581_, lean_object* v_b_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_578_, v___x_579_, v___x_580_, v_a_581_, v_b_582_);
lean_dec_ref(v___x_579_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_589_, 0, v_x_587_);
return v___x_589_;
}
else
{
lean_object* v_head_590_; lean_object* v_tail_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_604_; 
v_head_590_ = lean_ctor_get(v_x_588_, 0);
v_tail_591_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_604_ == 0)
{
v___x_593_ = v_x_588_;
v_isShared_594_ = v_isSharedCheck_604_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_tail_591_);
lean_inc(v_head_590_);
lean_dec(v_x_588_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_604_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = lean_string_utf8_byte_size(v_head_590_);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_nat_dec_eq(v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_598_ = l_Lake_stringToLegalOrSimpleName(v_head_590_);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 4);
lean_ctor_set(v___x_593_, 1, v___x_598_);
lean_ctor_set(v___x_593_, 0, v_x_587_);
v___x_600_ = v___x_593_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_x_587_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_602_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
v_x_587_ = v___x_600_;
v_x_588_ = v_tail_591_;
goto _start;
}
}
else
{
lean_object* v___x_603_; 
lean_del_object(v___x_593_);
lean_dec(v_tail_591_);
lean_dec(v_head_590_);
lean_dec_ref(v_x_587_);
v___x_603_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_603_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_610_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_611_ = lean_unsigned_to_nat(4u);
v___x_612_ = lean_unsigned_to_nat(65u);
v___x_613_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_614_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_615_ = l_mkPanicMessageWithDecl(v___x_614_, v___x_613_, v___x_612_, v___x_611_, v___x_610_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_string_utf8_byte_size(v_s_619_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_nat_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_inc_ref(v_s_619_);
v___x_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_623_, 0, v_s_619_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_620_);
v___x_624_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v___x_623_);
v___x_625_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_626_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_619_, v___x_623_, v___x_620_, v___x_624_, v___x_625_);
lean_dec_ref(v___x_623_);
v___x_627_ = lean_array_to_list(v___x_626_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_629_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_628_);
return v___x_629_;
}
else
{
lean_object* v_head_630_; lean_object* v_tail_631_; lean_object* v___x_632_; 
v_head_630_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_head_630_);
v_tail_631_ = lean_ctor_get(v___x_627_, 1);
lean_inc(v_tail_631_);
lean_dec_ref(v___x_627_);
v___x_632_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_630_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_dec(v_tail_631_);
return v___x_632_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_633_, v_tail_631_);
return v___x_634_;
}
}
}
else
{
lean_object* v___x_635_; 
lean_dec_ref(v_s_619_);
v___x_635_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_636_, lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v_inst_639_, lean_object* v_R_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_636_, v___x_637_, v___x_638_, v_a_641_, v_b_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v_inst_647_, lean_object* v_R_648_, lean_object* v_a_649_, lean_object* v_b_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_644_, v___x_645_, v___x_646_, v_inst_647_, v_R_648_, v_a_649_, v_b_650_);
lean_dec_ref(v___x_645_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_652_){
_start:
{
switch(lean_obj_tag(v_p_652_))
{
case 0:
{
return v_p_652_;
}
case 2:
{
lean_object* v_pre_653_; 
v_pre_653_ = lean_ctor_get(v_p_652_, 0);
if (lean_obj_tag(v_pre_653_) == 0)
{
return v_pre_653_;
}
else
{
lean_inc(v_pre_653_);
return v_pre_653_;
}
}
default: 
{
lean_inc(v_p_652_);
return v_p_652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_654_);
lean_dec(v_p_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_659_){
_start:
{
switch(lean_obj_tag(v_x_659_))
{
case 0:
{
lean_object* v_module_660_; lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_module_660_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_module_660_);
lean_dec_ref(v_x_659_);
v___x_661_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_662_ = 1;
v___x_663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_660_, v___x_662_);
v___x_664_ = lean_string_append(v___x_661_, v___x_663_);
lean_dec_ref(v___x_663_);
return v___x_664_;
}
case 1:
{
lean_object* v_package_665_; lean_object* v___x_666_; 
v_package_665_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_package_665_);
lean_dec_ref(v_x_659_);
v___x_666_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_665_);
lean_dec(v_package_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v___x_667_; 
v___x_667_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_667_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_668_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_669_ = 1;
v___x_670_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_666_, v___x_669_);
v___x_671_ = lean_string_append(v___x_668_, v___x_670_);
lean_dec_ref(v___x_670_);
return v___x_671_;
}
}
case 2:
{
lean_object* v_package_672_; lean_object* v_module_673_; lean_object* v___x_674_; 
v_package_672_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_package_672_);
v_module_673_ = lean_ctor_get(v_x_659_, 1);
lean_inc(v_module_673_);
lean_dec_ref(v_x_659_);
v___x_674_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_672_);
lean_dec(v_package_672_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_676_ = 1;
v___x_677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_673_, v___x_676_);
v___x_678_ = lean_string_append(v___x_675_, v___x_677_);
lean_dec_ref(v___x_677_);
return v___x_678_;
}
else
{
uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_679_ = 1;
v___x_680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_674_, v___x_679_);
v___x_681_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_682_ = lean_string_append(v___x_680_, v___x_681_);
v___x_683_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_673_, v___x_679_);
v___x_684_ = lean_string_append(v___x_682_, v___x_683_);
lean_dec_ref(v___x_683_);
return v___x_684_;
}
}
case 3:
{
lean_object* v_package_685_; lean_object* v_target_686_; lean_object* v___x_687_; 
v_package_685_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_package_685_);
v_target_686_ = lean_ctor_get(v_x_659_, 1);
lean_inc(v_target_686_);
lean_dec_ref(v_x_659_);
v___x_687_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_685_);
lean_dec(v_package_685_);
if (lean_obj_tag(v___x_687_) == 0)
{
uint8_t v___x_688_; lean_object* v___x_689_; 
v___x_688_ = 1;
v___x_689_ = l_Lean_Name_toString(v_target_686_, v___x_688_);
return v___x_689_;
}
else
{
uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_690_ = 1;
v___x_691_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_687_, v___x_690_);
v___x_692_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
v___x_694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_686_, v___x_690_);
v___x_695_ = lean_string_append(v___x_693_, v___x_694_);
lean_dec_ref(v___x_694_);
return v___x_695_;
}
}
default: 
{
lean_object* v_target_696_; lean_object* v_facet_697_; uint8_t v___x_698_; 
v_target_696_ = lean_ctor_get(v_x_659_, 0);
lean_inc_ref(v_target_696_);
v_facet_697_ = lean_ctor_get(v_x_659_, 1);
lean_inc(v_facet_697_);
lean_dec_ref(v_x_659_);
v___x_698_ = l_Lean_Name_isAnonymous(v_facet_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_699_ = l_Lake_PartialBuildKey_toString(v_target_696_);
v___x_700_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
v___x_702_ = 1;
v___x_703_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_697_, v___x_702_);
v___x_704_ = lean_string_append(v___x_701_, v___x_703_);
lean_dec_ref(v___x_703_);
return v___x_704_;
}
else
{
lean_dec(v_facet_697_);
v_x_659_ = v_target_696_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_708_, lean_object* v_facet_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_module_708_);
v___x_711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_facet_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_712_, lean_object* v_facet_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_package_712_);
v___x_715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v_facet_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_716_, lean_object* v_module_717_, lean_object* v_facet_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_719_, 0, v_package_716_);
lean_ctor_set(v___x_719_, 1, v_module_717_);
v___x_720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v_facet_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_721_, lean_object* v_target_722_, lean_object* v_facet_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_724_, 0, v_package_721_);
lean_ctor_set(v___x_724_, 1, v_target_722_);
v___x_725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_facet_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_726_, lean_object* v_target_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_728_, 0, v_package_726_);
lean_ctor_set(v___x_728_, 1, v_target_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_729_){
_start:
{
switch(lean_obj_tag(v_x_729_))
{
case 0:
{
lean_object* v_module_730_; lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_module_730_ = lean_ctor_get(v_x_729_, 0);
lean_inc(v_module_730_);
lean_dec_ref(v_x_729_);
v___x_731_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_732_ = 1;
v___x_733_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_730_, v___x_732_);
v___x_734_ = lean_string_append(v___x_731_, v___x_733_);
lean_dec_ref(v___x_733_);
return v___x_734_;
}
case 1:
{
lean_object* v_package_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_package_735_ = lean_ctor_get(v_x_729_, 0);
lean_inc(v_package_735_);
lean_dec_ref(v_x_729_);
v___x_736_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_737_ = l_Lean_Name_getPrefix(v_package_735_);
lean_dec(v_package_735_);
v___x_738_ = 1;
v___x_739_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_737_, v___x_738_);
v___x_740_ = lean_string_append(v___x_736_, v___x_739_);
lean_dec_ref(v___x_739_);
return v___x_740_;
}
case 2:
{
lean_object* v_package_741_; lean_object* v_module_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v_package_741_ = lean_ctor_get(v_x_729_, 0);
lean_inc(v_package_741_);
v_module_742_ = lean_ctor_get(v_x_729_, 1);
lean_inc(v_module_742_);
lean_dec_ref(v_x_729_);
v___x_743_ = l_Lean_Name_getPrefix(v_package_741_);
lean_dec(v_package_741_);
v___x_744_ = 1;
v___x_745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_743_, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_747_ = lean_string_append(v___x_745_, v___x_746_);
v___x_748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_742_, v___x_744_);
v___x_749_ = lean_string_append(v___x_747_, v___x_748_);
lean_dec_ref(v___x_748_);
return v___x_749_;
}
case 3:
{
lean_object* v_package_750_; lean_object* v_target_751_; lean_object* v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_package_750_ = lean_ctor_get(v_x_729_, 0);
lean_inc(v_package_750_);
v_target_751_ = lean_ctor_get(v_x_729_, 1);
lean_inc(v_target_751_);
lean_dec_ref(v_x_729_);
v___x_752_ = l_Lean_Name_getPrefix(v_package_750_);
lean_dec(v_package_750_);
v___x_753_ = 1;
v___x_754_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_752_, v___x_753_);
v___x_755_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
v___x_757_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_751_, v___x_753_);
v___x_758_ = lean_string_append(v___x_756_, v___x_757_);
lean_dec_ref(v___x_757_);
return v___x_758_;
}
default: 
{
lean_object* v_target_759_; lean_object* v_facet_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_target_759_ = lean_ctor_get(v_x_729_, 0);
lean_inc_ref(v_target_759_);
v_facet_760_ = lean_ctor_get(v_x_729_, 1);
lean_inc(v_facet_760_);
lean_dec_ref(v_x_729_);
v___x_761_ = l_Lake_BuildKey_toString(v_target_759_);
v___x_762_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_763_ = lean_string_append(v___x_761_, v___x_762_);
v___x_764_ = l_Lake_Name_eraseHead(v_facet_760_);
v___x_765_ = 1;
v___x_766_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_764_, v___x_765_);
v___x_767_ = lean_string_append(v___x_763_, v___x_766_);
lean_dec_ref(v___x_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_768_){
_start:
{
lean_object* v_p_770_; lean_object* v_m_771_; 
switch(lean_obj_tag(v_x_768_))
{
case 0:
{
lean_object* v_module_779_; uint8_t v___x_780_; lean_object* v___x_781_; 
v_module_779_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_module_779_);
lean_dec_ref(v_x_768_);
v___x_780_ = 1;
v___x_781_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_779_, v___x_780_);
return v___x_781_;
}
case 1:
{
lean_object* v_package_782_; lean_object* v___x_783_; uint8_t v___x_784_; lean_object* v___x_785_; 
v_package_782_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_package_782_);
lean_dec_ref(v_x_768_);
v___x_783_ = l_Lean_Name_getPrefix(v_package_782_);
lean_dec(v_package_782_);
v___x_784_ = 1;
v___x_785_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_783_, v___x_784_);
return v___x_785_;
}
case 4:
{
lean_object* v_target_786_; lean_object* v_facet_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_target_786_ = lean_ctor_get(v_x_768_, 0);
lean_inc_ref(v_target_786_);
v_facet_787_ = lean_ctor_get(v_x_768_, 1);
lean_inc(v_facet_787_);
lean_dec_ref(v_x_768_);
v___x_788_ = l_Lake_BuildKey_toSimpleString(v_target_786_);
v___x_789_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
v___x_791_ = l_Lake_Name_eraseHead(v_facet_787_);
v___x_792_ = 1;
v___x_793_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_791_, v___x_792_);
v___x_794_ = lean_string_append(v___x_790_, v___x_793_);
lean_dec_ref(v___x_793_);
return v___x_794_;
}
default: 
{
lean_object* v_package_795_; lean_object* v_module_796_; 
v_package_795_ = lean_ctor_get(v_x_768_, 0);
lean_inc(v_package_795_);
v_module_796_ = lean_ctor_get(v_x_768_, 1);
lean_inc(v_module_796_);
lean_dec_ref(v_x_768_);
v_p_770_ = v_package_795_;
v_m_771_ = v_module_796_;
goto v___jp_769_;
}
}
v___jp_769_:
{
lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_772_ = l_Lean_Name_getPrefix(v_p_770_);
lean_dec(v_p_770_);
v___x_773_ = 1;
v___x_774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_772_, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_776_ = lean_string_append(v___x_774_, v___x_775_);
v___x_777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_771_, v___x_773_);
v___x_778_ = lean_string_append(v___x_776_, v___x_777_);
lean_dec_ref(v___x_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_799_, lean_object* v_k_x27_800_){
_start:
{
switch(lean_obj_tag(v_k_799_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_800_) == 0)
{
lean_object* v_module_801_; lean_object* v_module_802_; uint8_t v___x_803_; 
v_module_801_ = lean_ctor_get(v_k_799_, 0);
v_module_802_ = lean_ctor_get(v_k_x27_800_, 0);
v___x_803_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_801_, v_module_802_);
return v___x_803_;
}
else
{
uint8_t v___x_804_; 
v___x_804_ = 0;
return v___x_804_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_800_))
{
case 0:
{
uint8_t v___x_805_; 
v___x_805_ = 2;
return v___x_805_;
}
case 1:
{
lean_object* v_package_806_; lean_object* v_package_807_; uint8_t v___x_808_; 
v_package_806_ = lean_ctor_get(v_k_799_, 0);
v_package_807_ = lean_ctor_get(v_k_x27_800_, 0);
v___x_808_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_806_, v_package_807_);
return v___x_808_;
}
default: 
{
uint8_t v___x_809_; 
v___x_809_ = 0;
return v___x_809_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_800_))
{
case 4:
{
uint8_t v___x_810_; 
v___x_810_ = 0;
return v___x_810_;
}
case 3:
{
uint8_t v___x_811_; 
v___x_811_ = 0;
return v___x_811_;
}
case 2:
{
lean_object* v_package_812_; lean_object* v_module_813_; lean_object* v_package_814_; lean_object* v_module_815_; uint8_t v___x_816_; 
v_package_812_ = lean_ctor_get(v_k_799_, 0);
v_module_813_ = lean_ctor_get(v_k_799_, 1);
v_package_814_ = lean_ctor_get(v_k_x27_800_, 0);
v_module_815_ = lean_ctor_get(v_k_x27_800_, 1);
v___x_816_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_813_, v_module_815_);
if (v___x_816_ == 1)
{
uint8_t v___x_817_; 
v___x_817_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_812_, v_package_814_);
return v___x_817_;
}
else
{
return v___x_816_;
}
}
default: 
{
uint8_t v___x_818_; 
v___x_818_ = 2;
return v___x_818_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_k_x27_800_))
{
case 4:
{
uint8_t v___x_819_; 
v___x_819_ = 0;
return v___x_819_;
}
case 3:
{
lean_object* v_package_820_; lean_object* v_target_821_; lean_object* v_package_822_; lean_object* v_target_823_; uint8_t v___x_824_; 
v_package_820_ = lean_ctor_get(v_k_799_, 0);
v_target_821_ = lean_ctor_get(v_k_799_, 1);
v_package_822_ = lean_ctor_get(v_k_x27_800_, 0);
v_target_823_ = lean_ctor_get(v_k_x27_800_, 1);
v___x_824_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_820_, v_package_822_);
if (v___x_824_ == 1)
{
uint8_t v___x_825_; 
v___x_825_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_821_, v_target_823_);
return v___x_825_;
}
else
{
return v___x_824_;
}
}
default: 
{
uint8_t v___x_826_; 
v___x_826_ = 2;
return v___x_826_;
}
}
}
default: 
{
if (lean_obj_tag(v_k_x27_800_) == 4)
{
lean_object* v_target_827_; lean_object* v_facet_828_; lean_object* v_target_829_; lean_object* v_facet_830_; uint8_t v___x_831_; 
v_target_827_ = lean_ctor_get(v_k_799_, 0);
v_facet_828_ = lean_ctor_get(v_k_799_, 1);
v_target_829_ = lean_ctor_get(v_k_x27_800_, 0);
v_facet_830_ = lean_ctor_get(v_k_x27_800_, 1);
v___x_831_ = l_Lake_BuildKey_quickCmp(v_target_827_, v_target_829_);
if (v___x_831_ == 1)
{
uint8_t v___x_832_; 
v___x_832_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_828_, v_facet_830_);
return v___x_832_;
}
else
{
return v___x_831_;
}
}
else
{
uint8_t v___x_833_; 
v___x_833_ = 2;
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* v_k_834_, lean_object* v_k_x27_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lake_BuildKey_quickCmp(v_k_834_, v_k_x27_835_);
lean_dec_ref(v_k_x27_835_);
lean_dec_ref(v_k_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* v_x_838_, lean_object* v_h__1_839_, lean_object* v_h__2_840_, lean_object* v_h__3_841_, lean_object* v_h__4_842_, lean_object* v_h__5_843_){
_start:
{
switch(lean_obj_tag(v_x_838_))
{
case 0:
{
lean_object* v_module_844_; lean_object* v___x_845_; 
lean_dec(v_h__5_843_);
lean_dec(v_h__4_842_);
lean_dec(v_h__3_841_);
lean_dec(v_h__2_840_);
v_module_844_ = lean_ctor_get(v_x_838_, 0);
lean_inc(v_module_844_);
lean_dec_ref(v_x_838_);
v___x_845_ = lean_apply_1(v_h__1_839_, v_module_844_);
return v___x_845_;
}
case 1:
{
lean_object* v_package_846_; lean_object* v___x_847_; 
lean_dec(v_h__5_843_);
lean_dec(v_h__4_842_);
lean_dec(v_h__3_841_);
lean_dec(v_h__1_839_);
v_package_846_ = lean_ctor_get(v_x_838_, 0);
lean_inc(v_package_846_);
lean_dec_ref(v_x_838_);
v___x_847_ = lean_apply_1(v_h__2_840_, v_package_846_);
return v___x_847_;
}
case 2:
{
lean_object* v_package_848_; lean_object* v_module_849_; lean_object* v___x_850_; 
lean_dec(v_h__5_843_);
lean_dec(v_h__4_842_);
lean_dec(v_h__2_840_);
lean_dec(v_h__1_839_);
v_package_848_ = lean_ctor_get(v_x_838_, 0);
lean_inc(v_package_848_);
v_module_849_ = lean_ctor_get(v_x_838_, 1);
lean_inc(v_module_849_);
lean_dec_ref(v_x_838_);
v___x_850_ = lean_apply_2(v_h__3_841_, v_package_848_, v_module_849_);
return v___x_850_;
}
case 3:
{
lean_object* v_package_851_; lean_object* v_target_852_; lean_object* v___x_853_; 
lean_dec(v_h__5_843_);
lean_dec(v_h__3_841_);
lean_dec(v_h__2_840_);
lean_dec(v_h__1_839_);
v_package_851_ = lean_ctor_get(v_x_838_, 0);
lean_inc(v_package_851_);
v_target_852_ = lean_ctor_get(v_x_838_, 1);
lean_inc(v_target_852_);
lean_dec_ref(v_x_838_);
v___x_853_ = lean_apply_2(v_h__4_842_, v_package_851_, v_target_852_);
return v___x_853_;
}
default: 
{
lean_object* v_target_854_; lean_object* v_facet_855_; lean_object* v___x_856_; 
lean_dec(v_h__4_842_);
lean_dec(v_h__3_841_);
lean_dec(v_h__2_840_);
lean_dec(v_h__1_839_);
v_target_854_ = lean_ctor_get(v_x_838_, 0);
lean_inc_ref(v_target_854_);
v_facet_855_ = lean_ctor_get(v_x_838_, 1);
lean_inc(v_facet_855_);
lean_dec_ref(v_x_838_);
v___x_856_ = lean_apply_2(v_h__5_843_, v_target_854_, v_facet_855_);
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_857_, lean_object* v_x_858_, lean_object* v_h__1_859_, lean_object* v_h__2_860_, lean_object* v_h__3_861_, lean_object* v_h__4_862_, lean_object* v_h__5_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(v_x_858_, v_h__1_859_, v_h__2_860_, v_h__3_861_, v_h__4_862_, v_h__5_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_865_, lean_object* v_h__1_866_, lean_object* v_h__2_867_){
_start:
{
if (lean_obj_tag(v_k_x27_865_) == 0)
{
lean_object* v_module_868_; lean_object* v___x_869_; 
lean_dec(v_h__2_867_);
v_module_868_ = lean_ctor_get(v_k_x27_865_, 0);
lean_inc(v_module_868_);
lean_dec_ref(v_k_x27_865_);
v___x_869_ = lean_apply_1(v_h__1_866_, v_module_868_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; 
lean_dec(v_h__1_866_);
v___x_870_ = lean_apply_2(v_h__2_867_, v_k_x27_865_, lean_box(0));
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_871_, lean_object* v_k_x27_872_, lean_object* v_h__1_873_, lean_object* v_h__2_874_){
_start:
{
if (lean_obj_tag(v_k_x27_872_) == 0)
{
lean_object* v_module_875_; lean_object* v___x_876_; 
lean_dec(v_h__2_874_);
v_module_875_ = lean_ctor_get(v_k_x27_872_, 0);
lean_inc(v_module_875_);
lean_dec_ref(v_k_x27_872_);
v___x_876_ = lean_apply_1(v_h__1_873_, v_module_875_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; 
lean_dec(v_h__1_873_);
v___x_877_ = lean_apply_2(v_h__2_874_, v_k_x27_872_, lean_box(0));
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_878_, lean_object* v_h__1_879_, lean_object* v_h__2_880_, lean_object* v_h__3_881_){
_start:
{
switch(lean_obj_tag(v_k_x27_878_))
{
case 0:
{
lean_object* v_module_882_; lean_object* v___x_883_; 
lean_dec(v_h__3_881_);
lean_dec(v_h__2_880_);
v_module_882_ = lean_ctor_get(v_k_x27_878_, 0);
lean_inc(v_module_882_);
lean_dec_ref(v_k_x27_878_);
v___x_883_ = lean_apply_1(v_h__1_879_, v_module_882_);
return v___x_883_;
}
case 1:
{
lean_object* v_package_884_; lean_object* v___x_885_; 
lean_dec(v_h__3_881_);
lean_dec(v_h__1_879_);
v_package_884_ = lean_ctor_get(v_k_x27_878_, 0);
lean_inc(v_package_884_);
lean_dec_ref(v_k_x27_878_);
v___x_885_ = lean_apply_1(v_h__2_880_, v_package_884_);
return v___x_885_;
}
default: 
{
lean_object* v___x_886_; 
lean_dec(v_h__2_880_);
lean_dec(v_h__1_879_);
v___x_886_ = lean_apply_3(v_h__3_881_, v_k_x27_878_, lean_box(0), lean_box(0));
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_887_, lean_object* v_k_x27_888_, lean_object* v_h__1_889_, lean_object* v_h__2_890_, lean_object* v_h__3_891_){
_start:
{
switch(lean_obj_tag(v_k_x27_888_))
{
case 0:
{
lean_object* v_module_892_; lean_object* v___x_893_; 
lean_dec(v_h__3_891_);
lean_dec(v_h__2_890_);
v_module_892_ = lean_ctor_get(v_k_x27_888_, 0);
lean_inc(v_module_892_);
lean_dec_ref(v_k_x27_888_);
v___x_893_ = lean_apply_1(v_h__1_889_, v_module_892_);
return v___x_893_;
}
case 1:
{
lean_object* v_package_894_; lean_object* v___x_895_; 
lean_dec(v_h__3_891_);
lean_dec(v_h__1_889_);
v_package_894_ = lean_ctor_get(v_k_x27_888_, 0);
lean_inc(v_package_894_);
lean_dec_ref(v_k_x27_888_);
v___x_895_ = lean_apply_1(v_h__2_890_, v_package_894_);
return v___x_895_;
}
default: 
{
lean_object* v___x_896_; 
lean_dec(v_h__2_890_);
lean_dec(v_h__1_889_);
v___x_896_ = lean_apply_3(v_h__3_891_, v_k_x27_888_, lean_box(0), lean_box(0));
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_897_, lean_object* v_h__1_898_, lean_object* v_h__2_899_, lean_object* v_h__3_900_, lean_object* v_h__4_901_){
_start:
{
switch(lean_obj_tag(v_k_x27_897_))
{
case 4:
{
lean_object* v_target_902_; lean_object* v_facet_903_; lean_object* v___x_904_; 
lean_dec(v_h__4_901_);
lean_dec(v_h__3_900_);
lean_dec(v_h__2_899_);
v_target_902_ = lean_ctor_get(v_k_x27_897_, 0);
lean_inc_ref(v_target_902_);
v_facet_903_ = lean_ctor_get(v_k_x27_897_, 1);
lean_inc(v_facet_903_);
lean_dec_ref(v_k_x27_897_);
v___x_904_ = lean_apply_2(v_h__1_898_, v_target_902_, v_facet_903_);
return v___x_904_;
}
case 3:
{
lean_object* v_package_905_; lean_object* v_target_906_; lean_object* v___x_907_; 
lean_dec(v_h__4_901_);
lean_dec(v_h__3_900_);
lean_dec(v_h__1_898_);
v_package_905_ = lean_ctor_get(v_k_x27_897_, 0);
lean_inc(v_package_905_);
v_target_906_ = lean_ctor_get(v_k_x27_897_, 1);
lean_inc(v_target_906_);
lean_dec_ref(v_k_x27_897_);
v___x_907_ = lean_apply_2(v_h__2_899_, v_package_905_, v_target_906_);
return v___x_907_;
}
case 2:
{
lean_object* v_package_908_; lean_object* v_module_909_; lean_object* v___x_910_; 
lean_dec(v_h__4_901_);
lean_dec(v_h__2_899_);
lean_dec(v_h__1_898_);
v_package_908_ = lean_ctor_get(v_k_x27_897_, 0);
lean_inc(v_package_908_);
v_module_909_ = lean_ctor_get(v_k_x27_897_, 1);
lean_inc(v_module_909_);
lean_dec_ref(v_k_x27_897_);
v___x_910_ = lean_apply_2(v_h__3_900_, v_package_908_, v_module_909_);
return v___x_910_;
}
default: 
{
lean_object* v___x_911_; 
lean_dec(v_h__3_900_);
lean_dec(v_h__2_899_);
lean_dec(v_h__1_898_);
v___x_911_ = lean_apply_4(v_h__4_901_, v_k_x27_897_, lean_box(0), lean_box(0), lean_box(0));
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_912_, lean_object* v_k_x27_913_, lean_object* v_h__1_914_, lean_object* v_h__2_915_, lean_object* v_h__3_916_, lean_object* v_h__4_917_){
_start:
{
switch(lean_obj_tag(v_k_x27_913_))
{
case 4:
{
lean_object* v_target_918_; lean_object* v_facet_919_; lean_object* v___x_920_; 
lean_dec(v_h__4_917_);
lean_dec(v_h__3_916_);
lean_dec(v_h__2_915_);
v_target_918_ = lean_ctor_get(v_k_x27_913_, 0);
lean_inc_ref(v_target_918_);
v_facet_919_ = lean_ctor_get(v_k_x27_913_, 1);
lean_inc(v_facet_919_);
lean_dec_ref(v_k_x27_913_);
v___x_920_ = lean_apply_2(v_h__1_914_, v_target_918_, v_facet_919_);
return v___x_920_;
}
case 3:
{
lean_object* v_package_921_; lean_object* v_target_922_; lean_object* v___x_923_; 
lean_dec(v_h__4_917_);
lean_dec(v_h__3_916_);
lean_dec(v_h__1_914_);
v_package_921_ = lean_ctor_get(v_k_x27_913_, 0);
lean_inc(v_package_921_);
v_target_922_ = lean_ctor_get(v_k_x27_913_, 1);
lean_inc(v_target_922_);
lean_dec_ref(v_k_x27_913_);
v___x_923_ = lean_apply_2(v_h__2_915_, v_package_921_, v_target_922_);
return v___x_923_;
}
case 2:
{
lean_object* v_package_924_; lean_object* v_module_925_; lean_object* v___x_926_; 
lean_dec(v_h__4_917_);
lean_dec(v_h__2_915_);
lean_dec(v_h__1_914_);
v_package_924_ = lean_ctor_get(v_k_x27_913_, 0);
lean_inc(v_package_924_);
v_module_925_ = lean_ctor_get(v_k_x27_913_, 1);
lean_inc(v_module_925_);
lean_dec_ref(v_k_x27_913_);
v___x_926_ = lean_apply_2(v_h__3_916_, v_package_924_, v_module_925_);
return v___x_926_;
}
default: 
{
lean_object* v___x_927_; 
lean_dec(v_h__3_916_);
lean_dec(v_h__2_915_);
lean_dec(v_h__1_914_);
v___x_927_ = lean_apply_4(v_h__4_917_, v_k_x27_913_, lean_box(0), lean_box(0), lean_box(0));
return v___x_927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_928_, lean_object* v_h__1_929_, lean_object* v_h__2_930_){
_start:
{
if (v_x_928_ == 1)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_h__2_930_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_apply_1(v_h__1_929_, v___x_931_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v_h__1_929_);
v___x_933_ = lean_box(v_x_928_);
v___x_934_ = lean_apply_2(v_h__2_930_, v___x_933_, lean_box(0));
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_935_, lean_object* v_h__1_936_, lean_object* v_h__2_937_){
_start:
{
uint8_t v_x_17__boxed_938_; lean_object* v_res_939_; 
v_x_17__boxed_938_ = lean_unbox(v_x_935_);
v_res_939_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_17__boxed_938_, v_h__1_936_, v_h__2_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_940_, uint8_t v_x_941_, lean_object* v_h__1_942_, lean_object* v_h__2_943_){
_start:
{
if (v_x_941_ == 1)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_h__2_943_);
v___x_944_ = lean_box(0);
v___x_945_ = lean_apply_1(v_h__1_942_, v___x_944_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec(v_h__1_942_);
v___x_946_ = lean_box(v_x_941_);
v___x_947_ = lean_apply_2(v_h__2_943_, v___x_946_, lean_box(0));
return v___x_947_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_948_, lean_object* v_x_949_, lean_object* v_h__1_950_, lean_object* v_h__2_951_){
_start:
{
uint8_t v_x_28__boxed_952_; lean_object* v_res_953_; 
v_x_28__boxed_952_ = lean_unbox(v_x_949_);
v_res_953_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_948_, v_x_28__boxed_952_, v_h__1_950_, v_h__2_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_954_, lean_object* v_h__1_955_, lean_object* v_h__2_956_, lean_object* v_h__3_957_){
_start:
{
switch(lean_obj_tag(v_k_x27_954_))
{
case 4:
{
lean_object* v_target_958_; lean_object* v_facet_959_; lean_object* v___x_960_; 
lean_dec(v_h__3_957_);
lean_dec(v_h__2_956_);
v_target_958_ = lean_ctor_get(v_k_x27_954_, 0);
lean_inc_ref(v_target_958_);
v_facet_959_ = lean_ctor_get(v_k_x27_954_, 1);
lean_inc(v_facet_959_);
lean_dec_ref(v_k_x27_954_);
v___x_960_ = lean_apply_2(v_h__1_955_, v_target_958_, v_facet_959_);
return v___x_960_;
}
case 3:
{
lean_object* v_package_961_; lean_object* v_target_962_; lean_object* v___x_963_; 
lean_dec(v_h__3_957_);
lean_dec(v_h__1_955_);
v_package_961_ = lean_ctor_get(v_k_x27_954_, 0);
lean_inc(v_package_961_);
v_target_962_ = lean_ctor_get(v_k_x27_954_, 1);
lean_inc(v_target_962_);
lean_dec_ref(v_k_x27_954_);
v___x_963_ = lean_apply_2(v_h__2_956_, v_package_961_, v_target_962_);
return v___x_963_;
}
default: 
{
lean_object* v___x_964_; 
lean_dec(v_h__2_956_);
lean_dec(v_h__1_955_);
v___x_964_ = lean_apply_3(v_h__3_957_, v_k_x27_954_, lean_box(0), lean_box(0));
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_965_, lean_object* v_k_x27_966_, lean_object* v_h__1_967_, lean_object* v_h__2_968_, lean_object* v_h__3_969_){
_start:
{
switch(lean_obj_tag(v_k_x27_966_))
{
case 4:
{
lean_object* v_target_970_; lean_object* v_facet_971_; lean_object* v___x_972_; 
lean_dec(v_h__3_969_);
lean_dec(v_h__2_968_);
v_target_970_ = lean_ctor_get(v_k_x27_966_, 0);
lean_inc_ref(v_target_970_);
v_facet_971_ = lean_ctor_get(v_k_x27_966_, 1);
lean_inc(v_facet_971_);
lean_dec_ref(v_k_x27_966_);
v___x_972_ = lean_apply_2(v_h__1_967_, v_target_970_, v_facet_971_);
return v___x_972_;
}
case 3:
{
lean_object* v_package_973_; lean_object* v_target_974_; lean_object* v___x_975_; 
lean_dec(v_h__3_969_);
lean_dec(v_h__1_967_);
v_package_973_ = lean_ctor_get(v_k_x27_966_, 0);
lean_inc(v_package_973_);
v_target_974_ = lean_ctor_get(v_k_x27_966_, 1);
lean_inc(v_target_974_);
lean_dec_ref(v_k_x27_966_);
v___x_975_ = lean_apply_2(v_h__2_968_, v_package_973_, v_target_974_);
return v___x_975_;
}
default: 
{
lean_object* v___x_976_; 
lean_dec(v_h__2_968_);
lean_dec(v_h__1_967_);
v___x_976_ = lean_apply_3(v_h__3_969_, v_k_x27_966_, lean_box(0), lean_box(0));
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_977_, lean_object* v_h__1_978_, lean_object* v_h__2_979_){
_start:
{
if (lean_obj_tag(v_k_x27_977_) == 4)
{
lean_object* v_target_980_; lean_object* v_facet_981_; lean_object* v___x_982_; 
lean_dec(v_h__2_979_);
v_target_980_ = lean_ctor_get(v_k_x27_977_, 0);
lean_inc_ref(v_target_980_);
v_facet_981_ = lean_ctor_get(v_k_x27_977_, 1);
lean_inc(v_facet_981_);
lean_dec_ref(v_k_x27_977_);
v___x_982_ = lean_apply_2(v_h__1_978_, v_target_980_, v_facet_981_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; 
lean_dec(v_h__1_978_);
v___x_983_ = lean_apply_2(v_h__2_979_, v_k_x27_977_, lean_box(0));
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_984_, lean_object* v_k_x27_985_, lean_object* v_h__1_986_, lean_object* v_h__2_987_){
_start:
{
if (lean_obj_tag(v_k_x27_985_) == 4)
{
lean_object* v_target_988_; lean_object* v_facet_989_; lean_object* v___x_990_; 
lean_dec(v_h__2_987_);
v_target_988_ = lean_ctor_get(v_k_x27_985_, 0);
lean_inc_ref(v_target_988_);
v_facet_989_ = lean_ctor_get(v_k_x27_985_, 1);
lean_inc(v_facet_989_);
lean_dec_ref(v_k_x27_985_);
v___x_990_ = lean_apply_2(v_h__1_986_, v_target_988_, v_facet_989_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; 
lean_dec(v_h__1_986_);
v___x_991_ = lean_apply_2(v_h__2_987_, v_k_x27_985_, lean_box(0));
return v___x_991_;
}
}
}
lean_object* runtime_initialize_Init_Data_Order(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Key(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Key(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Key(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Key(builtin);
}
#ifdef __cplusplus
}
#endif
