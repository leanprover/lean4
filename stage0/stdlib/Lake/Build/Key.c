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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_PartialBuildKey_instRepr___private__1___closed__0 = (const lean_object*)&l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instRepr___private__1 = (const lean_object*)&l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_PartialBuildKey_instRepr = (const lean_object*)&l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value;
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
lean_inc(v___y_116_);
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
lean_inc(v___y_131_);
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
lean_inc(v___y_150_);
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
lean_inc(v___y_176_);
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
lean_inc(v___y_203_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(lean_object* v_x_330_, lean_object* v_prec_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lake_instReprBuildKey_repr(v_x_330_, v_prec_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(lean_object* v_x_333_, lean_object* v_prec_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(v_x_333_, v_prec_334_);
lean_dec(v_prec_334_);
return v_res_335_;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_344_ = lean_string_utf8_byte_size(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* v_pkg_348_, lean_object* v_target_349_){
_start:
{
lean_object* v_str_350_; lean_object* v_startInclusive_351_; lean_object* v_endExclusive_352_; uint8_t v___y_354_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_str_350_ = lean_ctor_get(v_target_349_, 0);
v_startInclusive_351_ = lean_ctor_get(v_target_349_, 1);
v_endExclusive_352_ = lean_ctor_get(v_target_349_, 2);
v___x_367_ = lean_nat_sub(v_endExclusive_352_, v_startInclusive_351_);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_nat_dec_eq(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_370_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_371_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_372_ = lean_nat_dec_le(v___x_371_, v___x_367_);
lean_dec(v___x_367_);
if (v___x_372_ == 0)
{
v___y_354_ = v___x_369_;
goto v___jp_353_;
}
else
{
uint8_t v___x_373_; 
v___x_373_ = lean_string_memcmp(v_str_350_, v___x_370_, v_startInclusive_351_, v___x_368_, v___x_371_);
v___y_354_ = v___x_373_;
goto v___jp_353_;
}
}
else
{
lean_object* v___x_374_; 
lean_dec(v___x_367_);
lean_dec(v_pkg_348_);
v___x_374_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3));
return v___x_374_;
}
v___jp_353_:
{
if (v___y_354_ == 0)
{
lean_object* v___x_355_; lean_object* v_target_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = lean_string_utf8_extract(v_str_350_, v_startInclusive_351_, v_endExclusive_352_);
v_target_356_ = l_Lake_stringToLegalOrSimpleName(v___x_355_);
v___x_357_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_357_, 0, v_pkg_348_);
lean_ctor_set(v___x_357_, 1, v_target_356_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_target_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = l_String_Slice_Pos_nextn(v_target_349_, v___x_360_, v___x_359_);
v___x_362_ = lean_nat_add(v_startInclusive_351_, v___x_361_);
lean_dec(v___x_361_);
v___x_363_ = lean_string_utf8_extract(v_str_350_, v___x_362_, v_endExclusive_352_);
lean_dec(v___x_362_);
v_target_364_ = l_Lake_stringToLegalOrSimpleName(v___x_363_);
v___x_365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_365_, 0, v_pkg_348_);
lean_ctor_set(v___x_365_, 1, v_target_364_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* v_pkg_375_, lean_object* v_target_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v_pkg_375_, v_target_376_);
lean_dec_ref(v_target_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* v_s_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* v_s_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_382_);
lean_dec_ref(v_s_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* v_s_384_, lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
lean_object* v_it_390_; lean_object* v_startInclusive_391_; lean_object* v_endExclusive_392_; 
if (lean_obj_tag(v_a_387_) == 0)
{
lean_object* v_currPos_396_; lean_object* v_searcher_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_423_; 
v_currPos_396_ = lean_ctor_get(v_a_387_, 0);
v_searcher_397_ = lean_ctor_get(v_a_387_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_387_);
if (v_isSharedCheck_423_ == 0)
{
v___x_399_ = v_a_387_;
v_isShared_400_ = v_isSharedCheck_423_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_searcher_397_);
lean_inc(v_currPos_396_);
lean_dec(v_a_387_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_423_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v_startInclusive_401_; lean_object* v_endExclusive_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_startInclusive_401_ = lean_ctor_get(v___x_385_, 1);
v_endExclusive_402_ = lean_ctor_get(v___x_385_, 2);
v___x_403_ = lean_nat_sub(v_endExclusive_402_, v_startInclusive_401_);
v___x_404_ = lean_nat_dec_eq(v_searcher_397_, v___x_403_);
lean_dec(v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint32_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = 47;
v___x_406_ = lean_string_utf8_get_fast(v_s_384_, v_searcher_397_);
v___x_407_ = lean_uint32_dec_eq(v___x_406_, v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_string_utf8_next_fast(v_s_384_, v_searcher_397_);
lean_dec(v_searcher_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_408_);
v___x_410_ = v___x_399_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_currPos_396_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_412_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
v_a_387_ = v___x_410_;
goto _start;
}
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_slice_416_; lean_object* v_nextIt_418_; 
v___x_413_ = lean_string_utf8_next_fast(v_s_384_, v_searcher_397_);
v___x_414_ = lean_nat_sub(v___x_413_, v_searcher_397_);
v___x_415_ = lean_nat_add(v_searcher_397_, v___x_414_);
lean_dec(v___x_414_);
v_slice_416_ = l_String_Slice_subslice_x21(v___x_385_, v_currPos_396_, v_searcher_397_);
lean_inc(v___x_415_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_415_);
lean_ctor_set(v___x_399_, 0, v___x_415_);
v_nextIt_418_ = v___x_399_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_415_);
v_nextIt_418_ = v_reuseFailAlloc_421_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v_startInclusive_419_; lean_object* v_endExclusive_420_; 
v_startInclusive_419_ = lean_ctor_get(v_slice_416_, 0);
lean_inc(v_startInclusive_419_);
v_endExclusive_420_ = lean_ctor_get(v_slice_416_, 1);
lean_inc(v_endExclusive_420_);
lean_dec_ref(v_slice_416_);
v_it_390_ = v_nextIt_418_;
v_startInclusive_391_ = v_startInclusive_419_;
v_endExclusive_392_ = v_endExclusive_420_;
goto v___jp_389_;
}
}
}
else
{
lean_object* v___x_422_; 
lean_del_object(v___x_399_);
lean_dec(v_searcher_397_);
v___x_422_ = lean_box(1);
lean_inc(v___x_386_);
v_it_390_ = v___x_422_;
v_startInclusive_391_ = v_currPos_396_;
v_endExclusive_392_ = v___x_386_;
goto v___jp_389_;
}
}
}
else
{
lean_dec(v___x_386_);
lean_dec_ref(v_s_384_);
return v_b_388_;
}
v___jp_389_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_inc_ref(v_s_384_);
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v_s_384_);
lean_ctor_set(v___x_393_, 1, v_startInclusive_391_);
lean_ctor_set(v___x_393_, 2, v_endExclusive_392_);
v___x_394_ = lean_array_push(v_b_388_, v___x_393_);
v_a_387_ = v_it_390_;
v_b_388_ = v___x_394_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object* v_s_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v_a_427_, lean_object* v_b_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_424_, v___x_425_, v___x_426_, v_a_427_, v_b_428_);
lean_dec_ref(v___x_425_);
return v_res_429_;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_442_ = lean_string_utf8_byte_size(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object* v_s_443_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_string_utf8_byte_size(v_s_443_);
lean_inc_ref(v_s_443_);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v_s_443_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
lean_ctor_set(v___x_448_, 2, v___x_447_);
v___x_449_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v___x_448_);
v___x_450_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2));
v___x_451_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_443_, v___x_448_, v___x_447_, v___x_449_, v___x_450_);
lean_dec_ref(v___x_448_);
v___x_452_ = lean_array_to_list(v___x_451_);
if (lean_obj_tag(v___x_452_) == 1)
{
lean_object* v_head_453_; lean_object* v_tail_454_; 
v_head_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_head_453_);
v_tail_454_ = lean_ctor_get(v___x_452_, 1);
lean_inc(v_tail_454_);
lean_dec_ref(v___x_452_);
if (lean_obj_tag(v_tail_454_) == 0)
{
lean_object* v_str_458_; lean_object* v_startInclusive_459_; lean_object* v_endExclusive_460_; uint8_t v___y_462_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_str_458_ = lean_ctor_get(v_head_453_, 0);
v_startInclusive_459_ = lean_ctor_get(v_head_453_, 1);
v_endExclusive_460_ = lean_ctor_get(v_head_453_, 2);
v___x_488_ = lean_nat_sub(v_endExclusive_460_, v_startInclusive_459_);
v___x_489_ = lean_nat_dec_eq(v___x_488_, v___x_446_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_491_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
v___x_492_ = lean_nat_dec_le(v___x_491_, v___x_488_);
lean_dec(v___x_488_);
if (v___x_492_ == 0)
{
v___y_462_ = v___x_489_;
goto v___jp_461_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = lean_string_memcmp(v_str_458_, v___x_490_, v_startInclusive_459_, v___x_446_, v___x_491_);
v___y_462_ = v___x_493_;
goto v___jp_461_;
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v___x_488_);
lean_dec(v_head_453_);
v___x_494_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return v___x_494_;
}
v___jp_461_:
{
if (v___y_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_463_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_464_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_465_ = lean_nat_sub(v_endExclusive_460_, v_startInclusive_459_);
v___x_466_ = lean_nat_dec_le(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
if (v___x_466_ == 0)
{
goto v___jp_455_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = lean_string_memcmp(v_str_458_, v___x_463_, v_startInclusive_459_, v___x_446_, v___x_464_);
if (v___x_467_ == 0)
{
goto v___jp_455_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
lean_inc(v_endExclusive_460_);
lean_inc(v_startInclusive_459_);
lean_inc_ref(v_str_458_);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = l_String_Slice_Pos_nextn(v_head_453_, v___x_446_, v___x_468_);
lean_dec(v_head_453_);
v___x_470_ = lean_nat_add(v_startInclusive_459_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v_startInclusive_459_);
v___x_471_ = lean_nat_sub(v_endExclusive_460_, v___x_470_);
v___x_472_ = lean_nat_dec_eq(v___x_471_, v___x_446_);
lean_dec(v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_string_utf8_extract(v_str_458_, v___x_470_, v_endExclusive_460_);
lean_dec(v_endExclusive_460_);
lean_dec(v___x_470_);
lean_dec_ref(v_str_458_);
v___x_474_ = l_Lake_stringToLegalOrSimpleName(v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v___x_470_);
lean_dec(v_endExclusive_460_);
lean_dec_ref(v_str_458_);
v___x_477_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
lean_inc(v_endExclusive_460_);
lean_inc(v_startInclusive_459_);
lean_inc_ref(v_str_458_);
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = l_String_Slice_Pos_nextn(v_head_453_, v___x_446_, v___x_478_);
lean_dec(v_head_453_);
v___x_480_ = lean_nat_add(v_startInclusive_459_, v___x_479_);
lean_dec(v___x_479_);
lean_dec(v_startInclusive_459_);
v___x_481_ = lean_nat_sub(v_endExclusive_460_, v___x_480_);
v___x_482_ = lean_nat_dec_eq(v___x_481_, v___x_446_);
lean_dec(v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = lean_string_utf8_extract(v_str_458_, v___x_480_, v_endExclusive_460_);
lean_dec(v_endExclusive_460_);
lean_dec(v___x_480_);
lean_dec_ref(v_str_458_);
v___x_484_ = l_Lake_stringToLegalOrSimpleName(v___x_483_);
v___x_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; 
lean_dec(v___x_480_);
lean_dec(v_endExclusive_460_);
lean_dec_ref(v_str_458_);
v___x_487_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return v___x_487_;
}
}
}
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v_str_498_; lean_object* v_startInclusive_499_; lean_object* v_endExclusive_500_; 
v_head_495_ = lean_ctor_get(v_tail_454_, 0);
lean_inc(v_head_495_);
v_tail_496_ = lean_ctor_get(v_tail_454_, 1);
lean_inc(v_tail_496_);
lean_dec_ref(v_tail_454_);
if (lean_obj_tag(v_tail_496_) == 0)
{
lean_object* v_str_508_; lean_object* v_startInclusive_509_; lean_object* v_endExclusive_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_str_508_ = lean_ctor_get(v_head_453_, 0);
lean_inc_ref(v_str_508_);
v_startInclusive_509_ = lean_ctor_get(v_head_453_, 1);
lean_inc(v_startInclusive_509_);
v_endExclusive_510_ = lean_ctor_get(v_head_453_, 2);
lean_inc(v_endExclusive_510_);
v___x_511_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_512_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
v___x_513_ = lean_nat_sub(v_endExclusive_510_, v_startInclusive_509_);
v___x_514_ = lean_nat_dec_le(v___x_512_, v___x_513_);
lean_dec(v___x_513_);
if (v___x_514_ == 0)
{
lean_dec(v_head_453_);
v_str_498_ = v_str_508_;
v_startInclusive_499_ = v_startInclusive_509_;
v_endExclusive_500_ = v_endExclusive_510_;
goto v___jp_497_;
}
else
{
uint8_t v___x_515_; 
v___x_515_ = lean_string_memcmp(v_str_508_, v___x_511_, v_startInclusive_509_, v___x_446_, v___x_512_);
if (v___x_515_ == 0)
{
lean_dec(v_head_453_);
v_str_498_ = v_str_508_;
v_startInclusive_499_ = v_startInclusive_509_;
v_endExclusive_500_ = v_endExclusive_510_;
goto v___jp_497_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = l_String_Slice_Pos_nextn(v_head_453_, v___x_446_, v___x_516_);
lean_dec(v_head_453_);
v___x_518_ = lean_nat_add(v_startInclusive_509_, v___x_517_);
lean_dec(v___x_517_);
lean_dec(v_startInclusive_509_);
v_str_498_ = v_str_508_;
v_startInclusive_499_ = v___x_518_;
v_endExclusive_500_ = v_endExclusive_510_;
goto v___jp_497_;
}
}
}
else
{
lean_dec(v_tail_496_);
lean_dec(v_head_495_);
lean_dec(v_head_453_);
goto v___jp_444_;
}
v___jp_497_:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_nat_sub(v_endExclusive_500_, v_startInclusive_499_);
v___x_502_ = lean_nat_dec_eq(v___x_501_, v___x_446_);
lean_dec(v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_string_utf8_extract(v_str_498_, v_startInclusive_499_, v_endExclusive_500_);
lean_dec(v_endExclusive_500_);
lean_dec(v_startInclusive_499_);
lean_dec_ref(v_str_498_);
v___x_504_ = l_Lake_stringToLegalOrSimpleName(v___x_503_);
v___x_505_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_504_, v_head_495_);
lean_dec(v_head_495_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_endExclusive_500_);
lean_dec(v_startInclusive_499_);
lean_dec_ref(v_str_498_);
v___x_506_ = lean_box(0);
v___x_507_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_506_, v_head_495_);
lean_dec(v_head_495_);
return v___x_507_;
}
}
}
v___jp_455_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_box(0);
v___x_457_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_456_, v_head_453_);
lean_dec(v_head_453_);
return v___x_457_;
}
}
else
{
lean_dec(v___x_452_);
goto v___jp_444_;
}
v___jp_444_:
{
lean_object* v___x_445_; 
v___x_445_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1));
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* v_s_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_inst_522_, lean_object* v_R_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_519_, v___x_520_, v___x_521_, v_a_524_, v_b_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* v_s_527_, lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v_inst_530_, lean_object* v_R_531_, lean_object* v_a_532_, lean_object* v_b_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_527_, v___x_528_, v___x_529_, v_inst_530_, v_R_531_, v_a_532_, v_b_533_);
lean_dec_ref(v___x_528_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_537_);
lean_dec_ref(v_s_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___x_543_ = lean_panic_fn_borrowed(v___x_542_, v_msg_540_);
lean_dec_ref(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_544_, lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v_a_547_, lean_object* v_b_548_){
_start:
{
lean_object* v_it_550_; lean_object* v_startInclusive_551_; lean_object* v_endExclusive_552_; 
if (lean_obj_tag(v_a_547_) == 0)
{
lean_object* v_currPos_557_; lean_object* v_searcher_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_584_; 
v_currPos_557_ = lean_ctor_get(v_a_547_, 0);
v_searcher_558_ = lean_ctor_get(v_a_547_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_584_ == 0)
{
v___x_560_ = v_a_547_;
v_isShared_561_ = v_isSharedCheck_584_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_searcher_558_);
lean_inc(v_currPos_557_);
lean_dec(v_a_547_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_584_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_startInclusive_562_; lean_object* v_endExclusive_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_startInclusive_562_ = lean_ctor_get(v___x_545_, 1);
v_endExclusive_563_ = lean_ctor_get(v___x_545_, 2);
v___x_564_ = lean_nat_sub(v_endExclusive_563_, v_startInclusive_562_);
v___x_565_ = lean_nat_dec_eq(v_searcher_558_, v___x_564_);
lean_dec(v___x_564_);
if (v___x_565_ == 0)
{
uint32_t v___x_566_; uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_566_ = 58;
v___x_567_ = lean_string_utf8_get_fast(v_s_544_, v_searcher_558_);
v___x_568_ = lean_uint32_dec_eq(v___x_567_, v___x_566_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_string_utf8_next_fast(v_s_544_, v_searcher_558_);
lean_dec(v_searcher_558_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_569_);
v___x_571_ = v___x_560_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_currPos_557_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_573_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
v_a_547_ = v___x_571_;
goto _start;
}
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_slice_577_; lean_object* v_nextIt_579_; 
v___x_574_ = lean_string_utf8_next_fast(v_s_544_, v_searcher_558_);
v___x_575_ = lean_nat_sub(v___x_574_, v_searcher_558_);
v___x_576_ = lean_nat_add(v_searcher_558_, v___x_575_);
lean_dec(v___x_575_);
v_slice_577_ = l_String_Slice_subslice_x21(v___x_545_, v_currPos_557_, v_searcher_558_);
lean_inc(v___x_576_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_576_);
lean_ctor_set(v___x_560_, 0, v___x_576_);
v_nextIt_579_ = v___x_560_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_576_);
v_nextIt_579_ = v_reuseFailAlloc_582_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v_startInclusive_580_; lean_object* v_endExclusive_581_; 
v_startInclusive_580_ = lean_ctor_get(v_slice_577_, 0);
lean_inc(v_startInclusive_580_);
v_endExclusive_581_ = lean_ctor_get(v_slice_577_, 1);
lean_inc(v_endExclusive_581_);
lean_dec_ref(v_slice_577_);
v_it_550_ = v_nextIt_579_;
v_startInclusive_551_ = v_startInclusive_580_;
v_endExclusive_552_ = v_endExclusive_581_;
goto v___jp_549_;
}
}
}
else
{
lean_object* v___x_583_; 
lean_del_object(v___x_560_);
lean_dec(v_searcher_558_);
v___x_583_ = lean_box(1);
lean_inc(v___x_546_);
v_it_550_ = v___x_583_;
v_startInclusive_551_ = v_currPos_557_;
v_endExclusive_552_ = v___x_546_;
goto v___jp_549_;
}
}
}
else
{
lean_dec(v___x_546_);
lean_dec_ref(v_s_544_);
return v_b_548_;
}
v___jp_549_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc_ref(v_s_544_);
v___x_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_553_, 0, v_s_544_);
lean_ctor_set(v___x_553_, 1, v_startInclusive_551_);
lean_ctor_set(v___x_553_, 2, v_endExclusive_552_);
v___x_554_ = l_String_Slice_toString(v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = lean_array_push(v_b_548_, v___x_554_);
v_a_547_ = v_it_550_;
v_b_548_ = v___x_555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_585_, v___x_586_, v___x_587_, v_a_588_, v_b_589_);
lean_dec_ref(v___x_586_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v_x_594_);
return v___x_596_;
}
else
{
lean_object* v_head_597_; lean_object* v_tail_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_611_; 
v_head_597_ = lean_ctor_get(v_x_595_, 0);
v_tail_598_ = lean_ctor_get(v_x_595_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_611_ == 0)
{
v___x_600_ = v_x_595_;
v_isShared_601_ = v_isSharedCheck_611_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_tail_598_);
lean_inc(v_head_597_);
lean_dec(v_x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_611_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_string_utf8_byte_size(v_head_597_);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_nat_dec_eq(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = l_Lake_stringToLegalOrSimpleName(v_head_597_);
if (v_isShared_601_ == 0)
{
lean_ctor_set_tag(v___x_600_, 4);
lean_ctor_set(v___x_600_, 1, v___x_605_);
lean_ctor_set(v___x_600_, 0, v_x_594_);
v___x_607_ = v___x_600_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_x_594_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v_x_594_ = v___x_607_;
v_x_595_ = v_tail_598_;
goto _start;
}
}
else
{
lean_object* v___x_610_; 
lean_del_object(v___x_600_);
lean_dec(v_tail_598_);
lean_dec(v_head_597_);
lean_dec_ref(v_x_594_);
v___x_610_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_610_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_617_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_618_ = lean_unsigned_to_nat(4u);
v___x_619_ = lean_unsigned_to_nat(65u);
v___x_620_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_621_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_622_ = l_mkPanicMessageWithDecl(v___x_621_, v___x_620_, v___x_619_, v___x_618_, v___x_617_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_string_utf8_byte_size(v_s_626_);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_nat_dec_eq(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_inc_ref(v_s_626_);
v___x_630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_630_, 0, v_s_626_);
lean_ctor_set(v___x_630_, 1, v___x_628_);
lean_ctor_set(v___x_630_, 2, v___x_627_);
v___x_631_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v___x_630_);
v___x_632_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_633_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_626_, v___x_630_, v___x_627_, v___x_631_, v___x_632_);
lean_dec_ref(v___x_630_);
v___x_634_ = lean_array_to_list(v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_636_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_635_);
return v___x_636_;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v___x_639_; 
v_head_637_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_head_637_);
v_tail_638_ = lean_ctor_get(v___x_634_, 1);
lean_inc(v_tail_638_);
lean_dec_ref(v___x_634_);
v___x_639_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec(v_tail_638_);
return v___x_639_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
v___x_641_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_640_, v_tail_638_);
return v___x_641_;
}
}
}
else
{
lean_object* v___x_642_; 
lean_dec_ref(v_s_626_);
v___x_642_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_643_, lean_object* v___x_644_, lean_object* v___x_645_, lean_object* v_inst_646_, lean_object* v_R_647_, lean_object* v_a_648_, lean_object* v_b_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_643_, v___x_644_, v___x_645_, v_a_648_, v_b_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v_inst_654_, lean_object* v_R_655_, lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_651_, v___x_652_, v___x_653_, v_inst_654_, v_R_655_, v_a_656_, v_b_657_);
lean_dec_ref(v___x_652_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_659_){
_start:
{
switch(lean_obj_tag(v_p_659_))
{
case 0:
{
return v_p_659_;
}
case 2:
{
lean_object* v_pre_660_; 
v_pre_660_ = lean_ctor_get(v_p_659_, 0);
if (lean_obj_tag(v_pre_660_) == 0)
{
return v_pre_660_;
}
else
{
lean_inc(v_pre_660_);
return v_pre_660_;
}
}
default: 
{
lean_inc(v_p_659_);
return v_p_659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_661_);
lean_dec(v_p_661_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_666_){
_start:
{
switch(lean_obj_tag(v_x_666_))
{
case 0:
{
lean_object* v_module_667_; lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_module_667_ = lean_ctor_get(v_x_666_, 0);
lean_inc(v_module_667_);
lean_dec_ref(v_x_666_);
v___x_668_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_669_ = 1;
v___x_670_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_667_, v___x_669_);
v___x_671_ = lean_string_append(v___x_668_, v___x_670_);
lean_dec_ref(v___x_670_);
return v___x_671_;
}
case 1:
{
lean_object* v_package_672_; lean_object* v___x_673_; 
v_package_672_ = lean_ctor_get(v_x_666_, 0);
lean_inc(v_package_672_);
lean_dec_ref(v_x_666_);
v___x_673_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_672_);
lean_dec(v_package_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; 
v___x_674_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_674_;
}
else
{
lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_676_ = 1;
v___x_677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_673_, v___x_676_);
v___x_678_ = lean_string_append(v___x_675_, v___x_677_);
lean_dec_ref(v___x_677_);
return v___x_678_;
}
}
case 2:
{
lean_object* v_package_679_; lean_object* v_module_680_; lean_object* v___x_681_; 
v_package_679_ = lean_ctor_get(v_x_666_, 0);
lean_inc(v_package_679_);
v_module_680_ = lean_ctor_get(v_x_666_, 1);
lean_inc(v_module_680_);
lean_dec_ref(v_x_666_);
v___x_681_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_679_);
lean_dec(v_package_679_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_682_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_683_ = 1;
v___x_684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_680_, v___x_683_);
v___x_685_ = lean_string_append(v___x_682_, v___x_684_);
lean_dec_ref(v___x_684_);
return v___x_685_;
}
else
{
uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_686_ = 1;
v___x_687_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_681_, v___x_686_);
v___x_688_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
v___x_690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_680_, v___x_686_);
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
lean_dec_ref(v___x_690_);
return v___x_691_;
}
}
case 3:
{
lean_object* v_package_692_; lean_object* v_target_693_; lean_object* v___x_694_; 
v_package_692_ = lean_ctor_get(v_x_666_, 0);
lean_inc(v_package_692_);
v_target_693_ = lean_ctor_get(v_x_666_, 1);
lean_inc(v_target_693_);
lean_dec_ref(v_x_666_);
v___x_694_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_692_);
lean_dec(v_package_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
uint8_t v___x_695_; lean_object* v___x_696_; 
v___x_695_ = 1;
v___x_696_ = l_Lean_Name_toString(v_target_693_, v___x_695_);
return v___x_696_;
}
else
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = 1;
v___x_698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_694_, v___x_697_);
v___x_699_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
v___x_701_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_693_, v___x_697_);
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
lean_dec_ref(v___x_701_);
return v___x_702_;
}
}
default: 
{
lean_object* v_target_703_; lean_object* v_facet_704_; uint8_t v___x_705_; 
v_target_703_ = lean_ctor_get(v_x_666_, 0);
lean_inc_ref(v_target_703_);
v_facet_704_ = lean_ctor_get(v_x_666_, 1);
lean_inc(v_facet_704_);
lean_dec_ref(v_x_666_);
v___x_705_ = l_Lean_Name_isAnonymous(v_facet_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_706_ = l_Lake_PartialBuildKey_toString(v_target_703_);
v___x_707_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_708_ = lean_string_append(v___x_706_, v___x_707_);
v___x_709_ = 1;
v___x_710_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_704_, v___x_709_);
v___x_711_ = lean_string_append(v___x_708_, v___x_710_);
lean_dec_ref(v___x_710_);
return v___x_711_;
}
else
{
lean_dec(v_facet_704_);
v_x_666_ = v_target_703_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_715_, lean_object* v_facet_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_module_715_);
v___x_718_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_facet_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_719_, lean_object* v_facet_720_){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_721_, 0, v_package_719_);
v___x_722_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v_facet_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_723_, lean_object* v_module_724_, lean_object* v_facet_725_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v_package_723_);
lean_ctor_set(v___x_726_, 1, v_module_724_);
v___x_727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v_facet_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_728_, lean_object* v_target_729_, lean_object* v_facet_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_731_, 0, v_package_728_);
lean_ctor_set(v___x_731_, 1, v_target_729_);
v___x_732_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_facet_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_733_, lean_object* v_target_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_735_, 0, v_package_733_);
lean_ctor_set(v___x_735_, 1, v_target_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_736_){
_start:
{
switch(lean_obj_tag(v_x_736_))
{
case 0:
{
lean_object* v_module_737_; lean_object* v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_module_737_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_module_737_);
lean_dec_ref(v_x_736_);
v___x_738_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_739_ = 1;
v___x_740_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_737_, v___x_739_);
v___x_741_ = lean_string_append(v___x_738_, v___x_740_);
lean_dec_ref(v___x_740_);
return v___x_741_;
}
case 1:
{
lean_object* v_package_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_package_742_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_package_742_);
lean_dec_ref(v_x_736_);
v___x_743_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_744_ = l_Lean_Name_getPrefix(v_package_742_);
lean_dec(v_package_742_);
v___x_745_ = 1;
v___x_746_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_744_, v___x_745_);
v___x_747_ = lean_string_append(v___x_743_, v___x_746_);
lean_dec_ref(v___x_746_);
return v___x_747_;
}
case 2:
{
lean_object* v_package_748_; lean_object* v_module_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_package_748_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_package_748_);
v_module_749_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_module_749_);
lean_dec_ref(v_x_736_);
v___x_750_ = l_Lean_Name_getPrefix(v_package_748_);
lean_dec(v_package_748_);
v___x_751_ = 1;
v___x_752_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_750_, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
v___x_755_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_749_, v___x_751_);
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
lean_dec_ref(v___x_755_);
return v___x_756_;
}
case 3:
{
lean_object* v_package_757_; lean_object* v_target_758_; lean_object* v___x_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_package_757_ = lean_ctor_get(v_x_736_, 0);
lean_inc(v_package_757_);
v_target_758_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_target_758_);
lean_dec_ref(v_x_736_);
v___x_759_ = l_Lean_Name_getPrefix(v_package_757_);
lean_dec(v_package_757_);
v___x_760_ = 1;
v___x_761_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_759_, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_763_ = lean_string_append(v___x_761_, v___x_762_);
v___x_764_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_758_, v___x_760_);
v___x_765_ = lean_string_append(v___x_763_, v___x_764_);
lean_dec_ref(v___x_764_);
return v___x_765_;
}
default: 
{
lean_object* v_target_766_; lean_object* v_facet_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_target_766_ = lean_ctor_get(v_x_736_, 0);
lean_inc_ref(v_target_766_);
v_facet_767_ = lean_ctor_get(v_x_736_, 1);
lean_inc(v_facet_767_);
lean_dec_ref(v_x_736_);
v___x_768_ = l_Lake_BuildKey_toString(v_target_766_);
v___x_769_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_770_ = lean_string_append(v___x_768_, v___x_769_);
v___x_771_ = l_Lake_Name_eraseHead(v_facet_767_);
v___x_772_ = 1;
v___x_773_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_771_, v___x_772_);
v___x_774_ = lean_string_append(v___x_770_, v___x_773_);
lean_dec_ref(v___x_773_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_775_){
_start:
{
lean_object* v_p_777_; lean_object* v_m_778_; 
switch(lean_obj_tag(v_x_775_))
{
case 0:
{
lean_object* v_module_786_; uint8_t v___x_787_; lean_object* v___x_788_; 
v_module_786_ = lean_ctor_get(v_x_775_, 0);
lean_inc(v_module_786_);
lean_dec_ref(v_x_775_);
v___x_787_ = 1;
v___x_788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_786_, v___x_787_);
return v___x_788_;
}
case 1:
{
lean_object* v_package_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
v_package_789_ = lean_ctor_get(v_x_775_, 0);
lean_inc(v_package_789_);
lean_dec_ref(v_x_775_);
v___x_790_ = l_Lean_Name_getPrefix(v_package_789_);
lean_dec(v_package_789_);
v___x_791_ = 1;
v___x_792_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_790_, v___x_791_);
return v___x_792_;
}
case 4:
{
lean_object* v_target_793_; lean_object* v_facet_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_target_793_ = lean_ctor_get(v_x_775_, 0);
lean_inc_ref(v_target_793_);
v_facet_794_ = lean_ctor_get(v_x_775_, 1);
lean_inc(v_facet_794_);
lean_dec_ref(v_x_775_);
v___x_795_ = l_Lake_BuildKey_toSimpleString(v_target_793_);
v___x_796_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
v___x_798_ = l_Lake_Name_eraseHead(v_facet_794_);
v___x_799_ = 1;
v___x_800_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_798_, v___x_799_);
v___x_801_ = lean_string_append(v___x_797_, v___x_800_);
lean_dec_ref(v___x_800_);
return v___x_801_;
}
default: 
{
lean_object* v_package_802_; lean_object* v_module_803_; 
v_package_802_ = lean_ctor_get(v_x_775_, 0);
lean_inc(v_package_802_);
v_module_803_ = lean_ctor_get(v_x_775_, 1);
lean_inc(v_module_803_);
lean_dec_ref(v_x_775_);
v_p_777_ = v_package_802_;
v_m_778_ = v_module_803_;
goto v___jp_776_;
}
}
v___jp_776_:
{
lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_779_ = l_Lean_Name_getPrefix(v_p_777_);
lean_dec(v_p_777_);
v___x_780_ = 1;
v___x_781_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_779_, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
v___x_784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_778_, v___x_780_);
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
lean_dec_ref(v___x_784_);
return v___x_785_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_806_, lean_object* v_k_x27_807_){
_start:
{
switch(lean_obj_tag(v_k_806_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_807_) == 0)
{
lean_object* v_module_808_; lean_object* v_module_809_; uint8_t v___x_810_; 
v_module_808_ = lean_ctor_get(v_k_806_, 0);
v_module_809_ = lean_ctor_get(v_k_x27_807_, 0);
v___x_810_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_808_, v_module_809_);
return v___x_810_;
}
else
{
uint8_t v___x_811_; 
v___x_811_ = 0;
return v___x_811_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_807_))
{
case 0:
{
uint8_t v___x_812_; 
v___x_812_ = 2;
return v___x_812_;
}
case 1:
{
lean_object* v_package_813_; lean_object* v_package_814_; uint8_t v___x_815_; 
v_package_813_ = lean_ctor_get(v_k_806_, 0);
v_package_814_ = lean_ctor_get(v_k_x27_807_, 0);
v___x_815_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_813_, v_package_814_);
return v___x_815_;
}
default: 
{
uint8_t v___x_816_; 
v___x_816_ = 0;
return v___x_816_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_807_))
{
case 4:
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
case 3:
{
uint8_t v___x_818_; 
v___x_818_ = 0;
return v___x_818_;
}
case 2:
{
lean_object* v_package_819_; lean_object* v_module_820_; lean_object* v_package_821_; lean_object* v_module_822_; uint8_t v___x_823_; 
v_package_819_ = lean_ctor_get(v_k_806_, 0);
v_module_820_ = lean_ctor_get(v_k_806_, 1);
v_package_821_ = lean_ctor_get(v_k_x27_807_, 0);
v_module_822_ = lean_ctor_get(v_k_x27_807_, 1);
v___x_823_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_820_, v_module_822_);
if (v___x_823_ == 1)
{
uint8_t v___x_824_; 
v___x_824_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_819_, v_package_821_);
return v___x_824_;
}
else
{
return v___x_823_;
}
}
default: 
{
uint8_t v___x_825_; 
v___x_825_ = 2;
return v___x_825_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_k_x27_807_))
{
case 4:
{
uint8_t v___x_826_; 
v___x_826_ = 0;
return v___x_826_;
}
case 3:
{
lean_object* v_package_827_; lean_object* v_target_828_; lean_object* v_package_829_; lean_object* v_target_830_; uint8_t v___x_831_; 
v_package_827_ = lean_ctor_get(v_k_806_, 0);
v_target_828_ = lean_ctor_get(v_k_806_, 1);
v_package_829_ = lean_ctor_get(v_k_x27_807_, 0);
v_target_830_ = lean_ctor_get(v_k_x27_807_, 1);
v___x_831_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_827_, v_package_829_);
if (v___x_831_ == 1)
{
uint8_t v___x_832_; 
v___x_832_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_828_, v_target_830_);
return v___x_832_;
}
else
{
return v___x_831_;
}
}
default: 
{
uint8_t v___x_833_; 
v___x_833_ = 2;
return v___x_833_;
}
}
}
default: 
{
if (lean_obj_tag(v_k_x27_807_) == 4)
{
lean_object* v_target_834_; lean_object* v_facet_835_; lean_object* v_target_836_; lean_object* v_facet_837_; uint8_t v___x_838_; 
v_target_834_ = lean_ctor_get(v_k_806_, 0);
v_facet_835_ = lean_ctor_get(v_k_806_, 1);
v_target_836_ = lean_ctor_get(v_k_x27_807_, 0);
v_facet_837_ = lean_ctor_get(v_k_x27_807_, 1);
v___x_838_ = l_Lake_BuildKey_quickCmp(v_target_834_, v_target_836_);
if (v___x_838_ == 1)
{
uint8_t v___x_839_; 
v___x_839_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_835_, v_facet_837_);
return v___x_839_;
}
else
{
return v___x_838_;
}
}
else
{
uint8_t v___x_840_; 
v___x_840_ = 2;
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* v_k_841_, lean_object* v_k_x27_842_){
_start:
{
uint8_t v_res_843_; lean_object* v_r_844_; 
v_res_843_ = l_Lake_BuildKey_quickCmp(v_k_841_, v_k_x27_842_);
lean_dec_ref(v_k_x27_842_);
lean_dec_ref(v_k_841_);
v_r_844_ = lean_box(v_res_843_);
return v_r_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* v_x_845_, lean_object* v_h__1_846_, lean_object* v_h__2_847_, lean_object* v_h__3_848_, lean_object* v_h__4_849_, lean_object* v_h__5_850_){
_start:
{
switch(lean_obj_tag(v_x_845_))
{
case 0:
{
lean_object* v_module_851_; lean_object* v___x_852_; 
lean_dec(v_h__5_850_);
lean_dec(v_h__4_849_);
lean_dec(v_h__3_848_);
lean_dec(v_h__2_847_);
v_module_851_ = lean_ctor_get(v_x_845_, 0);
lean_inc(v_module_851_);
lean_dec_ref(v_x_845_);
v___x_852_ = lean_apply_1(v_h__1_846_, v_module_851_);
return v___x_852_;
}
case 1:
{
lean_object* v_package_853_; lean_object* v___x_854_; 
lean_dec(v_h__5_850_);
lean_dec(v_h__4_849_);
lean_dec(v_h__3_848_);
lean_dec(v_h__1_846_);
v_package_853_ = lean_ctor_get(v_x_845_, 0);
lean_inc(v_package_853_);
lean_dec_ref(v_x_845_);
v___x_854_ = lean_apply_1(v_h__2_847_, v_package_853_);
return v___x_854_;
}
case 2:
{
lean_object* v_package_855_; lean_object* v_module_856_; lean_object* v___x_857_; 
lean_dec(v_h__5_850_);
lean_dec(v_h__4_849_);
lean_dec(v_h__2_847_);
lean_dec(v_h__1_846_);
v_package_855_ = lean_ctor_get(v_x_845_, 0);
lean_inc(v_package_855_);
v_module_856_ = lean_ctor_get(v_x_845_, 1);
lean_inc(v_module_856_);
lean_dec_ref(v_x_845_);
v___x_857_ = lean_apply_2(v_h__3_848_, v_package_855_, v_module_856_);
return v___x_857_;
}
case 3:
{
lean_object* v_package_858_; lean_object* v_target_859_; lean_object* v___x_860_; 
lean_dec(v_h__5_850_);
lean_dec(v_h__3_848_);
lean_dec(v_h__2_847_);
lean_dec(v_h__1_846_);
v_package_858_ = lean_ctor_get(v_x_845_, 0);
lean_inc(v_package_858_);
v_target_859_ = lean_ctor_get(v_x_845_, 1);
lean_inc(v_target_859_);
lean_dec_ref(v_x_845_);
v___x_860_ = lean_apply_2(v_h__4_849_, v_package_858_, v_target_859_);
return v___x_860_;
}
default: 
{
lean_object* v_target_861_; lean_object* v_facet_862_; lean_object* v___x_863_; 
lean_dec(v_h__4_849_);
lean_dec(v_h__3_848_);
lean_dec(v_h__2_847_);
lean_dec(v_h__1_846_);
v_target_861_ = lean_ctor_get(v_x_845_, 0);
lean_inc_ref(v_target_861_);
v_facet_862_ = lean_ctor_get(v_x_845_, 1);
lean_inc(v_facet_862_);
lean_dec_ref(v_x_845_);
v___x_863_ = lean_apply_2(v_h__5_850_, v_target_861_, v_facet_862_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_864_, lean_object* v_x_865_, lean_object* v_h__1_866_, lean_object* v_h__2_867_, lean_object* v_h__3_868_, lean_object* v_h__4_869_, lean_object* v_h__5_870_){
_start:
{
switch(lean_obj_tag(v_x_865_))
{
case 0:
{
lean_object* v_module_871_; lean_object* v___x_872_; 
lean_dec(v_h__5_870_);
lean_dec(v_h__4_869_);
lean_dec(v_h__3_868_);
lean_dec(v_h__2_867_);
v_module_871_ = lean_ctor_get(v_x_865_, 0);
lean_inc(v_module_871_);
lean_dec_ref(v_x_865_);
v___x_872_ = lean_apply_1(v_h__1_866_, v_module_871_);
return v___x_872_;
}
case 1:
{
lean_object* v_package_873_; lean_object* v___x_874_; 
lean_dec(v_h__5_870_);
lean_dec(v_h__4_869_);
lean_dec(v_h__3_868_);
lean_dec(v_h__1_866_);
v_package_873_ = lean_ctor_get(v_x_865_, 0);
lean_inc(v_package_873_);
lean_dec_ref(v_x_865_);
v___x_874_ = lean_apply_1(v_h__2_867_, v_package_873_);
return v___x_874_;
}
case 2:
{
lean_object* v_package_875_; lean_object* v_module_876_; lean_object* v___x_877_; 
lean_dec(v_h__5_870_);
lean_dec(v_h__4_869_);
lean_dec(v_h__2_867_);
lean_dec(v_h__1_866_);
v_package_875_ = lean_ctor_get(v_x_865_, 0);
lean_inc(v_package_875_);
v_module_876_ = lean_ctor_get(v_x_865_, 1);
lean_inc(v_module_876_);
lean_dec_ref(v_x_865_);
v___x_877_ = lean_apply_2(v_h__3_868_, v_package_875_, v_module_876_);
return v___x_877_;
}
case 3:
{
lean_object* v_package_878_; lean_object* v_target_879_; lean_object* v___x_880_; 
lean_dec(v_h__5_870_);
lean_dec(v_h__3_868_);
lean_dec(v_h__2_867_);
lean_dec(v_h__1_866_);
v_package_878_ = lean_ctor_get(v_x_865_, 0);
lean_inc(v_package_878_);
v_target_879_ = lean_ctor_get(v_x_865_, 1);
lean_inc(v_target_879_);
lean_dec_ref(v_x_865_);
v___x_880_ = lean_apply_2(v_h__4_869_, v_package_878_, v_target_879_);
return v___x_880_;
}
default: 
{
lean_object* v_target_881_; lean_object* v_facet_882_; lean_object* v___x_883_; 
lean_dec(v_h__4_869_);
lean_dec(v_h__3_868_);
lean_dec(v_h__2_867_);
lean_dec(v_h__1_866_);
v_target_881_ = lean_ctor_get(v_x_865_, 0);
lean_inc_ref(v_target_881_);
v_facet_882_ = lean_ctor_get(v_x_865_, 1);
lean_inc(v_facet_882_);
lean_dec_ref(v_x_865_);
v___x_883_ = lean_apply_2(v_h__5_870_, v_target_881_, v_facet_882_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_){
_start:
{
if (lean_obj_tag(v_k_x27_884_) == 0)
{
lean_object* v_module_887_; lean_object* v___x_888_; 
lean_dec(v_h__2_886_);
v_module_887_ = lean_ctor_get(v_k_x27_884_, 0);
lean_inc(v_module_887_);
lean_dec_ref(v_k_x27_884_);
v___x_888_ = lean_apply_1(v_h__1_885_, v_module_887_);
return v___x_888_;
}
else
{
lean_object* v___x_889_; 
lean_dec(v_h__1_885_);
v___x_889_ = lean_apply_2(v_h__2_886_, v_k_x27_884_, lean_box(0));
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_890_, lean_object* v_k_x27_891_, lean_object* v_h__1_892_, lean_object* v_h__2_893_){
_start:
{
if (lean_obj_tag(v_k_x27_891_) == 0)
{
lean_object* v_module_894_; lean_object* v___x_895_; 
lean_dec(v_h__2_893_);
v_module_894_ = lean_ctor_get(v_k_x27_891_, 0);
lean_inc(v_module_894_);
lean_dec_ref(v_k_x27_891_);
v___x_895_ = lean_apply_1(v_h__1_892_, v_module_894_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; 
lean_dec(v_h__1_892_);
v___x_896_ = lean_apply_2(v_h__2_893_, v_k_x27_891_, lean_box(0));
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_897_, lean_object* v_h__1_898_, lean_object* v_h__2_899_, lean_object* v_h__3_900_){
_start:
{
switch(lean_obj_tag(v_k_x27_897_))
{
case 0:
{
lean_object* v_module_901_; lean_object* v___x_902_; 
lean_dec(v_h__3_900_);
lean_dec(v_h__2_899_);
v_module_901_ = lean_ctor_get(v_k_x27_897_, 0);
lean_inc(v_module_901_);
lean_dec_ref(v_k_x27_897_);
v___x_902_ = lean_apply_1(v_h__1_898_, v_module_901_);
return v___x_902_;
}
case 1:
{
lean_object* v_package_903_; lean_object* v___x_904_; 
lean_dec(v_h__3_900_);
lean_dec(v_h__1_898_);
v_package_903_ = lean_ctor_get(v_k_x27_897_, 0);
lean_inc(v_package_903_);
lean_dec_ref(v_k_x27_897_);
v___x_904_ = lean_apply_1(v_h__2_899_, v_package_903_);
return v___x_904_;
}
default: 
{
lean_object* v___x_905_; 
lean_dec(v_h__2_899_);
lean_dec(v_h__1_898_);
v___x_905_ = lean_apply_3(v_h__3_900_, v_k_x27_897_, lean_box(0), lean_box(0));
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_906_, lean_object* v_k_x27_907_, lean_object* v_h__1_908_, lean_object* v_h__2_909_, lean_object* v_h__3_910_){
_start:
{
switch(lean_obj_tag(v_k_x27_907_))
{
case 0:
{
lean_object* v_module_911_; lean_object* v___x_912_; 
lean_dec(v_h__3_910_);
lean_dec(v_h__2_909_);
v_module_911_ = lean_ctor_get(v_k_x27_907_, 0);
lean_inc(v_module_911_);
lean_dec_ref(v_k_x27_907_);
v___x_912_ = lean_apply_1(v_h__1_908_, v_module_911_);
return v___x_912_;
}
case 1:
{
lean_object* v_package_913_; lean_object* v___x_914_; 
lean_dec(v_h__3_910_);
lean_dec(v_h__1_908_);
v_package_913_ = lean_ctor_get(v_k_x27_907_, 0);
lean_inc(v_package_913_);
lean_dec_ref(v_k_x27_907_);
v___x_914_ = lean_apply_1(v_h__2_909_, v_package_913_);
return v___x_914_;
}
default: 
{
lean_object* v___x_915_; 
lean_dec(v_h__2_909_);
lean_dec(v_h__1_908_);
v___x_915_ = lean_apply_3(v_h__3_910_, v_k_x27_907_, lean_box(0), lean_box(0));
return v___x_915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_916_, lean_object* v_h__1_917_, lean_object* v_h__2_918_, lean_object* v_h__3_919_, lean_object* v_h__4_920_){
_start:
{
switch(lean_obj_tag(v_k_x27_916_))
{
case 4:
{
lean_object* v_target_921_; lean_object* v_facet_922_; lean_object* v___x_923_; 
lean_dec(v_h__4_920_);
lean_dec(v_h__3_919_);
lean_dec(v_h__2_918_);
v_target_921_ = lean_ctor_get(v_k_x27_916_, 0);
lean_inc_ref(v_target_921_);
v_facet_922_ = lean_ctor_get(v_k_x27_916_, 1);
lean_inc(v_facet_922_);
lean_dec_ref(v_k_x27_916_);
v___x_923_ = lean_apply_2(v_h__1_917_, v_target_921_, v_facet_922_);
return v___x_923_;
}
case 3:
{
lean_object* v_package_924_; lean_object* v_target_925_; lean_object* v___x_926_; 
lean_dec(v_h__4_920_);
lean_dec(v_h__3_919_);
lean_dec(v_h__1_917_);
v_package_924_ = lean_ctor_get(v_k_x27_916_, 0);
lean_inc(v_package_924_);
v_target_925_ = lean_ctor_get(v_k_x27_916_, 1);
lean_inc(v_target_925_);
lean_dec_ref(v_k_x27_916_);
v___x_926_ = lean_apply_2(v_h__2_918_, v_package_924_, v_target_925_);
return v___x_926_;
}
case 2:
{
lean_object* v_package_927_; lean_object* v_module_928_; lean_object* v___x_929_; 
lean_dec(v_h__4_920_);
lean_dec(v_h__2_918_);
lean_dec(v_h__1_917_);
v_package_927_ = lean_ctor_get(v_k_x27_916_, 0);
lean_inc(v_package_927_);
v_module_928_ = lean_ctor_get(v_k_x27_916_, 1);
lean_inc(v_module_928_);
lean_dec_ref(v_k_x27_916_);
v___x_929_ = lean_apply_2(v_h__3_919_, v_package_927_, v_module_928_);
return v___x_929_;
}
default: 
{
lean_object* v___x_930_; 
lean_dec(v_h__3_919_);
lean_dec(v_h__2_918_);
lean_dec(v_h__1_917_);
v___x_930_ = lean_apply_4(v_h__4_920_, v_k_x27_916_, lean_box(0), lean_box(0), lean_box(0));
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_931_, lean_object* v_k_x27_932_, lean_object* v_h__1_933_, lean_object* v_h__2_934_, lean_object* v_h__3_935_, lean_object* v_h__4_936_){
_start:
{
switch(lean_obj_tag(v_k_x27_932_))
{
case 4:
{
lean_object* v_target_937_; lean_object* v_facet_938_; lean_object* v___x_939_; 
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
v_target_937_ = lean_ctor_get(v_k_x27_932_, 0);
lean_inc_ref(v_target_937_);
v_facet_938_ = lean_ctor_get(v_k_x27_932_, 1);
lean_inc(v_facet_938_);
lean_dec_ref(v_k_x27_932_);
v___x_939_ = lean_apply_2(v_h__1_933_, v_target_937_, v_facet_938_);
return v___x_939_;
}
case 3:
{
lean_object* v_package_940_; lean_object* v_target_941_; lean_object* v___x_942_; 
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__1_933_);
v_package_940_ = lean_ctor_get(v_k_x27_932_, 0);
lean_inc(v_package_940_);
v_target_941_ = lean_ctor_get(v_k_x27_932_, 1);
lean_inc(v_target_941_);
lean_dec_ref(v_k_x27_932_);
v___x_942_ = lean_apply_2(v_h__2_934_, v_package_940_, v_target_941_);
return v___x_942_;
}
case 2:
{
lean_object* v_package_943_; lean_object* v_module_944_; lean_object* v___x_945_; 
lean_dec(v_h__4_936_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_package_943_ = lean_ctor_get(v_k_x27_932_, 0);
lean_inc(v_package_943_);
v_module_944_ = lean_ctor_get(v_k_x27_932_, 1);
lean_inc(v_module_944_);
lean_dec_ref(v_k_x27_932_);
v___x_945_ = lean_apply_2(v_h__3_935_, v_package_943_, v_module_944_);
return v___x_945_;
}
default: 
{
lean_object* v___x_946_; 
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v___x_946_ = lean_apply_4(v_h__4_936_, v_k_x27_932_, lean_box(0), lean_box(0), lean_box(0));
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_947_, lean_object* v_h__1_948_, lean_object* v_h__2_949_){
_start:
{
if (v_x_947_ == 1)
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_h__2_949_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_apply_1(v_h__1_948_, v___x_950_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_h__1_948_);
v___x_952_ = lean_box(v_x_947_);
v___x_953_ = lean_apply_2(v_h__2_949_, v___x_952_, lean_box(0));
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_954_, lean_object* v_h__1_955_, lean_object* v_h__2_956_){
_start:
{
uint8_t v_x_17__boxed_957_; lean_object* v_res_958_; 
v_x_17__boxed_957_ = lean_unbox(v_x_954_);
v_res_958_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_17__boxed_957_, v_h__1_955_, v_h__2_956_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_959_, uint8_t v_x_960_, lean_object* v_h__1_961_, lean_object* v_h__2_962_){
_start:
{
if (v_x_960_ == 1)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_h__2_962_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_apply_1(v_h__1_961_, v___x_963_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_h__1_961_);
v___x_965_ = lean_box(v_x_960_);
v___x_966_ = lean_apply_2(v_h__2_962_, v___x_965_, lean_box(0));
return v___x_966_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_967_, lean_object* v_x_968_, lean_object* v_h__1_969_, lean_object* v_h__2_970_){
_start:
{
uint8_t v_x_28__boxed_971_; lean_object* v_res_972_; 
v_x_28__boxed_971_ = lean_unbox(v_x_968_);
v_res_972_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_967_, v_x_28__boxed_971_, v_h__1_969_, v_h__2_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_973_, lean_object* v_h__1_974_, lean_object* v_h__2_975_, lean_object* v_h__3_976_){
_start:
{
switch(lean_obj_tag(v_k_x27_973_))
{
case 4:
{
lean_object* v_target_977_; lean_object* v_facet_978_; lean_object* v___x_979_; 
lean_dec(v_h__3_976_);
lean_dec(v_h__2_975_);
v_target_977_ = lean_ctor_get(v_k_x27_973_, 0);
lean_inc_ref(v_target_977_);
v_facet_978_ = lean_ctor_get(v_k_x27_973_, 1);
lean_inc(v_facet_978_);
lean_dec_ref(v_k_x27_973_);
v___x_979_ = lean_apply_2(v_h__1_974_, v_target_977_, v_facet_978_);
return v___x_979_;
}
case 3:
{
lean_object* v_package_980_; lean_object* v_target_981_; lean_object* v___x_982_; 
lean_dec(v_h__3_976_);
lean_dec(v_h__1_974_);
v_package_980_ = lean_ctor_get(v_k_x27_973_, 0);
lean_inc(v_package_980_);
v_target_981_ = lean_ctor_get(v_k_x27_973_, 1);
lean_inc(v_target_981_);
lean_dec_ref(v_k_x27_973_);
v___x_982_ = lean_apply_2(v_h__2_975_, v_package_980_, v_target_981_);
return v___x_982_;
}
default: 
{
lean_object* v___x_983_; 
lean_dec(v_h__2_975_);
lean_dec(v_h__1_974_);
v___x_983_ = lean_apply_3(v_h__3_976_, v_k_x27_973_, lean_box(0), lean_box(0));
return v___x_983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_984_, lean_object* v_k_x27_985_, lean_object* v_h__1_986_, lean_object* v_h__2_987_, lean_object* v_h__3_988_){
_start:
{
switch(lean_obj_tag(v_k_x27_985_))
{
case 4:
{
lean_object* v_target_989_; lean_object* v_facet_990_; lean_object* v___x_991_; 
lean_dec(v_h__3_988_);
lean_dec(v_h__2_987_);
v_target_989_ = lean_ctor_get(v_k_x27_985_, 0);
lean_inc_ref(v_target_989_);
v_facet_990_ = lean_ctor_get(v_k_x27_985_, 1);
lean_inc(v_facet_990_);
lean_dec_ref(v_k_x27_985_);
v___x_991_ = lean_apply_2(v_h__1_986_, v_target_989_, v_facet_990_);
return v___x_991_;
}
case 3:
{
lean_object* v_package_992_; lean_object* v_target_993_; lean_object* v___x_994_; 
lean_dec(v_h__3_988_);
lean_dec(v_h__1_986_);
v_package_992_ = lean_ctor_get(v_k_x27_985_, 0);
lean_inc(v_package_992_);
v_target_993_ = lean_ctor_get(v_k_x27_985_, 1);
lean_inc(v_target_993_);
lean_dec_ref(v_k_x27_985_);
v___x_994_ = lean_apply_2(v_h__2_987_, v_package_992_, v_target_993_);
return v___x_994_;
}
default: 
{
lean_object* v___x_995_; 
lean_dec(v_h__2_987_);
lean_dec(v_h__1_986_);
v___x_995_ = lean_apply_3(v_h__3_988_, v_k_x27_985_, lean_box(0), lean_box(0));
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_996_, lean_object* v_h__1_997_, lean_object* v_h__2_998_){
_start:
{
if (lean_obj_tag(v_k_x27_996_) == 4)
{
lean_object* v_target_999_; lean_object* v_facet_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__2_998_);
v_target_999_ = lean_ctor_get(v_k_x27_996_, 0);
lean_inc_ref(v_target_999_);
v_facet_1000_ = lean_ctor_get(v_k_x27_996_, 1);
lean_inc(v_facet_1000_);
lean_dec_ref(v_k_x27_996_);
v___x_1001_ = lean_apply_2(v_h__1_997_, v_target_999_, v_facet_1000_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; 
lean_dec(v_h__1_997_);
v___x_1002_ = lean_apply_2(v_h__2_998_, v_k_x27_996_, lean_box(0));
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_1003_, lean_object* v_k_x27_1004_, lean_object* v_h__1_1005_, lean_object* v_h__2_1006_){
_start:
{
if (lean_obj_tag(v_k_x27_1004_) == 4)
{
lean_object* v_target_1007_; lean_object* v_facet_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__2_1006_);
v_target_1007_ = lean_ctor_get(v_k_x27_1004_, 0);
lean_inc_ref(v_target_1007_);
v_facet_1008_ = lean_ctor_get(v_k_x27_1004_, 1);
lean_inc(v_facet_1008_);
lean_dec_ref(v_k_x27_1004_);
v___x_1009_ = lean_apply_2(v_h__1_1005_, v_target_1007_, v_facet_1008_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; 
lean_dec(v_h__1_1005_);
v___x_1010_ = lean_apply_2(v_h__2_1006_, v_k_x27_1004_, lean_box(0));
return v___x_1010_;
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
