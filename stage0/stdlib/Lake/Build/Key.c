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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_9_, 2);
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
lean_dec_ref_known(v_t_9_, 2);
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
lean_dec_ref_known(v_t_9_, 2);
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
lean_dec_ref_known(v_x_112_, 1);
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
lean_dec_ref_known(v_x_112_, 1);
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
uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v___x_270_; 
v___x_268_ = 1723ULL;
v___x_269_ = 0ULL;
v___x_270_ = lean_uint64_mix_hash(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static uint64_t _init_l_Lake_instHashableBuildKey_hash___closed__1(void){
_start:
{
uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; 
v___x_271_ = 1723ULL;
v___x_272_ = 1ULL;
v___x_273_ = lean_uint64_mix_hash(v___x_272_, v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT uint64_t l_Lake_instHashableBuildKey_hash(lean_object* v_x_274_){
_start:
{
switch(lean_obj_tag(v_x_274_))
{
case 0:
{
lean_object* v_module_275_; uint64_t v___x_276_; 
v_module_275_ = lean_ctor_get(v_x_274_, 0);
v___x_276_ = 0ULL;
if (lean_obj_tag(v_module_275_) == 0)
{
uint64_t v___x_277_; 
v___x_277_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__0, &l_Lake_instHashableBuildKey_hash___closed__0_once, _init_l_Lake_instHashableBuildKey_hash___closed__0);
return v___x_277_;
}
else
{
uint64_t v_hash_278_; uint64_t v___x_279_; 
v_hash_278_ = lean_ctor_get_uint64(v_module_275_, sizeof(void*)*2);
v___x_279_ = lean_uint64_mix_hash(v___x_276_, v_hash_278_);
return v___x_279_;
}
}
case 1:
{
lean_object* v_package_280_; uint64_t v___x_281_; 
v_package_280_ = lean_ctor_get(v_x_274_, 0);
v___x_281_ = 1ULL;
if (lean_obj_tag(v_package_280_) == 0)
{
uint64_t v___x_282_; 
v___x_282_ = lean_uint64_once(&l_Lake_instHashableBuildKey_hash___closed__1, &l_Lake_instHashableBuildKey_hash___closed__1_once, _init_l_Lake_instHashableBuildKey_hash___closed__1);
return v___x_282_;
}
else
{
uint64_t v_hash_283_; uint64_t v___x_284_; 
v_hash_283_ = lean_ctor_get_uint64(v_package_280_, sizeof(void*)*2);
v___x_284_ = lean_uint64_mix_hash(v___x_281_, v_hash_283_);
return v___x_284_;
}
}
case 2:
{
lean_object* v_package_285_; lean_object* v_module_286_; uint64_t v___x_287_; uint64_t v___y_289_; 
v_package_285_ = lean_ctor_get(v_x_274_, 0);
v_module_286_ = lean_ctor_get(v_x_274_, 1);
v___x_287_ = 2ULL;
if (lean_obj_tag(v_package_285_) == 0)
{
uint64_t v___x_295_; 
v___x_295_ = 1723ULL;
v___y_289_ = v___x_295_;
goto v___jp_288_;
}
else
{
uint64_t v_hash_296_; 
v_hash_296_ = lean_ctor_get_uint64(v_package_285_, sizeof(void*)*2);
v___y_289_ = v_hash_296_;
goto v___jp_288_;
}
v___jp_288_:
{
uint64_t v___x_290_; 
v___x_290_ = lean_uint64_mix_hash(v___x_287_, v___y_289_);
if (lean_obj_tag(v_module_286_) == 0)
{
uint64_t v___x_291_; uint64_t v___x_292_; 
v___x_291_ = 1723ULL;
v___x_292_ = lean_uint64_mix_hash(v___x_290_, v___x_291_);
return v___x_292_;
}
else
{
uint64_t v_hash_293_; uint64_t v___x_294_; 
v_hash_293_ = lean_ctor_get_uint64(v_module_286_, sizeof(void*)*2);
v___x_294_ = lean_uint64_mix_hash(v___x_290_, v_hash_293_);
return v___x_294_;
}
}
}
case 3:
{
lean_object* v_package_297_; lean_object* v_target_298_; uint64_t v___x_299_; uint64_t v___y_301_; 
v_package_297_ = lean_ctor_get(v_x_274_, 0);
v_target_298_ = lean_ctor_get(v_x_274_, 1);
v___x_299_ = 3ULL;
if (lean_obj_tag(v_package_297_) == 0)
{
uint64_t v___x_307_; 
v___x_307_ = 1723ULL;
v___y_301_ = v___x_307_;
goto v___jp_300_;
}
else
{
uint64_t v_hash_308_; 
v_hash_308_ = lean_ctor_get_uint64(v_package_297_, sizeof(void*)*2);
v___y_301_ = v_hash_308_;
goto v___jp_300_;
}
v___jp_300_:
{
uint64_t v___x_302_; 
v___x_302_ = lean_uint64_mix_hash(v___x_299_, v___y_301_);
if (lean_obj_tag(v_target_298_) == 0)
{
uint64_t v___x_303_; uint64_t v___x_304_; 
v___x_303_ = 1723ULL;
v___x_304_ = lean_uint64_mix_hash(v___x_302_, v___x_303_);
return v___x_304_;
}
else
{
uint64_t v_hash_305_; uint64_t v___x_306_; 
v_hash_305_ = lean_ctor_get_uint64(v_target_298_, sizeof(void*)*2);
v___x_306_ = lean_uint64_mix_hash(v___x_302_, v_hash_305_);
return v___x_306_;
}
}
}
default: 
{
lean_object* v_target_309_; lean_object* v_facet_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; 
v_target_309_ = lean_ctor_get(v_x_274_, 0);
v_facet_310_ = lean_ctor_get(v_x_274_, 1);
v___x_311_ = 4ULL;
v___x_312_ = l_Lake_instHashableBuildKey_hash(v_target_309_);
v___x_313_ = lean_uint64_mix_hash(v___x_311_, v___x_312_);
if (lean_obj_tag(v_facet_310_) == 0)
{
uint64_t v___x_314_; uint64_t v___x_315_; 
v___x_314_ = 1723ULL;
v___x_315_ = lean_uint64_mix_hash(v___x_313_, v___x_314_);
return v___x_315_;
}
else
{
uint64_t v_hash_316_; uint64_t v___x_317_; 
v_hash_316_ = lean_ctor_get_uint64(v_facet_310_, sizeof(void*)*2);
v___x_317_ = lean_uint64_mix_hash(v___x_313_, v_hash_316_);
return v___x_317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey_hash___boxed(lean_object* v_x_318_){
_start:
{
uint64_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Lake_instHashableBuildKey_hash(v_x_318_);
lean_dec_ref(v_x_318_);
v_r_320_ = lean_box_uint64(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object* v_key_323_){
_start:
{
lean_inc_ref(v_key_323_);
return v_key_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object* v_key_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lake_PartialBuildKey_mk(v_key_324_);
lean_dec_ref(v_key_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(lean_object* v_x_328_, lean_object* v_prec_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lake_instReprBuildKey_repr(v_x_328_, v_prec_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(lean_object* v_x_331_, lean_object* v_prec_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(v_x_331_, v_prec_332_);
lean_dec(v_prec_332_);
return v_res_333_;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_342_ = lean_string_utf8_byte_size(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* v_pkg_346_, lean_object* v_target_347_){
_start:
{
lean_object* v_str_348_; lean_object* v_startInclusive_349_; lean_object* v_endExclusive_350_; uint8_t v___y_352_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v_str_348_ = lean_ctor_get(v_target_347_, 0);
v_startInclusive_349_ = lean_ctor_get(v_target_347_, 1);
v_endExclusive_350_ = lean_ctor_get(v_target_347_, 2);
v___x_365_ = lean_nat_sub(v_endExclusive_350_, v_startInclusive_349_);
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_nat_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_369_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_370_ = lean_nat_dec_le(v___x_369_, v___x_365_);
lean_dec(v___x_365_);
if (v___x_370_ == 0)
{
v___y_352_ = v___x_367_;
goto v___jp_351_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = lean_string_memcmp(v_str_348_, v___x_368_, v_startInclusive_349_, v___x_366_, v___x_369_);
v___y_352_ = v___x_371_;
goto v___jp_351_;
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v___x_365_);
lean_dec(v_pkg_346_);
v___x_372_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3));
return v___x_372_;
}
v___jp_351_:
{
if (v___y_352_ == 0)
{
lean_object* v___x_353_; lean_object* v_target_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = lean_string_utf8_extract_fast(v_str_348_, v_startInclusive_349_, v_endExclusive_350_);
v_target_354_ = l_Lake_stringToLegalOrSimpleName(v___x_353_);
v___x_355_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_355_, 0, v_pkg_346_);
lean_ctor_set(v___x_355_, 1, v_target_354_);
v___x_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_target_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = l_String_Slice_Pos_nextn(v_target_347_, v___x_358_, v___x_357_);
v___x_360_ = lean_nat_add(v_startInclusive_349_, v___x_359_);
lean_dec(v___x_359_);
v___x_361_ = lean_string_utf8_extract_fast(v_str_348_, v___x_360_, v_endExclusive_350_);
lean_dec(v___x_360_);
v_target_362_ = l_Lake_stringToLegalOrSimpleName(v___x_361_);
v___x_363_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_363_, 0, v_pkg_346_);
lean_ctor_set(v___x_363_, 1, v_target_362_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* v_pkg_373_, lean_object* v_target_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v_pkg_373_, v_target_374_);
lean_dec_ref(v_target_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* v_s_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* v_s_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_380_);
lean_dec_ref(v_s_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* v_s_382_, lean_object* v___x_383_, lean_object* v___x_384_, lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
lean_object* v_it_388_; lean_object* v_startInclusive_389_; lean_object* v_endExclusive_390_; 
if (lean_obj_tag(v_a_385_) == 0)
{
lean_object* v_currPos_394_; lean_object* v_searcher_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_421_; 
v_currPos_394_ = lean_ctor_get(v_a_385_, 0);
v_searcher_395_ = lean_ctor_get(v_a_385_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_385_);
if (v_isSharedCheck_421_ == 0)
{
v___x_397_ = v_a_385_;
v_isShared_398_ = v_isSharedCheck_421_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_searcher_395_);
lean_inc(v_currPos_394_);
lean_dec(v_a_385_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_421_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_startInclusive_399_; lean_object* v_endExclusive_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_startInclusive_399_ = lean_ctor_get(v___x_383_, 1);
v_endExclusive_400_ = lean_ctor_get(v___x_383_, 2);
v___x_401_ = lean_nat_sub(v_endExclusive_400_, v_startInclusive_399_);
v___x_402_ = lean_nat_dec_eq(v_searcher_395_, v___x_401_);
lean_dec(v___x_401_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint32_t v___x_404_; uint8_t v___x_405_; 
v___x_403_ = 47;
v___x_404_ = lean_string_utf8_get_fast(v_s_382_, v_searcher_395_);
v___x_405_ = lean_uint32_dec_eq(v___x_404_, v___x_403_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_string_utf8_next_fast(v_s_382_, v_searcher_395_);
lean_dec(v_searcher_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_406_);
v___x_408_ = v___x_397_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_currPos_394_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_410_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
v_a_385_ = v___x_408_;
goto _start;
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_slice_414_; lean_object* v_nextIt_416_; 
v___x_411_ = lean_string_utf8_next_fast(v_s_382_, v_searcher_395_);
v___x_412_ = lean_nat_sub(v___x_411_, v_searcher_395_);
v___x_413_ = lean_nat_add(v_searcher_395_, v___x_412_);
lean_dec(v___x_412_);
v_slice_414_ = l_String_Slice_subslice_x21(v___x_383_, v_currPos_394_, v_searcher_395_);
lean_inc(v___x_413_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v___x_413_);
lean_ctor_set(v___x_397_, 0, v___x_413_);
v_nextIt_416_ = v___x_397_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_413_);
v_nextIt_416_ = v_reuseFailAlloc_419_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v_startInclusive_417_; lean_object* v_endExclusive_418_; 
v_startInclusive_417_ = lean_ctor_get(v_slice_414_, 0);
lean_inc(v_startInclusive_417_);
v_endExclusive_418_ = lean_ctor_get(v_slice_414_, 1);
lean_inc(v_endExclusive_418_);
lean_dec_ref(v_slice_414_);
v_it_388_ = v_nextIt_416_;
v_startInclusive_389_ = v_startInclusive_417_;
v_endExclusive_390_ = v_endExclusive_418_;
goto v___jp_387_;
}
}
}
else
{
lean_object* v___x_420_; 
lean_del_object(v___x_397_);
lean_dec(v_searcher_395_);
v___x_420_ = lean_box(1);
lean_inc(v___x_384_);
v_it_388_ = v___x_420_;
v_startInclusive_389_ = v_currPos_394_;
v_endExclusive_390_ = v___x_384_;
goto v___jp_387_;
}
}
}
else
{
lean_dec(v___x_384_);
lean_dec_ref(v_s_382_);
return v_b_386_;
}
v___jp_387_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc_ref(v_s_382_);
v___x_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_391_, 0, v_s_382_);
lean_ctor_set(v___x_391_, 1, v_startInclusive_389_);
lean_ctor_set(v___x_391_, 2, v_endExclusive_390_);
v___x_392_ = lean_array_push(v_b_386_, v___x_391_);
v_a_385_ = v_it_388_;
v_b_386_ = v___x_392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object* v_s_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v_a_425_, lean_object* v_b_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_422_, v___x_423_, v___x_424_, v_a_425_, v_b_426_);
lean_dec_ref(v___x_423_);
return v_res_427_;
}
}
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_440_ = lean_string_utf8_byte_size(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object* v_s_441_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_string_utf8_byte_size(v_s_441_);
lean_inc_ref(v_s_441_);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v_s_441_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
v___x_447_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v___x_446_);
v___x_448_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2));
v___x_449_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_441_, v___x_446_, v___x_445_, v___x_447_, v___x_448_);
lean_dec_ref_known(v___x_446_, 3);
v___x_450_ = lean_array_to_list(v___x_449_);
if (lean_obj_tag(v___x_450_) == 1)
{
lean_object* v_head_451_; lean_object* v_tail_452_; 
v_head_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_head_451_);
v_tail_452_ = lean_ctor_get(v___x_450_, 1);
lean_inc(v_tail_452_);
lean_dec_ref_known(v___x_450_, 2);
if (lean_obj_tag(v_tail_452_) == 0)
{
lean_object* v_str_456_; lean_object* v_startInclusive_457_; lean_object* v_endExclusive_458_; uint8_t v___y_460_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_str_456_ = lean_ctor_get(v_head_451_, 0);
v_startInclusive_457_ = lean_ctor_get(v_head_451_, 1);
v_endExclusive_458_ = lean_ctor_get(v_head_451_, 2);
v___x_486_ = lean_nat_sub(v_endExclusive_458_, v_startInclusive_457_);
v___x_487_ = lean_nat_dec_eq(v___x_486_, v___x_444_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_488_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_489_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
v___x_490_ = lean_nat_dec_le(v___x_489_, v___x_486_);
lean_dec(v___x_486_);
if (v___x_490_ == 0)
{
v___y_460_ = v___x_487_;
goto v___jp_459_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = lean_string_memcmp(v_str_456_, v___x_488_, v_startInclusive_457_, v___x_444_, v___x_489_);
v___y_460_ = v___x_491_;
goto v___jp_459_;
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v___x_486_);
lean_dec(v_head_451_);
v___x_492_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return v___x_492_;
}
v___jp_459_:
{
if (v___y_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_461_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_462_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_463_ = lean_nat_sub(v_endExclusive_458_, v_startInclusive_457_);
v___x_464_ = lean_nat_dec_le(v___x_462_, v___x_463_);
lean_dec(v___x_463_);
if (v___x_464_ == 0)
{
goto v___jp_453_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = lean_string_memcmp(v_str_456_, v___x_461_, v_startInclusive_457_, v___x_444_, v___x_462_);
if (v___x_465_ == 0)
{
goto v___jp_453_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
lean_inc(v_endExclusive_458_);
lean_inc(v_startInclusive_457_);
lean_inc_ref(v_str_456_);
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = l_String_Slice_Pos_nextn(v_head_451_, v___x_444_, v___x_466_);
lean_dec(v_head_451_);
v___x_468_ = lean_nat_add(v_startInclusive_457_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v_startInclusive_457_);
v___x_469_ = lean_nat_sub(v_endExclusive_458_, v___x_468_);
v___x_470_ = lean_nat_dec_eq(v___x_469_, v___x_444_);
lean_dec(v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_471_ = lean_string_utf8_extract_fast(v_str_456_, v___x_468_, v_endExclusive_458_);
lean_dec(v_endExclusive_458_);
lean_dec(v___x_468_);
lean_dec_ref(v_str_456_);
v___x_472_ = l_Lake_stringToLegalOrSimpleName(v___x_471_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; 
lean_dec(v___x_468_);
lean_dec(v_endExclusive_458_);
lean_dec_ref(v_str_456_);
v___x_475_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return v___x_475_;
}
}
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
lean_inc(v_endExclusive_458_);
lean_inc(v_startInclusive_457_);
lean_inc_ref(v_str_456_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = l_String_Slice_Pos_nextn(v_head_451_, v___x_444_, v___x_476_);
lean_dec(v_head_451_);
v___x_478_ = lean_nat_add(v_startInclusive_457_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v_startInclusive_457_);
v___x_479_ = lean_nat_sub(v_endExclusive_458_, v___x_478_);
v___x_480_ = lean_nat_dec_eq(v___x_479_, v___x_444_);
lean_dec(v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_string_utf8_extract_fast(v_str_456_, v___x_478_, v_endExclusive_458_);
lean_dec(v_endExclusive_458_);
lean_dec(v___x_478_);
lean_dec_ref(v_str_456_);
v___x_482_ = l_Lake_stringToLegalOrSimpleName(v___x_481_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
v___x_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; 
lean_dec(v___x_478_);
lean_dec(v_endExclusive_458_);
lean_dec_ref(v_str_456_);
v___x_485_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
return v___x_485_;
}
}
}
}
else
{
lean_object* v_head_493_; lean_object* v_tail_494_; lean_object* v_str_496_; lean_object* v_startInclusive_497_; lean_object* v_endExclusive_498_; 
v_head_493_ = lean_ctor_get(v_tail_452_, 0);
lean_inc(v_head_493_);
v_tail_494_ = lean_ctor_get(v_tail_452_, 1);
lean_inc(v_tail_494_);
lean_dec_ref_known(v_tail_452_, 2);
if (lean_obj_tag(v_tail_494_) == 0)
{
lean_object* v_str_506_; lean_object* v_startInclusive_507_; lean_object* v_endExclusive_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_str_506_ = lean_ctor_get(v_head_451_, 0);
lean_inc_ref(v_str_506_);
v_startInclusive_507_ = lean_ctor_get(v_head_451_, 1);
lean_inc(v_startInclusive_507_);
v_endExclusive_508_ = lean_ctor_get(v_head_451_, 2);
lean_inc(v_endExclusive_508_);
v___x_509_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_510_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
v___x_511_ = lean_nat_sub(v_endExclusive_508_, v_startInclusive_507_);
v___x_512_ = lean_nat_dec_le(v___x_510_, v___x_511_);
lean_dec(v___x_511_);
if (v___x_512_ == 0)
{
lean_dec(v_head_451_);
v_str_496_ = v_str_506_;
v_startInclusive_497_ = v_startInclusive_507_;
v_endExclusive_498_ = v_endExclusive_508_;
goto v___jp_495_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = lean_string_memcmp(v_str_506_, v___x_509_, v_startInclusive_507_, v___x_444_, v___x_510_);
if (v___x_513_ == 0)
{
lean_dec(v_head_451_);
v_str_496_ = v_str_506_;
v_startInclusive_497_ = v_startInclusive_507_;
v_endExclusive_498_ = v_endExclusive_508_;
goto v___jp_495_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = l_String_Slice_Pos_nextn(v_head_451_, v___x_444_, v___x_514_);
lean_dec(v_head_451_);
v___x_516_ = lean_nat_add(v_startInclusive_507_, v___x_515_);
lean_dec(v___x_515_);
lean_dec(v_startInclusive_507_);
v_str_496_ = v_str_506_;
v_startInclusive_497_ = v___x_516_;
v_endExclusive_498_ = v_endExclusive_508_;
goto v___jp_495_;
}
}
}
else
{
lean_dec(v_tail_494_);
lean_dec(v_head_493_);
lean_dec(v_head_451_);
goto v___jp_442_;
}
v___jp_495_:
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_nat_sub(v_endExclusive_498_, v_startInclusive_497_);
v___x_500_ = lean_nat_dec_eq(v___x_499_, v___x_444_);
lean_dec(v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_string_utf8_extract_fast(v_str_496_, v_startInclusive_497_, v_endExclusive_498_);
lean_dec(v_endExclusive_498_);
lean_dec(v_startInclusive_497_);
lean_dec_ref(v_str_496_);
v___x_502_ = l_Lake_stringToLegalOrSimpleName(v___x_501_);
v___x_503_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_502_, v_head_493_);
lean_dec(v_head_493_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_endExclusive_498_);
lean_dec(v_startInclusive_497_);
lean_dec_ref(v_str_496_);
v___x_504_ = lean_box(0);
v___x_505_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_504_, v_head_493_);
lean_dec(v_head_493_);
return v___x_505_;
}
}
}
v___jp_453_:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_box(0);
v___x_455_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_454_, v_head_451_);
lean_dec(v_head_451_);
return v___x_455_;
}
}
else
{
lean_dec(v___x_450_);
goto v___jp_442_;
}
v___jp_442_:
{
lean_object* v___x_443_; 
v___x_443_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1));
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* v_s_517_, lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v_inst_520_, lean_object* v_R_521_, lean_object* v_a_522_, lean_object* v_b_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_517_, v___x_518_, v___x_519_, v_a_522_, v_b_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* v_s_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v_inst_528_, lean_object* v_R_529_, lean_object* v_a_530_, lean_object* v_b_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_525_, v___x_526_, v___x_527_, v_inst_528_, v_R_529_, v_a_530_, v_b_531_);
lean_dec_ref(v___x_526_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_535_);
lean_dec_ref(v_s_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
v___x_541_ = lean_panic_fn_borrowed(v___x_540_, v_msg_538_);
lean_dec_ref_known(v___x_540_, 1);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_542_, lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
lean_object* v_it_548_; lean_object* v_startInclusive_549_; lean_object* v_endExclusive_550_; 
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v_currPos_555_; lean_object* v_searcher_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_582_; 
v_currPos_555_ = lean_ctor_get(v_a_545_, 0);
v_searcher_556_ = lean_ctor_get(v_a_545_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_a_545_);
if (v_isSharedCheck_582_ == 0)
{
v___x_558_ = v_a_545_;
v_isShared_559_ = v_isSharedCheck_582_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_searcher_556_);
lean_inc(v_currPos_555_);
lean_dec(v_a_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_582_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_startInclusive_560_; lean_object* v_endExclusive_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_startInclusive_560_ = lean_ctor_get(v___x_543_, 1);
v_endExclusive_561_ = lean_ctor_get(v___x_543_, 2);
v___x_562_ = lean_nat_sub(v_endExclusive_561_, v_startInclusive_560_);
v___x_563_ = lean_nat_dec_eq(v_searcher_556_, v___x_562_);
lean_dec(v___x_562_);
if (v___x_563_ == 0)
{
uint32_t v___x_564_; uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_564_ = 58;
v___x_565_ = lean_string_utf8_get_fast(v_s_542_, v_searcher_556_);
v___x_566_ = lean_uint32_dec_eq(v___x_565_, v___x_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_string_utf8_next_fast(v_s_542_, v_searcher_556_);
lean_dec(v_searcher_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_567_);
v___x_569_ = v___x_558_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_currPos_555_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v_a_545_ = v___x_569_;
goto _start;
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_slice_575_; lean_object* v_nextIt_577_; 
v___x_572_ = lean_string_utf8_next_fast(v_s_542_, v_searcher_556_);
v___x_573_ = lean_nat_sub(v___x_572_, v_searcher_556_);
v___x_574_ = lean_nat_add(v_searcher_556_, v___x_573_);
lean_dec(v___x_573_);
v_slice_575_ = l_String_Slice_subslice_x21(v___x_543_, v_currPos_555_, v_searcher_556_);
lean_inc(v___x_574_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_574_);
lean_ctor_set(v___x_558_, 0, v___x_574_);
v_nextIt_577_ = v___x_558_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_574_);
v_nextIt_577_ = v_reuseFailAlloc_580_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v_startInclusive_578_; lean_object* v_endExclusive_579_; 
v_startInclusive_578_ = lean_ctor_get(v_slice_575_, 0);
lean_inc(v_startInclusive_578_);
v_endExclusive_579_ = lean_ctor_get(v_slice_575_, 1);
lean_inc(v_endExclusive_579_);
lean_dec_ref(v_slice_575_);
v_it_548_ = v_nextIt_577_;
v_startInclusive_549_ = v_startInclusive_578_;
v_endExclusive_550_ = v_endExclusive_579_;
goto v___jp_547_;
}
}
}
else
{
lean_object* v___x_581_; 
lean_del_object(v___x_558_);
lean_dec(v_searcher_556_);
v___x_581_ = lean_box(1);
lean_inc(v___x_544_);
v_it_548_ = v___x_581_;
v_startInclusive_549_ = v_currPos_555_;
v_endExclusive_550_ = v___x_544_;
goto v___jp_547_;
}
}
}
else
{
lean_dec(v___x_544_);
lean_dec_ref(v_s_542_);
return v_b_546_;
}
v___jp_547_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_inc_ref(v_s_542_);
v___x_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_551_, 0, v_s_542_);
lean_ctor_set(v___x_551_, 1, v_startInclusive_549_);
lean_ctor_set(v___x_551_, 2, v_endExclusive_550_);
v___x_552_ = l_String_Slice_toString(v___x_551_);
lean_dec_ref_known(v___x_551_, 3);
v___x_553_ = lean_array_push(v_b_546_, v___x_552_);
v_a_545_ = v_it_548_;
v_b_546_ = v___x_553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_583_, lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v_a_586_, lean_object* v_b_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_583_, v___x_584_, v___x_585_, v_a_586_, v_b_587_);
lean_dec_ref(v___x_584_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_594_, 0, v_x_592_);
return v___x_594_;
}
else
{
lean_object* v_head_595_; lean_object* v_tail_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_609_; 
v_head_595_ = lean_ctor_get(v_x_593_, 0);
v_tail_596_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_609_ == 0)
{
v___x_598_ = v_x_593_;
v_isShared_599_ = v_isSharedCheck_609_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_tail_596_);
lean_inc(v_head_595_);
lean_dec(v_x_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_609_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = lean_string_utf8_byte_size(v_head_595_);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_nat_dec_eq(v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = l_Lake_stringToLegalOrSimpleName(v_head_595_);
if (v_isShared_599_ == 0)
{
lean_ctor_set_tag(v___x_598_, 4);
lean_ctor_set(v___x_598_, 1, v___x_603_);
lean_ctor_set(v___x_598_, 0, v_x_592_);
v___x_605_ = v___x_598_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_x_592_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v___x_603_);
v___x_605_ = v_reuseFailAlloc_607_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
v_x_592_ = v___x_605_;
v_x_593_ = v_tail_596_;
goto _start;
}
}
else
{
lean_object* v___x_608_; 
lean_del_object(v___x_598_);
lean_dec(v_tail_596_);
lean_dec(v_head_595_);
lean_dec_ref(v_x_592_);
v___x_608_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_608_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_616_ = lean_unsigned_to_nat(4u);
v___x_617_ = lean_unsigned_to_nat(65u);
v___x_618_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_619_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_620_ = l_mkPanicMessageWithDecl(v___x_619_, v___x_618_, v___x_617_, v___x_616_, v___x_615_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_string_utf8_byte_size(v_s_624_);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_nat_dec_eq(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_inc_ref(v_s_624_);
v___x_628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_628_, 0, v_s_624_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_625_);
v___x_629_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v___x_628_);
v___x_630_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_631_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_624_, v___x_628_, v___x_625_, v___x_629_, v___x_630_);
lean_dec_ref_known(v___x_628_, 3);
v___x_632_ = lean_array_to_list(v___x_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_634_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_633_);
return v___x_634_;
}
else
{
lean_object* v_head_635_; lean_object* v_tail_636_; lean_object* v___x_637_; 
v_head_635_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_head_635_);
v_tail_636_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_tail_636_);
lean_dec_ref_known(v___x_632_, 2);
v___x_637_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_635_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_dec(v_tail_636_);
return v___x_637_;
}
else
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_638_, v_tail_636_);
return v___x_639_;
}
}
}
else
{
lean_object* v___x_640_; 
lean_dec_ref(v_s_624_);
v___x_640_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_641_, lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v_inst_644_, lean_object* v_R_645_, lean_object* v_a_646_, lean_object* v_b_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_641_, v___x_642_, v___x_643_, v_a_646_, v_b_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v_inst_652_, lean_object* v_R_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_649_, v___x_650_, v___x_651_, v_inst_652_, v_R_653_, v_a_654_, v_b_655_);
lean_dec_ref(v___x_650_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_657_){
_start:
{
switch(lean_obj_tag(v_p_657_))
{
case 0:
{
return v_p_657_;
}
case 2:
{
lean_object* v_pre_658_; 
v_pre_658_ = lean_ctor_get(v_p_657_, 0);
if (lean_obj_tag(v_pre_658_) == 0)
{
return v_pre_658_;
}
else
{
lean_inc(v_pre_658_);
return v_pre_658_;
}
}
default: 
{
lean_inc(v_p_657_);
return v_p_657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_659_);
lean_dec(v_p_659_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_664_){
_start:
{
switch(lean_obj_tag(v_x_664_))
{
case 0:
{
lean_object* v_module_665_; lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_module_665_ = lean_ctor_get(v_x_664_, 0);
lean_inc(v_module_665_);
lean_dec_ref_known(v_x_664_, 1);
v___x_666_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_667_ = 1;
v___x_668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_665_, v___x_667_);
v___x_669_ = lean_string_append(v___x_666_, v___x_668_);
lean_dec_ref(v___x_668_);
return v___x_669_;
}
case 1:
{
lean_object* v_package_670_; lean_object* v___x_671_; 
v_package_670_ = lean_ctor_get(v_x_664_, 0);
lean_inc(v_package_670_);
lean_dec_ref_known(v_x_664_, 1);
v___x_671_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_670_);
lean_dec(v_package_670_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_672_; 
v___x_672_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_672_;
}
else
{
lean_object* v___x_673_; uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_673_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_674_ = 1;
v___x_675_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_671_, v___x_674_);
v___x_676_ = lean_string_append(v___x_673_, v___x_675_);
lean_dec_ref(v___x_675_);
return v___x_676_;
}
}
case 2:
{
lean_object* v_package_677_; lean_object* v_module_678_; lean_object* v___x_679_; 
v_package_677_ = lean_ctor_get(v_x_664_, 0);
lean_inc(v_package_677_);
v_module_678_ = lean_ctor_get(v_x_664_, 1);
lean_inc(v_module_678_);
lean_dec_ref_known(v_x_664_, 2);
v___x_679_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_677_);
lean_dec(v_package_677_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_680_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_681_ = 1;
v___x_682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_678_, v___x_681_);
v___x_683_ = lean_string_append(v___x_680_, v___x_682_);
lean_dec_ref(v___x_682_);
return v___x_683_;
}
else
{
uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_684_ = 1;
v___x_685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_679_, v___x_684_);
v___x_686_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_687_ = lean_string_append(v___x_685_, v___x_686_);
v___x_688_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_678_, v___x_684_);
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
lean_dec_ref(v___x_688_);
return v___x_689_;
}
}
case 3:
{
lean_object* v_package_690_; lean_object* v_target_691_; lean_object* v___x_692_; 
v_package_690_ = lean_ctor_get(v_x_664_, 0);
lean_inc(v_package_690_);
v_target_691_ = lean_ctor_get(v_x_664_, 1);
lean_inc(v_target_691_);
lean_dec_ref_known(v_x_664_, 2);
v___x_692_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_690_);
lean_dec(v_package_690_);
if (lean_obj_tag(v___x_692_) == 0)
{
uint8_t v___x_693_; lean_object* v___x_694_; 
v___x_693_ = 1;
v___x_694_ = l_Lean_Name_toString(v_target_691_, v___x_693_);
return v___x_694_;
}
else
{
uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_695_ = 1;
v___x_696_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_692_, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_698_ = lean_string_append(v___x_696_, v___x_697_);
v___x_699_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_691_, v___x_695_);
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
lean_dec_ref(v___x_699_);
return v___x_700_;
}
}
default: 
{
lean_object* v_target_701_; lean_object* v_facet_702_; uint8_t v___x_703_; 
v_target_701_ = lean_ctor_get(v_x_664_, 0);
lean_inc_ref(v_target_701_);
v_facet_702_ = lean_ctor_get(v_x_664_, 1);
lean_inc(v_facet_702_);
lean_dec_ref_known(v_x_664_, 2);
v___x_703_ = l_Lean_Name_isAnonymous(v_facet_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_704_ = l_Lake_PartialBuildKey_toString(v_target_701_);
v___x_705_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_706_ = lean_string_append(v___x_704_, v___x_705_);
v___x_707_ = 1;
v___x_708_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_702_, v___x_707_);
v___x_709_ = lean_string_append(v___x_706_, v___x_708_);
lean_dec_ref(v___x_708_);
return v___x_709_;
}
else
{
lean_dec(v_facet_702_);
v_x_664_ = v_target_701_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_713_, lean_object* v_facet_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v_module_713_);
v___x_716_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v_facet_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_717_, lean_object* v_facet_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v_package_717_);
v___x_720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v_facet_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_721_, lean_object* v_module_722_, lean_object* v_facet_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_724_, 0, v_package_721_);
lean_ctor_set(v___x_724_, 1, v_module_722_);
v___x_725_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v_facet_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_726_, lean_object* v_target_727_, lean_object* v_facet_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_729_, 0, v_package_726_);
lean_ctor_set(v___x_729_, 1, v_target_727_);
v___x_730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_facet_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_731_, lean_object* v_target_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_733_, 0, v_package_731_);
lean_ctor_set(v___x_733_, 1, v_target_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_734_){
_start:
{
switch(lean_obj_tag(v_x_734_))
{
case 0:
{
lean_object* v_module_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_module_735_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_module_735_);
lean_dec_ref_known(v_x_734_, 1);
v___x_736_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_737_ = 1;
v___x_738_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_735_, v___x_737_);
v___x_739_ = lean_string_append(v___x_736_, v___x_738_);
lean_dec_ref(v___x_738_);
return v___x_739_;
}
case 1:
{
lean_object* v_package_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_package_740_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_package_740_);
lean_dec_ref_known(v_x_734_, 1);
v___x_741_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
v___x_742_ = l_Lean_Name_getPrefix(v_package_740_);
lean_dec(v_package_740_);
v___x_743_ = 1;
v___x_744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_742_, v___x_743_);
v___x_745_ = lean_string_append(v___x_741_, v___x_744_);
lean_dec_ref(v___x_744_);
return v___x_745_;
}
case 2:
{
lean_object* v_package_746_; lean_object* v_module_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_package_746_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_package_746_);
v_module_747_ = lean_ctor_get(v_x_734_, 1);
lean_inc(v_module_747_);
lean_dec_ref_known(v_x_734_, 2);
v___x_748_ = l_Lean_Name_getPrefix(v_package_746_);
lean_dec(v_package_746_);
v___x_749_ = 1;
v___x_750_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_748_, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
v___x_753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_747_, v___x_749_);
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
lean_dec_ref(v___x_753_);
return v___x_754_;
}
case 3:
{
lean_object* v_package_755_; lean_object* v_target_756_; lean_object* v___x_757_; uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_package_755_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_package_755_);
v_target_756_ = lean_ctor_get(v_x_734_, 1);
lean_inc(v_target_756_);
lean_dec_ref_known(v_x_734_, 2);
v___x_757_ = l_Lean_Name_getPrefix(v_package_755_);
lean_dec(v_package_755_);
v___x_758_ = 1;
v___x_759_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_757_, v___x_758_);
v___x_760_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
v___x_762_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_756_, v___x_758_);
v___x_763_ = lean_string_append(v___x_761_, v___x_762_);
lean_dec_ref(v___x_762_);
return v___x_763_;
}
default: 
{
lean_object* v_target_764_; lean_object* v_facet_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_target_764_ = lean_ctor_get(v_x_734_, 0);
lean_inc_ref(v_target_764_);
v_facet_765_ = lean_ctor_get(v_x_734_, 1);
lean_inc(v_facet_765_);
lean_dec_ref_known(v_x_734_, 2);
v___x_766_ = l_Lake_BuildKey_toString(v_target_764_);
v___x_767_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_768_ = lean_string_append(v___x_766_, v___x_767_);
v___x_769_ = l_Lake_Name_eraseHead(v_facet_765_);
v___x_770_ = 1;
v___x_771_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_769_, v___x_770_);
v___x_772_ = lean_string_append(v___x_768_, v___x_771_);
lean_dec_ref(v___x_771_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_773_){
_start:
{
lean_object* v_p_775_; lean_object* v_m_776_; 
switch(lean_obj_tag(v_x_773_))
{
case 0:
{
lean_object* v_module_784_; uint8_t v___x_785_; lean_object* v___x_786_; 
v_module_784_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_module_784_);
lean_dec_ref_known(v_x_773_, 1);
v___x_785_ = 1;
v___x_786_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_784_, v___x_785_);
return v___x_786_;
}
case 1:
{
lean_object* v_package_787_; lean_object* v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; 
v_package_787_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_package_787_);
lean_dec_ref_known(v_x_773_, 1);
v___x_788_ = l_Lean_Name_getPrefix(v_package_787_);
lean_dec(v_package_787_);
v___x_789_ = 1;
v___x_790_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_788_, v___x_789_);
return v___x_790_;
}
case 4:
{
lean_object* v_target_791_; lean_object* v_facet_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_target_791_ = lean_ctor_get(v_x_773_, 0);
lean_inc_ref(v_target_791_);
v_facet_792_ = lean_ctor_get(v_x_773_, 1);
lean_inc(v_facet_792_);
lean_dec_ref_known(v_x_773_, 2);
v___x_793_ = l_Lake_BuildKey_toSimpleString(v_target_791_);
v___x_794_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
v___x_796_ = l_Lake_Name_eraseHead(v_facet_792_);
v___x_797_ = 1;
v___x_798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_796_, v___x_797_);
v___x_799_ = lean_string_append(v___x_795_, v___x_798_);
lean_dec_ref(v___x_798_);
return v___x_799_;
}
default: 
{
lean_object* v_package_800_; lean_object* v_module_801_; 
v_package_800_ = lean_ctor_get(v_x_773_, 0);
lean_inc(v_package_800_);
v_module_801_ = lean_ctor_get(v_x_773_, 1);
lean_inc(v_module_801_);
lean_dec_ref(v_x_773_);
v_p_775_ = v_package_800_;
v_m_776_ = v_module_801_;
goto v___jp_774_;
}
}
v___jp_774_:
{
lean_object* v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_777_ = l_Lean_Name_getPrefix(v_p_775_);
lean_dec(v_p_775_);
v___x_778_ = 1;
v___x_779_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_777_, v___x_778_);
v___x_780_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
v___x_782_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_776_, v___x_778_);
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
lean_dec_ref(v___x_782_);
return v___x_783_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_804_, lean_object* v_k_x27_805_){
_start:
{
switch(lean_obj_tag(v_k_804_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_805_) == 0)
{
lean_object* v_module_806_; lean_object* v_module_807_; uint8_t v___x_808_; 
v_module_806_ = lean_ctor_get(v_k_804_, 0);
v_module_807_ = lean_ctor_get(v_k_x27_805_, 0);
v___x_808_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_806_, v_module_807_);
return v___x_808_;
}
else
{
uint8_t v___x_809_; 
v___x_809_ = 0;
return v___x_809_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_805_))
{
case 0:
{
uint8_t v___x_810_; 
v___x_810_ = 2;
return v___x_810_;
}
case 1:
{
lean_object* v_package_811_; lean_object* v_package_812_; uint8_t v___x_813_; 
v_package_811_ = lean_ctor_get(v_k_804_, 0);
v_package_812_ = lean_ctor_get(v_k_x27_805_, 0);
v___x_813_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_811_, v_package_812_);
return v___x_813_;
}
default: 
{
uint8_t v___x_814_; 
v___x_814_ = 0;
return v___x_814_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_805_))
{
case 4:
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
case 3:
{
uint8_t v___x_816_; 
v___x_816_ = 0;
return v___x_816_;
}
case 2:
{
lean_object* v_package_817_; lean_object* v_module_818_; lean_object* v_package_819_; lean_object* v_module_820_; uint8_t v___x_821_; 
v_package_817_ = lean_ctor_get(v_k_804_, 0);
v_module_818_ = lean_ctor_get(v_k_804_, 1);
v_package_819_ = lean_ctor_get(v_k_x27_805_, 0);
v_module_820_ = lean_ctor_get(v_k_x27_805_, 1);
v___x_821_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_818_, v_module_820_);
if (v___x_821_ == 1)
{
uint8_t v___x_822_; 
v___x_822_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_817_, v_package_819_);
return v___x_822_;
}
else
{
return v___x_821_;
}
}
default: 
{
uint8_t v___x_823_; 
v___x_823_ = 2;
return v___x_823_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_k_x27_805_))
{
case 4:
{
uint8_t v___x_824_; 
v___x_824_ = 0;
return v___x_824_;
}
case 3:
{
lean_object* v_package_825_; lean_object* v_target_826_; lean_object* v_package_827_; lean_object* v_target_828_; uint8_t v___x_829_; 
v_package_825_ = lean_ctor_get(v_k_804_, 0);
v_target_826_ = lean_ctor_get(v_k_804_, 1);
v_package_827_ = lean_ctor_get(v_k_x27_805_, 0);
v_target_828_ = lean_ctor_get(v_k_x27_805_, 1);
v___x_829_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_825_, v_package_827_);
if (v___x_829_ == 1)
{
uint8_t v___x_830_; 
v___x_830_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_826_, v_target_828_);
return v___x_830_;
}
else
{
return v___x_829_;
}
}
default: 
{
uint8_t v___x_831_; 
v___x_831_ = 2;
return v___x_831_;
}
}
}
default: 
{
if (lean_obj_tag(v_k_x27_805_) == 4)
{
lean_object* v_target_832_; lean_object* v_facet_833_; lean_object* v_target_834_; lean_object* v_facet_835_; uint8_t v___x_836_; 
v_target_832_ = lean_ctor_get(v_k_804_, 0);
v_facet_833_ = lean_ctor_get(v_k_804_, 1);
v_target_834_ = lean_ctor_get(v_k_x27_805_, 0);
v_facet_835_ = lean_ctor_get(v_k_x27_805_, 1);
v___x_836_ = l_Lake_BuildKey_quickCmp(v_target_832_, v_target_834_);
if (v___x_836_ == 1)
{
uint8_t v___x_837_; 
v___x_837_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_833_, v_facet_835_);
return v___x_837_;
}
else
{
return v___x_836_;
}
}
else
{
uint8_t v___x_838_; 
v___x_838_ = 2;
return v___x_838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* v_k_839_, lean_object* v_k_x27_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lake_BuildKey_quickCmp(v_k_839_, v_k_x27_840_);
lean_dec_ref(v_k_x27_840_);
lean_dec_ref(v_k_839_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* v_x_843_, lean_object* v_h__1_844_, lean_object* v_h__2_845_, lean_object* v_h__3_846_, lean_object* v_h__4_847_, lean_object* v_h__5_848_){
_start:
{
switch(lean_obj_tag(v_x_843_))
{
case 0:
{
lean_object* v_module_849_; lean_object* v___x_850_; 
lean_dec(v_h__5_848_);
lean_dec(v_h__4_847_);
lean_dec(v_h__3_846_);
lean_dec(v_h__2_845_);
v_module_849_ = lean_ctor_get(v_x_843_, 0);
lean_inc(v_module_849_);
lean_dec_ref_known(v_x_843_, 1);
v___x_850_ = lean_apply_1(v_h__1_844_, v_module_849_);
return v___x_850_;
}
case 1:
{
lean_object* v_package_851_; lean_object* v___x_852_; 
lean_dec(v_h__5_848_);
lean_dec(v_h__4_847_);
lean_dec(v_h__3_846_);
lean_dec(v_h__1_844_);
v_package_851_ = lean_ctor_get(v_x_843_, 0);
lean_inc(v_package_851_);
lean_dec_ref_known(v_x_843_, 1);
v___x_852_ = lean_apply_1(v_h__2_845_, v_package_851_);
return v___x_852_;
}
case 2:
{
lean_object* v_package_853_; lean_object* v_module_854_; lean_object* v___x_855_; 
lean_dec(v_h__5_848_);
lean_dec(v_h__4_847_);
lean_dec(v_h__2_845_);
lean_dec(v_h__1_844_);
v_package_853_ = lean_ctor_get(v_x_843_, 0);
lean_inc(v_package_853_);
v_module_854_ = lean_ctor_get(v_x_843_, 1);
lean_inc(v_module_854_);
lean_dec_ref_known(v_x_843_, 2);
v___x_855_ = lean_apply_2(v_h__3_846_, v_package_853_, v_module_854_);
return v___x_855_;
}
case 3:
{
lean_object* v_package_856_; lean_object* v_target_857_; lean_object* v___x_858_; 
lean_dec(v_h__5_848_);
lean_dec(v_h__3_846_);
lean_dec(v_h__2_845_);
lean_dec(v_h__1_844_);
v_package_856_ = lean_ctor_get(v_x_843_, 0);
lean_inc(v_package_856_);
v_target_857_ = lean_ctor_get(v_x_843_, 1);
lean_inc(v_target_857_);
lean_dec_ref_known(v_x_843_, 2);
v___x_858_ = lean_apply_2(v_h__4_847_, v_package_856_, v_target_857_);
return v___x_858_;
}
default: 
{
lean_object* v_target_859_; lean_object* v_facet_860_; lean_object* v___x_861_; 
lean_dec(v_h__4_847_);
lean_dec(v_h__3_846_);
lean_dec(v_h__2_845_);
lean_dec(v_h__1_844_);
v_target_859_ = lean_ctor_get(v_x_843_, 0);
lean_inc_ref(v_target_859_);
v_facet_860_ = lean_ctor_get(v_x_843_, 1);
lean_inc(v_facet_860_);
lean_dec_ref_known(v_x_843_, 2);
v___x_861_ = lean_apply_2(v_h__5_848_, v_target_859_, v_facet_860_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_862_, lean_object* v_x_863_, lean_object* v_h__1_864_, lean_object* v_h__2_865_, lean_object* v_h__3_866_, lean_object* v_h__4_867_, lean_object* v_h__5_868_){
_start:
{
switch(lean_obj_tag(v_x_863_))
{
case 0:
{
lean_object* v_module_869_; lean_object* v___x_870_; 
lean_dec(v_h__5_868_);
lean_dec(v_h__4_867_);
lean_dec(v_h__3_866_);
lean_dec(v_h__2_865_);
v_module_869_ = lean_ctor_get(v_x_863_, 0);
lean_inc(v_module_869_);
lean_dec_ref_known(v_x_863_, 1);
v___x_870_ = lean_apply_1(v_h__1_864_, v_module_869_);
return v___x_870_;
}
case 1:
{
lean_object* v_package_871_; lean_object* v___x_872_; 
lean_dec(v_h__5_868_);
lean_dec(v_h__4_867_);
lean_dec(v_h__3_866_);
lean_dec(v_h__1_864_);
v_package_871_ = lean_ctor_get(v_x_863_, 0);
lean_inc(v_package_871_);
lean_dec_ref_known(v_x_863_, 1);
v___x_872_ = lean_apply_1(v_h__2_865_, v_package_871_);
return v___x_872_;
}
case 2:
{
lean_object* v_package_873_; lean_object* v_module_874_; lean_object* v___x_875_; 
lean_dec(v_h__5_868_);
lean_dec(v_h__4_867_);
lean_dec(v_h__2_865_);
lean_dec(v_h__1_864_);
v_package_873_ = lean_ctor_get(v_x_863_, 0);
lean_inc(v_package_873_);
v_module_874_ = lean_ctor_get(v_x_863_, 1);
lean_inc(v_module_874_);
lean_dec_ref_known(v_x_863_, 2);
v___x_875_ = lean_apply_2(v_h__3_866_, v_package_873_, v_module_874_);
return v___x_875_;
}
case 3:
{
lean_object* v_package_876_; lean_object* v_target_877_; lean_object* v___x_878_; 
lean_dec(v_h__5_868_);
lean_dec(v_h__3_866_);
lean_dec(v_h__2_865_);
lean_dec(v_h__1_864_);
v_package_876_ = lean_ctor_get(v_x_863_, 0);
lean_inc(v_package_876_);
v_target_877_ = lean_ctor_get(v_x_863_, 1);
lean_inc(v_target_877_);
lean_dec_ref_known(v_x_863_, 2);
v___x_878_ = lean_apply_2(v_h__4_867_, v_package_876_, v_target_877_);
return v___x_878_;
}
default: 
{
lean_object* v_target_879_; lean_object* v_facet_880_; lean_object* v___x_881_; 
lean_dec(v_h__4_867_);
lean_dec(v_h__3_866_);
lean_dec(v_h__2_865_);
lean_dec(v_h__1_864_);
v_target_879_ = lean_ctor_get(v_x_863_, 0);
lean_inc_ref(v_target_879_);
v_facet_880_ = lean_ctor_get(v_x_863_, 1);
lean_inc(v_facet_880_);
lean_dec_ref_known(v_x_863_, 2);
v___x_881_ = lean_apply_2(v_h__5_868_, v_target_879_, v_facet_880_);
return v___x_881_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_882_, lean_object* v_h__1_883_, lean_object* v_h__2_884_){
_start:
{
if (lean_obj_tag(v_k_x27_882_) == 0)
{
lean_object* v_module_885_; lean_object* v___x_886_; 
lean_dec(v_h__2_884_);
v_module_885_ = lean_ctor_get(v_k_x27_882_, 0);
lean_inc(v_module_885_);
lean_dec_ref_known(v_k_x27_882_, 1);
v___x_886_ = lean_apply_1(v_h__1_883_, v_module_885_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; 
lean_dec(v_h__1_883_);
v___x_887_ = lean_apply_2(v_h__2_884_, v_k_x27_882_, lean_box(0));
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_888_, lean_object* v_k_x27_889_, lean_object* v_h__1_890_, lean_object* v_h__2_891_){
_start:
{
if (lean_obj_tag(v_k_x27_889_) == 0)
{
lean_object* v_module_892_; lean_object* v___x_893_; 
lean_dec(v_h__2_891_);
v_module_892_ = lean_ctor_get(v_k_x27_889_, 0);
lean_inc(v_module_892_);
lean_dec_ref_known(v_k_x27_889_, 1);
v___x_893_ = lean_apply_1(v_h__1_890_, v_module_892_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
lean_dec(v_h__1_890_);
v___x_894_ = lean_apply_2(v_h__2_891_, v_k_x27_889_, lean_box(0));
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_895_, lean_object* v_h__1_896_, lean_object* v_h__2_897_, lean_object* v_h__3_898_){
_start:
{
switch(lean_obj_tag(v_k_x27_895_))
{
case 0:
{
lean_object* v_module_899_; lean_object* v___x_900_; 
lean_dec(v_h__3_898_);
lean_dec(v_h__2_897_);
v_module_899_ = lean_ctor_get(v_k_x27_895_, 0);
lean_inc(v_module_899_);
lean_dec_ref_known(v_k_x27_895_, 1);
v___x_900_ = lean_apply_1(v_h__1_896_, v_module_899_);
return v___x_900_;
}
case 1:
{
lean_object* v_package_901_; lean_object* v___x_902_; 
lean_dec(v_h__3_898_);
lean_dec(v_h__1_896_);
v_package_901_ = lean_ctor_get(v_k_x27_895_, 0);
lean_inc(v_package_901_);
lean_dec_ref_known(v_k_x27_895_, 1);
v___x_902_ = lean_apply_1(v_h__2_897_, v_package_901_);
return v___x_902_;
}
default: 
{
lean_object* v___x_903_; 
lean_dec(v_h__2_897_);
lean_dec(v_h__1_896_);
v___x_903_ = lean_apply_3(v_h__3_898_, v_k_x27_895_, lean_box(0), lean_box(0));
return v___x_903_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_904_, lean_object* v_k_x27_905_, lean_object* v_h__1_906_, lean_object* v_h__2_907_, lean_object* v_h__3_908_){
_start:
{
switch(lean_obj_tag(v_k_x27_905_))
{
case 0:
{
lean_object* v_module_909_; lean_object* v___x_910_; 
lean_dec(v_h__3_908_);
lean_dec(v_h__2_907_);
v_module_909_ = lean_ctor_get(v_k_x27_905_, 0);
lean_inc(v_module_909_);
lean_dec_ref_known(v_k_x27_905_, 1);
v___x_910_ = lean_apply_1(v_h__1_906_, v_module_909_);
return v___x_910_;
}
case 1:
{
lean_object* v_package_911_; lean_object* v___x_912_; 
lean_dec(v_h__3_908_);
lean_dec(v_h__1_906_);
v_package_911_ = lean_ctor_get(v_k_x27_905_, 0);
lean_inc(v_package_911_);
lean_dec_ref_known(v_k_x27_905_, 1);
v___x_912_ = lean_apply_1(v_h__2_907_, v_package_911_);
return v___x_912_;
}
default: 
{
lean_object* v___x_913_; 
lean_dec(v_h__2_907_);
lean_dec(v_h__1_906_);
v___x_913_ = lean_apply_3(v_h__3_908_, v_k_x27_905_, lean_box(0), lean_box(0));
return v___x_913_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_914_, lean_object* v_h__1_915_, lean_object* v_h__2_916_, lean_object* v_h__3_917_, lean_object* v_h__4_918_){
_start:
{
switch(lean_obj_tag(v_k_x27_914_))
{
case 4:
{
lean_object* v_target_919_; lean_object* v_facet_920_; lean_object* v___x_921_; 
lean_dec(v_h__4_918_);
lean_dec(v_h__3_917_);
lean_dec(v_h__2_916_);
v_target_919_ = lean_ctor_get(v_k_x27_914_, 0);
lean_inc_ref(v_target_919_);
v_facet_920_ = lean_ctor_get(v_k_x27_914_, 1);
lean_inc(v_facet_920_);
lean_dec_ref_known(v_k_x27_914_, 2);
v___x_921_ = lean_apply_2(v_h__1_915_, v_target_919_, v_facet_920_);
return v___x_921_;
}
case 3:
{
lean_object* v_package_922_; lean_object* v_target_923_; lean_object* v___x_924_; 
lean_dec(v_h__4_918_);
lean_dec(v_h__3_917_);
lean_dec(v_h__1_915_);
v_package_922_ = lean_ctor_get(v_k_x27_914_, 0);
lean_inc(v_package_922_);
v_target_923_ = lean_ctor_get(v_k_x27_914_, 1);
lean_inc(v_target_923_);
lean_dec_ref_known(v_k_x27_914_, 2);
v___x_924_ = lean_apply_2(v_h__2_916_, v_package_922_, v_target_923_);
return v___x_924_;
}
case 2:
{
lean_object* v_package_925_; lean_object* v_module_926_; lean_object* v___x_927_; 
lean_dec(v_h__4_918_);
lean_dec(v_h__2_916_);
lean_dec(v_h__1_915_);
v_package_925_ = lean_ctor_get(v_k_x27_914_, 0);
lean_inc(v_package_925_);
v_module_926_ = lean_ctor_get(v_k_x27_914_, 1);
lean_inc(v_module_926_);
lean_dec_ref_known(v_k_x27_914_, 2);
v___x_927_ = lean_apply_2(v_h__3_917_, v_package_925_, v_module_926_);
return v___x_927_;
}
default: 
{
lean_object* v___x_928_; 
lean_dec(v_h__3_917_);
lean_dec(v_h__2_916_);
lean_dec(v_h__1_915_);
v___x_928_ = lean_apply_4(v_h__4_918_, v_k_x27_914_, lean_box(0), lean_box(0), lean_box(0));
return v___x_928_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_929_, lean_object* v_k_x27_930_, lean_object* v_h__1_931_, lean_object* v_h__2_932_, lean_object* v_h__3_933_, lean_object* v_h__4_934_){
_start:
{
switch(lean_obj_tag(v_k_x27_930_))
{
case 4:
{
lean_object* v_target_935_; lean_object* v_facet_936_; lean_object* v___x_937_; 
lean_dec(v_h__4_934_);
lean_dec(v_h__3_933_);
lean_dec(v_h__2_932_);
v_target_935_ = lean_ctor_get(v_k_x27_930_, 0);
lean_inc_ref(v_target_935_);
v_facet_936_ = lean_ctor_get(v_k_x27_930_, 1);
lean_inc(v_facet_936_);
lean_dec_ref_known(v_k_x27_930_, 2);
v___x_937_ = lean_apply_2(v_h__1_931_, v_target_935_, v_facet_936_);
return v___x_937_;
}
case 3:
{
lean_object* v_package_938_; lean_object* v_target_939_; lean_object* v___x_940_; 
lean_dec(v_h__4_934_);
lean_dec(v_h__3_933_);
lean_dec(v_h__1_931_);
v_package_938_ = lean_ctor_get(v_k_x27_930_, 0);
lean_inc(v_package_938_);
v_target_939_ = lean_ctor_get(v_k_x27_930_, 1);
lean_inc(v_target_939_);
lean_dec_ref_known(v_k_x27_930_, 2);
v___x_940_ = lean_apply_2(v_h__2_932_, v_package_938_, v_target_939_);
return v___x_940_;
}
case 2:
{
lean_object* v_package_941_; lean_object* v_module_942_; lean_object* v___x_943_; 
lean_dec(v_h__4_934_);
lean_dec(v_h__2_932_);
lean_dec(v_h__1_931_);
v_package_941_ = lean_ctor_get(v_k_x27_930_, 0);
lean_inc(v_package_941_);
v_module_942_ = lean_ctor_get(v_k_x27_930_, 1);
lean_inc(v_module_942_);
lean_dec_ref_known(v_k_x27_930_, 2);
v___x_943_ = lean_apply_2(v_h__3_933_, v_package_941_, v_module_942_);
return v___x_943_;
}
default: 
{
lean_object* v___x_944_; 
lean_dec(v_h__3_933_);
lean_dec(v_h__2_932_);
lean_dec(v_h__1_931_);
v___x_944_ = lean_apply_4(v_h__4_934_, v_k_x27_930_, lean_box(0), lean_box(0), lean_box(0));
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_945_, lean_object* v_h__1_946_, lean_object* v_h__2_947_){
_start:
{
if (v_x_945_ == 1)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_h__2_947_);
v___x_948_ = lean_box(0);
v___x_949_ = lean_apply_1(v_h__1_946_, v___x_948_);
return v___x_949_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v_h__1_946_);
v___x_950_ = lean_box(v_x_945_);
v___x_951_ = lean_apply_2(v_h__2_947_, v___x_950_, lean_box(0));
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_952_, lean_object* v_h__1_953_, lean_object* v_h__2_954_){
_start:
{
uint8_t v_x_17__boxed_955_; lean_object* v_res_956_; 
v_x_17__boxed_955_ = lean_unbox(v_x_952_);
v_res_956_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_17__boxed_955_, v_h__1_953_, v_h__2_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_957_, uint8_t v_x_958_, lean_object* v_h__1_959_, lean_object* v_h__2_960_){
_start:
{
if (v_x_958_ == 1)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v_h__2_960_);
v___x_961_ = lean_box(0);
v___x_962_ = lean_apply_1(v_h__1_959_, v___x_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_h__1_959_);
v___x_963_ = lean_box(v_x_958_);
v___x_964_ = lean_apply_2(v_h__2_960_, v___x_963_, lean_box(0));
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_965_, lean_object* v_x_966_, lean_object* v_h__1_967_, lean_object* v_h__2_968_){
_start:
{
uint8_t v_x_28__boxed_969_; lean_object* v_res_970_; 
v_x_28__boxed_969_ = lean_unbox(v_x_966_);
v_res_970_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_965_, v_x_28__boxed_969_, v_h__1_967_, v_h__2_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_971_, lean_object* v_h__1_972_, lean_object* v_h__2_973_, lean_object* v_h__3_974_){
_start:
{
switch(lean_obj_tag(v_k_x27_971_))
{
case 4:
{
lean_object* v_target_975_; lean_object* v_facet_976_; lean_object* v___x_977_; 
lean_dec(v_h__3_974_);
lean_dec(v_h__2_973_);
v_target_975_ = lean_ctor_get(v_k_x27_971_, 0);
lean_inc_ref(v_target_975_);
v_facet_976_ = lean_ctor_get(v_k_x27_971_, 1);
lean_inc(v_facet_976_);
lean_dec_ref_known(v_k_x27_971_, 2);
v___x_977_ = lean_apply_2(v_h__1_972_, v_target_975_, v_facet_976_);
return v___x_977_;
}
case 3:
{
lean_object* v_package_978_; lean_object* v_target_979_; lean_object* v___x_980_; 
lean_dec(v_h__3_974_);
lean_dec(v_h__1_972_);
v_package_978_ = lean_ctor_get(v_k_x27_971_, 0);
lean_inc(v_package_978_);
v_target_979_ = lean_ctor_get(v_k_x27_971_, 1);
lean_inc(v_target_979_);
lean_dec_ref_known(v_k_x27_971_, 2);
v___x_980_ = lean_apply_2(v_h__2_973_, v_package_978_, v_target_979_);
return v___x_980_;
}
default: 
{
lean_object* v___x_981_; 
lean_dec(v_h__2_973_);
lean_dec(v_h__1_972_);
v___x_981_ = lean_apply_3(v_h__3_974_, v_k_x27_971_, lean_box(0), lean_box(0));
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_982_, lean_object* v_k_x27_983_, lean_object* v_h__1_984_, lean_object* v_h__2_985_, lean_object* v_h__3_986_){
_start:
{
switch(lean_obj_tag(v_k_x27_983_))
{
case 4:
{
lean_object* v_target_987_; lean_object* v_facet_988_; lean_object* v___x_989_; 
lean_dec(v_h__3_986_);
lean_dec(v_h__2_985_);
v_target_987_ = lean_ctor_get(v_k_x27_983_, 0);
lean_inc_ref(v_target_987_);
v_facet_988_ = lean_ctor_get(v_k_x27_983_, 1);
lean_inc(v_facet_988_);
lean_dec_ref_known(v_k_x27_983_, 2);
v___x_989_ = lean_apply_2(v_h__1_984_, v_target_987_, v_facet_988_);
return v___x_989_;
}
case 3:
{
lean_object* v_package_990_; lean_object* v_target_991_; lean_object* v___x_992_; 
lean_dec(v_h__3_986_);
lean_dec(v_h__1_984_);
v_package_990_ = lean_ctor_get(v_k_x27_983_, 0);
lean_inc(v_package_990_);
v_target_991_ = lean_ctor_get(v_k_x27_983_, 1);
lean_inc(v_target_991_);
lean_dec_ref_known(v_k_x27_983_, 2);
v___x_992_ = lean_apply_2(v_h__2_985_, v_package_990_, v_target_991_);
return v___x_992_;
}
default: 
{
lean_object* v___x_993_; 
lean_dec(v_h__2_985_);
lean_dec(v_h__1_984_);
v___x_993_ = lean_apply_3(v_h__3_986_, v_k_x27_983_, lean_box(0), lean_box(0));
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_994_, lean_object* v_h__1_995_, lean_object* v_h__2_996_){
_start:
{
if (lean_obj_tag(v_k_x27_994_) == 4)
{
lean_object* v_target_997_; lean_object* v_facet_998_; lean_object* v___x_999_; 
lean_dec(v_h__2_996_);
v_target_997_ = lean_ctor_get(v_k_x27_994_, 0);
lean_inc_ref(v_target_997_);
v_facet_998_ = lean_ctor_get(v_k_x27_994_, 1);
lean_inc(v_facet_998_);
lean_dec_ref_known(v_k_x27_994_, 2);
v___x_999_ = lean_apply_2(v_h__1_995_, v_target_997_, v_facet_998_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; 
lean_dec(v_h__1_995_);
v___x_1000_ = lean_apply_2(v_h__2_996_, v_k_x27_994_, lean_box(0));
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_1001_, lean_object* v_k_x27_1002_, lean_object* v_h__1_1003_, lean_object* v_h__2_1004_){
_start:
{
if (lean_obj_tag(v_k_x27_1002_) == 4)
{
lean_object* v_target_1005_; lean_object* v_facet_1006_; lean_object* v___x_1007_; 
lean_dec(v_h__2_1004_);
v_target_1005_ = lean_ctor_get(v_k_x27_1002_, 0);
lean_inc_ref(v_target_1005_);
v_facet_1006_ = lean_ctor_get(v_k_x27_1002_, 1);
lean_inc(v_facet_1006_);
lean_dec_ref_known(v_k_x27_1002_, 2);
v___x_1007_ = lean_apply_2(v_h__1_1003_, v_target_1005_, v_facet_1006_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; 
lean_dec(v_h__1_1003_);
v___x_1008_ = lean_apply_2(v_h__2_1004_, v_k_x27_1002_, lean_box(0));
return v___x_1008_;
}
}
}
lean_object* runtime_initialize_Init_Data_Order(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Key(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
