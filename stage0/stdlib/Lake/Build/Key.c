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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value;
static lean_once_cell_t l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PartialBuildKey_instInhabited___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_value;
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
lean_object* v_str_348_; lean_object* v_startInclusive_349_; lean_object* v_endExclusive_350_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_str_348_ = lean_ctor_get(v_target_347_, 0);
v_startInclusive_349_ = lean_ctor_get(v_target_347_, 1);
v_endExclusive_350_ = lean_ctor_get(v_target_347_, 2);
v___x_356_ = lean_nat_sub(v_endExclusive_350_, v_startInclusive_349_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_nat_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_360_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_361_ = lean_nat_dec_le(v___x_360_, v___x_356_);
lean_dec(v___x_356_);
if (v___x_361_ == 0)
{
goto v___jp_351_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = lean_string_memcmp(v_str_348_, v___x_359_, v_startInclusive_349_, v___x_357_, v___x_360_);
if (v___x_362_ == 0)
{
goto v___jp_351_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_target_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = l_String_Slice_Pos_nextn(v_target_347_, v___x_357_, v___x_363_);
v___x_365_ = lean_nat_add(v_startInclusive_349_, v___x_364_);
lean_dec(v___x_364_);
v___x_366_ = lean_string_utf8_extract_fast(v_str_348_, v___x_365_, v_endExclusive_350_);
lean_dec(v___x_365_);
v_target_367_ = l_Lake_stringToLegalOrSimpleName(v___x_366_);
v___x_368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_368_, 0, v_pkg_346_);
lean_ctor_set(v___x_368_, 1, v_target_367_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
}
}
else
{
lean_object* v___x_370_; 
lean_dec(v___x_356_);
lean_dec(v_pkg_346_);
v___x_370_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3));
return v___x_370_;
}
v___jp_351_:
{
lean_object* v___x_352_; lean_object* v_target_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_string_utf8_extract_fast(v_str_348_, v_startInclusive_349_, v_endExclusive_350_);
v_target_353_ = l_Lake_stringToLegalOrSimpleName(v___x_352_);
v___x_354_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_354_, 0, v_pkg_346_);
lean_ctor_set(v___x_354_, 1, v_target_353_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* v_pkg_371_, lean_object* v_target_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v_pkg_371_, v_target_372_);
lean_dec_ref(v_target_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* v_s_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* v_s_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_378_);
lean_dec_ref(v_s_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* v_s_380_, lean_object* v___x_381_, lean_object* v___x_382_, lean_object* v_a_383_, lean_object* v_b_384_){
_start:
{
lean_object* v_it_386_; lean_object* v_startInclusive_387_; lean_object* v_endExclusive_388_; 
if (lean_obj_tag(v_a_383_) == 0)
{
lean_object* v_currPos_392_; lean_object* v_searcher_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_416_; 
v_currPos_392_ = lean_ctor_get(v_a_383_, 0);
v_searcher_393_ = lean_ctor_get(v_a_383_, 1);
v_isSharedCheck_416_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_416_ == 0)
{
v___x_395_ = v_a_383_;
v_isShared_396_ = v_isSharedCheck_416_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_searcher_393_);
lean_inc(v_currPos_392_);
lean_dec(v_a_383_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_416_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v_decide_397_; 
v_decide_397_ = lean_nat_dec_eq(v_searcher_393_, v___x_382_);
if (v_decide_397_ == 0)
{
uint32_t v___x_398_; uint32_t v___x_399_; uint8_t v___x_400_; 
v___x_398_ = 47;
v___x_399_ = lean_string_utf8_get_fast(v_s_380_, v_searcher_393_);
v___x_400_ = lean_uint32_dec_eq(v___x_399_, v___x_398_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_string_utf8_next_fast(v_s_380_, v_searcher_393_);
lean_dec(v_searcher_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v___x_401_);
v___x_403_ = v___x_395_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_currPos_392_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_405_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
v_a_383_ = v___x_403_;
goto _start;
}
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_slice_409_; lean_object* v_nextIt_411_; 
v___x_406_ = lean_string_utf8_next_fast(v_s_380_, v_searcher_393_);
v___x_407_ = lean_nat_sub(v___x_406_, v_searcher_393_);
v___x_408_ = lean_nat_add(v_searcher_393_, v___x_407_);
lean_dec(v___x_407_);
v_slice_409_ = l_String_Slice_subslice_x21(v___x_381_, v_currPos_392_, v_searcher_393_);
lean_inc(v___x_408_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v___x_408_);
lean_ctor_set(v___x_395_, 0, v___x_408_);
v_nextIt_411_ = v___x_395_;
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
v_it_386_ = v_nextIt_411_;
v_startInclusive_387_ = v_startInclusive_412_;
v_endExclusive_388_ = v_endExclusive_413_;
goto v___jp_385_;
}
}
}
else
{
lean_object* v___x_415_; 
lean_del_object(v___x_395_);
lean_dec(v_searcher_393_);
v___x_415_ = lean_box(1);
lean_inc(v___x_382_);
v_it_386_ = v___x_415_;
v_startInclusive_387_ = v_currPos_392_;
v_endExclusive_388_ = v___x_382_;
goto v___jp_385_;
}
}
}
else
{
lean_dec(v___x_382_);
lean_dec_ref(v_s_380_);
return v_b_384_;
}
v___jp_385_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_inc_ref(v_s_380_);
v___x_389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_389_, 0, v_s_380_);
lean_ctor_set(v___x_389_, 1, v_startInclusive_387_);
lean_ctor_set(v___x_389_, 2, v_endExclusive_388_);
v___x_390_ = lean_array_push(v_b_384_, v___x_389_);
v_a_383_ = v_it_386_;
v_b_384_ = v___x_390_;
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
static lean_object* _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_433_ = lean_string_utf8_byte_size(v___x_432_);
return v___x_433_;
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
lean_dec_ref_known(v___x_441_, 3);
v___x_445_ = lean_array_to_list(v___x_444_);
if (lean_obj_tag(v___x_445_) == 1)
{
lean_object* v_head_446_; lean_object* v_tail_447_; 
v_head_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_head_446_);
v_tail_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc(v_tail_447_);
lean_dec_ref_known(v___x_445_, 2);
if (lean_obj_tag(v_tail_447_) == 0)
{
lean_object* v_str_451_; lean_object* v_startInclusive_452_; lean_object* v_endExclusive_453_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_str_451_ = lean_ctor_get(v_head_446_, 0);
v_startInclusive_452_ = lean_ctor_get(v_head_446_, 1);
v_endExclusive_453_ = lean_ctor_get(v_head_446_, 2);
v___x_470_ = lean_nat_sub(v_endExclusive_453_, v_startInclusive_452_);
v___x_471_ = lean_nat_dec_eq(v___x_470_, v___x_439_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_473_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6);
v___x_474_ = lean_nat_dec_le(v___x_473_, v___x_470_);
lean_dec(v___x_470_);
if (v___x_474_ == 0)
{
goto v___jp_454_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = lean_string_memcmp(v_str_451_, v___x_472_, v_startInclusive_452_, v___x_439_, v___x_473_);
if (v___x_475_ == 0)
{
goto v___jp_454_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
lean_inc(v_endExclusive_453_);
lean_inc(v_startInclusive_452_);
lean_inc_ref(v_str_451_);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = l_String_Slice_Pos_nextn(v_head_446_, v___x_439_, v___x_476_);
lean_dec(v_head_446_);
v___x_478_ = lean_nat_add(v_startInclusive_452_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v_startInclusive_452_);
v___x_479_ = lean_nat_sub(v_endExclusive_453_, v___x_478_);
v___x_480_ = lean_nat_dec_eq(v___x_479_, v___x_439_);
lean_dec(v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_string_utf8_extract_fast(v_str_451_, v___x_478_, v_endExclusive_453_);
lean_dec(v_endExclusive_453_);
lean_dec(v___x_478_);
lean_dec_ref(v_str_451_);
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
lean_dec(v_endExclusive_453_);
lean_dec_ref(v_str_451_);
v___x_485_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7));
return v___x_485_;
}
}
}
}
else
{
lean_object* v___x_486_; 
lean_dec(v___x_470_);
lean_dec(v_head_446_);
v___x_486_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7));
return v___x_486_;
}
v___jp_454_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_455_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_456_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
v___x_457_ = lean_nat_sub(v_endExclusive_453_, v_startInclusive_452_);
v___x_458_ = lean_nat_dec_le(v___x_456_, v___x_457_);
lean_dec(v___x_457_);
if (v___x_458_ == 0)
{
goto v___jp_448_;
}
else
{
uint8_t v___x_459_; 
v___x_459_ = lean_string_memcmp(v_str_451_, v___x_455_, v_startInclusive_452_, v___x_439_, v___x_456_);
if (v___x_459_ == 0)
{
goto v___jp_448_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
lean_inc(v_endExclusive_453_);
lean_inc(v_startInclusive_452_);
lean_inc_ref(v_str_451_);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = l_String_Slice_Pos_nextn(v_head_446_, v___x_439_, v___x_460_);
lean_dec(v_head_446_);
v___x_462_ = lean_nat_add(v_startInclusive_452_, v___x_461_);
lean_dec(v___x_461_);
lean_dec(v_startInclusive_452_);
v___x_463_ = lean_nat_sub(v_endExclusive_453_, v___x_462_);
v___x_464_ = lean_nat_dec_eq(v___x_463_, v___x_439_);
lean_dec(v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_465_ = lean_string_utf8_extract_fast(v_str_451_, v___x_462_, v_endExclusive_453_);
lean_dec(v_endExclusive_453_);
lean_dec(v___x_462_);
lean_dec_ref(v_str_451_);
v___x_466_ = l_Lake_stringToLegalOrSimpleName(v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; 
lean_dec(v___x_462_);
lean_dec(v_endExclusive_453_);
lean_dec_ref(v_str_451_);
v___x_469_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return v___x_469_;
}
}
}
}
}
else
{
lean_object* v_head_487_; lean_object* v_tail_488_; lean_object* v_str_490_; lean_object* v_startInclusive_491_; lean_object* v_endExclusive_492_; 
v_head_487_ = lean_ctor_get(v_tail_447_, 0);
lean_inc(v_head_487_);
v_tail_488_ = lean_ctor_get(v_tail_447_, 1);
lean_inc(v_tail_488_);
lean_dec_ref_known(v_tail_447_, 2);
if (lean_obj_tag(v_tail_488_) == 0)
{
lean_object* v_str_500_; lean_object* v_startInclusive_501_; lean_object* v_endExclusive_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_str_500_ = lean_ctor_get(v_head_446_, 0);
lean_inc_ref(v_str_500_);
v_startInclusive_501_ = lean_ctor_get(v_head_446_, 1);
lean_inc(v_startInclusive_501_);
v_endExclusive_502_ = lean_ctor_get(v_head_446_, 2);
lean_inc(v_endExclusive_502_);
v___x_503_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_504_ = lean_obj_once(&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6, &l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_once, _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6);
v___x_505_ = lean_nat_sub(v_endExclusive_502_, v_startInclusive_501_);
v___x_506_ = lean_nat_dec_le(v___x_504_, v___x_505_);
lean_dec(v___x_505_);
if (v___x_506_ == 0)
{
lean_dec(v_head_446_);
v_str_490_ = v_str_500_;
v_startInclusive_491_ = v_startInclusive_501_;
v_endExclusive_492_ = v_endExclusive_502_;
goto v___jp_489_;
}
else
{
uint8_t v___x_507_; 
v___x_507_ = lean_string_memcmp(v_str_500_, v___x_503_, v_startInclusive_501_, v___x_439_, v___x_504_);
if (v___x_507_ == 0)
{
lean_dec(v_head_446_);
v_str_490_ = v_str_500_;
v_startInclusive_491_ = v_startInclusive_501_;
v_endExclusive_492_ = v_endExclusive_502_;
goto v___jp_489_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = l_String_Slice_Pos_nextn(v_head_446_, v___x_439_, v___x_508_);
lean_dec(v_head_446_);
v___x_510_ = lean_nat_add(v_startInclusive_501_, v___x_509_);
lean_dec(v___x_509_);
lean_dec(v_startInclusive_501_);
v_str_490_ = v_str_500_;
v_startInclusive_491_ = v___x_510_;
v_endExclusive_492_ = v_endExclusive_502_;
goto v___jp_489_;
}
}
}
else
{
lean_dec(v_tail_488_);
lean_dec(v_head_487_);
lean_dec(v_head_446_);
goto v___jp_437_;
}
v___jp_489_:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_nat_sub(v_endExclusive_492_, v_startInclusive_491_);
v___x_494_ = lean_nat_dec_eq(v___x_493_, v___x_439_);
lean_dec(v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_string_utf8_extract_fast(v_str_490_, v_startInclusive_491_, v_endExclusive_492_);
lean_dec(v_endExclusive_492_);
lean_dec(v_startInclusive_491_);
lean_dec_ref(v_str_490_);
v___x_496_ = l_Lake_stringToLegalOrSimpleName(v___x_495_);
v___x_497_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_496_, v_head_487_);
lean_dec(v_head_487_);
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_endExclusive_492_);
lean_dec(v_startInclusive_491_);
lean_dec_ref(v_str_490_);
v___x_498_ = lean_box(0);
v___x_499_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_498_, v_head_487_);
lean_dec(v_head_487_);
return v___x_499_;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* v_s_511_, lean_object* v___x_512_, lean_object* v___x_513_, lean_object* v_inst_514_, lean_object* v_R_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_511_, v___x_512_, v___x_513_, v_a_516_, v_b_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* v_s_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v_inst_522_, lean_object* v_R_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_519_, v___x_520_, v___x_521_, v_inst_522_, v_R_523_, v_a_524_, v_b_525_);
lean_dec_ref(v___x_520_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_529_);
lean_dec_ref(v_s_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
v___x_535_ = lean_panic_fn_borrowed(v___x_534_, v_msg_532_);
lean_dec_ref_known(v___x_534_, 1);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_536_, lean_object* v___x_537_, lean_object* v___x_538_, lean_object* v_a_539_, lean_object* v_b_540_){
_start:
{
lean_object* v_it_542_; lean_object* v_startInclusive_543_; lean_object* v_endExclusive_544_; 
if (lean_obj_tag(v_a_539_) == 0)
{
lean_object* v_currPos_549_; lean_object* v_searcher_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_573_; 
v_currPos_549_ = lean_ctor_get(v_a_539_, 0);
v_searcher_550_ = lean_ctor_get(v_a_539_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_573_ == 0)
{
v___x_552_ = v_a_539_;
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_searcher_550_);
lean_inc(v_currPos_549_);
lean_dec(v_a_539_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
uint8_t v_decide_554_; 
v_decide_554_ = lean_nat_dec_eq(v_searcher_550_, v___x_538_);
if (v_decide_554_ == 0)
{
uint32_t v___x_555_; uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = 58;
v___x_556_ = lean_string_utf8_get_fast(v_s_536_, v_searcher_550_);
v___x_557_ = lean_uint32_dec_eq(v___x_556_, v___x_555_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = lean_string_utf8_next_fast(v_s_536_, v_searcher_550_);
lean_dec(v_searcher_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_558_);
v___x_560_ = v___x_552_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_currPos_549_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_558_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v_a_539_ = v___x_560_;
goto _start;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v_slice_566_; lean_object* v_nextIt_568_; 
v___x_563_ = lean_string_utf8_next_fast(v_s_536_, v_searcher_550_);
v___x_564_ = lean_nat_sub(v___x_563_, v_searcher_550_);
v___x_565_ = lean_nat_add(v_searcher_550_, v___x_564_);
lean_dec(v___x_564_);
v_slice_566_ = l_String_Slice_subslice_x21(v___x_537_, v_currPos_549_, v_searcher_550_);
lean_inc(v___x_565_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v___x_565_);
lean_ctor_set(v___x_552_, 0, v___x_565_);
v_nextIt_568_ = v___x_552_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_565_);
v_nextIt_568_ = v_reuseFailAlloc_571_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v_startInclusive_569_; lean_object* v_endExclusive_570_; 
v_startInclusive_569_ = lean_ctor_get(v_slice_566_, 0);
lean_inc(v_startInclusive_569_);
v_endExclusive_570_ = lean_ctor_get(v_slice_566_, 1);
lean_inc(v_endExclusive_570_);
lean_dec_ref(v_slice_566_);
v_it_542_ = v_nextIt_568_;
v_startInclusive_543_ = v_startInclusive_569_;
v_endExclusive_544_ = v_endExclusive_570_;
goto v___jp_541_;
}
}
}
else
{
lean_object* v___x_572_; 
lean_del_object(v___x_552_);
lean_dec(v_searcher_550_);
v___x_572_ = lean_box(1);
lean_inc(v___x_538_);
v_it_542_ = v___x_572_;
v_startInclusive_543_ = v_currPos_549_;
v_endExclusive_544_ = v___x_538_;
goto v___jp_541_;
}
}
}
else
{
lean_dec(v___x_538_);
lean_dec_ref(v_s_536_);
return v_b_540_;
}
v___jp_541_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_inc_ref(v_s_536_);
v___x_545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_545_, 0, v_s_536_);
lean_ctor_set(v___x_545_, 1, v_startInclusive_543_);
lean_ctor_set(v___x_545_, 2, v_endExclusive_544_);
v___x_546_ = l_String_Slice_toString(v___x_545_);
lean_dec_ref_known(v___x_545_, 3);
v___x_547_ = lean_array_push(v_b_540_, v___x_546_);
v_a_539_ = v_it_542_;
v_b_540_ = v___x_547_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_574_, lean_object* v___x_575_, lean_object* v___x_576_, lean_object* v_a_577_, lean_object* v_b_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_574_, v___x_575_, v___x_576_, v_a_577_, v_b_578_);
lean_dec_ref(v___x_575_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_x_583_);
return v___x_585_;
}
else
{
lean_object* v_head_586_; lean_object* v_tail_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_600_; 
v_head_586_ = lean_ctor_get(v_x_584_, 0);
v_tail_587_ = lean_ctor_get(v_x_584_, 1);
v_isSharedCheck_600_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_600_ == 0)
{
v___x_589_ = v_x_584_;
v_isShared_590_ = v_isSharedCheck_600_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_tail_587_);
lean_inc(v_head_586_);
lean_dec(v_x_584_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_600_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_string_utf8_byte_size(v_head_586_);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_nat_dec_eq(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_594_ = l_Lake_stringToLegalOrSimpleName(v_head_586_);
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 4);
lean_ctor_set(v___x_589_, 1, v___x_594_);
lean_ctor_set(v___x_589_, 0, v_x_583_);
v___x_596_ = v___x_589_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_x_583_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v_x_583_ = v___x_596_;
v_x_584_ = v_tail_587_;
goto _start;
}
}
else
{
lean_object* v___x_599_; 
lean_del_object(v___x_589_);
lean_dec(v_tail_587_);
lean_dec(v_head_586_);
lean_dec_ref(v_x_583_);
v___x_599_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_599_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_606_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_607_ = lean_unsigned_to_nat(4u);
v___x_608_ = lean_unsigned_to_nat(65u);
v___x_609_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_610_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_611_ = l_mkPanicMessageWithDecl(v___x_610_, v___x_609_, v___x_608_, v___x_607_, v___x_606_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = lean_string_utf8_byte_size(v_s_615_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_nat_dec_eq(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_inc_ref(v_s_615_);
v___x_619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_619_, 0, v_s_615_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_616_);
v___x_620_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v___x_619_);
v___x_621_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_622_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_615_, v___x_619_, v___x_616_, v___x_620_, v___x_621_);
lean_dec_ref_known(v___x_619_, 3);
v___x_623_ = lean_array_to_list(v___x_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_625_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_624_);
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_628_; 
v_head_626_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_head_626_);
v_tail_627_ = lean_ctor_get(v___x_623_, 1);
lean_inc(v_tail_627_);
lean_dec_ref_known(v___x_623_, 2);
v___x_628_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_626_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_dec(v_tail_627_);
return v___x_628_;
}
else
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_629_, v_tail_627_);
return v___x_630_;
}
}
}
else
{
lean_object* v___x_631_; 
lean_dec_ref(v_s_615_);
v___x_631_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v_inst_635_, lean_object* v_R_636_, lean_object* v_a_637_, lean_object* v_b_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_632_, v___x_633_, v___x_634_, v_a_637_, v_b_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v_inst_643_, lean_object* v_R_644_, lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_640_, v___x_641_, v___x_642_, v_inst_643_, v_R_644_, v_a_645_, v_b_646_);
lean_dec_ref(v___x_641_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_648_){
_start:
{
switch(lean_obj_tag(v_p_648_))
{
case 0:
{
return v_p_648_;
}
case 2:
{
lean_object* v_pre_649_; 
v_pre_649_ = lean_ctor_get(v_p_648_, 0);
if (lean_obj_tag(v_pre_649_) == 0)
{
return v_pre_649_;
}
else
{
lean_inc(v_pre_649_);
return v_pre_649_;
}
}
default: 
{
lean_inc(v_p_648_);
return v_p_648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_650_);
lean_dec(v_p_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_655_){
_start:
{
switch(lean_obj_tag(v_x_655_))
{
case 0:
{
lean_object* v_module_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_module_656_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_module_656_);
lean_dec_ref_known(v_x_655_, 1);
v___x_657_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_658_ = 1;
v___x_659_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_656_, v___x_658_);
v___x_660_ = lean_string_append(v___x_657_, v___x_659_);
lean_dec_ref(v___x_659_);
return v___x_660_;
}
case 1:
{
lean_object* v_package_661_; lean_object* v___x_662_; 
v_package_661_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_package_661_);
lean_dec_ref_known(v_x_655_, 1);
v___x_662_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_661_);
lean_dec(v_package_661_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_663_; 
v___x_663_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_663_;
}
else
{
lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_664_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_665_ = 1;
v___x_666_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_662_, v___x_665_);
v___x_667_ = lean_string_append(v___x_664_, v___x_666_);
lean_dec_ref(v___x_666_);
return v___x_667_;
}
}
case 2:
{
lean_object* v_package_668_; lean_object* v_module_669_; lean_object* v___x_670_; 
v_package_668_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_package_668_);
v_module_669_ = lean_ctor_get(v_x_655_, 1);
lean_inc(v_module_669_);
lean_dec_ref_known(v_x_655_, 2);
v___x_670_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_668_);
lean_dec(v_package_668_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_672_ = 1;
v___x_673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_669_, v___x_672_);
v___x_674_ = lean_string_append(v___x_671_, v___x_673_);
lean_dec_ref(v___x_673_);
return v___x_674_;
}
else
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_675_ = 1;
v___x_676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_670_, v___x_675_);
v___x_677_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_678_ = lean_string_append(v___x_676_, v___x_677_);
v___x_679_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_669_, v___x_675_);
v___x_680_ = lean_string_append(v___x_678_, v___x_679_);
lean_dec_ref(v___x_679_);
return v___x_680_;
}
}
case 3:
{
lean_object* v_package_681_; lean_object* v_target_682_; lean_object* v___x_683_; 
v_package_681_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_package_681_);
v_target_682_ = lean_ctor_get(v_x_655_, 1);
lean_inc(v_target_682_);
lean_dec_ref_known(v_x_655_, 2);
v___x_683_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_package_681_);
lean_dec(v_package_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
uint8_t v___x_684_; lean_object* v___x_685_; 
v___x_684_ = 1;
v___x_685_ = l_Lean_Name_toString(v_target_682_, v___x_684_);
return v___x_685_;
}
else
{
uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_686_ = 1;
v___x_687_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_683_, v___x_686_);
v___x_688_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_689_ = lean_string_append(v___x_687_, v___x_688_);
v___x_690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_682_, v___x_686_);
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
lean_dec_ref(v___x_690_);
return v___x_691_;
}
}
default: 
{
lean_object* v_target_692_; lean_object* v_facet_693_; uint8_t v___x_694_; 
v_target_692_ = lean_ctor_get(v_x_655_, 0);
lean_inc_ref(v_target_692_);
v_facet_693_ = lean_ctor_get(v_x_655_, 1);
lean_inc(v_facet_693_);
lean_dec_ref_known(v_x_655_, 2);
v___x_694_ = l_Lean_Name_isAnonymous(v_facet_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_695_ = l_Lake_PartialBuildKey_toString(v_target_692_);
v___x_696_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_697_ = lean_string_append(v___x_695_, v___x_696_);
v___x_698_ = 1;
v___x_699_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_693_, v___x_698_);
v___x_700_ = lean_string_append(v___x_697_, v___x_699_);
lean_dec_ref(v___x_699_);
return v___x_700_;
}
else
{
lean_dec(v_facet_693_);
v_x_655_ = v_target_692_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_704_, lean_object* v_facet_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_706_, 0, v_module_704_);
v___x_707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_facet_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_708_, lean_object* v_facet_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_package_708_);
v___x_711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_facet_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_712_, lean_object* v_module_713_, lean_object* v_facet_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_715_, 0, v_package_712_);
lean_ctor_set(v___x_715_, 1, v_module_713_);
v___x_716_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v_facet_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_717_, lean_object* v_target_718_, lean_object* v_facet_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_720_, 0, v_package_717_);
lean_ctor_set(v___x_720_, 1, v_target_718_);
v___x_721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_facet_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_722_, lean_object* v_target_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_724_, 0, v_package_722_);
lean_ctor_set(v___x_724_, 1, v_target_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_725_){
_start:
{
switch(lean_obj_tag(v_x_725_))
{
case 0:
{
lean_object* v_module_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_module_726_ = lean_ctor_get(v_x_725_, 0);
lean_inc(v_module_726_);
lean_dec_ref_known(v_x_725_, 1);
v___x_727_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_728_ = 1;
v___x_729_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_726_, v___x_728_);
v___x_730_ = lean_string_append(v___x_727_, v___x_729_);
lean_dec_ref(v___x_729_);
return v___x_730_;
}
case 1:
{
lean_object* v_package_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_package_731_ = lean_ctor_get(v_x_725_, 0);
lean_inc(v_package_731_);
lean_dec_ref_known(v_x_725_, 1);
v___x_732_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_733_ = l_Lean_Name_getPrefix(v_package_731_);
lean_dec(v_package_731_);
v___x_734_ = 1;
v___x_735_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_733_, v___x_734_);
v___x_736_ = lean_string_append(v___x_732_, v___x_735_);
lean_dec_ref(v___x_735_);
return v___x_736_;
}
case 2:
{
lean_object* v_package_737_; lean_object* v_module_738_; lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_package_737_ = lean_ctor_get(v_x_725_, 0);
lean_inc(v_package_737_);
v_module_738_ = lean_ctor_get(v_x_725_, 1);
lean_inc(v_module_738_);
lean_dec_ref_known(v_x_725_, 2);
v___x_739_ = l_Lean_Name_getPrefix(v_package_737_);
lean_dec(v_package_737_);
v___x_740_ = 1;
v___x_741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_739_, v___x_740_);
v___x_742_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_743_ = lean_string_append(v___x_741_, v___x_742_);
v___x_744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_738_, v___x_740_);
v___x_745_ = lean_string_append(v___x_743_, v___x_744_);
lean_dec_ref(v___x_744_);
return v___x_745_;
}
case 3:
{
lean_object* v_package_746_; lean_object* v_target_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_package_746_ = lean_ctor_get(v_x_725_, 0);
lean_inc(v_package_746_);
v_target_747_ = lean_ctor_get(v_x_725_, 1);
lean_inc(v_target_747_);
lean_dec_ref_known(v_x_725_, 2);
v___x_748_ = l_Lean_Name_getPrefix(v_package_746_);
lean_dec(v_package_746_);
v___x_749_ = 1;
v___x_750_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_748_, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_752_ = lean_string_append(v___x_750_, v___x_751_);
v___x_753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_747_, v___x_749_);
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
lean_dec_ref(v___x_753_);
return v___x_754_;
}
default: 
{
lean_object* v_target_755_; lean_object* v_facet_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_target_755_ = lean_ctor_get(v_x_725_, 0);
lean_inc_ref(v_target_755_);
v_facet_756_ = lean_ctor_get(v_x_725_, 1);
lean_inc(v_facet_756_);
lean_dec_ref_known(v_x_725_, 2);
v___x_757_ = l_Lake_BuildKey_toString(v_target_755_);
v___x_758_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_759_ = lean_string_append(v___x_757_, v___x_758_);
v___x_760_ = l_Lake_Name_eraseHead(v_facet_756_);
v___x_761_ = 1;
v___x_762_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_760_, v___x_761_);
v___x_763_ = lean_string_append(v___x_759_, v___x_762_);
lean_dec_ref(v___x_762_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_764_){
_start:
{
lean_object* v_p_766_; lean_object* v_m_767_; 
switch(lean_obj_tag(v_x_764_))
{
case 0:
{
lean_object* v_module_775_; uint8_t v___x_776_; lean_object* v___x_777_; 
v_module_775_ = lean_ctor_get(v_x_764_, 0);
lean_inc(v_module_775_);
lean_dec_ref_known(v_x_764_, 1);
v___x_776_ = 1;
v___x_777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_775_, v___x_776_);
return v___x_777_;
}
case 1:
{
lean_object* v_package_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; 
v_package_778_ = lean_ctor_get(v_x_764_, 0);
lean_inc(v_package_778_);
lean_dec_ref_known(v_x_764_, 1);
v___x_779_ = l_Lean_Name_getPrefix(v_package_778_);
lean_dec(v_package_778_);
v___x_780_ = 1;
v___x_781_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_779_, v___x_780_);
return v___x_781_;
}
case 4:
{
lean_object* v_target_782_; lean_object* v_facet_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_target_782_ = lean_ctor_get(v_x_764_, 0);
lean_inc_ref(v_target_782_);
v_facet_783_ = lean_ctor_get(v_x_764_, 1);
lean_inc(v_facet_783_);
lean_dec_ref_known(v_x_764_, 2);
v___x_784_ = l_Lake_BuildKey_toSimpleString(v_target_782_);
v___x_785_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_786_ = lean_string_append(v___x_784_, v___x_785_);
v___x_787_ = l_Lake_Name_eraseHead(v_facet_783_);
v___x_788_ = 1;
v___x_789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_787_, v___x_788_);
v___x_790_ = lean_string_append(v___x_786_, v___x_789_);
lean_dec_ref(v___x_789_);
return v___x_790_;
}
default: 
{
lean_object* v_package_791_; lean_object* v_module_792_; 
v_package_791_ = lean_ctor_get(v_x_764_, 0);
lean_inc(v_package_791_);
v_module_792_ = lean_ctor_get(v_x_764_, 1);
lean_inc(v_module_792_);
lean_dec_ref(v_x_764_);
v_p_766_ = v_package_791_;
v_m_767_ = v_module_792_;
goto v___jp_765_;
}
}
v___jp_765_:
{
lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_768_ = l_Lean_Name_getPrefix(v_p_766_);
lean_dec(v_p_766_);
v___x_769_ = 1;
v___x_770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_768_, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_772_ = lean_string_append(v___x_770_, v___x_771_);
v___x_773_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_767_, v___x_769_);
v___x_774_ = lean_string_append(v___x_772_, v___x_773_);
lean_dec_ref(v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_795_, lean_object* v_k_x27_796_){
_start:
{
switch(lean_obj_tag(v_k_795_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_796_) == 0)
{
lean_object* v_module_797_; lean_object* v_module_798_; uint8_t v___x_799_; 
v_module_797_ = lean_ctor_get(v_k_795_, 0);
v_module_798_ = lean_ctor_get(v_k_x27_796_, 0);
v___x_799_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_797_, v_module_798_);
return v___x_799_;
}
else
{
uint8_t v___x_800_; 
v___x_800_ = 0;
return v___x_800_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_796_))
{
case 0:
{
uint8_t v___x_801_; 
v___x_801_ = 2;
return v___x_801_;
}
case 1:
{
lean_object* v_package_802_; lean_object* v_package_803_; uint8_t v___x_804_; 
v_package_802_ = lean_ctor_get(v_k_795_, 0);
v_package_803_ = lean_ctor_get(v_k_x27_796_, 0);
v___x_804_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_802_, v_package_803_);
return v___x_804_;
}
default: 
{
uint8_t v___x_805_; 
v___x_805_ = 0;
return v___x_805_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_796_))
{
case 4:
{
uint8_t v___x_806_; 
v___x_806_ = 0;
return v___x_806_;
}
case 3:
{
uint8_t v___x_807_; 
v___x_807_ = 0;
return v___x_807_;
}
case 2:
{
lean_object* v_package_808_; lean_object* v_module_809_; lean_object* v_package_810_; lean_object* v_module_811_; uint8_t v___x_812_; 
v_package_808_ = lean_ctor_get(v_k_795_, 0);
v_module_809_ = lean_ctor_get(v_k_795_, 1);
v_package_810_ = lean_ctor_get(v_k_x27_796_, 0);
v_module_811_ = lean_ctor_get(v_k_x27_796_, 1);
v___x_812_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_809_, v_module_811_);
if (v___x_812_ == 1)
{
uint8_t v___x_813_; 
v___x_813_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_808_, v_package_810_);
return v___x_813_;
}
else
{
return v___x_812_;
}
}
default: 
{
uint8_t v___x_814_; 
v___x_814_ = 2;
return v___x_814_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_k_x27_796_))
{
case 4:
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
case 3:
{
lean_object* v_package_816_; lean_object* v_target_817_; lean_object* v_package_818_; lean_object* v_target_819_; uint8_t v___x_820_; 
v_package_816_ = lean_ctor_get(v_k_795_, 0);
v_target_817_ = lean_ctor_get(v_k_795_, 1);
v_package_818_ = lean_ctor_get(v_k_x27_796_, 0);
v_target_819_ = lean_ctor_get(v_k_x27_796_, 1);
v___x_820_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_816_, v_package_818_);
if (v___x_820_ == 1)
{
uint8_t v___x_821_; 
v___x_821_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_817_, v_target_819_);
return v___x_821_;
}
else
{
return v___x_820_;
}
}
default: 
{
uint8_t v___x_822_; 
v___x_822_ = 2;
return v___x_822_;
}
}
}
default: 
{
if (lean_obj_tag(v_k_x27_796_) == 4)
{
lean_object* v_target_823_; lean_object* v_facet_824_; lean_object* v_target_825_; lean_object* v_facet_826_; uint8_t v___x_827_; 
v_target_823_ = lean_ctor_get(v_k_795_, 0);
v_facet_824_ = lean_ctor_get(v_k_795_, 1);
v_target_825_ = lean_ctor_get(v_k_x27_796_, 0);
v_facet_826_ = lean_ctor_get(v_k_x27_796_, 1);
v___x_827_ = l_Lake_BuildKey_quickCmp(v_target_823_, v_target_825_);
if (v___x_827_ == 1)
{
uint8_t v___x_828_; 
v___x_828_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_824_, v_facet_826_);
return v___x_828_;
}
else
{
return v___x_827_;
}
}
else
{
uint8_t v___x_829_; 
v___x_829_ = 2;
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* v_k_830_, lean_object* v_k_x27_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lake_BuildKey_quickCmp(v_k_830_, v_k_x27_831_);
lean_dec_ref(v_k_x27_831_);
lean_dec_ref(v_k_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* v_x_834_, lean_object* v_h__1_835_, lean_object* v_h__2_836_, lean_object* v_h__3_837_, lean_object* v_h__4_838_, lean_object* v_h__5_839_){
_start:
{
switch(lean_obj_tag(v_x_834_))
{
case 0:
{
lean_object* v_module_840_; lean_object* v___x_841_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__4_838_);
lean_dec(v_h__3_837_);
lean_dec(v_h__2_836_);
v_module_840_ = lean_ctor_get(v_x_834_, 0);
lean_inc(v_module_840_);
lean_dec_ref_known(v_x_834_, 1);
v___x_841_ = lean_apply_1(v_h__1_835_, v_module_840_);
return v___x_841_;
}
case 1:
{
lean_object* v_package_842_; lean_object* v___x_843_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__4_838_);
lean_dec(v_h__3_837_);
lean_dec(v_h__1_835_);
v_package_842_ = lean_ctor_get(v_x_834_, 0);
lean_inc(v_package_842_);
lean_dec_ref_known(v_x_834_, 1);
v___x_843_ = lean_apply_1(v_h__2_836_, v_package_842_);
return v___x_843_;
}
case 2:
{
lean_object* v_package_844_; lean_object* v_module_845_; lean_object* v___x_846_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__4_838_);
lean_dec(v_h__2_836_);
lean_dec(v_h__1_835_);
v_package_844_ = lean_ctor_get(v_x_834_, 0);
lean_inc(v_package_844_);
v_module_845_ = lean_ctor_get(v_x_834_, 1);
lean_inc(v_module_845_);
lean_dec_ref_known(v_x_834_, 2);
v___x_846_ = lean_apply_2(v_h__3_837_, v_package_844_, v_module_845_);
return v___x_846_;
}
case 3:
{
lean_object* v_package_847_; lean_object* v_target_848_; lean_object* v___x_849_; 
lean_dec(v_h__5_839_);
lean_dec(v_h__3_837_);
lean_dec(v_h__2_836_);
lean_dec(v_h__1_835_);
v_package_847_ = lean_ctor_get(v_x_834_, 0);
lean_inc(v_package_847_);
v_target_848_ = lean_ctor_get(v_x_834_, 1);
lean_inc(v_target_848_);
lean_dec_ref_known(v_x_834_, 2);
v___x_849_ = lean_apply_2(v_h__4_838_, v_package_847_, v_target_848_);
return v___x_849_;
}
default: 
{
lean_object* v_target_850_; lean_object* v_facet_851_; lean_object* v___x_852_; 
lean_dec(v_h__4_838_);
lean_dec(v_h__3_837_);
lean_dec(v_h__2_836_);
lean_dec(v_h__1_835_);
v_target_850_ = lean_ctor_get(v_x_834_, 0);
lean_inc_ref(v_target_850_);
v_facet_851_ = lean_ctor_get(v_x_834_, 1);
lean_inc(v_facet_851_);
lean_dec_ref_known(v_x_834_, 2);
v___x_852_ = lean_apply_2(v_h__5_839_, v_target_850_, v_facet_851_);
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_853_, lean_object* v_x_854_, lean_object* v_h__1_855_, lean_object* v_h__2_856_, lean_object* v_h__3_857_, lean_object* v_h__4_858_, lean_object* v_h__5_859_){
_start:
{
switch(lean_obj_tag(v_x_854_))
{
case 0:
{
lean_object* v_module_860_; lean_object* v___x_861_; 
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
v_module_860_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_module_860_);
lean_dec_ref_known(v_x_854_, 1);
v___x_861_ = lean_apply_1(v_h__1_855_, v_module_860_);
return v___x_861_;
}
case 1:
{
lean_object* v_package_862_; lean_object* v___x_863_; 
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__1_855_);
v_package_862_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_package_862_);
lean_dec_ref_known(v_x_854_, 1);
v___x_863_ = lean_apply_1(v_h__2_856_, v_package_862_);
return v___x_863_;
}
case 2:
{
lean_object* v_package_864_; lean_object* v_module_865_; lean_object* v___x_866_; 
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_package_864_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_package_864_);
v_module_865_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_module_865_);
lean_dec_ref_known(v_x_854_, 2);
v___x_866_ = lean_apply_2(v_h__3_857_, v_package_864_, v_module_865_);
return v___x_866_;
}
case 3:
{
lean_object* v_package_867_; lean_object* v_target_868_; lean_object* v___x_869_; 
lean_dec(v_h__5_859_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_package_867_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_package_867_);
v_target_868_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_target_868_);
lean_dec_ref_known(v_x_854_, 2);
v___x_869_ = lean_apply_2(v_h__4_858_, v_package_867_, v_target_868_);
return v___x_869_;
}
default: 
{
lean_object* v_target_870_; lean_object* v_facet_871_; lean_object* v___x_872_; 
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_target_870_ = lean_ctor_get(v_x_854_, 0);
lean_inc_ref(v_target_870_);
v_facet_871_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_facet_871_);
lean_dec_ref_known(v_x_854_, 2);
v___x_872_ = lean_apply_2(v_h__5_859_, v_target_870_, v_facet_871_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_873_, lean_object* v_h__1_874_, lean_object* v_h__2_875_){
_start:
{
if (lean_obj_tag(v_k_x27_873_) == 0)
{
lean_object* v_module_876_; lean_object* v___x_877_; 
lean_dec(v_h__2_875_);
v_module_876_ = lean_ctor_get(v_k_x27_873_, 0);
lean_inc(v_module_876_);
lean_dec_ref_known(v_k_x27_873_, 1);
v___x_877_ = lean_apply_1(v_h__1_874_, v_module_876_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; 
lean_dec(v_h__1_874_);
v___x_878_ = lean_apply_2(v_h__2_875_, v_k_x27_873_, lean_box(0));
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_879_, lean_object* v_k_x27_880_, lean_object* v_h__1_881_, lean_object* v_h__2_882_){
_start:
{
if (lean_obj_tag(v_k_x27_880_) == 0)
{
lean_object* v_module_883_; lean_object* v___x_884_; 
lean_dec(v_h__2_882_);
v_module_883_ = lean_ctor_get(v_k_x27_880_, 0);
lean_inc(v_module_883_);
lean_dec_ref_known(v_k_x27_880_, 1);
v___x_884_ = lean_apply_1(v_h__1_881_, v_module_883_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
lean_dec(v_h__1_881_);
v___x_885_ = lean_apply_2(v_h__2_882_, v_k_x27_880_, lean_box(0));
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_886_, lean_object* v_h__1_887_, lean_object* v_h__2_888_, lean_object* v_h__3_889_){
_start:
{
switch(lean_obj_tag(v_k_x27_886_))
{
case 0:
{
lean_object* v_module_890_; lean_object* v___x_891_; 
lean_dec(v_h__3_889_);
lean_dec(v_h__2_888_);
v_module_890_ = lean_ctor_get(v_k_x27_886_, 0);
lean_inc(v_module_890_);
lean_dec_ref_known(v_k_x27_886_, 1);
v___x_891_ = lean_apply_1(v_h__1_887_, v_module_890_);
return v___x_891_;
}
case 1:
{
lean_object* v_package_892_; lean_object* v___x_893_; 
lean_dec(v_h__3_889_);
lean_dec(v_h__1_887_);
v_package_892_ = lean_ctor_get(v_k_x27_886_, 0);
lean_inc(v_package_892_);
lean_dec_ref_known(v_k_x27_886_, 1);
v___x_893_ = lean_apply_1(v_h__2_888_, v_package_892_);
return v___x_893_;
}
default: 
{
lean_object* v___x_894_; 
lean_dec(v_h__2_888_);
lean_dec(v_h__1_887_);
v___x_894_ = lean_apply_3(v_h__3_889_, v_k_x27_886_, lean_box(0), lean_box(0));
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_895_, lean_object* v_k_x27_896_, lean_object* v_h__1_897_, lean_object* v_h__2_898_, lean_object* v_h__3_899_){
_start:
{
switch(lean_obj_tag(v_k_x27_896_))
{
case 0:
{
lean_object* v_module_900_; lean_object* v___x_901_; 
lean_dec(v_h__3_899_);
lean_dec(v_h__2_898_);
v_module_900_ = lean_ctor_get(v_k_x27_896_, 0);
lean_inc(v_module_900_);
lean_dec_ref_known(v_k_x27_896_, 1);
v___x_901_ = lean_apply_1(v_h__1_897_, v_module_900_);
return v___x_901_;
}
case 1:
{
lean_object* v_package_902_; lean_object* v___x_903_; 
lean_dec(v_h__3_899_);
lean_dec(v_h__1_897_);
v_package_902_ = lean_ctor_get(v_k_x27_896_, 0);
lean_inc(v_package_902_);
lean_dec_ref_known(v_k_x27_896_, 1);
v___x_903_ = lean_apply_1(v_h__2_898_, v_package_902_);
return v___x_903_;
}
default: 
{
lean_object* v___x_904_; 
lean_dec(v_h__2_898_);
lean_dec(v_h__1_897_);
v___x_904_ = lean_apply_3(v_h__3_899_, v_k_x27_896_, lean_box(0), lean_box(0));
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_905_, lean_object* v_h__1_906_, lean_object* v_h__2_907_, lean_object* v_h__3_908_, lean_object* v_h__4_909_){
_start:
{
switch(lean_obj_tag(v_k_x27_905_))
{
case 4:
{
lean_object* v_target_910_; lean_object* v_facet_911_; lean_object* v___x_912_; 
lean_dec(v_h__4_909_);
lean_dec(v_h__3_908_);
lean_dec(v_h__2_907_);
v_target_910_ = lean_ctor_get(v_k_x27_905_, 0);
lean_inc_ref(v_target_910_);
v_facet_911_ = lean_ctor_get(v_k_x27_905_, 1);
lean_inc(v_facet_911_);
lean_dec_ref_known(v_k_x27_905_, 2);
v___x_912_ = lean_apply_2(v_h__1_906_, v_target_910_, v_facet_911_);
return v___x_912_;
}
case 3:
{
lean_object* v_package_913_; lean_object* v_target_914_; lean_object* v___x_915_; 
lean_dec(v_h__4_909_);
lean_dec(v_h__3_908_);
lean_dec(v_h__1_906_);
v_package_913_ = lean_ctor_get(v_k_x27_905_, 0);
lean_inc(v_package_913_);
v_target_914_ = lean_ctor_get(v_k_x27_905_, 1);
lean_inc(v_target_914_);
lean_dec_ref_known(v_k_x27_905_, 2);
v___x_915_ = lean_apply_2(v_h__2_907_, v_package_913_, v_target_914_);
return v___x_915_;
}
case 2:
{
lean_object* v_package_916_; lean_object* v_module_917_; lean_object* v___x_918_; 
lean_dec(v_h__4_909_);
lean_dec(v_h__2_907_);
lean_dec(v_h__1_906_);
v_package_916_ = lean_ctor_get(v_k_x27_905_, 0);
lean_inc(v_package_916_);
v_module_917_ = lean_ctor_get(v_k_x27_905_, 1);
lean_inc(v_module_917_);
lean_dec_ref_known(v_k_x27_905_, 2);
v___x_918_ = lean_apply_2(v_h__3_908_, v_package_916_, v_module_917_);
return v___x_918_;
}
default: 
{
lean_object* v___x_919_; 
lean_dec(v_h__3_908_);
lean_dec(v_h__2_907_);
lean_dec(v_h__1_906_);
v___x_919_ = lean_apply_4(v_h__4_909_, v_k_x27_905_, lean_box(0), lean_box(0), lean_box(0));
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_920_, lean_object* v_k_x27_921_, lean_object* v_h__1_922_, lean_object* v_h__2_923_, lean_object* v_h__3_924_, lean_object* v_h__4_925_){
_start:
{
switch(lean_obj_tag(v_k_x27_921_))
{
case 4:
{
lean_object* v_target_926_; lean_object* v_facet_927_; lean_object* v___x_928_; 
lean_dec(v_h__4_925_);
lean_dec(v_h__3_924_);
lean_dec(v_h__2_923_);
v_target_926_ = lean_ctor_get(v_k_x27_921_, 0);
lean_inc_ref(v_target_926_);
v_facet_927_ = lean_ctor_get(v_k_x27_921_, 1);
lean_inc(v_facet_927_);
lean_dec_ref_known(v_k_x27_921_, 2);
v___x_928_ = lean_apply_2(v_h__1_922_, v_target_926_, v_facet_927_);
return v___x_928_;
}
case 3:
{
lean_object* v_package_929_; lean_object* v_target_930_; lean_object* v___x_931_; 
lean_dec(v_h__4_925_);
lean_dec(v_h__3_924_);
lean_dec(v_h__1_922_);
v_package_929_ = lean_ctor_get(v_k_x27_921_, 0);
lean_inc(v_package_929_);
v_target_930_ = lean_ctor_get(v_k_x27_921_, 1);
lean_inc(v_target_930_);
lean_dec_ref_known(v_k_x27_921_, 2);
v___x_931_ = lean_apply_2(v_h__2_923_, v_package_929_, v_target_930_);
return v___x_931_;
}
case 2:
{
lean_object* v_package_932_; lean_object* v_module_933_; lean_object* v___x_934_; 
lean_dec(v_h__4_925_);
lean_dec(v_h__2_923_);
lean_dec(v_h__1_922_);
v_package_932_ = lean_ctor_get(v_k_x27_921_, 0);
lean_inc(v_package_932_);
v_module_933_ = lean_ctor_get(v_k_x27_921_, 1);
lean_inc(v_module_933_);
lean_dec_ref_known(v_k_x27_921_, 2);
v___x_934_ = lean_apply_2(v_h__3_924_, v_package_932_, v_module_933_);
return v___x_934_;
}
default: 
{
lean_object* v___x_935_; 
lean_dec(v_h__3_924_);
lean_dec(v_h__2_923_);
lean_dec(v_h__1_922_);
v___x_935_ = lean_apply_4(v_h__4_925_, v_k_x27_921_, lean_box(0), lean_box(0), lean_box(0));
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_936_, lean_object* v_h__1_937_, lean_object* v_h__2_938_){
_start:
{
if (v_x_936_ == 1)
{
lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec(v_h__2_938_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_apply_1(v_h__1_937_, v___x_939_);
return v___x_940_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_h__1_937_);
v___x_941_ = lean_box(v_x_936_);
v___x_942_ = lean_apply_2(v_h__2_938_, v___x_941_, lean_box(0));
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_943_, lean_object* v_h__1_944_, lean_object* v_h__2_945_){
_start:
{
uint8_t v_x_13__boxed_946_; lean_object* v_res_947_; 
v_x_13__boxed_946_ = lean_unbox(v_x_943_);
v_res_947_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_13__boxed_946_, v_h__1_944_, v_h__2_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_948_, uint8_t v_x_949_, lean_object* v_h__1_950_, lean_object* v_h__2_951_){
_start:
{
if (v_x_949_ == 1)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec(v_h__2_951_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_apply_1(v_h__1_950_, v___x_952_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_h__1_950_);
v___x_954_ = lean_box(v_x_949_);
v___x_955_ = lean_apply_2(v_h__2_951_, v___x_954_, lean_box(0));
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_956_, lean_object* v_x_957_, lean_object* v_h__1_958_, lean_object* v_h__2_959_){
_start:
{
uint8_t v_x_24__boxed_960_; lean_object* v_res_961_; 
v_x_24__boxed_960_ = lean_unbox(v_x_957_);
v_res_961_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_956_, v_x_24__boxed_960_, v_h__1_958_, v_h__2_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_962_, lean_object* v_h__1_963_, lean_object* v_h__2_964_, lean_object* v_h__3_965_){
_start:
{
switch(lean_obj_tag(v_k_x27_962_))
{
case 4:
{
lean_object* v_target_966_; lean_object* v_facet_967_; lean_object* v___x_968_; 
lean_dec(v_h__3_965_);
lean_dec(v_h__2_964_);
v_target_966_ = lean_ctor_get(v_k_x27_962_, 0);
lean_inc_ref(v_target_966_);
v_facet_967_ = lean_ctor_get(v_k_x27_962_, 1);
lean_inc(v_facet_967_);
lean_dec_ref_known(v_k_x27_962_, 2);
v___x_968_ = lean_apply_2(v_h__1_963_, v_target_966_, v_facet_967_);
return v___x_968_;
}
case 3:
{
lean_object* v_package_969_; lean_object* v_target_970_; lean_object* v___x_971_; 
lean_dec(v_h__3_965_);
lean_dec(v_h__1_963_);
v_package_969_ = lean_ctor_get(v_k_x27_962_, 0);
lean_inc(v_package_969_);
v_target_970_ = lean_ctor_get(v_k_x27_962_, 1);
lean_inc(v_target_970_);
lean_dec_ref_known(v_k_x27_962_, 2);
v___x_971_ = lean_apply_2(v_h__2_964_, v_package_969_, v_target_970_);
return v___x_971_;
}
default: 
{
lean_object* v___x_972_; 
lean_dec(v_h__2_964_);
lean_dec(v_h__1_963_);
v___x_972_ = lean_apply_3(v_h__3_965_, v_k_x27_962_, lean_box(0), lean_box(0));
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_973_, lean_object* v_k_x27_974_, lean_object* v_h__1_975_, lean_object* v_h__2_976_, lean_object* v_h__3_977_){
_start:
{
switch(lean_obj_tag(v_k_x27_974_))
{
case 4:
{
lean_object* v_target_978_; lean_object* v_facet_979_; lean_object* v___x_980_; 
lean_dec(v_h__3_977_);
lean_dec(v_h__2_976_);
v_target_978_ = lean_ctor_get(v_k_x27_974_, 0);
lean_inc_ref(v_target_978_);
v_facet_979_ = lean_ctor_get(v_k_x27_974_, 1);
lean_inc(v_facet_979_);
lean_dec_ref_known(v_k_x27_974_, 2);
v___x_980_ = lean_apply_2(v_h__1_975_, v_target_978_, v_facet_979_);
return v___x_980_;
}
case 3:
{
lean_object* v_package_981_; lean_object* v_target_982_; lean_object* v___x_983_; 
lean_dec(v_h__3_977_);
lean_dec(v_h__1_975_);
v_package_981_ = lean_ctor_get(v_k_x27_974_, 0);
lean_inc(v_package_981_);
v_target_982_ = lean_ctor_get(v_k_x27_974_, 1);
lean_inc(v_target_982_);
lean_dec_ref_known(v_k_x27_974_, 2);
v___x_983_ = lean_apply_2(v_h__2_976_, v_package_981_, v_target_982_);
return v___x_983_;
}
default: 
{
lean_object* v___x_984_; 
lean_dec(v_h__2_976_);
lean_dec(v_h__1_975_);
v___x_984_ = lean_apply_3(v_h__3_977_, v_k_x27_974_, lean_box(0), lean_box(0));
return v___x_984_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_985_, lean_object* v_h__1_986_, lean_object* v_h__2_987_){
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
lean_dec_ref_known(v_k_x27_985_, 2);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_992_, lean_object* v_k_x27_993_, lean_object* v_h__1_994_, lean_object* v_h__2_995_){
_start:
{
if (lean_obj_tag(v_k_x27_993_) == 4)
{
lean_object* v_target_996_; lean_object* v_facet_997_; lean_object* v___x_998_; 
lean_dec(v_h__2_995_);
v_target_996_ = lean_ctor_get(v_k_x27_993_, 0);
lean_inc_ref(v_target_996_);
v_facet_997_ = lean_ctor_get(v_k_x27_993_, 1);
lean_inc(v_facet_997_);
lean_dec_ref_known(v_k_x27_993_, 2);
v___x_998_ = lean_apply_2(v_h__1_994_, v_target_996_, v_facet_997_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; 
lean_dec(v_h__1_994_);
v___x_999_ = lean_apply_2(v_h__2_995_, v_k_x27_993_, lean_box(0));
return v___x_999_;
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
