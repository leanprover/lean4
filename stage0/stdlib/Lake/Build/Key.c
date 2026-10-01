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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
static const lean_string_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "ill-formed target: default package targets are not supported in partial build keys"};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0;
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
static const lean_ctor_object l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PartialBuildKey_instInhabited___closed__0_value)}};
static const lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6 = (const lean_object*)&l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0;
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
LEAN_EXPORT uint64_t l_Lake_instHashableBuildKey_hash(lean_object* v_x_268_){
_start:
{
switch(lean_obj_tag(v_x_268_))
{
case 0:
{
lean_object* v_module_269_; uint64_t v___x_270_; 
v_module_269_ = lean_ctor_get(v_x_268_, 0);
v___x_270_ = 0ULL;
if (lean_obj_tag(v_module_269_) == 0)
{
uint64_t v___x_271_; 
v___x_271_ = 8934034000889494153ULL;
return v___x_271_;
}
else
{
uint64_t v_hash_272_; uint64_t v___x_273_; 
v_hash_272_ = lean_ctor_get_uint64(v_module_269_, sizeof(void*)*2);
v___x_273_ = lean_uint64_mix_hash(v___x_270_, v_hash_272_);
return v___x_273_;
}
}
case 1:
{
lean_object* v_package_274_; uint64_t v___x_275_; 
v_package_274_ = lean_ctor_get(v_x_268_, 0);
v___x_275_ = 1ULL;
if (lean_obj_tag(v_package_274_) == 0)
{
uint64_t v___x_276_; 
v___x_276_ = 13067028307566252276ULL;
return v___x_276_;
}
else
{
uint64_t v_hash_277_; uint64_t v___x_278_; 
v_hash_277_ = lean_ctor_get_uint64(v_package_274_, sizeof(void*)*2);
v___x_278_ = lean_uint64_mix_hash(v___x_275_, v_hash_277_);
return v___x_278_;
}
}
case 2:
{
lean_object* v_package_279_; lean_object* v_module_280_; uint64_t v___x_281_; uint64_t v___y_283_; 
v_package_279_ = lean_ctor_get(v_x_268_, 0);
v_module_280_ = lean_ctor_get(v_x_268_, 1);
v___x_281_ = 2ULL;
if (lean_obj_tag(v_package_279_) == 0)
{
uint64_t v___x_289_; 
v___x_289_ = 1723ULL;
v___y_283_ = v___x_289_;
goto v___jp_282_;
}
else
{
uint64_t v_hash_290_; 
v_hash_290_ = lean_ctor_get_uint64(v_package_279_, sizeof(void*)*2);
v___y_283_ = v_hash_290_;
goto v___jp_282_;
}
v___jp_282_:
{
uint64_t v___x_284_; 
v___x_284_ = lean_uint64_mix_hash(v___x_281_, v___y_283_);
if (lean_obj_tag(v_module_280_) == 0)
{
uint64_t v___x_285_; uint64_t v___x_286_; 
v___x_285_ = 1723ULL;
v___x_286_ = lean_uint64_mix_hash(v___x_284_, v___x_285_);
return v___x_286_;
}
else
{
uint64_t v_hash_287_; uint64_t v___x_288_; 
v_hash_287_ = lean_ctor_get_uint64(v_module_280_, sizeof(void*)*2);
v___x_288_ = lean_uint64_mix_hash(v___x_284_, v_hash_287_);
return v___x_288_;
}
}
}
case 3:
{
lean_object* v_package_291_; lean_object* v_target_292_; uint64_t v___x_293_; uint64_t v___y_295_; 
v_package_291_ = lean_ctor_get(v_x_268_, 0);
v_target_292_ = lean_ctor_get(v_x_268_, 1);
v___x_293_ = 3ULL;
if (lean_obj_tag(v_package_291_) == 0)
{
uint64_t v___x_301_; 
v___x_301_ = 1723ULL;
v___y_295_ = v___x_301_;
goto v___jp_294_;
}
else
{
uint64_t v_hash_302_; 
v_hash_302_ = lean_ctor_get_uint64(v_package_291_, sizeof(void*)*2);
v___y_295_ = v_hash_302_;
goto v___jp_294_;
}
v___jp_294_:
{
uint64_t v___x_296_; 
v___x_296_ = lean_uint64_mix_hash(v___x_293_, v___y_295_);
if (lean_obj_tag(v_target_292_) == 0)
{
uint64_t v___x_297_; uint64_t v___x_298_; 
v___x_297_ = 1723ULL;
v___x_298_ = lean_uint64_mix_hash(v___x_296_, v___x_297_);
return v___x_298_;
}
else
{
uint64_t v_hash_299_; uint64_t v___x_300_; 
v_hash_299_ = lean_ctor_get_uint64(v_target_292_, sizeof(void*)*2);
v___x_300_ = lean_uint64_mix_hash(v___x_296_, v_hash_299_);
return v___x_300_;
}
}
}
default: 
{
lean_object* v_target_303_; lean_object* v_facet_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; 
v_target_303_ = lean_ctor_get(v_x_268_, 0);
v_facet_304_ = lean_ctor_get(v_x_268_, 1);
v___x_305_ = 4ULL;
v___x_306_ = l_Lake_instHashableBuildKey_hash(v_target_303_);
v___x_307_ = lean_uint64_mix_hash(v___x_305_, v___x_306_);
if (lean_obj_tag(v_facet_304_) == 0)
{
uint64_t v___x_308_; uint64_t v___x_309_; 
v___x_308_ = 1723ULL;
v___x_309_ = lean_uint64_mix_hash(v___x_307_, v___x_308_);
return v___x_309_;
}
else
{
uint64_t v_hash_310_; uint64_t v___x_311_; 
v_hash_310_ = lean_ctor_get_uint64(v_facet_304_, sizeof(void*)*2);
v___x_311_ = lean_uint64_mix_hash(v___x_307_, v_hash_310_);
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey_hash___boxed(lean_object* v_x_312_){
_start:
{
uint64_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_Lake_instHashableBuildKey_hash(v_x_312_);
lean_dec_ref(v_x_312_);
v_r_314_ = lean_box_uint64(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object* v_key_317_){
_start:
{
lean_inc_ref(v_key_317_);
return v_key_317_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object* v_key_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lake_PartialBuildKey_mk(v_key_318_);
lean_dec_ref(v_key_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(lean_object* v_x_322_, lean_object* v_prec_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lake_instReprBuildKey_repr(v_x_322_, v_prec_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(lean_object* v_x_325_, lean_object* v_prec_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(v_x_325_, v_prec_326_);
lean_dec(v_prec_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* v_pkg_338_, lean_object* v_target_339_){
_start:
{
lean_object* v_str_340_; lean_object* v_startInclusive_341_; lean_object* v_endExclusive_342_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_str_340_ = lean_ctor_get(v_target_339_, 0);
v_startInclusive_341_ = lean_ctor_get(v_target_339_, 1);
v_endExclusive_342_ = lean_ctor_get(v_target_339_, 2);
v___x_348_ = lean_nat_sub(v_endExclusive_342_, v_startInclusive_341_);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_nat_dec_eq(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_dec_le(v___x_351_, v___x_348_);
lean_dec(v___x_348_);
if (v___x_352_ == 0)
{
goto v___jp_343_;
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_354_ = lean_string_memcmp(v_str_340_, v___x_353_, v_startInclusive_341_, v___x_349_, v___x_351_);
if (v___x_354_ == 0)
{
goto v___jp_343_;
}
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_target_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = l_String_Slice_Pos_nextn(v_target_339_, v___x_349_, v___x_351_);
v___x_356_ = lean_nat_add(v_startInclusive_341_, v___x_355_);
lean_dec(v___x_355_);
v___x_357_ = lean_string_utf8_extract_fast(v_str_340_, v___x_356_, v_endExclusive_342_);
lean_dec(v___x_356_);
v_target_358_ = l_Lake_stringToLegalOrSimpleName(v___x_357_);
v___x_359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_359_, 0, v_pkg_338_);
lean_ctor_set(v___x_359_, 1, v_target_358_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
}
else
{
lean_object* v___x_361_; 
lean_dec(v___x_348_);
lean_dec(v_pkg_338_);
v___x_361_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2));
return v___x_361_;
}
v___jp_343_:
{
lean_object* v___x_344_; lean_object* v_target_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_344_ = lean_string_utf8_extract_fast(v_str_340_, v_startInclusive_341_, v_endExclusive_342_);
v_target_345_ = l_Lake_stringToLegalOrSimpleName(v___x_344_);
v___x_346_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_346_, 0, v_pkg_338_);
lean_ctor_set(v___x_346_, 1, v_target_345_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* v_pkg_362_, lean_object* v_target_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v_pkg_362_, v_target_363_);
lean_dec_ref(v_target_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg(){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___boxed(lean_object* v___dummy_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
return v_res_370_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(lean_object* v_s_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(lean_object* v_s_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_374_);
lean_dec_ref(v_s_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(lean_object* v_s_376_, lean_object* v___x_377_, lean_object* v___x_378_, lean_object* v_a_379_, lean_object* v_b_380_){
_start:
{
lean_object* v_it_382_; lean_object* v_startInclusive_383_; lean_object* v_endExclusive_384_; 
if (lean_obj_tag(v_a_379_) == 0)
{
lean_object* v_currPos_388_; lean_object* v_searcher_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_412_; 
v_currPos_388_ = lean_ctor_get(v_a_379_, 0);
v_searcher_389_ = lean_ctor_get(v_a_379_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_a_379_);
if (v_isSharedCheck_412_ == 0)
{
v___x_391_ = v_a_379_;
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_searcher_389_);
lean_inc(v_currPos_388_);
lean_dec(v_a_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_412_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint8_t v_decide_393_; 
v_decide_393_ = lean_nat_dec_eq(v_searcher_389_, v___x_378_);
if (v_decide_393_ == 0)
{
uint32_t v___x_394_; uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_394_ = 47;
v___x_395_ = lean_string_utf8_get_fast(v_s_376_, v_searcher_389_);
v___x_396_ = lean_uint32_dec_eq(v___x_395_, v___x_394_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_string_utf8_next_fast(v_s_376_, v_searcher_389_);
lean_dec(v_searcher_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_397_);
v___x_399_ = v___x_391_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_currPos_388_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_401_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
v_a_379_ = v___x_399_;
goto _start;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_slice_405_; lean_object* v_nextIt_407_; 
v___x_402_ = lean_string_utf8_next_fast(v_s_376_, v_searcher_389_);
v___x_403_ = lean_nat_sub(v___x_402_, v_searcher_389_);
v___x_404_ = lean_nat_add(v_searcher_389_, v___x_403_);
lean_dec(v___x_403_);
v_slice_405_ = l_String_Slice_subslice_x21(v___x_377_, v_currPos_388_, v_searcher_389_);
lean_inc(v___x_404_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_404_);
lean_ctor_set(v___x_391_, 0, v___x_404_);
v_nextIt_407_ = v___x_391_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_404_);
v_nextIt_407_ = v_reuseFailAlloc_410_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v_startInclusive_408_; lean_object* v_endExclusive_409_; 
v_startInclusive_408_ = lean_ctor_get(v_slice_405_, 0);
lean_inc(v_startInclusive_408_);
v_endExclusive_409_ = lean_ctor_get(v_slice_405_, 1);
lean_inc(v_endExclusive_409_);
lean_dec_ref(v_slice_405_);
v_it_382_ = v_nextIt_407_;
v_startInclusive_383_ = v_startInclusive_408_;
v_endExclusive_384_ = v_endExclusive_409_;
goto v___jp_381_;
}
}
}
else
{
lean_object* v___x_411_; 
lean_del_object(v___x_391_);
lean_dec(v_searcher_389_);
v___x_411_ = lean_box(1);
lean_inc(v___x_378_);
v_it_382_ = v___x_411_;
v_startInclusive_383_ = v_currPos_388_;
v_endExclusive_384_ = v___x_378_;
goto v___jp_381_;
}
}
}
else
{
lean_dec(v___x_378_);
lean_dec_ref(v_s_376_);
return v_b_380_;
}
v___jp_381_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
lean_inc_ref(v_s_376_);
v___x_385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_385_, 0, v_s_376_);
lean_ctor_set(v___x_385_, 1, v_startInclusive_383_);
lean_ctor_set(v___x_385_, 2, v_endExclusive_384_);
v___x_386_ = lean_array_push(v_b_380_, v___x_385_);
v_a_379_ = v_it_382_;
v_b_380_ = v___x_386_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(lean_object* v_s_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_a_416_, lean_object* v_b_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_413_, v___x_414_, v___x_415_, v_a_416_, v_b_417_);
lean_dec_ref(v___x_414_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(lean_object* v_s_430_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_string_utf8_byte_size(v_s_430_);
lean_inc_ref(v_s_430_);
v___x_435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_435_, 0, v_s_430_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_434_);
v___x_436_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0);
v___x_437_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2));
v___x_438_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_430_, v___x_435_, v___x_434_, v___x_436_, v___x_437_);
lean_dec_ref_known(v___x_435_, 3);
v___x_439_ = lean_array_to_list(v___x_438_);
if (lean_obj_tag(v___x_439_) == 1)
{
lean_object* v_head_440_; lean_object* v_tail_441_; 
v_head_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_head_440_);
v_tail_441_ = lean_ctor_get(v___x_439_, 1);
lean_inc(v_tail_441_);
lean_dec_ref_known(v___x_439_, 2);
if (lean_obj_tag(v_tail_441_) == 0)
{
lean_object* v_str_445_; lean_object* v_startInclusive_446_; lean_object* v_endExclusive_447_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_str_445_ = lean_ctor_get(v_head_440_, 0);
v_startInclusive_446_ = lean_ctor_get(v_head_440_, 1);
v_endExclusive_447_ = lean_ctor_get(v_head_440_, 2);
v___x_463_ = lean_nat_sub(v_endExclusive_447_, v_startInclusive_446_);
v___x_464_ = lean_nat_dec_eq(v___x_463_, v___x_433_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_dec_le(v___x_465_, v___x_463_);
lean_dec(v___x_463_);
if (v___x_466_ == 0)
{
goto v___jp_448_;
}
else
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_468_ = lean_string_memcmp(v_str_445_, v___x_467_, v_startInclusive_446_, v___x_433_, v___x_465_);
if (v___x_468_ == 0)
{
goto v___jp_448_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
lean_inc(v_endExclusive_447_);
lean_inc(v_startInclusive_446_);
lean_inc_ref(v_str_445_);
v___x_469_ = l_String_Slice_Pos_nextn(v_head_440_, v___x_433_, v___x_465_);
lean_dec(v_head_440_);
v___x_470_ = lean_nat_add(v_startInclusive_446_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v_startInclusive_446_);
v___x_471_ = lean_nat_sub(v_endExclusive_447_, v___x_470_);
v___x_472_ = lean_nat_dec_eq(v___x_471_, v___x_433_);
lean_dec(v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_473_ = lean_string_utf8_extract_fast(v_str_445_, v___x_470_, v_endExclusive_447_);
lean_dec(v_endExclusive_447_);
lean_dec(v___x_470_);
lean_dec_ref(v_str_445_);
v___x_474_ = l_Lake_stringToLegalOrSimpleName(v___x_473_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v___x_470_);
lean_dec(v_endExclusive_447_);
lean_dec_ref(v_str_445_);
v___x_477_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
return v___x_477_;
}
}
}
}
else
{
lean_object* v___x_478_; 
lean_dec(v___x_463_);
lean_dec(v_head_440_);
v___x_478_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6));
return v___x_478_;
}
v___jp_448_:
{
lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_sub(v_endExclusive_447_, v_startInclusive_446_);
v___x_451_ = lean_nat_dec_le(v___x_449_, v___x_450_);
lean_dec(v___x_450_);
if (v___x_451_ == 0)
{
goto v___jp_442_;
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_453_ = lean_string_memcmp(v_str_445_, v___x_452_, v_startInclusive_446_, v___x_433_, v___x_449_);
if (v___x_453_ == 0)
{
goto v___jp_442_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
lean_inc(v_endExclusive_447_);
lean_inc(v_startInclusive_446_);
lean_inc_ref(v_str_445_);
v___x_454_ = l_String_Slice_Pos_nextn(v_head_440_, v___x_433_, v___x_449_);
lean_dec(v_head_440_);
v___x_455_ = lean_nat_add(v_startInclusive_446_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v_startInclusive_446_);
v___x_456_ = lean_nat_sub(v_endExclusive_447_, v___x_455_);
v___x_457_ = lean_nat_dec_eq(v___x_456_, v___x_433_);
lean_dec(v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_458_ = lean_string_utf8_extract_fast(v_str_445_, v___x_455_, v_endExclusive_447_);
lean_dec(v_endExclusive_447_);
lean_dec(v___x_455_);
lean_dec_ref(v_str_445_);
v___x_459_ = l_Lake_stringToLegalOrSimpleName(v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; 
lean_dec(v___x_455_);
lean_dec(v_endExclusive_447_);
lean_dec_ref(v_str_445_);
v___x_462_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4));
return v___x_462_;
}
}
}
}
}
else
{
lean_object* v_head_479_; lean_object* v_tail_480_; lean_object* v_str_482_; lean_object* v_startInclusive_483_; lean_object* v_endExclusive_484_; 
v_head_479_ = lean_ctor_get(v_tail_441_, 0);
lean_inc(v_head_479_);
v_tail_480_ = lean_ctor_get(v_tail_441_, 1);
lean_inc(v_tail_480_);
lean_dec_ref_known(v_tail_441_, 2);
if (lean_obj_tag(v_tail_480_) == 0)
{
lean_object* v_str_492_; lean_object* v_startInclusive_493_; lean_object* v_endExclusive_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_str_492_ = lean_ctor_get(v_head_440_, 0);
lean_inc_ref(v_str_492_);
v_startInclusive_493_ = lean_ctor_get(v_head_440_, 1);
lean_inc(v_startInclusive_493_);
v_endExclusive_494_ = lean_ctor_get(v_head_440_, 2);
lean_inc(v_endExclusive_494_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_sub(v_endExclusive_494_, v_startInclusive_493_);
v___x_497_ = lean_nat_dec_le(v___x_495_, v___x_496_);
lean_dec(v___x_496_);
if (v___x_497_ == 0)
{
lean_dec(v_head_440_);
v_str_482_ = v_str_492_;
v_startInclusive_483_ = v_startInclusive_493_;
v_endExclusive_484_ = v_endExclusive_494_;
goto v___jp_481_;
}
else
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_499_ = lean_string_memcmp(v_str_492_, v___x_498_, v_startInclusive_493_, v___x_433_, v___x_495_);
if (v___x_499_ == 0)
{
lean_dec(v_head_440_);
v_str_482_ = v_str_492_;
v_startInclusive_483_ = v_startInclusive_493_;
v_endExclusive_484_ = v_endExclusive_494_;
goto v___jp_481_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = l_String_Slice_Pos_nextn(v_head_440_, v___x_433_, v___x_495_);
lean_dec(v_head_440_);
v___x_501_ = lean_nat_add(v_startInclusive_493_, v___x_500_);
lean_dec(v___x_500_);
lean_dec(v_startInclusive_493_);
v_str_482_ = v_str_492_;
v_startInclusive_483_ = v___x_501_;
v_endExclusive_484_ = v_endExclusive_494_;
goto v___jp_481_;
}
}
}
else
{
lean_dec(v_tail_480_);
lean_dec(v_head_479_);
lean_dec(v_head_440_);
goto v___jp_431_;
}
v___jp_481_:
{
lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_485_ = lean_nat_sub(v_endExclusive_484_, v_startInclusive_483_);
v___x_486_ = lean_nat_dec_eq(v___x_485_, v___x_433_);
lean_dec(v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_string_utf8_extract_fast(v_str_482_, v_startInclusive_483_, v_endExclusive_484_);
lean_dec(v_endExclusive_484_);
lean_dec(v_startInclusive_483_);
lean_dec_ref(v_str_482_);
v___x_488_ = l_Lake_stringToLegalOrSimpleName(v___x_487_);
v___x_489_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_488_, v_head_479_);
lean_dec(v_head_479_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_endExclusive_484_);
lean_dec(v_startInclusive_483_);
lean_dec_ref(v_str_482_);
v___x_490_ = lean_box(0);
v___x_491_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_490_, v_head_479_);
lean_dec(v_head_479_);
return v___x_491_;
}
}
}
v___jp_442_:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_box(0);
v___x_444_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v___x_443_, v_head_440_);
lean_dec(v_head_440_);
return v___x_444_;
}
}
else
{
lean_dec(v___x_439_);
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1));
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(lean_object* v_s_502_, lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v_inst_505_, lean_object* v_R_506_, lean_object* v_a_507_, lean_object* v_b_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_502_, v___x_503_, v___x_504_, v_a_507_, v_b_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(lean_object* v_s_510_, lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v_inst_513_, lean_object* v_R_514_, lean_object* v_a_515_, lean_object* v_b_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_510_, v___x_511_, v___x_512_, v_inst_513_, v_R_514_, v_a_515_, v_b_516_);
lean_dec_ref(v___x_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg___boxed(lean_object* v___dummy_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v_res_521_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_525_);
lean_dec_ref(v_s_525_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___x_531_ = lean_panic_fn_borrowed(v___x_530_, v_msg_528_);
lean_dec_ref_known(v___x_530_, 1);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_it_538_; lean_object* v_startInclusive_539_; lean_object* v_endExclusive_540_; 
if (lean_obj_tag(v_a_535_) == 0)
{
lean_object* v_currPos_545_; lean_object* v_searcher_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_569_; 
v_currPos_545_ = lean_ctor_get(v_a_535_, 0);
v_searcher_546_ = lean_ctor_get(v_a_535_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_a_535_);
if (v_isSharedCheck_569_ == 0)
{
v___x_548_ = v_a_535_;
v_isShared_549_ = v_isSharedCheck_569_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_searcher_546_);
lean_inc(v_currPos_545_);
lean_dec(v_a_535_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_569_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint8_t v_decide_550_; 
v_decide_550_ = lean_nat_dec_eq(v_searcher_546_, v___x_534_);
if (v_decide_550_ == 0)
{
uint32_t v___x_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v___x_551_ = 58;
v___x_552_ = lean_string_utf8_get_fast(v_s_532_, v_searcher_546_);
v___x_553_ = lean_uint32_dec_eq(v___x_552_, v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = lean_string_utf8_next_fast(v_s_532_, v_searcher_546_);
lean_dec(v_searcher_546_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_554_);
v___x_556_ = v___x_548_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_currPos_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_554_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
v_a_535_ = v___x_556_;
goto _start;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v_slice_562_; lean_object* v_nextIt_564_; 
v___x_559_ = lean_string_utf8_next_fast(v_s_532_, v_searcher_546_);
v___x_560_ = lean_nat_sub(v___x_559_, v_searcher_546_);
v___x_561_ = lean_nat_add(v_searcher_546_, v___x_560_);
lean_dec(v___x_560_);
v_slice_562_ = l_String_Slice_subslice_x21(v___x_533_, v_currPos_545_, v_searcher_546_);
lean_inc(v___x_561_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 1, v___x_561_);
lean_ctor_set(v___x_548_, 0, v___x_561_);
v_nextIt_564_ = v___x_548_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_561_);
v_nextIt_564_ = v_reuseFailAlloc_567_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v_startInclusive_565_; lean_object* v_endExclusive_566_; 
v_startInclusive_565_ = lean_ctor_get(v_slice_562_, 0);
lean_inc(v_startInclusive_565_);
v_endExclusive_566_ = lean_ctor_get(v_slice_562_, 1);
lean_inc(v_endExclusive_566_);
lean_dec_ref(v_slice_562_);
v_it_538_ = v_nextIt_564_;
v_startInclusive_539_ = v_startInclusive_565_;
v_endExclusive_540_ = v_endExclusive_566_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v___x_568_; 
lean_del_object(v___x_548_);
lean_dec(v_searcher_546_);
v___x_568_ = lean_box(1);
lean_inc(v___x_534_);
v_it_538_ = v___x_568_;
v_startInclusive_539_ = v_currPos_545_;
v_endExclusive_540_ = v___x_534_;
goto v___jp_537_;
}
}
}
else
{
lean_dec(v___x_534_);
lean_dec_ref(v_s_532_);
return v_b_536_;
}
v___jp_537_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc_ref(v_s_532_);
v___x_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_541_, 0, v_s_532_);
lean_ctor_set(v___x_541_, 1, v_startInclusive_539_);
lean_ctor_set(v___x_541_, 2, v_endExclusive_540_);
v___x_542_ = l_String_Slice_toString(v___x_541_);
lean_dec_ref_known(v___x_541_, 3);
v___x_543_ = lean_array_push(v_b_536_, v___x_542_);
v_a_535_ = v_it_538_;
v_b_536_ = v___x_543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v_a_573_, lean_object* v_b_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_570_, v___x_571_, v___x_572_, v_a_573_, v_b_574_);
lean_dec_ref(v___x_571_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v_x_579_);
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v_tail_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_596_; 
v_head_582_ = lean_ctor_get(v_x_580_, 0);
v_tail_583_ = lean_ctor_get(v_x_580_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_596_ == 0)
{
v___x_585_ = v_x_580_;
v_isShared_586_ = v_isSharedCheck_596_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_tail_583_);
lean_inc(v_head_582_);
lean_dec(v_x_580_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_596_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_string_utf8_byte_size(v_head_582_);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_nat_dec_eq(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_590_ = l_Lake_stringToLegalOrSimpleName(v_head_582_);
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 4);
lean_ctor_set(v___x_585_, 1, v___x_590_);
lean_ctor_set(v___x_585_, 0, v_x_579_);
v___x_592_ = v___x_585_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_x_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v_x_579_ = v___x_592_;
v_x_580_ = v_tail_583_;
goto _start;
}
}
else
{
lean_object* v___x_595_; 
lean_del_object(v___x_585_);
lean_dec(v_tail_583_);
lean_dec(v_head_582_);
lean_dec_ref(v_x_579_);
v___x_595_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_595_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_602_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_603_ = lean_unsigned_to_nat(4u);
v___x_604_ = lean_unsigned_to_nat(65u);
v___x_605_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_606_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_607_ = l_mkPanicMessageWithDecl(v___x_606_, v___x_605_, v___x_604_, v___x_603_, v___x_602_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_string_utf8_byte_size(v_s_611_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_inc_ref(v_s_611_);
v___x_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_615_, 0, v_s_611_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
lean_ctor_set(v___x_615_, 2, v___x_612_);
v___x_616_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
v___x_617_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_618_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_611_, v___x_615_, v___x_612_, v___x_616_, v___x_617_);
lean_dec_ref_known(v___x_615_, 3);
v___x_619_ = lean_array_to_list(v___x_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_621_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_624_; 
v_head_622_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_head_622_);
v_tail_623_ = lean_ctor_get(v___x_619_, 1);
lean_inc(v_tail_623_);
lean_dec_ref_known(v___x_619_, 2);
v___x_624_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_622_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec(v_tail_623_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_626_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v___x_626_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_625_, v_tail_623_);
return v___x_626_;
}
}
}
else
{
lean_object* v___x_627_; 
lean_dec_ref(v_s_611_);
v___x_627_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_628_, lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v_inst_631_, lean_object* v_R_632_, lean_object* v_a_633_, lean_object* v_b_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_628_, v___x_629_, v___x_630_, v_a_633_, v_b_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_636_, lean_object* v___x_637_, lean_object* v___x_638_, lean_object* v_inst_639_, lean_object* v_R_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_636_, v___x_637_, v___x_638_, v_inst_639_, v_R_640_, v_a_641_, v_b_642_);
lean_dec_ref(v___x_637_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_644_){
_start:
{
if (lean_obj_tag(v_p_644_) == 2)
{
lean_object* v_pre_645_; 
v_pre_645_ = lean_ctor_get(v_p_644_, 0);
lean_inc(v_pre_645_);
return v_pre_645_;
}
else
{
lean_inc(v_p_644_);
return v_p_644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_646_);
lean_dec(v_p_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_651_){
_start:
{
lean_object* v___y_653_; 
switch(lean_obj_tag(v_x_651_))
{
case 0:
{
lean_object* v_module_659_; lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_module_659_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_module_659_);
lean_dec_ref_known(v_x_651_, 1);
v___x_660_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_661_ = 1;
v___x_662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_659_, v___x_661_);
v___x_663_ = lean_string_append(v___x_660_, v___x_662_);
lean_dec_ref(v___x_662_);
return v___x_663_;
}
case 1:
{
lean_object* v_package_664_; 
v_package_664_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_package_664_);
lean_dec_ref_known(v_x_651_, 1);
if (lean_obj_tag(v_package_664_) == 2)
{
lean_object* v_pre_665_; 
v_pre_665_ = lean_ctor_get(v_package_664_, 0);
lean_inc(v_pre_665_);
lean_dec_ref_known(v_package_664_, 2);
v___y_653_ = v_pre_665_;
goto v___jp_652_;
}
else
{
v___y_653_ = v_package_664_;
goto v___jp_652_;
}
}
case 2:
{
lean_object* v_package_666_; lean_object* v_module_667_; lean_object* v___y_669_; 
v_package_666_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_package_666_);
v_module_667_ = lean_ctor_get(v_x_651_, 1);
lean_inc(v_module_667_);
lean_dec_ref_known(v_x_651_, 2);
if (lean_obj_tag(v_package_666_) == 2)
{
lean_object* v_pre_680_; 
v_pre_680_ = lean_ctor_get(v_package_666_, 0);
lean_inc(v_pre_680_);
lean_dec_ref_known(v_package_666_, 2);
v___y_669_ = v_pre_680_;
goto v___jp_668_;
}
else
{
v___y_669_ = v_package_666_;
goto v___jp_668_;
}
v___jp_668_:
{
if (lean_obj_tag(v___y_669_) == 0)
{
lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_671_ = 1;
v___x_672_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_667_, v___x_671_);
v___x_673_ = lean_string_append(v___x_670_, v___x_672_);
lean_dec_ref(v___x_672_);
return v___x_673_;
}
else
{
uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_674_ = 1;
v___x_675_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_669_, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_677_ = lean_string_append(v___x_675_, v___x_676_);
v___x_678_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_667_, v___x_674_);
v___x_679_ = lean_string_append(v___x_677_, v___x_678_);
lean_dec_ref(v___x_678_);
return v___x_679_;
}
}
}
case 3:
{
lean_object* v_package_681_; lean_object* v_target_682_; lean_object* v___y_684_; 
v_package_681_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_package_681_);
v_target_682_ = lean_ctor_get(v_x_651_, 1);
lean_inc(v_target_682_);
lean_dec_ref_known(v_x_651_, 2);
if (lean_obj_tag(v_package_681_) == 2)
{
lean_object* v_pre_693_; 
v_pre_693_ = lean_ctor_get(v_package_681_, 0);
lean_inc(v_pre_693_);
lean_dec_ref_known(v_package_681_, 2);
v___y_684_ = v_pre_693_;
goto v___jp_683_;
}
else
{
v___y_684_ = v_package_681_;
goto v___jp_683_;
}
v___jp_683_:
{
if (lean_obj_tag(v___y_684_) == 0)
{
uint8_t v___x_685_; lean_object* v___x_686_; 
v___x_685_ = 1;
v___x_686_ = l_Lean_Name_toString(v_target_682_, v___x_685_);
return v___x_686_;
}
else
{
uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_687_ = 1;
v___x_688_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_684_, v___x_687_);
v___x_689_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_690_ = lean_string_append(v___x_688_, v___x_689_);
v___x_691_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_682_, v___x_687_);
v___x_692_ = lean_string_append(v___x_690_, v___x_691_);
lean_dec_ref(v___x_691_);
return v___x_692_;
}
}
}
default: 
{
lean_object* v_target_694_; lean_object* v_facet_695_; uint8_t v___x_696_; 
v_target_694_ = lean_ctor_get(v_x_651_, 0);
lean_inc_ref(v_target_694_);
v_facet_695_ = lean_ctor_get(v_x_651_, 1);
lean_inc(v_facet_695_);
lean_dec_ref_known(v_x_651_, 2);
v___x_696_ = l_Lean_Name_isAnonymous(v_facet_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = l_Lake_PartialBuildKey_toString(v_target_694_);
v___x_698_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
v___x_700_ = 1;
v___x_701_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_695_, v___x_700_);
v___x_702_ = lean_string_append(v___x_699_, v___x_701_);
lean_dec_ref(v___x_701_);
return v___x_702_;
}
else
{
lean_dec(v_facet_695_);
v_x_651_ = v_target_694_;
goto _start;
}
}
}
v___jp_652_:
{
if (lean_obj_tag(v___y_653_) == 0)
{
lean_object* v___x_654_; 
v___x_654_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_654_;
}
else
{
lean_object* v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_655_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_656_ = 1;
v___x_657_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_653_, v___x_656_);
v___x_658_ = lean_string_append(v___x_655_, v___x_657_);
lean_dec_ref(v___x_657_);
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_706_, lean_object* v_facet_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v_module_706_);
v___x_709_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
lean_ctor_set(v___x_709_, 1, v_facet_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_710_, lean_object* v_facet_711_){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v_package_710_);
v___x_713_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v_facet_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_714_, lean_object* v_module_715_, lean_object* v_facet_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_717_, 0, v_package_714_);
lean_ctor_set(v___x_717_, 1, v_module_715_);
v___x_718_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v_facet_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_719_, lean_object* v_target_720_, lean_object* v_facet_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_722_, 0, v_package_719_);
lean_ctor_set(v___x_722_, 1, v_target_720_);
v___x_723_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v_facet_721_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_724_, lean_object* v_target_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_726_, 0, v_package_724_);
lean_ctor_set(v___x_726_, 1, v_target_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_727_){
_start:
{
switch(lean_obj_tag(v_x_727_))
{
case 0:
{
lean_object* v_module_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_module_728_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_module_728_);
lean_dec_ref_known(v_x_727_, 1);
v___x_729_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_730_ = 1;
v___x_731_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_728_, v___x_730_);
v___x_732_ = lean_string_append(v___x_729_, v___x_731_);
lean_dec_ref(v___x_731_);
return v___x_732_;
}
case 1:
{
lean_object* v_package_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_package_733_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_package_733_);
lean_dec_ref_known(v_x_727_, 1);
v___x_734_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_735_ = l_Lean_Name_getPrefix(v_package_733_);
lean_dec(v_package_733_);
v___x_736_ = 1;
v___x_737_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_735_, v___x_736_);
v___x_738_ = lean_string_append(v___x_734_, v___x_737_);
lean_dec_ref(v___x_737_);
return v___x_738_;
}
case 2:
{
lean_object* v_package_739_; lean_object* v_module_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_package_739_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_package_739_);
v_module_740_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_module_740_);
lean_dec_ref_known(v_x_727_, 2);
v___x_741_ = l_Lean_Name_getPrefix(v_package_739_);
lean_dec(v_package_739_);
v___x_742_ = 1;
v___x_743_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_741_, v___x_742_);
v___x_744_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_745_ = lean_string_append(v___x_743_, v___x_744_);
v___x_746_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_740_, v___x_742_);
v___x_747_ = lean_string_append(v___x_745_, v___x_746_);
lean_dec_ref(v___x_746_);
return v___x_747_;
}
case 3:
{
lean_object* v_package_748_; lean_object* v_target_749_; lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_package_748_ = lean_ctor_get(v_x_727_, 0);
lean_inc(v_package_748_);
v_target_749_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_target_749_);
lean_dec_ref_known(v_x_727_, 2);
v___x_750_ = l_Lean_Name_getPrefix(v_package_748_);
lean_dec(v_package_748_);
v___x_751_ = 1;
v___x_752_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_750_, v___x_751_);
v___x_753_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_754_ = lean_string_append(v___x_752_, v___x_753_);
v___x_755_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_749_, v___x_751_);
v___x_756_ = lean_string_append(v___x_754_, v___x_755_);
lean_dec_ref(v___x_755_);
return v___x_756_;
}
default: 
{
lean_object* v_target_757_; lean_object* v_facet_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_target_757_ = lean_ctor_get(v_x_727_, 0);
lean_inc_ref(v_target_757_);
v_facet_758_ = lean_ctor_get(v_x_727_, 1);
lean_inc(v_facet_758_);
lean_dec_ref_known(v_x_727_, 2);
v___x_759_ = l_Lake_BuildKey_toString(v_target_757_);
v___x_760_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_761_ = lean_string_append(v___x_759_, v___x_760_);
v___x_762_ = l_Lake_Name_eraseHead(v_facet_758_);
v___x_763_ = 1;
v___x_764_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_762_, v___x_763_);
v___x_765_ = lean_string_append(v___x_761_, v___x_764_);
lean_dec_ref(v___x_764_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_766_){
_start:
{
lean_object* v_p_768_; lean_object* v_m_769_; 
switch(lean_obj_tag(v_x_766_))
{
case 0:
{
lean_object* v_module_777_; uint8_t v___x_778_; lean_object* v___x_779_; 
v_module_777_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_module_777_);
lean_dec_ref_known(v_x_766_, 1);
v___x_778_ = 1;
v___x_779_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_777_, v___x_778_);
return v___x_779_;
}
case 1:
{
lean_object* v_package_780_; lean_object* v___x_781_; uint8_t v___x_782_; lean_object* v___x_783_; 
v_package_780_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_package_780_);
lean_dec_ref_known(v_x_766_, 1);
v___x_781_ = l_Lean_Name_getPrefix(v_package_780_);
lean_dec(v_package_780_);
v___x_782_ = 1;
v___x_783_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_781_, v___x_782_);
return v___x_783_;
}
case 4:
{
lean_object* v_target_784_; lean_object* v_facet_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_target_784_ = lean_ctor_get(v_x_766_, 0);
lean_inc_ref(v_target_784_);
v_facet_785_ = lean_ctor_get(v_x_766_, 1);
lean_inc(v_facet_785_);
lean_dec_ref_known(v_x_766_, 2);
v___x_786_ = l_Lake_BuildKey_toSimpleString(v_target_784_);
v___x_787_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
v___x_789_ = l_Lake_Name_eraseHead(v_facet_785_);
v___x_790_ = 1;
v___x_791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_789_, v___x_790_);
v___x_792_ = lean_string_append(v___x_788_, v___x_791_);
lean_dec_ref(v___x_791_);
return v___x_792_;
}
default: 
{
lean_object* v_package_793_; lean_object* v_module_794_; 
v_package_793_ = lean_ctor_get(v_x_766_, 0);
lean_inc(v_package_793_);
v_module_794_ = lean_ctor_get(v_x_766_, 1);
lean_inc(v_module_794_);
lean_dec_ref(v_x_766_);
v_p_768_ = v_package_793_;
v_m_769_ = v_module_794_;
goto v___jp_767_;
}
}
v___jp_767_:
{
lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_770_ = l_Lean_Name_getPrefix(v_p_768_);
lean_dec(v_p_768_);
v___x_771_ = 1;
v___x_772_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_770_, v___x_771_);
v___x_773_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_774_ = lean_string_append(v___x_772_, v___x_773_);
v___x_775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_769_, v___x_771_);
v___x_776_ = lean_string_append(v___x_774_, v___x_775_);
lean_dec_ref(v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_797_, lean_object* v_k_x27_798_){
_start:
{
switch(lean_obj_tag(v_k_797_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_798_) == 0)
{
lean_object* v_module_799_; lean_object* v_module_800_; uint8_t v___x_801_; 
v_module_799_ = lean_ctor_get(v_k_797_, 0);
v_module_800_ = lean_ctor_get(v_k_x27_798_, 0);
v___x_801_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_799_, v_module_800_);
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = 0;
return v___x_802_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_798_))
{
case 0:
{
uint8_t v___x_803_; 
v___x_803_ = 2;
return v___x_803_;
}
case 1:
{
lean_object* v_package_804_; lean_object* v_package_805_; uint8_t v___x_806_; 
v_package_804_ = lean_ctor_get(v_k_797_, 0);
v_package_805_ = lean_ctor_get(v_k_x27_798_, 0);
v___x_806_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_804_, v_package_805_);
return v___x_806_;
}
default: 
{
uint8_t v___x_807_; 
v___x_807_ = 0;
return v___x_807_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_798_))
{
case 4:
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
case 3:
{
uint8_t v___x_809_; 
v___x_809_ = 0;
return v___x_809_;
}
case 2:
{
lean_object* v_package_810_; lean_object* v_module_811_; lean_object* v_package_812_; lean_object* v_module_813_; uint8_t v___x_814_; 
v_package_810_ = lean_ctor_get(v_k_797_, 0);
v_module_811_ = lean_ctor_get(v_k_797_, 1);
v_package_812_ = lean_ctor_get(v_k_x27_798_, 0);
v_module_813_ = lean_ctor_get(v_k_x27_798_, 1);
v___x_814_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_811_, v_module_813_);
if (v___x_814_ == 1)
{
uint8_t v___x_815_; 
v___x_815_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_810_, v_package_812_);
return v___x_815_;
}
else
{
return v___x_814_;
}
}
default: 
{
uint8_t v___x_816_; 
v___x_816_ = 2;
return v___x_816_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_k_x27_798_))
{
case 4:
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
case 3:
{
lean_object* v_package_818_; lean_object* v_target_819_; lean_object* v_package_820_; lean_object* v_target_821_; uint8_t v___x_822_; 
v_package_818_ = lean_ctor_get(v_k_797_, 0);
v_target_819_ = lean_ctor_get(v_k_797_, 1);
v_package_820_ = lean_ctor_get(v_k_x27_798_, 0);
v_target_821_ = lean_ctor_get(v_k_x27_798_, 1);
v___x_822_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_818_, v_package_820_);
if (v___x_822_ == 1)
{
uint8_t v___x_823_; 
v___x_823_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_819_, v_target_821_);
return v___x_823_;
}
else
{
return v___x_822_;
}
}
default: 
{
uint8_t v___x_824_; 
v___x_824_ = 2;
return v___x_824_;
}
}
}
default: 
{
if (lean_obj_tag(v_k_x27_798_) == 4)
{
lean_object* v_target_825_; lean_object* v_facet_826_; lean_object* v_target_827_; lean_object* v_facet_828_; uint8_t v___x_829_; 
v_target_825_ = lean_ctor_get(v_k_797_, 0);
v_facet_826_ = lean_ctor_get(v_k_797_, 1);
v_target_827_ = lean_ctor_get(v_k_x27_798_, 0);
v_facet_828_ = lean_ctor_get(v_k_x27_798_, 1);
v___x_829_ = l_Lake_BuildKey_quickCmp(v_target_825_, v_target_827_);
if (v___x_829_ == 1)
{
uint8_t v___x_830_; 
v___x_830_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_826_, v_facet_828_);
return v___x_830_;
}
else
{
return v___x_829_;
}
}
else
{
uint8_t v___x_831_; 
v___x_831_ = 2;
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_quickCmp___boxed(lean_object* v_k_832_, lean_object* v_k_x27_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_Lake_BuildKey_quickCmp(v_k_832_, v_k_x27_833_);
lean_dec_ref(v_k_x27_833_);
lean_dec_ref(v_k_832_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(lean_object* v_x_836_, lean_object* v_h__1_837_, lean_object* v_h__2_838_, lean_object* v_h__3_839_, lean_object* v_h__4_840_, lean_object* v_h__5_841_){
_start:
{
switch(lean_obj_tag(v_x_836_))
{
case 0:
{
lean_object* v_module_842_; lean_object* v___x_843_; 
lean_dec(v_h__5_841_);
lean_dec(v_h__4_840_);
lean_dec(v_h__3_839_);
lean_dec(v_h__2_838_);
v_module_842_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_module_842_);
lean_dec_ref_known(v_x_836_, 1);
v___x_843_ = lean_apply_1(v_h__1_837_, v_module_842_);
return v___x_843_;
}
case 1:
{
lean_object* v_package_844_; lean_object* v___x_845_; 
lean_dec(v_h__5_841_);
lean_dec(v_h__4_840_);
lean_dec(v_h__3_839_);
lean_dec(v_h__1_837_);
v_package_844_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_package_844_);
lean_dec_ref_known(v_x_836_, 1);
v___x_845_ = lean_apply_1(v_h__2_838_, v_package_844_);
return v___x_845_;
}
case 2:
{
lean_object* v_package_846_; lean_object* v_module_847_; lean_object* v___x_848_; 
lean_dec(v_h__5_841_);
lean_dec(v_h__4_840_);
lean_dec(v_h__2_838_);
lean_dec(v_h__1_837_);
v_package_846_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_package_846_);
v_module_847_ = lean_ctor_get(v_x_836_, 1);
lean_inc(v_module_847_);
lean_dec_ref_known(v_x_836_, 2);
v___x_848_ = lean_apply_2(v_h__3_839_, v_package_846_, v_module_847_);
return v___x_848_;
}
case 3:
{
lean_object* v_package_849_; lean_object* v_target_850_; lean_object* v___x_851_; 
lean_dec(v_h__5_841_);
lean_dec(v_h__3_839_);
lean_dec(v_h__2_838_);
lean_dec(v_h__1_837_);
v_package_849_ = lean_ctor_get(v_x_836_, 0);
lean_inc(v_package_849_);
v_target_850_ = lean_ctor_get(v_x_836_, 1);
lean_inc(v_target_850_);
lean_dec_ref_known(v_x_836_, 2);
v___x_851_ = lean_apply_2(v_h__4_840_, v_package_849_, v_target_850_);
return v___x_851_;
}
default: 
{
lean_object* v_target_852_; lean_object* v_facet_853_; lean_object* v___x_854_; 
lean_dec(v_h__4_840_);
lean_dec(v_h__3_839_);
lean_dec(v_h__2_838_);
lean_dec(v_h__1_837_);
v_target_852_ = lean_ctor_get(v_x_836_, 0);
lean_inc_ref(v_target_852_);
v_facet_853_ = lean_ctor_get(v_x_836_, 1);
lean_inc(v_facet_853_);
lean_dec_ref_known(v_x_836_, 2);
v___x_854_ = lean_apply_2(v_h__5_841_, v_target_852_, v_facet_853_);
return v___x_854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_855_, lean_object* v_x_856_, lean_object* v_h__1_857_, lean_object* v_h__2_858_, lean_object* v_h__3_859_, lean_object* v_h__4_860_, lean_object* v_h__5_861_){
_start:
{
switch(lean_obj_tag(v_x_856_))
{
case 0:
{
lean_object* v_module_862_; lean_object* v___x_863_; 
lean_dec(v_h__5_861_);
lean_dec(v_h__4_860_);
lean_dec(v_h__3_859_);
lean_dec(v_h__2_858_);
v_module_862_ = lean_ctor_get(v_x_856_, 0);
lean_inc(v_module_862_);
lean_dec_ref_known(v_x_856_, 1);
v___x_863_ = lean_apply_1(v_h__1_857_, v_module_862_);
return v___x_863_;
}
case 1:
{
lean_object* v_package_864_; lean_object* v___x_865_; 
lean_dec(v_h__5_861_);
lean_dec(v_h__4_860_);
lean_dec(v_h__3_859_);
lean_dec(v_h__1_857_);
v_package_864_ = lean_ctor_get(v_x_856_, 0);
lean_inc(v_package_864_);
lean_dec_ref_known(v_x_856_, 1);
v___x_865_ = lean_apply_1(v_h__2_858_, v_package_864_);
return v___x_865_;
}
case 2:
{
lean_object* v_package_866_; lean_object* v_module_867_; lean_object* v___x_868_; 
lean_dec(v_h__5_861_);
lean_dec(v_h__4_860_);
lean_dec(v_h__2_858_);
lean_dec(v_h__1_857_);
v_package_866_ = lean_ctor_get(v_x_856_, 0);
lean_inc(v_package_866_);
v_module_867_ = lean_ctor_get(v_x_856_, 1);
lean_inc(v_module_867_);
lean_dec_ref_known(v_x_856_, 2);
v___x_868_ = lean_apply_2(v_h__3_859_, v_package_866_, v_module_867_);
return v___x_868_;
}
case 3:
{
lean_object* v_package_869_; lean_object* v_target_870_; lean_object* v___x_871_; 
lean_dec(v_h__5_861_);
lean_dec(v_h__3_859_);
lean_dec(v_h__2_858_);
lean_dec(v_h__1_857_);
v_package_869_ = lean_ctor_get(v_x_856_, 0);
lean_inc(v_package_869_);
v_target_870_ = lean_ctor_get(v_x_856_, 1);
lean_inc(v_target_870_);
lean_dec_ref_known(v_x_856_, 2);
v___x_871_ = lean_apply_2(v_h__4_860_, v_package_869_, v_target_870_);
return v___x_871_;
}
default: 
{
lean_object* v_target_872_; lean_object* v_facet_873_; lean_object* v___x_874_; 
lean_dec(v_h__4_860_);
lean_dec(v_h__3_859_);
lean_dec(v_h__2_858_);
lean_dec(v_h__1_857_);
v_target_872_ = lean_ctor_get(v_x_856_, 0);
lean_inc_ref(v_target_872_);
v_facet_873_ = lean_ctor_get(v_x_856_, 1);
lean_inc(v_facet_873_);
lean_dec_ref_known(v_x_856_, 2);
v___x_874_ = lean_apply_2(v_h__5_861_, v_target_872_, v_facet_873_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_875_, lean_object* v_h__1_876_, lean_object* v_h__2_877_){
_start:
{
if (lean_obj_tag(v_k_x27_875_) == 0)
{
lean_object* v_module_878_; lean_object* v___x_879_; 
lean_dec(v_h__2_877_);
v_module_878_ = lean_ctor_get(v_k_x27_875_, 0);
lean_inc(v_module_878_);
lean_dec_ref_known(v_k_x27_875_, 1);
v___x_879_ = lean_apply_1(v_h__1_876_, v_module_878_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; 
lean_dec(v_h__1_876_);
v___x_880_ = lean_apply_2(v_h__2_877_, v_k_x27_875_, lean_box(0));
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_881_, lean_object* v_k_x27_882_, lean_object* v_h__1_883_, lean_object* v_h__2_884_){
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_888_, lean_object* v_h__1_889_, lean_object* v_h__2_890_, lean_object* v_h__3_891_){
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
lean_dec_ref_known(v_k_x27_888_, 1);
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
lean_dec_ref_known(v_k_x27_888_, 1);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_897_, lean_object* v_k_x27_898_, lean_object* v_h__1_899_, lean_object* v_h__2_900_, lean_object* v_h__3_901_){
_start:
{
switch(lean_obj_tag(v_k_x27_898_))
{
case 0:
{
lean_object* v_module_902_; lean_object* v___x_903_; 
lean_dec(v_h__3_901_);
lean_dec(v_h__2_900_);
v_module_902_ = lean_ctor_get(v_k_x27_898_, 0);
lean_inc(v_module_902_);
lean_dec_ref_known(v_k_x27_898_, 1);
v___x_903_ = lean_apply_1(v_h__1_899_, v_module_902_);
return v___x_903_;
}
case 1:
{
lean_object* v_package_904_; lean_object* v___x_905_; 
lean_dec(v_h__3_901_);
lean_dec(v_h__1_899_);
v_package_904_ = lean_ctor_get(v_k_x27_898_, 0);
lean_inc(v_package_904_);
lean_dec_ref_known(v_k_x27_898_, 1);
v___x_905_ = lean_apply_1(v_h__2_900_, v_package_904_);
return v___x_905_;
}
default: 
{
lean_object* v___x_906_; 
lean_dec(v_h__2_900_);
lean_dec(v_h__1_899_);
v___x_906_ = lean_apply_3(v_h__3_901_, v_k_x27_898_, lean_box(0), lean_box(0));
return v___x_906_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_907_, lean_object* v_h__1_908_, lean_object* v_h__2_909_, lean_object* v_h__3_910_, lean_object* v_h__4_911_){
_start:
{
switch(lean_obj_tag(v_k_x27_907_))
{
case 4:
{
lean_object* v_target_912_; lean_object* v_facet_913_; lean_object* v___x_914_; 
lean_dec(v_h__4_911_);
lean_dec(v_h__3_910_);
lean_dec(v_h__2_909_);
v_target_912_ = lean_ctor_get(v_k_x27_907_, 0);
lean_inc_ref(v_target_912_);
v_facet_913_ = lean_ctor_get(v_k_x27_907_, 1);
lean_inc(v_facet_913_);
lean_dec_ref_known(v_k_x27_907_, 2);
v___x_914_ = lean_apply_2(v_h__1_908_, v_target_912_, v_facet_913_);
return v___x_914_;
}
case 3:
{
lean_object* v_package_915_; lean_object* v_target_916_; lean_object* v___x_917_; 
lean_dec(v_h__4_911_);
lean_dec(v_h__3_910_);
lean_dec(v_h__1_908_);
v_package_915_ = lean_ctor_get(v_k_x27_907_, 0);
lean_inc(v_package_915_);
v_target_916_ = lean_ctor_get(v_k_x27_907_, 1);
lean_inc(v_target_916_);
lean_dec_ref_known(v_k_x27_907_, 2);
v___x_917_ = lean_apply_2(v_h__2_909_, v_package_915_, v_target_916_);
return v___x_917_;
}
case 2:
{
lean_object* v_package_918_; lean_object* v_module_919_; lean_object* v___x_920_; 
lean_dec(v_h__4_911_);
lean_dec(v_h__2_909_);
lean_dec(v_h__1_908_);
v_package_918_ = lean_ctor_get(v_k_x27_907_, 0);
lean_inc(v_package_918_);
v_module_919_ = lean_ctor_get(v_k_x27_907_, 1);
lean_inc(v_module_919_);
lean_dec_ref_known(v_k_x27_907_, 2);
v___x_920_ = lean_apply_2(v_h__3_910_, v_package_918_, v_module_919_);
return v___x_920_;
}
default: 
{
lean_object* v___x_921_; 
lean_dec(v_h__3_910_);
lean_dec(v_h__2_909_);
lean_dec(v_h__1_908_);
v___x_921_ = lean_apply_4(v_h__4_911_, v_k_x27_907_, lean_box(0), lean_box(0), lean_box(0));
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_922_, lean_object* v_k_x27_923_, lean_object* v_h__1_924_, lean_object* v_h__2_925_, lean_object* v_h__3_926_, lean_object* v_h__4_927_){
_start:
{
switch(lean_obj_tag(v_k_x27_923_))
{
case 4:
{
lean_object* v_target_928_; lean_object* v_facet_929_; lean_object* v___x_930_; 
lean_dec(v_h__4_927_);
lean_dec(v_h__3_926_);
lean_dec(v_h__2_925_);
v_target_928_ = lean_ctor_get(v_k_x27_923_, 0);
lean_inc_ref(v_target_928_);
v_facet_929_ = lean_ctor_get(v_k_x27_923_, 1);
lean_inc(v_facet_929_);
lean_dec_ref_known(v_k_x27_923_, 2);
v___x_930_ = lean_apply_2(v_h__1_924_, v_target_928_, v_facet_929_);
return v___x_930_;
}
case 3:
{
lean_object* v_package_931_; lean_object* v_target_932_; lean_object* v___x_933_; 
lean_dec(v_h__4_927_);
lean_dec(v_h__3_926_);
lean_dec(v_h__1_924_);
v_package_931_ = lean_ctor_get(v_k_x27_923_, 0);
lean_inc(v_package_931_);
v_target_932_ = lean_ctor_get(v_k_x27_923_, 1);
lean_inc(v_target_932_);
lean_dec_ref_known(v_k_x27_923_, 2);
v___x_933_ = lean_apply_2(v_h__2_925_, v_package_931_, v_target_932_);
return v___x_933_;
}
case 2:
{
lean_object* v_package_934_; lean_object* v_module_935_; lean_object* v___x_936_; 
lean_dec(v_h__4_927_);
lean_dec(v_h__2_925_);
lean_dec(v_h__1_924_);
v_package_934_ = lean_ctor_get(v_k_x27_923_, 0);
lean_inc(v_package_934_);
v_module_935_ = lean_ctor_get(v_k_x27_923_, 1);
lean_inc(v_module_935_);
lean_dec_ref_known(v_k_x27_923_, 2);
v___x_936_ = lean_apply_2(v_h__3_926_, v_package_934_, v_module_935_);
return v___x_936_;
}
default: 
{
lean_object* v___x_937_; 
lean_dec(v_h__3_926_);
lean_dec(v_h__2_925_);
lean_dec(v_h__1_924_);
v___x_937_ = lean_apply_4(v_h__4_927_, v_k_x27_923_, lean_box(0), lean_box(0), lean_box(0));
return v___x_937_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_938_, lean_object* v_h__1_939_, lean_object* v_h__2_940_){
_start:
{
if (v_x_938_ == 1)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_h__2_940_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_apply_1(v_h__1_939_, v___x_941_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_h__1_939_);
v___x_943_ = lean_box(v_x_938_);
v___x_944_ = lean_apply_2(v_h__2_940_, v___x_943_, lean_box(0));
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_945_, lean_object* v_h__1_946_, lean_object* v_h__2_947_){
_start:
{
uint8_t v_x_13__boxed_948_; lean_object* v_res_949_; 
v_x_13__boxed_948_ = lean_unbox(v_x_945_);
v_res_949_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_13__boxed_948_, v_h__1_946_, v_h__2_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_950_, uint8_t v_x_951_, lean_object* v_h__1_952_, lean_object* v_h__2_953_){
_start:
{
if (v_x_951_ == 1)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_dec(v_h__2_953_);
v___x_954_ = lean_box(0);
v___x_955_ = lean_apply_1(v_h__1_952_, v___x_954_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v_h__1_952_);
v___x_956_ = lean_box(v_x_951_);
v___x_957_ = lean_apply_2(v_h__2_953_, v___x_956_, lean_box(0));
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_958_, lean_object* v_x_959_, lean_object* v_h__1_960_, lean_object* v_h__2_961_){
_start:
{
uint8_t v_x_24__boxed_962_; lean_object* v_res_963_; 
v_x_24__boxed_962_ = lean_unbox(v_x_959_);
v_res_963_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_958_, v_x_24__boxed_962_, v_h__1_960_, v_h__2_961_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_964_, lean_object* v_h__1_965_, lean_object* v_h__2_966_, lean_object* v_h__3_967_){
_start:
{
switch(lean_obj_tag(v_k_x27_964_))
{
case 4:
{
lean_object* v_target_968_; lean_object* v_facet_969_; lean_object* v___x_970_; 
lean_dec(v_h__3_967_);
lean_dec(v_h__2_966_);
v_target_968_ = lean_ctor_get(v_k_x27_964_, 0);
lean_inc_ref(v_target_968_);
v_facet_969_ = lean_ctor_get(v_k_x27_964_, 1);
lean_inc(v_facet_969_);
lean_dec_ref_known(v_k_x27_964_, 2);
v___x_970_ = lean_apply_2(v_h__1_965_, v_target_968_, v_facet_969_);
return v___x_970_;
}
case 3:
{
lean_object* v_package_971_; lean_object* v_target_972_; lean_object* v___x_973_; 
lean_dec(v_h__3_967_);
lean_dec(v_h__1_965_);
v_package_971_ = lean_ctor_get(v_k_x27_964_, 0);
lean_inc(v_package_971_);
v_target_972_ = lean_ctor_get(v_k_x27_964_, 1);
lean_inc(v_target_972_);
lean_dec_ref_known(v_k_x27_964_, 2);
v___x_973_ = lean_apply_2(v_h__2_966_, v_package_971_, v_target_972_);
return v___x_973_;
}
default: 
{
lean_object* v___x_974_; 
lean_dec(v_h__2_966_);
lean_dec(v_h__1_965_);
v___x_974_ = lean_apply_3(v_h__3_967_, v_k_x27_964_, lean_box(0), lean_box(0));
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_975_, lean_object* v_k_x27_976_, lean_object* v_h__1_977_, lean_object* v_h__2_978_, lean_object* v_h__3_979_){
_start:
{
switch(lean_obj_tag(v_k_x27_976_))
{
case 4:
{
lean_object* v_target_980_; lean_object* v_facet_981_; lean_object* v___x_982_; 
lean_dec(v_h__3_979_);
lean_dec(v_h__2_978_);
v_target_980_ = lean_ctor_get(v_k_x27_976_, 0);
lean_inc_ref(v_target_980_);
v_facet_981_ = lean_ctor_get(v_k_x27_976_, 1);
lean_inc(v_facet_981_);
lean_dec_ref_known(v_k_x27_976_, 2);
v___x_982_ = lean_apply_2(v_h__1_977_, v_target_980_, v_facet_981_);
return v___x_982_;
}
case 3:
{
lean_object* v_package_983_; lean_object* v_target_984_; lean_object* v___x_985_; 
lean_dec(v_h__3_979_);
lean_dec(v_h__1_977_);
v_package_983_ = lean_ctor_get(v_k_x27_976_, 0);
lean_inc(v_package_983_);
v_target_984_ = lean_ctor_get(v_k_x27_976_, 1);
lean_inc(v_target_984_);
lean_dec_ref_known(v_k_x27_976_, 2);
v___x_985_ = lean_apply_2(v_h__2_978_, v_package_983_, v_target_984_);
return v___x_985_;
}
default: 
{
lean_object* v___x_986_; 
lean_dec(v_h__2_978_);
lean_dec(v_h__1_977_);
v___x_986_ = lean_apply_3(v_h__3_979_, v_k_x27_976_, lean_box(0), lean_box(0));
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_987_, lean_object* v_h__1_988_, lean_object* v_h__2_989_){
_start:
{
if (lean_obj_tag(v_k_x27_987_) == 4)
{
lean_object* v_target_990_; lean_object* v_facet_991_; lean_object* v___x_992_; 
lean_dec(v_h__2_989_);
v_target_990_ = lean_ctor_get(v_k_x27_987_, 0);
lean_inc_ref(v_target_990_);
v_facet_991_ = lean_ctor_get(v_k_x27_987_, 1);
lean_inc(v_facet_991_);
lean_dec_ref_known(v_k_x27_987_, 2);
v___x_992_ = lean_apply_2(v_h__1_988_, v_target_990_, v_facet_991_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; 
lean_dec(v_h__1_988_);
v___x_993_ = lean_apply_2(v_h__2_989_, v_k_x27_987_, lean_box(0));
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_994_, lean_object* v_k_x27_995_, lean_object* v_h__1_996_, lean_object* v_h__2_997_){
_start:
{
if (lean_obj_tag(v_k_x27_995_) == 4)
{
lean_object* v_target_998_; lean_object* v_facet_999_; lean_object* v___x_1000_; 
lean_dec(v_h__2_997_);
v_target_998_ = lean_ctor_get(v_k_x27_995_, 0);
lean_inc_ref(v_target_998_);
v_facet_999_ = lean_ctor_get(v_k_x27_995_, 1);
lean_inc(v_facet_999_);
lean_dec_ref_known(v_k_x27_995_, 2);
v___x_1000_ = lean_apply_2(v_h__1_996_, v_target_998_, v_facet_999_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; 
lean_dec(v_h__1_996_);
v___x_1001_ = lean_apply_2(v_h__2_997_, v_k_x27_995_, lean_box(0));
return v___x_1001_;
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
