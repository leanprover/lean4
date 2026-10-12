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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_BuildKey_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 2:
{
lean_object* v_package_7_; lean_object* v_module_8_; lean_object* v___x_9_; 
v_package_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_package_7_);
v_module_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_module_8_);
lean_dec_ref_known(v_t_5_, 2);
v___x_9_ = lean_apply_2(v_k_6_, v_package_7_, v_module_8_);
return v___x_9_;
}
case 3:
{
lean_object* v_package_10_; lean_object* v_target_11_; lean_object* v___x_12_; 
v_package_10_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_package_10_);
v_target_11_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_target_11_);
lean_dec_ref_known(v_t_5_, 2);
v___x_12_ = lean_apply_2(v_k_6_, v_package_10_, v_target_11_);
return v___x_12_;
}
case 4:
{
lean_object* v_target_13_; lean_object* v_facet_14_; lean_object* v___x_15_; 
v_target_13_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_target_13_);
v_facet_14_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_facet_14_);
lean_dec_ref_known(v_t_5_, 2);
v___x_15_ = lean_apply_2(v_k_6_, v_target_13_, v_facet_14_);
return v___x_15_;
}
default: 
{
lean_object* v_module_16_; lean_object* v___x_17_; 
v_module_16_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_module_16_);
lean_dec_ref(v_t_5_);
v___x_17_ = lean_apply_1(v_k_6_, v_module_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lake_BuildKey_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_BuildKey_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim___redArg(lean_object* v_t_30_, lean_object* v_module_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lake_BuildKey_ctorElim___redArg(v_t_30_, v_module_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_module_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_module_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lake_BuildKey_ctorElim___redArg(v_t_34_, v_module_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim___redArg(lean_object* v_t_38_, lean_object* v_package_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lake_BuildKey_ctorElim___redArg(v_t_38_, v_package_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_package_elim(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_package_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lake_BuildKey_ctorElim___redArg(v_t_42_, v_package_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim___redArg(lean_object* v_t_46_, lean_object* v_packageModule_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lake_BuildKey_ctorElim___redArg(v_t_46_, v_packageModule_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModule_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_packageModule_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lake_BuildKey_ctorElim___redArg(v_t_50_, v_packageModule_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim___redArg(lean_object* v_t_54_, lean_object* v_packageTarget_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lake_BuildKey_ctorElim___redArg(v_t_54_, v_packageTarget_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageTarget_elim(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_packageTarget_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lake_BuildKey_ctorElim___redArg(v_t_58_, v_packageTarget_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim___redArg(lean_object* v_t_62_, lean_object* v_facet_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lake_BuildKey_ctorElim___redArg(v_t_62_, v_facet_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_facet_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_facet_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lake_BuildKey_ctorElim___redArg(v_t_66_, v_facet_68_);
return v___x_69_;
}
}
static lean_object* _init_l_Lake_instReprBuildKey_repr___closed__3(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lake_instReprBuildKey_repr___closed__4(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_to_int(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr(lean_object* v_x_108_, lean_object* v_prec_109_){
_start:
{
switch(lean_obj_tag(v_x_108_))
{
case 0:
{
lean_object* v_module_110_; lean_object* v___y_112_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_module_110_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_module_110_);
lean_dec_ref_known(v_x_108_, 1);
v___x_121_ = lean_unsigned_to_nat(1024u);
v___x_122_ = lean_nat_dec_le(v___x_121_, v_prec_109_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_112_ = v___x_123_;
goto v___jp_111_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_112_ = v___x_124_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_113_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__2));
v___x_114_ = lean_unsigned_to_nat(1024u);
v___x_115_ = l_Lean_Name_reprPrec(v_module_110_, v___x_114_);
v___x_116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_113_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
lean_inc(v___y_112_);
v___x_117_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_117_, 0, v___y_112_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = 0;
v___x_119_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_119_, 0, v___x_117_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*1, v___x_118_);
v___x_120_ = l_Repr_addAppParen(v___x_119_, v_prec_109_);
return v___x_120_;
}
}
case 1:
{
lean_object* v_package_125_; lean_object* v___y_127_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_package_125_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_package_125_);
lean_dec_ref_known(v_x_108_, 1);
v___x_136_ = lean_unsigned_to_nat(1024u);
v___x_137_ = lean_nat_dec_le(v___x_136_, v_prec_109_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_127_ = v___x_138_;
goto v___jp_126_;
}
else
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_127_ = v___x_139_;
goto v___jp_126_;
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_128_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__7));
v___x_129_ = lean_unsigned_to_nat(1024u);
v___x_130_ = l_Lean_Name_reprPrec(v_package_125_, v___x_129_);
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_128_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
lean_inc(v___y_127_);
v___x_132_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_132_, 0, v___y_127_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = 0;
v___x_134_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set_uint8(v___x_134_, sizeof(void*)*1, v___x_133_);
v___x_135_ = l_Repr_addAppParen(v___x_134_, v_prec_109_);
return v___x_135_;
}
}
case 2:
{
lean_object* v_package_140_; lean_object* v_module_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_165_; 
v_package_140_ = lean_ctor_get(v_x_108_, 0);
v_module_141_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_165_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_165_ == 0)
{
v___x_143_ = v_x_108_;
v_isShared_144_ = v_isSharedCheck_165_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_module_141_);
lean_inc(v_package_140_);
lean_dec(v_x_108_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_165_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___y_146_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_unsigned_to_nat(1024u);
v___x_162_ = lean_nat_dec_le(v___x_161_, v_prec_109_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_146_ = v___x_163_;
goto v___jp_145_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_146_ = v___x_164_;
goto v___jp_145_;
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_147_ = lean_box(1);
v___x_148_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__10));
v___x_149_ = lean_unsigned_to_nat(1024u);
v___x_150_ = l_Lean_Name_reprPrec(v_package_140_, v___x_149_);
if (v_isShared_144_ == 0)
{
lean_ctor_set_tag(v___x_143_, 5);
lean_ctor_set(v___x_143_, 1, v___x_150_);
lean_ctor_set(v___x_143_, 0, v___x_148_);
v___x_152_ = v___x_143_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v___x_150_);
v___x_152_ = v_reuseFailAlloc_160_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_147_);
v___x_154_ = l_Lean_Name_reprPrec(v_module_141_, v___x_149_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
lean_inc(v___y_146_);
v___x_156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_156_, 0, v___y_146_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v___x_157_ = 0;
v___x_158_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_158_, 0, v___x_156_);
lean_ctor_set_uint8(v___x_158_, sizeof(void*)*1, v___x_157_);
v___x_159_ = l_Repr_addAppParen(v___x_158_, v_prec_109_);
return v___x_159_;
}
}
}
}
case 3:
{
lean_object* v_package_166_; lean_object* v_target_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_191_; 
v_package_166_ = lean_ctor_get(v_x_108_, 0);
v_target_167_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_191_ == 0)
{
v___x_169_ = v_x_108_;
v_isShared_170_ = v_isSharedCheck_191_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_target_167_);
lean_inc(v_package_166_);
lean_dec(v_x_108_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_191_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___y_172_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(1024u);
v___x_188_ = lean_nat_dec_le(v___x_187_, v_prec_109_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_172_ = v___x_189_;
goto v___jp_171_;
}
else
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_172_ = v___x_190_;
goto v___jp_171_;
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_173_ = lean_box(1);
v___x_174_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__13));
v___x_175_ = lean_unsigned_to_nat(1024u);
v___x_176_ = l_Lean_Name_reprPrec(v_package_166_, v___x_175_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 5);
lean_ctor_set(v___x_169_, 1, v___x_176_);
lean_ctor_set(v___x_169_, 0, v___x_174_);
v___x_178_ = v___x_169_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_186_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_173_);
v___x_180_ = l_Lean_Name_reprPrec(v_target_167_, v___x_175_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_inc(v___y_172_);
v___x_182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_182_, 0, v___y_172_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = 0;
v___x_184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_183_);
v___x_185_ = l_Repr_addAppParen(v___x_184_, v_prec_109_);
return v___x_185_;
}
}
}
}
default: 
{
lean_object* v_target_192_; lean_object* v_facet_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_216_; 
v_target_192_ = lean_ctor_get(v_x_108_, 0);
v_facet_193_ = lean_ctor_get(v_x_108_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_216_ == 0)
{
v___x_195_ = v_x_108_;
v_isShared_196_ = v_isSharedCheck_216_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_facet_193_);
lean_inc(v_target_192_);
lean_dec(v_x_108_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_216_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___y_199_; uint8_t v___x_213_; 
v___x_197_ = lean_unsigned_to_nat(1024u);
v___x_213_ = lean_nat_dec_le(v___x_197_, v_prec_109_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__3, &l_Lake_instReprBuildKey_repr___closed__3_once, _init_l_Lake_instReprBuildKey_repr___closed__3);
v___y_199_ = v___x_214_;
goto v___jp_198_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lake_instReprBuildKey_repr___closed__4, &l_Lake_instReprBuildKey_repr___closed__4_once, _init_l_Lake_instReprBuildKey_repr___closed__4);
v___y_199_ = v___x_215_;
goto v___jp_198_;
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_200_ = lean_box(1);
v___x_201_ = ((lean_object*)(l_Lake_instReprBuildKey_repr___closed__16));
v___x_202_ = l_Lake_instReprBuildKey_repr(v_target_192_, v___x_197_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 5);
lean_ctor_set(v___x_195_, 1, v___x_202_);
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_204_ = v___x_195_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_212_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_200_);
v___x_206_ = l_Lean_Name_reprPrec(v_facet_193_, v___x_197_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_inc(v___y_199_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_199_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_109_);
return v___x_211_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildKey_repr___boxed(lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_instReprBuildKey_repr(v_x_217_, v_prec_218_);
lean_dec(v_prec_218_);
return v_res_219_;
}
}
uint8_t l_Lake_instDecidableEqBuildKey_decEq(lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
switch(lean_obj_tag(v_x_222_))
{
case 0:
{
if (lean_obj_tag(v_x_223_) == 0)
{
lean_object* v_module_224_; lean_object* v_module_225_; uint8_t v___x_226_; 
v_module_224_ = lean_ctor_get(v_x_222_, 0);
v_module_225_ = lean_ctor_get(v_x_223_, 0);
v___x_226_ = lean_name_eq(v_module_224_, v_module_225_);
return v___x_226_;
}
else
{
uint8_t v___x_227_; 
v___x_227_ = 0;
return v___x_227_;
}
}
case 1:
{
if (lean_obj_tag(v_x_223_) == 1)
{
lean_object* v_package_228_; lean_object* v_package_229_; uint8_t v___x_230_; 
v_package_228_ = lean_ctor_get(v_x_222_, 0);
v_package_229_ = lean_ctor_get(v_x_223_, 0);
v___x_230_ = lean_name_eq(v_package_228_, v_package_229_);
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
v___x_231_ = 0;
return v___x_231_;
}
}
case 2:
{
if (lean_obj_tag(v_x_223_) == 2)
{
lean_object* v_package_232_; lean_object* v_module_233_; lean_object* v_package_234_; lean_object* v_module_235_; uint8_t v___x_236_; 
v_package_232_ = lean_ctor_get(v_x_222_, 0);
v_module_233_ = lean_ctor_get(v_x_222_, 1);
v_package_234_ = lean_ctor_get(v_x_223_, 0);
v_module_235_ = lean_ctor_get(v_x_223_, 1);
v___x_236_ = lean_name_eq(v_package_232_, v_package_234_);
if (v___x_236_ == 0)
{
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = lean_name_eq(v_module_233_, v_module_235_);
return v___x_237_;
}
}
else
{
uint8_t v___x_238_; 
v___x_238_ = 0;
return v___x_238_;
}
}
case 3:
{
if (lean_obj_tag(v_x_223_) == 3)
{
lean_object* v_package_239_; lean_object* v_target_240_; lean_object* v_package_241_; lean_object* v_target_242_; uint8_t v___x_243_; 
v_package_239_ = lean_ctor_get(v_x_222_, 0);
v_target_240_ = lean_ctor_get(v_x_222_, 1);
v_package_241_ = lean_ctor_get(v_x_223_, 0);
v_target_242_ = lean_ctor_get(v_x_223_, 1);
v___x_243_ = lean_name_eq(v_package_239_, v_package_241_);
if (v___x_243_ == 0)
{
return v___x_243_;
}
else
{
uint8_t v___x_244_; 
v___x_244_ = lean_name_eq(v_target_240_, v_target_242_);
return v___x_244_;
}
}
else
{
uint8_t v___x_245_; 
v___x_245_ = 0;
return v___x_245_;
}
}
default: 
{
if (lean_obj_tag(v_x_223_) == 4)
{
lean_object* v_target_246_; lean_object* v_facet_247_; lean_object* v_target_248_; lean_object* v_facet_249_; uint8_t v_inst_250_; 
v_target_246_ = lean_ctor_get(v_x_222_, 0);
v_facet_247_ = lean_ctor_get(v_x_222_, 1);
v_target_248_ = lean_ctor_get(v_x_223_, 0);
v_facet_249_ = lean_ctor_get(v_x_223_, 1);
v_inst_250_ = l_Lake_instDecidableEqBuildKey_decEq(v_target_246_, v_target_248_);
if (v_inst_250_ == 0)
{
return v_inst_250_;
}
else
{
uint8_t v___x_251_; 
v___x_251_ = lean_name_eq(v_facet_247_, v_facet_249_);
return v___x_251_;
}
}
else
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instDecidableEqBuildKey_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_222_ = stack[0].m_obj;
lean_object* v_x_223_ = stack[1].m_obj;
uint8_t v_res_253_;
v_res_253_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_222_, v_x_223_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey_decEq___boxed(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_254_, v_x_255_);
lean_dec_ref(v_x_255_);
lean_dec_ref(v_x_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
uint8_t l_Lake_instDecidableEqBuildKey(lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
uint8_t v___x_260_; 
v___x_260_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_258_, v_x_259_);
return v___x_260_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqBuildKey_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_258_ = stack[0].m_obj;
lean_object* v_x_259_ = stack[1].m_obj;
uint8_t v_res_261_;
v_res_261_ = l_Lake_instDecidableEqBuildKey(v_x_258_, v_x_259_);
stack->m_num = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildKey___boxed(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Lake_instDecidableEqBuildKey(v_x_262_, v_x_263_);
lean_dec_ref(v_x_263_);
lean_dec_ref(v_x_262_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
uint64_t l_Lake_instHashableBuildKey_hash(lean_object* v_x_266_){
_start:
{
switch(lean_obj_tag(v_x_266_))
{
case 0:
{
lean_object* v_module_267_; uint64_t v___x_268_; 
v_module_267_ = lean_ctor_get(v_x_266_, 0);
v___x_268_ = 0ULL;
if (lean_obj_tag(v_module_267_) == 0)
{
uint64_t v___x_269_; 
v___x_269_ = 8934034000889494153ULL;
return v___x_269_;
}
else
{
uint64_t v_hash_270_; uint64_t v___x_271_; 
v_hash_270_ = lean_ctor_get_uint64(v_module_267_, sizeof(void*)*2);
v___x_271_ = lean_uint64_mix_hash(v___x_268_, v_hash_270_);
return v___x_271_;
}
}
case 1:
{
lean_object* v_package_272_; uint64_t v___x_273_; 
v_package_272_ = lean_ctor_get(v_x_266_, 0);
v___x_273_ = 1ULL;
if (lean_obj_tag(v_package_272_) == 0)
{
uint64_t v___x_274_; 
v___x_274_ = 13067028307566252276ULL;
return v___x_274_;
}
else
{
uint64_t v_hash_275_; uint64_t v___x_276_; 
v_hash_275_ = lean_ctor_get_uint64(v_package_272_, sizeof(void*)*2);
v___x_276_ = lean_uint64_mix_hash(v___x_273_, v_hash_275_);
return v___x_276_;
}
}
case 2:
{
lean_object* v_package_277_; lean_object* v_module_278_; uint64_t v___x_279_; uint64_t v___y_281_; 
v_package_277_ = lean_ctor_get(v_x_266_, 0);
v_module_278_ = lean_ctor_get(v_x_266_, 1);
v___x_279_ = 2ULL;
if (lean_obj_tag(v_package_277_) == 0)
{
uint64_t v___x_287_; 
v___x_287_ = 1723ULL;
v___y_281_ = v___x_287_;
goto v___jp_280_;
}
else
{
uint64_t v_hash_288_; 
v_hash_288_ = lean_ctor_get_uint64(v_package_277_, sizeof(void*)*2);
v___y_281_ = v_hash_288_;
goto v___jp_280_;
}
v___jp_280_:
{
uint64_t v___x_282_; 
v___x_282_ = lean_uint64_mix_hash(v___x_279_, v___y_281_);
if (lean_obj_tag(v_module_278_) == 0)
{
uint64_t v___x_283_; uint64_t v___x_284_; 
v___x_283_ = 1723ULL;
v___x_284_ = lean_uint64_mix_hash(v___x_282_, v___x_283_);
return v___x_284_;
}
else
{
uint64_t v_hash_285_; uint64_t v___x_286_; 
v_hash_285_ = lean_ctor_get_uint64(v_module_278_, sizeof(void*)*2);
v___x_286_ = lean_uint64_mix_hash(v___x_282_, v_hash_285_);
return v___x_286_;
}
}
}
case 3:
{
lean_object* v_package_289_; lean_object* v_target_290_; uint64_t v___x_291_; uint64_t v___y_293_; 
v_package_289_ = lean_ctor_get(v_x_266_, 0);
v_target_290_ = lean_ctor_get(v_x_266_, 1);
v___x_291_ = 3ULL;
if (lean_obj_tag(v_package_289_) == 0)
{
uint64_t v___x_299_; 
v___x_299_ = 1723ULL;
v___y_293_ = v___x_299_;
goto v___jp_292_;
}
else
{
uint64_t v_hash_300_; 
v_hash_300_ = lean_ctor_get_uint64(v_package_289_, sizeof(void*)*2);
v___y_293_ = v_hash_300_;
goto v___jp_292_;
}
v___jp_292_:
{
uint64_t v___x_294_; 
v___x_294_ = lean_uint64_mix_hash(v___x_291_, v___y_293_);
if (lean_obj_tag(v_target_290_) == 0)
{
uint64_t v___x_295_; uint64_t v___x_296_; 
v___x_295_ = 1723ULL;
v___x_296_ = lean_uint64_mix_hash(v___x_294_, v___x_295_);
return v___x_296_;
}
else
{
uint64_t v_hash_297_; uint64_t v___x_298_; 
v_hash_297_ = lean_ctor_get_uint64(v_target_290_, sizeof(void*)*2);
v___x_298_ = lean_uint64_mix_hash(v___x_294_, v_hash_297_);
return v___x_298_;
}
}
}
default: 
{
lean_object* v_target_301_; lean_object* v_facet_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; 
v_target_301_ = lean_ctor_get(v_x_266_, 0);
v_facet_302_ = lean_ctor_get(v_x_266_, 1);
v___x_303_ = 4ULL;
v___x_304_ = l_Lake_instHashableBuildKey_hash(v_target_301_);
v___x_305_ = lean_uint64_mix_hash(v___x_303_, v___x_304_);
if (lean_obj_tag(v_facet_302_) == 0)
{
uint64_t v___x_306_; uint64_t v___x_307_; 
v___x_306_ = 1723ULL;
v___x_307_ = lean_uint64_mix_hash(v___x_305_, v___x_306_);
return v___x_307_;
}
else
{
uint64_t v_hash_308_; uint64_t v___x_309_; 
v_hash_308_ = lean_ctor_get_uint64(v_facet_302_, sizeof(void*)*2);
v___x_309_ = lean_uint64_mix_hash(v___x_305_, v_hash_308_);
return v___x_309_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instHashableBuildKey_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_266_ = stack[0].m_obj;
uint64_t v_res_310_;
v_res_310_ = l_Lake_instHashableBuildKey_hash(v_x_266_);
stack->m_num = v_res_310_;
}
LEAN_EXPORT lean_object* l_Lake_instHashableBuildKey_hash___boxed(lean_object* v_x_311_){
_start:
{
uint64_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lake_instHashableBuildKey_hash(v_x_311_);
lean_dec_ref(v_x_311_);
v_r_313_ = lean_box_uint64(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk(lean_object* v_key_316_){
_start:
{
lean_inc_ref(v_key_316_);
return v_key_316_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_mk___boxed(lean_object* v_key_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lake_PartialBuildKey_mk(v_key_317_);
lean_dec_ref(v_key_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(lean_object* v_x_321_, lean_object* v_prec_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lake_instReprBuildKey_repr(v_x_321_, v_prec_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(lean_object* v_x_324_, lean_object* v_prec_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(v_x_324_, v_prec_325_);
lean_dec(v_prec_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(lean_object* v_pkg_337_, lean_object* v_target_338_){
_start:
{
lean_object* v_str_339_; lean_object* v_startInclusive_340_; lean_object* v_endExclusive_341_; lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_str_339_ = lean_ctor_get(v_target_338_, 0);
v_startInclusive_340_ = lean_ctor_get(v_target_338_, 1);
v_endExclusive_341_ = lean_ctor_get(v_target_338_, 2);
v___x_347_ = lean_nat_sub(v_endExclusive_341_, v_startInclusive_340_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_dec_le(v___x_350_, v___x_347_);
lean_dec(v___x_347_);
if (v___x_351_ == 0)
{
goto v___jp_342_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_353_ = lean_string_memcmp(v_str_339_, v___x_352_, v_startInclusive_340_, v___x_348_, v___x_350_);
if (v___x_353_ == 0)
{
goto v___jp_342_;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_target_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_354_ = l_String_Slice_Pos_nextn(v_target_338_, v___x_348_, v___x_350_);
v___x_355_ = lean_nat_add(v_startInclusive_340_, v___x_354_);
lean_dec(v___x_354_);
v___x_356_ = lean_string_utf8_extract_fast(v_str_339_, v___x_355_, v_endExclusive_341_);
lean_dec(v___x_355_);
v_target_357_ = l_Lake_stringToLegalOrSimpleName(v___x_356_);
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v_pkg_337_);
lean_ctor_set(v___x_358_, 1, v_target_357_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
else
{
lean_object* v___x_360_; 
lean_dec(v___x_347_);
lean_dec(v_pkg_337_);
v___x_360_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2));
return v___x_360_;
}
v___jp_342_:
{
lean_object* v___x_343_; lean_object* v_target_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_string_utf8_extract_fast(v_str_339_, v_startInclusive_340_, v_endExclusive_341_);
v_target_344_ = l_Lake_stringToLegalOrSimpleName(v___x_343_);
v___x_345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_345_, 0, v_pkg_337_);
lean_ctor_set(v___x_345_, 1, v_target_344_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(lean_object* v_pkg_361_, lean_object* v_target_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(v_pkg_361_, v_target_362_);
lean_dec_ref(v_target_362_);
return v_res_363_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg(){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_367_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_368_;
v_res_368_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg();
stack->m_obj
 = v_res_368_;
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
lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg(){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___redArg___closed__0));
return v___x_519_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_520_;
v_res_520_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
stack->m_obj
 = v_res_520_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg___boxed(lean_object* v___dummy_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v_res_522_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___redArg();
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(lean_object* v_s_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(lean_object* v_s_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_526_);
lean_dec_ref(v_s_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_PartialBuildKey_parse_spec__2(lean_object* v_msg_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_panic_fn_borrowed(v___x_531_, v_msg_529_);
lean_dec_ref_known(v___x_531_, 1);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(lean_object* v_s_533_, lean_object* v___x_534_, lean_object* v___x_535_, lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
lean_object* v_it_539_; lean_object* v_startInclusive_540_; lean_object* v_endExclusive_541_; 
if (lean_obj_tag(v_a_536_) == 0)
{
lean_object* v_currPos_546_; lean_object* v_searcher_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_570_; 
v_currPos_546_ = lean_ctor_get(v_a_536_, 0);
v_searcher_547_ = lean_ctor_get(v_a_536_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_570_ == 0)
{
v___x_549_ = v_a_536_;
v_isShared_550_ = v_isSharedCheck_570_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_searcher_547_);
lean_inc(v_currPos_546_);
lean_dec(v_a_536_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_570_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v_decide_551_; 
v_decide_551_ = lean_nat_dec_eq(v_searcher_547_, v___x_535_);
if (v_decide_551_ == 0)
{
uint32_t v___x_552_; uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = 58;
v___x_553_ = lean_string_utf8_get_fast(v_s_533_, v_searcher_547_);
v___x_554_ = lean_uint32_dec_eq(v___x_553_, v___x_552_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_string_utf8_next_fast(v_s_533_, v_searcher_547_);
lean_dec(v_searcher_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_555_);
v___x_557_ = v___x_549_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_currPos_546_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_555_);
v___x_557_ = v_reuseFailAlloc_559_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
v_a_536_ = v___x_557_;
goto _start;
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_slice_563_; lean_object* v_nextIt_565_; 
v___x_560_ = lean_string_utf8_next_fast(v_s_533_, v_searcher_547_);
v___x_561_ = lean_nat_sub(v___x_560_, v_searcher_547_);
v___x_562_ = lean_nat_add(v_searcher_547_, v___x_561_);
lean_dec(v___x_561_);
v_slice_563_ = l_String_Slice_subslice_x21(v___x_534_, v_currPos_546_, v_searcher_547_);
lean_inc(v___x_562_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_562_);
lean_ctor_set(v___x_549_, 0, v___x_562_);
v_nextIt_565_ = v___x_549_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_562_);
v_nextIt_565_ = v_reuseFailAlloc_568_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v_startInclusive_566_; lean_object* v_endExclusive_567_; 
v_startInclusive_566_ = lean_ctor_get(v_slice_563_, 0);
lean_inc(v_startInclusive_566_);
v_endExclusive_567_ = lean_ctor_get(v_slice_563_, 1);
lean_inc(v_endExclusive_567_);
lean_dec_ref(v_slice_563_);
v_it_539_ = v_nextIt_565_;
v_startInclusive_540_ = v_startInclusive_566_;
v_endExclusive_541_ = v_endExclusive_567_;
goto v___jp_538_;
}
}
}
else
{
lean_object* v___x_569_; 
lean_del_object(v___x_549_);
lean_dec(v_searcher_547_);
v___x_569_ = lean_box(1);
lean_inc(v___x_535_);
v_it_539_ = v___x_569_;
v_startInclusive_540_ = v_currPos_546_;
v_endExclusive_541_ = v___x_535_;
goto v___jp_538_;
}
}
}
else
{
lean_dec(v___x_535_);
lean_dec_ref(v_s_533_);
return v_b_537_;
}
v___jp_538_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_inc_ref(v_s_533_);
v___x_542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_542_, 0, v_s_533_);
lean_ctor_set(v___x_542_, 1, v_startInclusive_540_);
lean_ctor_set(v___x_542_, 2, v_endExclusive_541_);
v___x_543_ = l_String_Slice_toString(v___x_542_);
lean_dec_ref_known(v___x_542_, 3);
v___x_544_ = lean_array_push(v_b_537_, v___x_543_);
v_a_536_ = v_it_539_;
v_b_537_ = v___x_544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(lean_object* v_s_571_, lean_object* v___x_572_, lean_object* v___x_573_, lean_object* v_a_574_, lean_object* v_b_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_571_, v___x_572_, v___x_573_, v_a_574_, v_b_575_);
lean_dec_ref(v___x_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v___x_582_; 
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_x_580_);
return v___x_582_;
}
else
{
lean_object* v_head_583_; lean_object* v_tail_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_597_; 
v_head_583_ = lean_ctor_get(v_x_581_, 0);
v_tail_584_ = lean_ctor_get(v_x_581_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_597_ == 0)
{
v___x_586_ = v_x_581_;
v_isShared_587_ = v_isSharedCheck_597_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_tail_584_);
lean_inc(v_head_583_);
lean_dec(v_x_581_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_597_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_string_utf8_byte_size(v_head_583_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_nat_dec_eq(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_591_ = l_Lake_stringToLegalOrSimpleName(v_head_583_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 4);
lean_ctor_set(v___x_586_, 1, v___x_591_);
lean_ctor_set(v___x_586_, 0, v_x_580_);
v___x_593_ = v___x_586_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_x_580_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_591_);
v___x_593_ = v_reuseFailAlloc_595_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
v_x_580_ = v___x_593_;
v_x_581_ = v_tail_584_;
goto _start;
}
}
else
{
lean_object* v___x_596_; 
lean_del_object(v___x_586_);
lean_dec(v_tail_584_);
lean_dec(v_head_583_);
lean_dec_ref(v_x_580_);
v___x_596_ = ((lean_object*)(l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1));
return v___x_596_;
}
}
}
}
}
static lean_object* _init_l_Lake_PartialBuildKey_parse___closed__4(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_603_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__3));
v___x_604_ = lean_unsigned_to_nat(4u);
v___x_605_ = lean_unsigned_to_nat(65u);
v___x_606_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__2));
v___x_607_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__1));
v___x_608_ = l_mkPanicMessageWithDecl(v___x_607_, v___x_606_, v___x_605_, v___x_604_, v___x_603_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_parse(lean_object* v_s_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_string_utf8_byte_size(v_s_612_);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_dec_eq(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_inc_ref(v_s_612_);
v___x_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_616_, 0, v_s_612_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
lean_ctor_set(v___x_616_, 2, v___x_613_);
v___x_617_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___closed__0);
v___x_618_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__0));
v___x_619_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_612_, v___x_616_, v___x_613_, v___x_617_, v___x_618_);
lean_dec_ref_known(v___x_616_, 3);
v___x_620_ = lean_array_to_list(v___x_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l_Lake_PartialBuildKey_parse___closed__4, &l_Lake_PartialBuildKey_parse___closed__4_once, _init_l_Lake_PartialBuildKey_parse___closed__4);
v___x_622_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_621_);
return v___x_622_;
}
else
{
lean_object* v_head_623_; lean_object* v_tail_624_; lean_object* v___x_625_; 
v_head_623_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_head_623_);
v_tail_624_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_tail_624_);
lean_dec_ref_known(v___x_620_, 2);
v___x_625_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_623_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_dec(v_tail_624_);
return v___x_625_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(v_a_626_, v_tail_624_);
return v___x_627_;
}
}
}
else
{
lean_object* v___x_628_; 
lean_dec_ref(v_s_612_);
v___x_628_ = ((lean_object*)(l_Lake_PartialBuildKey_parse___closed__6));
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(lean_object* v_s_629_, lean_object* v___x_630_, lean_object* v___x_631_, lean_object* v_inst_632_, lean_object* v_R_633_, lean_object* v_a_634_, lean_object* v_b_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_629_, v___x_630_, v___x_631_, v_a_634_, v_b_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(lean_object* v_s_637_, lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v_inst_640_, lean_object* v_R_641_, lean_object* v_a_642_, lean_object* v_b_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_637_, v___x_638_, v___x_639_, v_inst_640_, v_R_641_, v_a_642_, v_b_643_);
lean_dec_ref(v___x_638_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(lean_object* v_p_645_){
_start:
{
if (lean_obj_tag(v_p_645_) == 2)
{
lean_object* v_pre_646_; 
v_pre_646_ = lean_ctor_get(v_p_645_, 0);
lean_inc(v_pre_646_);
return v_pre_646_;
}
else
{
lean_inc(v_p_645_);
return v_p_645_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(lean_object* v_p_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_647_);
lean_dec(v_p_647_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lake_PartialBuildKey_toString(lean_object* v_x_652_){
_start:
{
lean_object* v___y_654_; 
switch(lean_obj_tag(v_x_652_))
{
case 0:
{
lean_object* v_module_660_; lean_object* v___x_661_; uint8_t v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_module_660_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_module_660_);
lean_dec_ref_known(v_x_652_, 1);
v___x_661_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_662_ = 1;
v___x_663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_660_, v___x_662_);
v___x_664_ = lean_string_append(v___x_661_, v___x_663_);
lean_dec_ref(v___x_663_);
return v___x_664_;
}
case 1:
{
lean_object* v_package_665_; 
v_package_665_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_package_665_);
lean_dec_ref_known(v_x_652_, 1);
if (lean_obj_tag(v_package_665_) == 2)
{
lean_object* v_pre_666_; 
v_pre_666_ = lean_ctor_get(v_package_665_, 0);
lean_inc(v_pre_666_);
lean_dec_ref_known(v_package_665_, 2);
v___y_654_ = v_pre_666_;
goto v___jp_653_;
}
else
{
v___y_654_ = v_package_665_;
goto v___jp_653_;
}
}
case 2:
{
lean_object* v_package_667_; lean_object* v_module_668_; lean_object* v___y_670_; 
v_package_667_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_package_667_);
v_module_668_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_module_668_);
lean_dec_ref_known(v_x_652_, 2);
if (lean_obj_tag(v_package_667_) == 2)
{
lean_object* v_pre_681_; 
v_pre_681_ = lean_ctor_get(v_package_667_, 0);
lean_inc(v_pre_681_);
lean_dec_ref_known(v_package_667_, 2);
v___y_670_ = v_pre_681_;
goto v___jp_669_;
}
else
{
v___y_670_ = v_package_667_;
goto v___jp_669_;
}
v___jp_669_:
{
if (lean_obj_tag(v___y_670_) == 0)
{
lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_671_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_672_ = 1;
v___x_673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_668_, v___x_672_);
v___x_674_ = lean_string_append(v___x_671_, v___x_673_);
lean_dec_ref(v___x_673_);
return v___x_674_;
}
else
{
uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_675_ = 1;
v___x_676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_670_, v___x_675_);
v___x_677_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_678_ = lean_string_append(v___x_676_, v___x_677_);
v___x_679_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_668_, v___x_675_);
v___x_680_ = lean_string_append(v___x_678_, v___x_679_);
lean_dec_ref(v___x_679_);
return v___x_680_;
}
}
}
case 3:
{
lean_object* v_package_682_; lean_object* v_target_683_; lean_object* v___y_685_; 
v_package_682_ = lean_ctor_get(v_x_652_, 0);
lean_inc(v_package_682_);
v_target_683_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_target_683_);
lean_dec_ref_known(v_x_652_, 2);
if (lean_obj_tag(v_package_682_) == 2)
{
lean_object* v_pre_694_; 
v_pre_694_ = lean_ctor_get(v_package_682_, 0);
lean_inc(v_pre_694_);
lean_dec_ref_known(v_package_682_, 2);
v___y_685_ = v_pre_694_;
goto v___jp_684_;
}
else
{
v___y_685_ = v_package_682_;
goto v___jp_684_;
}
v___jp_684_:
{
if (lean_obj_tag(v___y_685_) == 0)
{
uint8_t v___x_686_; lean_object* v___x_687_; 
v___x_686_ = 1;
v___x_687_ = l_Lean_Name_toString(v_target_683_, v___x_686_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_688_ = 1;
v___x_689_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_685_, v___x_688_);
v___x_690_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_691_ = lean_string_append(v___x_689_, v___x_690_);
v___x_692_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_683_, v___x_688_);
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
lean_dec_ref(v___x_692_);
return v___x_693_;
}
}
}
default: 
{
lean_object* v_target_695_; lean_object* v_facet_696_; uint8_t v___x_697_; 
v_target_695_ = lean_ctor_get(v_x_652_, 0);
lean_inc_ref(v_target_695_);
v_facet_696_ = lean_ctor_get(v_x_652_, 1);
lean_inc(v_facet_696_);
lean_dec_ref_known(v_x_652_, 2);
v___x_697_ = l_Lean_Name_isAnonymous(v_facet_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_698_ = l_Lake_PartialBuildKey_toString(v_target_695_);
v___x_699_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
v___x_701_ = 1;
v___x_702_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_facet_696_, v___x_701_);
v___x_703_ = lean_string_append(v___x_700_, v___x_702_);
lean_dec_ref(v___x_702_);
return v___x_703_;
}
else
{
lean_dec(v_facet_696_);
v_x_652_ = v_target_695_;
goto _start;
}
}
}
v___jp_653_:
{
if (lean_obj_tag(v___y_654_) == 0)
{
lean_object* v___x_655_; 
v___x_655_ = ((lean_object*)(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0));
return v___x_655_;
}
else
{
lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_657_ = 1;
v___x_658_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___y_654_, v___x_657_);
v___x_659_ = lean_string_append(v___x_656_, v___x_658_);
lean_dec_ref(v___x_658_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_moduleFacet(lean_object* v_module_707_, lean_object* v_facet_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_module_707_);
v___x_710_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_facet_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageFacet(lean_object* v_package_711_, lean_object* v_facet_712_){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v_package_711_);
v___x_714_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_facet_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_packageModuleFacet(lean_object* v_package_715_, lean_object* v_module_716_, lean_object* v_facet_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v_package_715_);
lean_ctor_set(v___x_718_, 1, v_module_716_);
v___x_719_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_facet_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_targetFacet(lean_object* v_package_720_, lean_object* v_target_721_, lean_object* v_facet_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_723_, 0, v_package_720_);
lean_ctor_set(v___x_723_, 1, v_target_721_);
v___x_724_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_facet_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_customTarget(lean_object* v_package_725_, lean_object* v_target_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_727_, 0, v_package_725_);
lean_ctor_set(v___x_727_, 1, v_target_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toString(lean_object* v_x_728_){
_start:
{
switch(lean_obj_tag(v_x_728_))
{
case 0:
{
lean_object* v_module_729_; lean_object* v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_module_729_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_module_729_);
lean_dec_ref_known(v_x_728_, 1);
v___x_730_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0));
v___x_731_ = 1;
v___x_732_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_729_, v___x_731_);
v___x_733_ = lean_string_append(v___x_730_, v___x_732_);
lean_dec_ref(v___x_732_);
return v___x_733_;
}
case 1:
{
lean_object* v_package_734_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_package_734_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_package_734_);
lean_dec_ref_known(v_x_728_, 1);
v___x_735_ = ((lean_object*)(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5));
v___x_736_ = l_Lean_Name_getPrefix(v_package_734_);
lean_dec(v_package_734_);
v___x_737_ = 1;
v___x_738_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_736_, v___x_737_);
v___x_739_ = lean_string_append(v___x_735_, v___x_738_);
lean_dec_ref(v___x_738_);
return v___x_739_;
}
case 2:
{
lean_object* v_package_740_; lean_object* v_module_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_package_740_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_package_740_);
v_module_741_ = lean_ctor_get(v_x_728_, 1);
lean_inc(v_module_741_);
lean_dec_ref_known(v_x_728_, 2);
v___x_742_ = l_Lean_Name_getPrefix(v_package_740_);
lean_dec(v_package_740_);
v___x_743_ = 1;
v___x_744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_742_, v___x_743_);
v___x_745_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__0));
v___x_746_ = lean_string_append(v___x_744_, v___x_745_);
v___x_747_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_741_, v___x_743_);
v___x_748_ = lean_string_append(v___x_746_, v___x_747_);
lean_dec_ref(v___x_747_);
return v___x_748_;
}
case 3:
{
lean_object* v_package_749_; lean_object* v_target_750_; lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_package_749_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_package_749_);
v_target_750_ = lean_ctor_get(v_x_728_, 1);
lean_inc(v_target_750_);
lean_dec_ref_known(v_x_728_, 2);
v___x_751_ = l_Lean_Name_getPrefix(v_package_749_);
lean_dec(v_package_749_);
v___x_752_ = 1;
v___x_753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_751_, v___x_752_);
v___x_754_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_755_ = lean_string_append(v___x_753_, v___x_754_);
v___x_756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_target_750_, v___x_752_);
v___x_757_ = lean_string_append(v___x_755_, v___x_756_);
lean_dec_ref(v___x_756_);
return v___x_757_;
}
default: 
{
lean_object* v_target_758_; lean_object* v_facet_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_target_758_ = lean_ctor_get(v_x_728_, 0);
lean_inc_ref(v_target_758_);
v_facet_759_ = lean_ctor_get(v_x_728_, 1);
lean_inc(v_facet_759_);
lean_dec_ref_known(v_x_728_, 2);
v___x_760_ = l_Lake_BuildKey_toString(v_target_758_);
v___x_761_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_762_ = lean_string_append(v___x_760_, v___x_761_);
v___x_763_ = l_Lake_Name_eraseHead(v_facet_759_);
v___x_764_ = 1;
v___x_765_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_763_, v___x_764_);
v___x_766_ = lean_string_append(v___x_762_, v___x_765_);
lean_dec_ref(v___x_765_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_toSimpleString(lean_object* v_x_767_){
_start:
{
lean_object* v_p_769_; lean_object* v_m_770_; 
switch(lean_obj_tag(v_x_767_))
{
case 0:
{
lean_object* v_module_778_; uint8_t v___x_779_; lean_object* v___x_780_; 
v_module_778_ = lean_ctor_get(v_x_767_, 0);
lean_inc(v_module_778_);
lean_dec_ref_known(v_x_767_, 1);
v___x_779_ = 1;
v___x_780_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_778_, v___x_779_);
return v___x_780_;
}
case 1:
{
lean_object* v_package_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; 
v_package_781_ = lean_ctor_get(v_x_767_, 0);
lean_inc(v_package_781_);
lean_dec_ref_known(v_x_767_, 1);
v___x_782_ = l_Lean_Name_getPrefix(v_package_781_);
lean_dec(v_package_781_);
v___x_783_ = 1;
v___x_784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_782_, v___x_783_);
return v___x_784_;
}
case 4:
{
lean_object* v_target_785_; lean_object* v_facet_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_target_785_ = lean_ctor_get(v_x_767_, 0);
lean_inc_ref(v_target_785_);
v_facet_786_ = lean_ctor_get(v_x_767_, 1);
lean_inc(v_facet_786_);
lean_dec_ref_known(v_x_767_, 2);
v___x_787_ = l_Lake_BuildKey_toSimpleString(v_target_785_);
v___x_788_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__2));
v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
v___x_790_ = l_Lake_Name_eraseHead(v_facet_786_);
v___x_791_ = 1;
v___x_792_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_790_, v___x_791_);
v___x_793_ = lean_string_append(v___x_789_, v___x_792_);
lean_dec_ref(v___x_792_);
return v___x_793_;
}
default: 
{
lean_object* v_package_794_; lean_object* v_module_795_; 
v_package_794_ = lean_ctor_get(v_x_767_, 0);
lean_inc(v_package_794_);
v_module_795_ = lean_ctor_get(v_x_767_, 1);
lean_inc(v_module_795_);
lean_dec_ref(v_x_767_);
v_p_769_ = v_package_794_;
v_m_770_ = v_module_795_;
goto v___jp_768_;
}
}
v___jp_768_:
{
lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_771_ = l_Lean_Name_getPrefix(v_p_769_);
lean_dec(v_p_769_);
v___x_772_ = 1;
v___x_773_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_771_, v___x_772_);
v___x_774_ = ((lean_object*)(l_Lake_PartialBuildKey_toString___closed__1));
v___x_775_ = lean_string_append(v___x_773_, v___x_774_);
v___x_776_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_m_770_, v___x_772_);
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
lean_dec_ref(v___x_776_);
return v___x_777_;
}
}
}
uint8_t l_Lake_BuildKey_quickCmp(lean_object* v_k_798_, lean_object* v_k_x27_799_){
_start:
{
switch(lean_obj_tag(v_k_798_))
{
case 0:
{
if (lean_obj_tag(v_k_x27_799_) == 0)
{
lean_object* v_module_800_; lean_object* v_module_801_; uint8_t v___x_802_; 
v_module_800_ = lean_ctor_get(v_k_798_, 0);
v_module_801_ = lean_ctor_get(v_k_x27_799_, 0);
v___x_802_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_800_, v_module_801_);
return v___x_802_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
}
case 1:
{
switch(lean_obj_tag(v_k_x27_799_))
{
case 0:
{
uint8_t v___x_804_; 
v___x_804_ = 2;
return v___x_804_;
}
case 1:
{
lean_object* v_package_805_; lean_object* v_package_806_; uint8_t v___x_807_; 
v_package_805_ = lean_ctor_get(v_k_798_, 0);
v_package_806_ = lean_ctor_get(v_k_x27_799_, 0);
v___x_807_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_805_, v_package_806_);
return v___x_807_;
}
default: 
{
uint8_t v___x_808_; 
v___x_808_ = 0;
return v___x_808_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_k_x27_799_))
{
case 4:
{
uint8_t v___x_809_; 
v___x_809_ = 0;
return v___x_809_;
}
case 3:
{
uint8_t v___x_810_; 
v___x_810_ = 0;
return v___x_810_;
}
case 2:
{
lean_object* v_package_811_; lean_object* v_module_812_; lean_object* v_package_813_; lean_object* v_module_814_; uint8_t v___x_815_; 
v_package_811_ = lean_ctor_get(v_k_798_, 0);
v_module_812_ = lean_ctor_get(v_k_798_, 1);
v_package_813_ = lean_ctor_get(v_k_x27_799_, 0);
v_module_814_ = lean_ctor_get(v_k_x27_799_, 1);
v___x_815_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_module_812_, v_module_814_);
if (v___x_815_ == 1)
{
uint8_t v___x_816_; 
v___x_816_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_811_, v_package_813_);
return v___x_816_;
}
else
{
return v___x_815_;
}
}
default: 
{
uint8_t v___x_817_; 
v___x_817_ = 2;
return v___x_817_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_k_x27_799_))
{
case 4:
{
uint8_t v___x_818_; 
v___x_818_ = 0;
return v___x_818_;
}
case 3:
{
lean_object* v_package_819_; lean_object* v_target_820_; lean_object* v_package_821_; lean_object* v_target_822_; uint8_t v___x_823_; 
v_package_819_ = lean_ctor_get(v_k_798_, 0);
v_target_820_ = lean_ctor_get(v_k_798_, 1);
v_package_821_ = lean_ctor_get(v_k_x27_799_, 0);
v_target_822_ = lean_ctor_get(v_k_x27_799_, 1);
v___x_823_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_package_819_, v_package_821_);
if (v___x_823_ == 1)
{
uint8_t v___x_824_; 
v___x_824_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_target_820_, v_target_822_);
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
default: 
{
if (lean_obj_tag(v_k_x27_799_) == 4)
{
lean_object* v_target_826_; lean_object* v_facet_827_; lean_object* v_target_828_; lean_object* v_facet_829_; uint8_t v___x_830_; 
v_target_826_ = lean_ctor_get(v_k_798_, 0);
v_facet_827_ = lean_ctor_get(v_k_798_, 1);
v_target_828_ = lean_ctor_get(v_k_x27_799_, 0);
v_facet_829_ = lean_ctor_get(v_k_x27_799_, 1);
v___x_830_ = l_Lake_BuildKey_quickCmp(v_target_826_, v_target_828_);
if (v___x_830_ == 1)
{
uint8_t v___x_831_; 
v___x_831_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_facet_827_, v_facet_829_);
return v___x_831_;
}
else
{
return v___x_830_;
}
}
else
{
uint8_t v___x_832_; 
v___x_832_ = 2;
return v___x_832_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_BuildKey_quickCmp_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_798_ = stack[0].m_obj;
lean_object* v_k_x27_799_ = stack[1].m_obj;
uint8_t v_res_833_;
v_res_833_ = l_Lake_BuildKey_quickCmp(v_k_798_, v_k_x27_799_);
stack->m_num = v_res_833_;
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
lean_dec_ref_known(v_x_838_, 1);
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
lean_dec_ref_known(v_x_838_, 1);
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
lean_dec_ref_known(v_x_838_, 2);
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
lean_dec_ref_known(v_x_838_, 2);
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
lean_dec_ref_known(v_x_838_, 2);
v___x_856_ = lean_apply_2(v_h__5_843_, v_target_854_, v_facet_855_);
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(lean_object* v_motive_857_, lean_object* v_x_858_, lean_object* v_h__1_859_, lean_object* v_h__2_860_, lean_object* v_h__3_861_, lean_object* v_h__4_862_, lean_object* v_h__5_863_){
_start:
{
switch(lean_obj_tag(v_x_858_))
{
case 0:
{
lean_object* v_module_864_; lean_object* v___x_865_; 
lean_dec(v_h__5_863_);
lean_dec(v_h__4_862_);
lean_dec(v_h__3_861_);
lean_dec(v_h__2_860_);
v_module_864_ = lean_ctor_get(v_x_858_, 0);
lean_inc(v_module_864_);
lean_dec_ref_known(v_x_858_, 1);
v___x_865_ = lean_apply_1(v_h__1_859_, v_module_864_);
return v___x_865_;
}
case 1:
{
lean_object* v_package_866_; lean_object* v___x_867_; 
lean_dec(v_h__5_863_);
lean_dec(v_h__4_862_);
lean_dec(v_h__3_861_);
lean_dec(v_h__1_859_);
v_package_866_ = lean_ctor_get(v_x_858_, 0);
lean_inc(v_package_866_);
lean_dec_ref_known(v_x_858_, 1);
v___x_867_ = lean_apply_1(v_h__2_860_, v_package_866_);
return v___x_867_;
}
case 2:
{
lean_object* v_package_868_; lean_object* v_module_869_; lean_object* v___x_870_; 
lean_dec(v_h__5_863_);
lean_dec(v_h__4_862_);
lean_dec(v_h__2_860_);
lean_dec(v_h__1_859_);
v_package_868_ = lean_ctor_get(v_x_858_, 0);
lean_inc(v_package_868_);
v_module_869_ = lean_ctor_get(v_x_858_, 1);
lean_inc(v_module_869_);
lean_dec_ref_known(v_x_858_, 2);
v___x_870_ = lean_apply_2(v_h__3_861_, v_package_868_, v_module_869_);
return v___x_870_;
}
case 3:
{
lean_object* v_package_871_; lean_object* v_target_872_; lean_object* v___x_873_; 
lean_dec(v_h__5_863_);
lean_dec(v_h__3_861_);
lean_dec(v_h__2_860_);
lean_dec(v_h__1_859_);
v_package_871_ = lean_ctor_get(v_x_858_, 0);
lean_inc(v_package_871_);
v_target_872_ = lean_ctor_get(v_x_858_, 1);
lean_inc(v_target_872_);
lean_dec_ref_known(v_x_858_, 2);
v___x_873_ = lean_apply_2(v_h__4_862_, v_package_871_, v_target_872_);
return v___x_873_;
}
default: 
{
lean_object* v_target_874_; lean_object* v_facet_875_; lean_object* v___x_876_; 
lean_dec(v_h__4_862_);
lean_dec(v_h__3_861_);
lean_dec(v_h__2_860_);
lean_dec(v_h__1_859_);
v_target_874_ = lean_ctor_get(v_x_858_, 0);
lean_inc_ref(v_target_874_);
v_facet_875_ = lean_ctor_get(v_x_858_, 1);
lean_inc(v_facet_875_);
lean_dec_ref_known(v_x_858_, 2);
v___x_876_ = lean_apply_2(v_h__5_863_, v_target_874_, v_facet_875_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(lean_object* v_k_x27_877_, lean_object* v_h__1_878_, lean_object* v_h__2_879_){
_start:
{
if (lean_obj_tag(v_k_x27_877_) == 0)
{
lean_object* v_module_880_; lean_object* v___x_881_; 
lean_dec(v_h__2_879_);
v_module_880_ = lean_ctor_get(v_k_x27_877_, 0);
lean_inc(v_module_880_);
lean_dec_ref_known(v_k_x27_877_, 1);
v___x_881_ = lean_apply_1(v_h__1_878_, v_module_880_);
return v___x_881_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v_h__1_878_);
v___x_882_ = lean_apply_2(v_h__2_879_, v_k_x27_877_, lean_box(0));
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(lean_object* v_motive_883_, lean_object* v_k_x27_884_, lean_object* v_h__1_885_, lean_object* v_h__2_886_){
_start:
{
if (lean_obj_tag(v_k_x27_884_) == 0)
{
lean_object* v_module_887_; lean_object* v___x_888_; 
lean_dec(v_h__2_886_);
v_module_887_ = lean_ctor_get(v_k_x27_884_, 0);
lean_inc(v_module_887_);
lean_dec_ref_known(v_k_x27_884_, 1);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(lean_object* v_k_x27_890_, lean_object* v_h__1_891_, lean_object* v_h__2_892_, lean_object* v_h__3_893_){
_start:
{
switch(lean_obj_tag(v_k_x27_890_))
{
case 0:
{
lean_object* v_module_894_; lean_object* v___x_895_; 
lean_dec(v_h__3_893_);
lean_dec(v_h__2_892_);
v_module_894_ = lean_ctor_get(v_k_x27_890_, 0);
lean_inc(v_module_894_);
lean_dec_ref_known(v_k_x27_890_, 1);
v___x_895_ = lean_apply_1(v_h__1_891_, v_module_894_);
return v___x_895_;
}
case 1:
{
lean_object* v_package_896_; lean_object* v___x_897_; 
lean_dec(v_h__3_893_);
lean_dec(v_h__1_891_);
v_package_896_ = lean_ctor_get(v_k_x27_890_, 0);
lean_inc(v_package_896_);
lean_dec_ref_known(v_k_x27_890_, 1);
v___x_897_ = lean_apply_1(v_h__2_892_, v_package_896_);
return v___x_897_;
}
default: 
{
lean_object* v___x_898_; 
lean_dec(v_h__2_892_);
lean_dec(v_h__1_891_);
v___x_898_ = lean_apply_3(v_h__3_893_, v_k_x27_890_, lean_box(0), lean_box(0));
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(lean_object* v_motive_899_, lean_object* v_k_x27_900_, lean_object* v_h__1_901_, lean_object* v_h__2_902_, lean_object* v_h__3_903_){
_start:
{
switch(lean_obj_tag(v_k_x27_900_))
{
case 0:
{
lean_object* v_module_904_; lean_object* v___x_905_; 
lean_dec(v_h__3_903_);
lean_dec(v_h__2_902_);
v_module_904_ = lean_ctor_get(v_k_x27_900_, 0);
lean_inc(v_module_904_);
lean_dec_ref_known(v_k_x27_900_, 1);
v___x_905_ = lean_apply_1(v_h__1_901_, v_module_904_);
return v___x_905_;
}
case 1:
{
lean_object* v_package_906_; lean_object* v___x_907_; 
lean_dec(v_h__3_903_);
lean_dec(v_h__1_901_);
v_package_906_ = lean_ctor_get(v_k_x27_900_, 0);
lean_inc(v_package_906_);
lean_dec_ref_known(v_k_x27_900_, 1);
v___x_907_ = lean_apply_1(v_h__2_902_, v_package_906_);
return v___x_907_;
}
default: 
{
lean_object* v___x_908_; 
lean_dec(v_h__2_902_);
lean_dec(v_h__1_901_);
v___x_908_ = lean_apply_3(v_h__3_903_, v_k_x27_900_, lean_box(0), lean_box(0));
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(lean_object* v_k_x27_909_, lean_object* v_h__1_910_, lean_object* v_h__2_911_, lean_object* v_h__3_912_, lean_object* v_h__4_913_){
_start:
{
switch(lean_obj_tag(v_k_x27_909_))
{
case 4:
{
lean_object* v_target_914_; lean_object* v_facet_915_; lean_object* v___x_916_; 
lean_dec(v_h__4_913_);
lean_dec(v_h__3_912_);
lean_dec(v_h__2_911_);
v_target_914_ = lean_ctor_get(v_k_x27_909_, 0);
lean_inc_ref(v_target_914_);
v_facet_915_ = lean_ctor_get(v_k_x27_909_, 1);
lean_inc(v_facet_915_);
lean_dec_ref_known(v_k_x27_909_, 2);
v___x_916_ = lean_apply_2(v_h__1_910_, v_target_914_, v_facet_915_);
return v___x_916_;
}
case 3:
{
lean_object* v_package_917_; lean_object* v_target_918_; lean_object* v___x_919_; 
lean_dec(v_h__4_913_);
lean_dec(v_h__3_912_);
lean_dec(v_h__1_910_);
v_package_917_ = lean_ctor_get(v_k_x27_909_, 0);
lean_inc(v_package_917_);
v_target_918_ = lean_ctor_get(v_k_x27_909_, 1);
lean_inc(v_target_918_);
lean_dec_ref_known(v_k_x27_909_, 2);
v___x_919_ = lean_apply_2(v_h__2_911_, v_package_917_, v_target_918_);
return v___x_919_;
}
case 2:
{
lean_object* v_package_920_; lean_object* v_module_921_; lean_object* v___x_922_; 
lean_dec(v_h__4_913_);
lean_dec(v_h__2_911_);
lean_dec(v_h__1_910_);
v_package_920_ = lean_ctor_get(v_k_x27_909_, 0);
lean_inc(v_package_920_);
v_module_921_ = lean_ctor_get(v_k_x27_909_, 1);
lean_inc(v_module_921_);
lean_dec_ref_known(v_k_x27_909_, 2);
v___x_922_ = lean_apply_2(v_h__3_912_, v_package_920_, v_module_921_);
return v___x_922_;
}
default: 
{
lean_object* v___x_923_; 
lean_dec(v_h__3_912_);
lean_dec(v_h__2_911_);
lean_dec(v_h__1_910_);
v___x_923_ = lean_apply_4(v_h__4_913_, v_k_x27_909_, lean_box(0), lean_box(0), lean_box(0));
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(lean_object* v_motive_924_, lean_object* v_k_x27_925_, lean_object* v_h__1_926_, lean_object* v_h__2_927_, lean_object* v_h__3_928_, lean_object* v_h__4_929_){
_start:
{
switch(lean_obj_tag(v_k_x27_925_))
{
case 4:
{
lean_object* v_target_930_; lean_object* v_facet_931_; lean_object* v___x_932_; 
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
v_target_930_ = lean_ctor_get(v_k_x27_925_, 0);
lean_inc_ref(v_target_930_);
v_facet_931_ = lean_ctor_get(v_k_x27_925_, 1);
lean_inc(v_facet_931_);
lean_dec_ref_known(v_k_x27_925_, 2);
v___x_932_ = lean_apply_2(v_h__1_926_, v_target_930_, v_facet_931_);
return v___x_932_;
}
case 3:
{
lean_object* v_package_933_; lean_object* v_target_934_; lean_object* v___x_935_; 
lean_dec(v_h__4_929_);
lean_dec(v_h__3_928_);
lean_dec(v_h__1_926_);
v_package_933_ = lean_ctor_get(v_k_x27_925_, 0);
lean_inc(v_package_933_);
v_target_934_ = lean_ctor_get(v_k_x27_925_, 1);
lean_inc(v_target_934_);
lean_dec_ref_known(v_k_x27_925_, 2);
v___x_935_ = lean_apply_2(v_h__2_927_, v_package_933_, v_target_934_);
return v___x_935_;
}
case 2:
{
lean_object* v_package_936_; lean_object* v_module_937_; lean_object* v___x_938_; 
lean_dec(v_h__4_929_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v_package_936_ = lean_ctor_get(v_k_x27_925_, 0);
lean_inc(v_package_936_);
v_module_937_ = lean_ctor_get(v_k_x27_925_, 1);
lean_inc(v_module_937_);
lean_dec_ref_known(v_k_x27_925_, 2);
v___x_938_ = lean_apply_2(v_h__3_928_, v_package_936_, v_module_937_);
return v___x_938_;
}
default: 
{
lean_object* v___x_939_; 
lean_dec(v_h__3_928_);
lean_dec(v_h__2_927_);
lean_dec(v_h__1_926_);
v___x_939_ = lean_apply_4(v_h__4_929_, v_k_x27_925_, lean_box(0), lean_box(0), lean_box(0));
return v___x_939_;
}
}
}
}
lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(uint8_t v_x_940_, lean_object* v_h__1_941_, lean_object* v_h__2_942_){
_start:
{
if (v_x_940_ == 1)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_h__2_942_);
v___x_943_ = lean_box(0);
v___x_944_ = lean_apply_1(v_h__1_941_, v___x_943_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_h__1_941_);
v___x_945_ = lean_box(v_x_940_);
v___x_946_ = lean_apply_2(v_h__2_942_, v___x_945_, lean_box(0));
return v___x_946_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_940_ = stack[0].m_num;
lean_object* v_h__1_941_ = stack[1].m_obj;
lean_object* v_h__2_942_ = stack[2].m_obj;
lean_object* v_res_947_;
v_res_947_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_940_, v_h__1_941_, v_h__2_942_);
stack->m_obj
 = v_res_947_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(lean_object* v_x_948_, lean_object* v_h__1_949_, lean_object* v_h__2_950_){
_start:
{
uint8_t v_x_13__boxed_951_; lean_object* v_res_952_; 
v_x_13__boxed_951_ = lean_unbox(v_x_948_);
v_res_952_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(v_x_13__boxed_951_, v_h__1_949_, v_h__2_950_);
return v_res_952_;
}
}
lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_object* v_motive_953_, uint8_t v_x_954_, lean_object* v_h__1_955_, lean_object* v_h__2_956_){
_start:
{
if (v_x_954_ == 1)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_h__2_956_);
v___x_957_ = lean_box(0);
v___x_958_ = lean_apply_1(v_h__1_955_, v___x_957_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v_h__1_955_);
v___x_959_ = lean_box(v_x_954_);
v___x_960_ = lean_apply_2(v_h__2_956_, v___x_959_, lean_box(0));
return v___x_960_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_954_ = stack[1].m_num;
lean_object* v_h__1_955_ = stack[2].m_obj;
lean_object* v_h__2_956_ = stack[3].m_obj;
lean_object* v_res_961_;
v_res_961_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(lean_box(0), v_x_954_, v_h__1_955_, v_h__2_956_);
stack->m_obj
 = v_res_961_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(lean_object* v_motive_962_, lean_object* v_x_963_, lean_object* v_h__1_964_, lean_object* v_h__2_965_){
_start:
{
uint8_t v_x_30__boxed_966_; lean_object* v_res_967_; 
v_x_30__boxed_966_ = lean_unbox(v_x_963_);
v_res_967_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(v_motive_962_, v_x_30__boxed_966_, v_h__1_964_, v_h__2_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(lean_object* v_k_x27_968_, lean_object* v_h__1_969_, lean_object* v_h__2_970_, lean_object* v_h__3_971_){
_start:
{
switch(lean_obj_tag(v_k_x27_968_))
{
case 4:
{
lean_object* v_target_972_; lean_object* v_facet_973_; lean_object* v___x_974_; 
lean_dec(v_h__3_971_);
lean_dec(v_h__2_970_);
v_target_972_ = lean_ctor_get(v_k_x27_968_, 0);
lean_inc_ref(v_target_972_);
v_facet_973_ = lean_ctor_get(v_k_x27_968_, 1);
lean_inc(v_facet_973_);
lean_dec_ref_known(v_k_x27_968_, 2);
v___x_974_ = lean_apply_2(v_h__1_969_, v_target_972_, v_facet_973_);
return v___x_974_;
}
case 3:
{
lean_object* v_package_975_; lean_object* v_target_976_; lean_object* v___x_977_; 
lean_dec(v_h__3_971_);
lean_dec(v_h__1_969_);
v_package_975_ = lean_ctor_get(v_k_x27_968_, 0);
lean_inc(v_package_975_);
v_target_976_ = lean_ctor_get(v_k_x27_968_, 1);
lean_inc(v_target_976_);
lean_dec_ref_known(v_k_x27_968_, 2);
v___x_977_ = lean_apply_2(v_h__2_970_, v_package_975_, v_target_976_);
return v___x_977_;
}
default: 
{
lean_object* v___x_978_; 
lean_dec(v_h__2_970_);
lean_dec(v_h__1_969_);
v___x_978_ = lean_apply_3(v_h__3_971_, v_k_x27_968_, lean_box(0), lean_box(0));
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(lean_object* v_motive_979_, lean_object* v_k_x27_980_, lean_object* v_h__1_981_, lean_object* v_h__2_982_, lean_object* v_h__3_983_){
_start:
{
switch(lean_obj_tag(v_k_x27_980_))
{
case 4:
{
lean_object* v_target_984_; lean_object* v_facet_985_; lean_object* v___x_986_; 
lean_dec(v_h__3_983_);
lean_dec(v_h__2_982_);
v_target_984_ = lean_ctor_get(v_k_x27_980_, 0);
lean_inc_ref(v_target_984_);
v_facet_985_ = lean_ctor_get(v_k_x27_980_, 1);
lean_inc(v_facet_985_);
lean_dec_ref_known(v_k_x27_980_, 2);
v___x_986_ = lean_apply_2(v_h__1_981_, v_target_984_, v_facet_985_);
return v___x_986_;
}
case 3:
{
lean_object* v_package_987_; lean_object* v_target_988_; lean_object* v___x_989_; 
lean_dec(v_h__3_983_);
lean_dec(v_h__1_981_);
v_package_987_ = lean_ctor_get(v_k_x27_980_, 0);
lean_inc(v_package_987_);
v_target_988_ = lean_ctor_get(v_k_x27_980_, 1);
lean_inc(v_target_988_);
lean_dec_ref_known(v_k_x27_980_, 2);
v___x_989_ = lean_apply_2(v_h__2_982_, v_package_987_, v_target_988_);
return v___x_989_;
}
default: 
{
lean_object* v___x_990_; 
lean_dec(v_h__2_982_);
lean_dec(v_h__1_981_);
v___x_990_ = lean_apply_3(v_h__3_983_, v_k_x27_980_, lean_box(0), lean_box(0));
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(lean_object* v_k_x27_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_){
_start:
{
if (lean_obj_tag(v_k_x27_991_) == 4)
{
lean_object* v_target_994_; lean_object* v_facet_995_; lean_object* v___x_996_; 
lean_dec(v_h__2_993_);
v_target_994_ = lean_ctor_get(v_k_x27_991_, 0);
lean_inc_ref(v_target_994_);
v_facet_995_ = lean_ctor_get(v_k_x27_991_, 1);
lean_inc(v_facet_995_);
lean_dec_ref_known(v_k_x27_991_, 2);
v___x_996_ = lean_apply_2(v_h__1_992_, v_target_994_, v_facet_995_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; 
lean_dec(v_h__1_992_);
v___x_997_ = lean_apply_2(v_h__2_993_, v_k_x27_991_, lean_box(0));
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(lean_object* v_motive_998_, lean_object* v_k_x27_999_, lean_object* v_h__1_1000_, lean_object* v_h__2_1001_){
_start:
{
if (lean_obj_tag(v_k_x27_999_) == 4)
{
lean_object* v_target_1002_; lean_object* v_facet_1003_; lean_object* v___x_1004_; 
lean_dec(v_h__2_1001_);
v_target_1002_ = lean_ctor_get(v_k_x27_999_, 0);
lean_inc_ref(v_target_1002_);
v_facet_1003_ = lean_ctor_get(v_k_x27_999_, 1);
lean_inc(v_facet_1003_);
lean_dec_ref_known(v_k_x27_999_, 2);
v___x_1004_ = lean_apply_2(v_h__1_1000_, v_target_1002_, v_facet_1003_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; 
lean_dec(v_h__1_1000_);
v___x_1005_ = lean_apply_2(v_h__2_1001_, v_k_x27_999_, lean_box(0));
return v___x_1005_;
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
